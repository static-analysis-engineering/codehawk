(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:
 
   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.
  
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

(* chlib *)
open CHLanguage 
open CHUtils
open CHPretty

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil
open CHXmlDocument
   
(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI
open JCHPreFileIO
open JCHTaintOrigin

open JCHGlobals
open JCHSystemUtils
open JCHPrintUtils

module H = Hashtbl


let dbg = ref false

(* Depending on the node_type, nodes encode type of taint on 
 * variables and static fields or the the type of transmission of
 * taint such as in object -> field, length -> array *)
class taint_node_t ~(index:int) ~(nodetype:taint_node_type_t):taint_node_int =
object (self:'a)

  val index = index
  val node_type = nodetype

  val mutable untrusted_origins = JCHTaintOrigin.mk_taint_origin_set []
  val mutable stub_untrusted = None

  (* cfsix -> taint_origin_set. 
   * The taint of a field that is not listed is untrusted_origins *)
  val mutable field_untrusted_origins =  new IntCollections.table_t 
  val mutable size_untrusted_origins = JCHTaintOrigin.mk_taint_origin_set [] 

  method set_stub_untrusted (name:symbol_t) = stub_untrusted <- Some name
                                            
  method get_stub_untrusted = stub_untrusted

  method get_node_type = node_type
                       
  method get_index = index
                   
  method compare (a:'a) = Stdlib.compare self#get_index a#get_index

  method is_field =
    match node_type with TN_FIELD _ -> true | _ -> false

  method is_var =
    match node_type with TN_VAR _ -> true | _ -> false

  method is_size =
    match node_type with TN_SIZE _ -> true | _ -> false

  method is_obj_field =
    match node_type with TN_OBJECT_FIELD _ -> true | _ -> false

  method is_ref_equal =
    match node_type with TN_REF_EQUAL -> true | _ -> false
      
  method is_conditional =
    match node_type with TN_CONDITIONAL _ -> true | _ -> false

  method get_var =
    match node_type with
    | TN_VAR (_,v,_) -> v
    | _ ->
       raise (JCH_failure (LBLOCK [ STR "taint_node: not a VAR: " ; self#toPretty ]))

  method is_bool_var =
    match node_type with
    | TN_VAR (cmsix, v, _) ->
       let proc_name = make_procname cmsix in
       begin
         try (* the proc_name might not be in the system *)
           let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
           List.for_all JCHTypeUtils.is_bool (jproc_info#get_jvar_info v)#get_types
         with _ -> false
       end
    | _ -> false

  method is_loop_counter_var =
    match node_type with
    | TN_VAR (_,v,_) -> JCHSystemUtils.is_loop_counter v
    | _ -> false

  method is_const_var =
    match node_type with
    | TN_VAR (_,v,_) -> JCHSystemUtils.is_constant v
    | _ -> false

  method is_immutable_var =
    match node_type with
    | TN_VAR (cmsix, v, _) ->
       let proc_name = make_procname cmsix in
       begin
         try
           let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
           let vtypes = (jproc_info#get_jvar_info v)#get_types in
           JCHTypeUtils.is_immutable_type vtypes
         with _ -> false
       end
    | _ -> false

  method is_immutable = self#is_immutable_var

  method is_call = match node_type with TN_CALL _ -> true | _ -> false

  method is_unknown_call =
    match node_type with TN_UNKNOWN_CALL _ -> true | _ -> false 

  method get_untrusted_origins = untrusted_origins
  method set_untrusted_origins (origs:taint_origin_set_int) =
    untrusted_origins <- origs
  method add_untrusted_origins (origs:taint_origin_set_int) =
    if JCHTaintOrigin.is_taint_origin_subset origs untrusted_origins then false
    else
      begin
	untrusted_origins <-
          JCHTaintOrigin.join_taint_origin_sets untrusted_origins origs ;
	true
      end

  method get_size_untrusted_origins = size_untrusted_origins
                                    
  method set_size_untrusted_origins (origs:taint_origin_set_int) =
    size_untrusted_origins <- origs
    
  method add_size_untrusted_origins (origs:taint_origin_set_int) =
    if JCHTaintOrigin.is_taint_origin_subset origs size_untrusted_origins then
      false
    else
      begin
	size_untrusted_origins <-
          JCHTaintOrigin.join_taint_origin_sets size_untrusted_origins origs ;
	true
      end

  method get_field_inds = field_untrusted_origins#listOfKeys
      
  method get_field_untrusted_origins (cfsix: int) =
    match field_untrusted_origins#get cfsix with
    | Some set -> set
    | _ -> untrusted_origins
         
  method set_field_untrusted_origins (cfsix: int) (origs:taint_origin_set_int) =
    field_untrusted_origins#set cfsix origs
    
  method add_field_untrusted_origins (cfsix: int) (origs:taint_origin_set_int) =
    if origs#is_empty then
      false
    else
      begin
        let res =
	  (match field_untrusted_origins#get cfsix with
	  | Some untrusted_origs ->
	      if JCHTaintOrigin.is_taint_origin_subset origs untrusted_origs then
		false
	      else
		begin
		  let new_origs =
                    JCHTaintOrigin.join_taint_origin_sets untrusted_origs origs in
		  field_untrusted_origins#set cfsix new_origs ;
		  true
		end
	  | _ ->
	     if JCHTaintOrigin.is_taint_origin_subset origs untrusted_origins then
               false
	      else
		begin
		  let new_origs =
                    JCHTaintOrigin.join_taint_origin_sets untrusted_origins origs in
		  field_untrusted_origins#set cfsix new_origs;
		  true
		end) in
        res
      end
    
  method private get_all_field_untrusted_origins =
    let origs = ref (JCHTaintOrigin.mk_taint_origin_set []) in
    let add_field_origs forigs =
      origs := JCHTaintOrigin.join_taint_origin_sets !origs forigs in
    begin
      List.iter add_field_origs field_untrusted_origins#listOfValues ;
      !origs
    end

  method add_all_field_untrusted_origins
           (field_origs: taint_origin_set_int IntCollections.table_t) = 
    List.exists
      (fun b -> b = true)
      (List.map (fun (i, origs) ->
           self#add_field_untrusted_origins i origs) field_origs#listOfPairs)

  method add_all_untrusted_origins (node: 'a) : bool = 
    let b1 = node#add_untrusted_origins untrusted_origins in 
    let b2 = node#add_size_untrusted_origins size_untrusted_origins in 
    let b3 = node#add_all_field_untrusted_origins field_untrusted_origins in 
    b1 || b2 || b3 

  method private add_untrusted_origins_to_all (node: 'a) = 
    let origs = self#get_untrusted_origins in
    match node#get_node_type with
    | TN_VAR (cmsix, v, _) ->
	let proc_name = make_procname cmsix in
	begin
          try (* the proc_name might not be in the system *)
            let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
	    let jvar_info = jproc_info#get_jvar_info v in
	    let b1 = node#add_untrusted_origins origs in
	    let b2 =
	      if jvar_info#has_length then
                node#add_size_untrusted_origins origs
	      else
                false in
	    let b3 =
	      List.exists
                (fun b -> b)
                (List.map (fun cfsix ->
                     node#add_field_untrusted_origins cfsix origs) node#get_field_inds)  in
	    b1 || b2 || b3
          with _ -> false
	end
    | _ -> false

  method private add_all_untrusted_origins_to_untrusted (node: 'a) =
    let b1 = node#add_untrusted_origins self#get_untrusted_origins in
    let b2 = node#add_untrusted_origins self#get_size_untrusted_origins in
    let b3 = node#add_untrusted_origins self#get_all_field_untrusted_origins in
    b1 || b2 || b3 


  (* transfer taint from this to node *)
  (* returns true if new taint was added *)
  method propagate_taint (node: 'a) =
    try
      match (node_type, node#get_node_type) with
      | (TN_REF_EQUAL, _)
        | (_, TN_REF_EQUAL) -> self#add_all_untrusted_origins node
      | (TN_SIZE (_, array, _), _) ->
         if node#get_var#equal array then
           (* transmission length -> array *)
           (* TN_SIZE has untrusted_origins set not the size_origins *)
	   node#add_size_untrusted_origins self#get_untrusted_origins
	 else (* transmission array -> length *)
	   node#add_untrusted_origins (self#get_untrusted_origins)
      | (_, TN_SIZE (_, array, _)) ->
	 if self#get_var#equal array then (* transmission array -> length *)
	   node#add_untrusted_origins self#get_size_untrusted_origins
	 else (* transmission length -> array *)
	   node#add_untrusted_origins (self#get_untrusted_origins)
      | (TN_OBJECT_FIELD (_, var, cfsix, _), _) ->
         if node#get_var#equal var then
           (* transmission field -> object *)
           (* TN_OBJECT_FIELD has untrusted_origins set not a field_origin *)
	   node#add_field_untrusted_origins cfsix (self#get_untrusted_origins)
	 else (* transmission object -> field *)
	   node#add_untrusted_origins self#get_untrusted_origins
      | (_, TN_OBJECT_FIELD (_, var, cfsix, _)) ->
	 if self#get_var#equal var then (* transmission object -> field *)
	   node#add_untrusted_origins (self#get_field_untrusted_origins cfsix)
	 else (* transmission field -> object *)
	   node#add_untrusted_origins self#get_untrusted_origins
      | (TN_UNKNOWN_CALL _, _) ->
	 self#add_untrusted_origins_to_all node
      | (_, TN_UNKNOWN_CALL _) ->
	 self#add_all_untrusted_origins_to_untrusted node
      | _ -> node#add_untrusted_origins (self#get_untrusted_origins)
    with
    | JCH_failure p ->
       let msg = LBLOCK [ STR "propagate_taint: " ; node#toPretty ;
                          STR ": " ; p ] in
       begin
         ch_error_log#add "propagate_taint" msg ;
         (* raise (JCH_failure msg) *)
         self#add_untrusted_origins (self#get_untrusted_origins)
       end
	

  method get_call_vars =
    match node_type with
    | TN_CALL (_, _, _, _, r_opt, args) ->
       begin
         match r_opt with
         | Some r -> r :: args
         | _ -> args
       end
    | _ -> []

  method get_call_pc =
    match node_type with
    | TN_CALL (_, pc, _, _, _, _) -> pc
    | _ ->
       begin
         pr__debug [ STR "get_call_pc expected CALL" ; NL ] ;
         raise
           (JCH_failure
              (LBLOCK [ STR "taint_node:get_call_pc: " ; self#toPretty ]))
       end

  method write_xml (node:xml_element_int) =
    let seti = node#setIntAttribute in
    begin
      seti "ut" untrusted_origins#get_index ;
      (match stub_untrusted with
       | Some s -> seti "stut" s#getSeqNumber
       | _ -> ()) 
    end

      
  method private to_pretty_debug =
    let pp_origs_inds =
      let pp_origs orig_set =
        LBLOCK [STR "TN"; orig_set#to_pretty_inds ; STR ""] in
      let pp_untr_origs = pp_origs untrusted_origins in
      let pp_s_untr_origs =
	if size_untrusted_origins#is_empty then
          STR ""
	else
          LBLOCK [STR " s: "; pp_origs size_untrusted_origins] in
      let pp_f_untr_origs =
	let pp_f (cfsix, f_untr_origs) =
          LBLOCK [STR " "; INT cfsix; STR ": "; pp_origs f_untr_origs] in
	LBLOCK (List.map pp_f field_untrusted_origins#listOfPairs) in
      LBLOCK[STR "_<<";  pp_untr_origs;
             pp_s_untr_origs; pp_f_untr_origs; STR ">>"] in
    
    let pp_node = 
      match node_type with 
      |	TN_FIELD cfsix  ->
          let cfs = retrieve_cfs cfsix in
	  LBLOCK [STR "FIELD ("; STR cfs#field_signature#to_string ; STR ")"]
      | TN_OBJECT_FIELD (cmsix, var, cfsix, pc) ->
          let cfs = retrieve_cfs cfsix in
          LBLOCK [ STR "OBJECT-FIELD(" ; INT cmsix ; STR ", " ; 
                   var#toPretty ; STR ":" ; STR cfs#field_signature#to_string ;
                   STR " @ pc=" ; INT pc ; STR ")"]
      |	TN_VAR (cmsix, var, pc) ->
	  LBLOCK [STR "VAR("; INT cmsix; STR ", "; var#toPretty; STR ")"]
      |	TN_VAR_EQ (cmsix, var1, var2, statelist) ->
          let states = new SymbolCollections.set_t in
          let _ = states#addList statelist in
	  LBLOCK [STR "VAR_EQ("; INT cmsix; STR ", "; var1#toPretty; STR " = ";
                  var2#toPretty; STR " on "; states#toPretty; STR ")"] 
      |	TN_CALL (_, pc, callerix, tgtix , _, _) ->
          let tgtcms = retrieve_cms tgtix in
          let callercms = retrieve_cms callerix in
	  let tstr =
            try
              let tinfo = app#get_method tgtcms in
	      match tinfo#get_implementation with 
	      | ConcreteMethod _ -> "METH_CALL "
	      | Stub _ -> "STUB_CALL "
	      | _ -> "UNKN_CALL" 
            with
              _ -> "UNKN_CALL" in
	  LBLOCK [STR tstr; STR " ("; callercms#toPretty ; STR " @pc=" ; INT pc;
                   STR " => "; tgtcms#toPretty ; STR ")"]
      |	TN_UNKNOWN_CALL (_, pc, callerix, _, _) ->
	  LBLOCK [STR "UNKNOWN_CALL("; INT callerix ; STR " @pc=" ; INT pc; STR ")"]
      | TN_CONDITIONAL (cmsix, pc) ->
          LBLOCK [ STR "CONDITIONAL(" ; INT cmsix ; STR " @pc=" ; INT pc ; STR ")"]
      | TN_SIZE (cmsix, var, pc) ->
         LBLOCK [ STR "SIZE(" ; INT cmsix ; STR ", " ; var#toPretty ; STR " @pc=" ;
                  INT pc ; STR ")"]
      | TN_REF_EQUAL -> STR "TN_REF_EQUAL" in
    LBLOCK [pp_node; pp_origs_inds]


  (* does not print taint info *)
  method to_pretty_no_taint =
    let proc_name_pp n = INT n#getSeqNumber in
    match node_type with 
    | TN_FIELD cfsix  ->
       let cfs = retrieve_cfs cfsix in
       LBLOCK [STR "FIELD "; STR cfs#field_signature#to_string ]
    | TN_OBJECT_FIELD (cmsix, var, cfsix, pc) ->
       let proc_name = make_procname cmsix in
       let cfs = retrieve_cfs cfsix in
       LBLOCK [ STR "OBJECT-FIELD(" ; proc_name_pp proc_name ; STR ", " ;
                var#toPretty ; STR ":" ; STR cfs#field_signature#to_string ;
                STR " @ pc=" ; INT pc ]
    | TN_VAR (cmsix, var, pc) ->
       let proc_name = make_procname cmsix in 
       LBLOCK [STR "VAR ("; proc_name_pp proc_name; 
	       STR ", "; var#toPretty; STR ", "; INT pc; STR ")"]
    | TN_VAR_EQ (cmsix, var1, var2, statelist) ->
       let proc_name = make_procname cmsix in
       let states = new SymbolCollections.set_t in
       let _ = states#addList statelist in
       LBLOCK [STR "VAR_EQ ("; proc_name_pp proc_name; 
	       STR ", "; var1#toPretty; 
	       STR " = "; var2#toPretty; 
	       STR " on "; states#toPretty; STR ")"] 
    | TN_CALL (_, pc, callerix, tgtix , _, _) ->
       let tgtcms = retrieve_cms tgtix in
       let callercms = retrieve_cms callerix in
       let tstr =
         try
           let tinfo = app#get_method tgtcms in
	   match tinfo#get_implementation with 
	   | ConcreteMethod _ -> "METH_CALL "
	   | Stub _ -> "STUB_CALL "
	   | _ -> "UNKN_CALL" 
         with
           _ -> "UNKN_CALL" in
       LBLOCK [STR tstr; callercms#toPretty ; STR " @pc=" ; INT pc;
               STR " => "; tgtcms#toPretty ]
    | TN_UNKNOWN_CALL (_, pc, callerix, _, _) ->
       let callercms = retrieve_cms callerix in
       LBLOCK [STR "UNKNOWN_CALL "; callercms#toPretty ; STR " @pc=" ; INT pc]
    | TN_CONDITIONAL (cmsix, pc) ->
       let cms = retrieve_cms cmsix in
       LBLOCK [ STR "CONDITIONAL(" ; cms#toPretty ; STR " @pc=" ; INT pc ]
    | TN_SIZE (cmsix, var, pc) ->
       let cms = retrieve_cms cmsix in
       LBLOCK [ STR "SIZE(" ; cms#toPretty ; STR ", " ;
                var#toPretty ; STR " @pc=" ; INT pc ]
    | TN_REF_EQUAL -> STR "TN_REF_EQUAL"

    method private to_pretty = 
      let proc_name_pp n = INT n#getSeqNumber in
      let pp_var mInfo pc v = 
	match v#getName#getBaseName with
        | "r0" when mInfo#has_local_variable_name 0 pc ->
           STR (mInfo#get_local_variable_name 0 pc) 
        | "r1" when mInfo#has_local_variable_name 1 pc ->
           STR (mInfo#get_local_variable_name 1 pc) 
        | "r2" when mInfo#has_local_variable_name 2 pc ->
           STR (mInfo#get_local_variable_name 2 pc) 
        | "r3" when mInfo#has_local_variable_name 3 pc ->
           STR (mInfo#get_local_variable_name 3 pc) 
        | "r4" when mInfo#has_local_variable_name 4 pc ->
           STR (mInfo#get_local_variable_name 4 pc)
        | "r5" when mInfo#has_local_variable_name 5 pc ->
           STR (mInfo#get_local_variable_name 5 pc)
        | _ -> v#toPretty in
      match node_type with 
      |	TN_FIELD cfsix  ->
         let cfs = retrieve_cfs cfsix in
	 LBLOCK [STR "FIELD "; STR cfs#field_signature#to_string ; STR ")"]
      | TN_OBJECT_FIELD (cmsix, var, cfsix, pc) ->
         let proc_name = make_procname cmsix in
         let cfs = retrieve_cfs cfsix in
         LBLOCK [ STR "OBJECT-FIELD(" ; proc_name_pp proc_name ; STR ", " ;
                  var#toPretty ; STR ":" ; STR cfs#field_signature#to_string ;
                  STR " @ pc=" ; INT pc; STR ")"]
      |	TN_VAR (cmsix, var, pc) ->
         let mInfo = app#get_method (retrieve_cms cmsix) in
	  LBLOCK [STR "VAR ("; (retrieve_cms cmsix)#to_abbreviated_pretty ; 
		   STR ", "; pp_var mInfo pc var ; STR ", "; INT pc; STR ")"]
      |	TN_VAR_EQ (cmsix, var1, var2, statelist) ->
         let proc_name = make_procname cmsix in
         let states = new SymbolCollections.set_t in
         let _ = states#addList statelist in
	 LBLOCK [STR "VAR_EQ ("; proc_name_pp proc_name; 
		 STR ", "; var1#toPretty; 
		 STR " = "; var2#toPretty; 
		 STR " on "; states#toPretty; STR ")"] 
      |	TN_CALL (_, pc, callerix, tgtix , _, _) -> 
         let tgtcms = retrieve_cms tgtix in
         let callercms = retrieve_cms callerix in
	 let tstr =
           try
             let tinfo = app#get_method tgtcms in
	     match tinfo#get_implementation with 
	     | JCHPreAPI.ConcreteMethod _ -> "METH_CALL "
	     | JCHPreAPI.Stub _ -> "STUB_CALL "
	     | _ -> "UNKN_CALL" 
           with
             _ -> "UNKN_CALL" in
	 LBLOCK [STR tstr; callercms#toPretty ; STR " @ pc=" ; INT pc;
                 STR " => "; tgtcms#toPretty ]
      |	TN_UNKNOWN_CALL (_, pc, callerix, _, _) ->
         let callercms = retrieve_cms callerix in
	 LBLOCK [STR "UNKNOWN_CALL "; callercms#toPretty ; STR " @ pc=" ; INT pc]
      | TN_CONDITIONAL (cmsix, pc) ->
         let cms = retrieve_cms cmsix in
         LBLOCK [ STR "CONDITIONAL(" ; cms#toPretty ; STR " @pc=" ; INT pc ]
      | TN_SIZE (cmsix, var, pc) ->
         let cms = retrieve_cms cmsix in
         LBLOCK [ STR "SIZE(" ; cms#toPretty ; STR ", " ; var#toPretty ;
                  STR " @pc=" ; INT pc ]
      | TN_REF_EQUAL -> STR "REF_EQUAL"

  method toPretty =
    if  JCHPrintUtils.is_dbg_on () then self#to_pretty_debug else self#to_pretty
      
  end
    
       
                   
let node_dictionary = H.create 3

let add_taint_node nodetype index =
  if H.mem node_dictionary index then
    H.find node_dictionary index
  else
    let t = new taint_node_t ~index ~nodetype in
    begin H.add node_dictionary index t ; t end

let mk_var_node proc_name var: taint_node_t =
  let jproc_info = (JCHSystem.jsystem#get_jproc_info proc_name)#get_jvar_info var in
  let pc = jproc_info#get_pc_in_scope in
  let nodetype = TN_VAR (proc_name#getSeqNumber, var, pc) in
  let index = taint_dictionary#index_taint_node_type nodetype in
  add_taint_node nodetype index

let mk_var_node_pc pc proc_name var:taint_node_t =
  let nodetype = TN_VAR (proc_name#getSeqNumber, var, pc) in
  let index = taint_dictionary#index_taint_node_type nodetype in
  add_taint_node nodetype index

let mk_eq_node proc_name var1 var2 states:taint_node_t =
  let nodetype = TN_VAR_EQ (proc_name#getSeqNumber, var1, var2, states#toList) in
  let index = taint_dictionary#index_taint_node_type nodetype in
  add_taint_node nodetype index

let mk_field_node field_info:taint_node_t =
  let nodetype = TN_FIELD field_info#get_index in
  let index = taint_dictionary#index_taint_node_type nodetype in
  add_taint_node nodetype index

let mk_call_node index pc cinfo tinfo return_opt call_args =
  let nodetype = TN_CALL (index, pc, cinfo#get_index, tinfo#get_index, return_opt, call_args) in
  let index = taint_dictionary#index_taint_node_type nodetype in
  add_taint_node nodetype index

let mk_unknown_call_node index pc cinfo return_opt call_args =
  let nodetype = TN_UNKNOWN_CALL (index, pc, cinfo#get_index, return_opt, call_args) in
  let index = taint_dictionary#index_taint_node_type nodetype in
  add_taint_node nodetype index

let mk_cond_node proc_name pc =
  let node_type = TN_CONDITIONAL (proc_name#getSeqNumber, pc) in
  let index = taint_dictionary#index_taint_node_type node_type in
  add_taint_node node_type index

let mk_obj_field_node proc_name var cfsix pc  =
  let node_type = TN_OBJECT_FIELD (proc_name#getSeqNumber, var, cfsix, pc) in
  let index = taint_dictionary#index_taint_node_type node_type in
  add_taint_node node_type index

let mk_size_node proc_name var pc = 
  let node_type = TN_SIZE (proc_name#getSeqNumber, var, pc) in
  let index = taint_dictionary#index_taint_node_type node_type in
  add_taint_node node_type index

let mk_ref_equal_node () =
  let node_type = TN_REF_EQUAL in
  let index = taint_dictionary#index_taint_node_type node_type in
  add_taint_node node_type index


  
let set_stub_origins
      (proc_name: symbol_t)
      (pc: int)
      (stub_node: taint_node_t)
      (inode: taint_node_t)
      (node: taint_node_t) =
  
  (if !dbg then
     pr__debug [ STR "set_stub_origins "; INT pc; NL;
                 stub_node#toPretty; NL;
	         inode#toPretty; NL; node#toPretty; NL;
                 STR "end set_stub_origin"; NL]) ;
  
  let return_node = ref None in
  (match inode#get_stub_untrusted with 
  | Some stub_name -> 
      let orig = mk_stub_origin stub_name proc_name pc in 
      let new_origins = JCHTaintOrigin.mk_taint_origin_set [orig] in
      let _ = node#add_untrusted_origins new_origins in
      let _ = stub_node#add_untrusted_origins new_origins in
      return_node := Some stub_node 
  | _ -> ()) ;
  !return_node

let get_call_args args = 
  let return_opt = ref None in
  let other_vars = ref [] in
  let get_vars (s,v,m) = 
    match s with 
    | "return" -> return_opt := Some v  
    | "throw" -> ()
    | _ -> other_vars := v :: !other_vars in
  begin
    List.iter get_vars args ;
    (!return_opt, exception_var, List.rev !other_vars)
  end
  
let get_node (index:int) =
  if H.mem node_dictionary index then
    H.find node_dictionary index
  else
    raise
      (JCH_failure
         (LBLOCK [ STR "Taint node with index " ;
                   INT index ; STR " not found" ]))
             
module TaintNodeCollections = CHCollections.Make 
    (struct
      type t = taint_node_t
      let compare n1 n2 = compare n1#get_index n2#get_index
      let toPretty n = n#toPretty
    end)
  
let print_dictionary () =
  let nodes = H.fold (fun k v a -> (k,v)::a) node_dictionary [] in
  let pnodes =
    LBLOCK (List.map (fun (k,v) ->
                LBLOCK [ INT k ; STR " -> " ; v#toPretty ; NL ]) nodes) in
  pr__debug [ STR "node_dictionary: " ; NL ; pnodes ; NL ]

let taint_node_set_to_pretty (set: TaintNodeCollections.set_t) = 
  pretty_print_list set#toList (fun n -> n#to_pretty_no_taint) "{" ", " "}"

let taint_node_table_to_pretty
      (table:TaintNodeCollections.set_t TaintNodeCollections.table_t) = 
  LBLOCK (List.map (fun (n, set) ->
              LBLOCK [n#to_pretty_no_taint;
                      STR " -> "; taint_node_set_to_pretty set; NL]) table#listOfPairs)


let write_xml_node_dictionary
      (node:xml_element_int) (taint_node_indices:int list) =
  let tnodes = ref [] in
  let _ =
    List.iter
      (fun i -> tnodes := (H.find node_dictionary i) :: !tnodes)
      taint_node_indices in
  node#appendChildren
    (List.map
       (fun v ->
         let tnode = xmlElement "tn" in
         begin
           v#write_xml tnode ;
           tnode#setIntAttribute "ix" v#get_index ;
           tnode
         end) !tnodes)

let write_xml_trail
      (node:xml_element_int)
      (table:TaintNodeCollections.set_t TaintNodeCollections.table_t) =
  let pairs = table#listOfPairs in    (* taint-node -> taint-node set *)
  node#appendChildren
    (List.map (fun (tnode,tnodeset) ->
         let n = xmlElement "edge" in
         begin
           n#setIntAttribute "src" tnode#get_index ;
           n#setAttribute
             "tgts" (String.concat
                       "," (List.map string_of_int
                                     (List.map (fun tn -> tn#get_index) tnodeset#toList))) ;
           n
         end) pairs)
  
let save_taint_trail
      (table:TaintNodeCollections.set_t TaintNodeCollections.table_t)
      (taintorigin_index:int) =
  let doc = xmlDocument () in
  let root = get_jch_root "taint-trails" in
  let filename = get_taint_trails_filename taintorigin_index in
  let trnode = xmlElement "taint-trails" in
  let dnode = xmlElement "node-dictionary" in
  let enode = xmlElement "edges" in
  let pairs = table#listOfPairs in  (* taint-node -> taint-node set *)
  let indices = new IntCollections.set_t in
  let _ = List.iter (fun (tn,tnset) ->
              begin
                indices#add tn#get_index ;
                tnset#iter (fun n -> indices#add n#get_index)
              end) pairs in
  begin
    doc#setNode root ;
    write_xml_trail enode table ;
    write_xml_node_dictionary dnode indices#toList;
    root#appendChildren [ trnode ] ;
    trnode#appendChildren [ dnode ; enode ] ;
    file_output#saveFile filename doc#toPretty
  end

