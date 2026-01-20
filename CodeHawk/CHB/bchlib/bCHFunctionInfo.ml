(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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
open CHCommon
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHTraceResult
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHBTerm
open BCHCallTargetInfo
open BCHCPURegisters
open BCHConstantDefinitions
open BCHCppClass
open BCHCStruct
open BCHDoubleword
open BCHFtsParameter
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionSemantics
open BCHFunctionStackframe
open BCHFunctionSummary
open BCHJavaSignatures
open BCHLibTypes
open BCHMemoryReference
open BCHPreFileIO
open BCHProofObligations
open BCHSystemInfo
open BCHUtilities
open BCHVariable
open BCHVariableNames
open BCHXPODictionary

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory
module TR = CHTraceResult

let x2p = xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)

let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)
let elocm (line: int): string = (eloc line) ^ ": "

let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("finfo:" ^ tag) msg


module NumericalCollections = CHCollections.Make
  (struct
    type t = numerical_t
    let compare x y = x#compare y
    let toPretty n = n#toPretty
   end)

module DoublewordCollections = CHCollections.Make
  (struct
    type t = doubleword_int
    let compare dw1 dw2 = dw1#compare dw2
    let toPretty dw = STR dw#to_fixed_length_hex_string
   end)


let id = BCHInterfaceDictionary.interface_dictionary

let memmap = BCHGlobalMemoryMap.global_memory_map


type po_anchor_t =                      (* proof obligation anchor *)
| DirectAccess
| IndirectAccess of bterm_t


let po_anchor_compare a1 a2 =
  match (a1,a2) with
  | (DirectAccess, DirectAccess) -> 0
  | (DirectAccess, _) -> -1
  | (_, DirectAccess ) -> 1
  | (IndirectAccess n1, IndirectAccess n2) -> bterm_compare n1 n2


let po_anchor_to_pretty a =
  match a with
  | DirectAccess -> STR "direct"
  | IndirectAccess n -> LBLOCK [ STR "indirect ( " ; bterm_to_pretty n ; STR " )" ]


let pr_expr = xpr_formatter#pr_expr


class function_environment_t
        (faddr:doubleword_int)
        (fndata: function_data_int)
        (varmgr:variable_manager_int):function_environment_int =
object (self)

  val scope = LF.mkScope ()
  val virtual_calls = H.create 3
  val initial_string_values = H.create 3

  initializer
    List.iter (fun av ->
        let atts = self#varmgr#get_av_attributes av#index in
        ignore (self#mk_variable ~atts av)) varmgr#get_assembly_variables

  method get_variable_comparator = varmgr#get_external_variable_comparator

  method private log_dc_error_result (line: int) (e: string list) =
    if BCHSystemSettings.system_settings#collect_data then
      self#log_error_result line e
    else
      ()

  method private log_error_result (line: int) (e: string list) =
    log_error_result ~msg:(faddr#to_hex_string ^ ":env") __FILE__ line e

  (* ------------------------------------------------------ variable names -- *)

  val variable_names = make_variable_names ()

  method variable_names = variable_names

  method varmgr: variable_manager_int = varmgr

  method set_variable_name (v:variable_t) (name:string) =
    variable_names#add v#getName#getSeqNumber name

  method variable_name_to_string v =
    let index = v#getName#getSeqNumber in
    if variable_names#has index then
      variable_names#get index
    else
      v#getName#getBaseName

  method variable_name_to_pretty v = STR (self#variable_name_to_string v)

  method private set_pointedto_struct_field_names
                   (level:int) (v:variable_t) (vname:string) (ty:btype_t) =
    if level > 2 then () else
      let cstruct = get_pointedto_struct ty in
      let _ = chlog#add "c-struct field names" cstruct#toPretty in
      cstruct#iter (fun fld ->
          log_tfold
            (log_error
               "set_pointed_to_struct_field_names"
               ("invalid memref for " ^ fld.fld_name))
            ~ok:(fun memref ->
              let fldvar =
                self#mk_memory_variable
                  ~save_name:false
                  memref
                  (mkNumerical fld.fld_offset) in
              let fldname = vname ^ "->" ^ fld.fld_name in
              let fldtype = fld.fld_type in
              let ifldvar = TR.tget_ok (self#mk_initial_memory_value fldvar) in
              let ifldname = fldname ^  "_in" in
              let _ = chlog#add "set field var" (STR  fldname) in
              begin
	        self#set_variable_name fldvar fldname ;
                self#set_variable_name ifldvar ifldname ;
	        if is_ptrto_known_struct fldtype then
	          self#set_pointedto_struct_field_names
                    (level + 1) ifldvar fldname fldtype
              end)
            ~error:(fun _ -> ())
            (self#mk_base_variable_reference v))

  method set_java_native_method_signature (api:java_native_method_api_t) =
    let args = api.jnm_signature#descriptor#arguments in
    let isStatic = api.jnm_static in
    let jthis = if isStatic then "this$obj" else "this$class" in
    let stackPars = [(8, jthis, t_voidptr); (4, "jni$Env", t_voidptr)] in
    let (_,_,stackPars) = List.fold_left (fun (count,off,pars) ty ->
      let name = (get_java_type_name_prefix ty) ^ "_" ^ (string_of_int count) in
      (count+1, off + (get_java_type_length ty),
       (off, name, (get_java_type_btype ty)) :: pars)) (3,12,stackPars) args in
    List.iter (fun (offset, name, _ty) ->
      let memref = self#mk_local_stack_reference in
      let v = self#mk_memory_variable memref (mkNumerical offset) in
      let initV = TR.tget_ok (self#mk_initial_memory_value v) in
      begin
	self#set_variable_name initV name ;
        if offset = 4 then
          log_tfold
            (log_error "set_java_native_method_signature" "invalid memref")
            ~ok:(fun memref ->
	      let jniInterfacePtr =
                self#mk_memory_variable memref numerical_zero in
	      let jniInterfacePtrIn =
                TR.tget_ok (self#mk_initial_memory_value jniInterfacePtr) in
	      self#set_variable_name jniInterfacePtrIn "jni$Ifp")
            ~error:(fun _ -> ())
            (self#mk_base_variable_reference initV)
      end ) stackPars

  method set_unknown_java_native_method_signature =
    let stackPars = [ (4, "jni$Env", t_voidptr) ] in
    List.iter (fun (offset, name, _ty) ->
      let memref = self#mk_local_stack_reference in
      let v = self#mk_memory_variable memref (mkNumerical offset) in
      let initV = TR.tget_ok (self#mk_initial_memory_value v) in
      begin
	self#set_variable_name initV name ;
        if offset = 4 then
          log_tfold
            (log_error
               "set_unknown_java_native_method_signature" ("invalid memref"))
            ~ok:(fun memref ->
	      let jniInterfacePtr =
                self#mk_memory_variable memref numerical_zero in
	      let jniInterfacePtrIn =
                TR.tget_ok (self#mk_initial_memory_value jniInterfacePtr) in
	      self#set_variable_name jniInterfacePtrIn "jni$Ifp")
            ~error:(fun _ -> ())
            (self#mk_base_variable_reference initV)
      end ) stackPars

  method set_argument_structconstant par sc =
    match par.apar_location with
    | [StackParameter (i, _)] ->
      let memref = self#mk_local_stack_reference  in
      let argvar =
        self#mk_memory_variable ~save_name:false memref (mkNumerical (4*i)) in
      let argvarin = TR.tget_ok (self#mk_initial_memory_value argvar) in
      begin
	match sc with
	| FieldValues l ->
	   List.iter (fun (offset, ssc) ->
               log_tfold
                 (log_error "set_argument_structconstant" "invalid memref")
                 ~ok:(fun mref ->
	           let mvar = self#mk_memory_variable mref (mkNumerical offset) in
	           let mvarin = TR.tget_ok (self#mk_initial_memory_value mvar) in
	           match ssc with
	           | FieldString s ->
		      begin
		        H.add
                          initial_string_values
                          (argvarin#getName#getSeqNumber,offset)
                          s;
		        chlog#add
                          "struct constant string"
		          (LBLOCK [
                               faddr#toPretty;
                               STR ": &";
                               mvarin#toPretty;
                               STR " -- ";
			       STR s])
		      end
	           | _ -> ())
                 ~error:(fun _ -> ())
                 (self#mk_base_variable_reference argvarin)) l
	| _ -> ()
      end
    | _ -> ()

  method set_class_member_variable_names
    (classinfos:(string * function_interface_t * bool) list) =
    match classinfos with
    | [(classname, fintf, isStatic)] ->
      let stackpardata =
         List.map (fun p ->
             let name = get_parameter_name p in
             let offset =
               fail_tvalue
                 (trerror_record (STR "set_class_member_variable_names"))
                 (get_stack_parameter_offset p) in
             (offset, name)) (get_stack_parameters fintf) in
       let regpardata =
         List.map (fun p ->
             let name = get_parameter_name p in
             let register =
               fail_tvalue
                 (trerror_record (STR "set_class_member_variable_names"))
                 (get_register_parameter_register p) in
             (register, name)) (get_register_parameters fintf) in
       let stackVars =
         List.map (fun (i,name) ->
	     let memref = self#mk_local_stack_reference in
	     let memvar =
               self#mk_memory_variable
                 ~save_name:false
                 memref
                 (mkNumerical
                    (i * 4)) in
	     let memInitVar = TR.tget_ok (self#mk_initial_memory_value memvar) in
	     (name,memInitVar)) stackpardata in
       let regVars =
         List.map (fun (r,name) ->
	     let regInitVar = self#mk_initial_register_value ~level:0 r in
	     (name,regInitVar)) regpardata in
       let paramVars = stackVars @ regVars in
       let _ =
         List.iter (fun (name,v) ->
             self#set_variable_name v name) paramVars in
       if isStatic then
         ()
       else
         let (_, thisVar) =
	   try
             List.find (fun (name,_) -> name = "this") paramVars
           with Not_found ->
	     raise
               (BCH_failure
                  (LBLOCK [
                       STR "No this variable found in function ";
		       faddr#toPretty;
                       STR " in class ";
		       STR classname])) in
         let cppClass = get_cpp_class classname in
         let add_dm_class_members (ty:btype_t) (basevar:variable_t) =
	   if is_class_type ty then
	     let _=
               chlog#add
                 "member class type"
	         (LBLOCK [
                      basevar#toPretty;
                      STR ": ";
                      STR (btype_to_string ty)]) in
	     let cls = get_class_from_type ty in
	     begin
	       cls#dm_iter (fun dm ->
                   log_tfold
                     (log_error
                        "set_class_member_variable_names" "invalid memref")
                     ~ok:(fun memref ->
	               let memberVar =
                         self#mk_memory_variable
                           ~save_name:false
                           memref
                           (mkNumerical dm.cppdm_offset) in
	               let memberInitVar =
                         TR.tget_ok (self#mk_initial_memory_value memberVar) in
	               let mName = self#variable_name_to_string basevar in
	               let name = mName ^ "->" ^ dm.cppdm_name in
	               self#set_variable_name memberInitVar name)
                     ~error:(fun _ -> ())
                     (self#mk_base_variable_reference basevar));

	       cls#vf_iter (fun vf ->
                   log_tfold
                     (log_error
                        "set_class_member_variable_names" "invalid memref (2)")
                     ~ok:(fun memref ->
	               let vfptrVar =
                         self#mk_memory_variable
                           ~save_name:false
                           memref
                           (mkNumerical vf.cppvf_offset) in
	               let vfptrInitVar =
                         TR.tget_ok (self#mk_initial_memory_value vfptrVar) in
	               let mName = self#variable_name_to_string basevar in
	               let vfptrName = mName ^ "->vtableptr" in
	               let vfsummaries = get_vtable_summaries vf.cppvf_table in
	               begin
		         List.iter (fun (vfOffset, summary) ->
                             log_tfold
                               (log_error
                                  "set_class_member_variable_names"
                                  "invalid memref (3)")
                               ~ok:(fun vfmemref ->
		                 let vfVar =
                                   self#mk_memory_variable
                                     ~save_name:false
                                     vfmemref
                                     (mkNumerical vfOffset) in
		                 let vfInitVar =
                                   TR.tget_ok (self#mk_initial_memory_value vfVar) in
		                 self#register_virtual_call vfInitVar summary)
                               ~error:(fun _ -> ())
                               (self#mk_base_variable_reference vfptrInitVar))
                           vfsummaries;
		         self#set_variable_name vfptrInitVar vfptrName
	               end)
                     ~error:(fun _ -> ())
                     (self#mk_base_variable_reference basevar))
	     end
	   else
	     () in
         begin
	   cppClass#dm_iter (fun dm ->
               log_tfold
                 (log_error
                    "set_class_member_variable_names" "invalid memref (4)")
                 ~ok:(fun memref ->
	           let memberVar =
                     self#mk_memory_variable
                       ~save_name:false
                       memref
                       (mkNumerical dm.cppdm_offset) in
	           let memberInitVar =
                     TR.tget_ok (self#mk_initial_memory_value memberVar) in
	           let name = "this->" ^ dm.cppdm_name in
	           begin
	             self#set_variable_name memberInitVar name ;
	             add_dm_class_members dm.cppdm_type memberInitVar
	           end)
                 ~error:(fun _ -> ())
                 (self#mk_base_variable_reference thisVar));

	   cppClass#vf_iter (fun vf ->
               log_tfold
                 (log_error
                    "set_class_member_variable_names" "invalid memref (5)")
	         ~ok:(fun memref ->
                   let vfptrVar =
                     self#mk_memory_variable
                       ~save_name:false
                       memref
                       (mkNumerical vf.cppvf_offset) in
	           let vfptrInitVar =
                     TR.tget_ok (self#mk_initial_memory_value vfptrVar) in
	           let vfptrVarName = "this->" ^ "vtableptr" in
	           let vfsummaries = get_vtable_summaries vf.cppvf_table in
	           begin
	             List.iter (fun (vfOffset,summary) ->
                         log_tfold
                           (log_error
                              "set_class_member_variable_names"
                              "invalid memref (6)")
	                   ~ok:(fun vfmemref ->
                             let vfVar =
                               self#mk_memory_variable
                                 ~save_name:false
                                 vfmemref
                                 (mkNumerical vfOffset) in
	                     let vfInitVar =
                               TR.tget_ok (self#mk_initial_memory_value vfVar) in
	                     self#register_virtual_call vfInitVar summary)
                           ~error:(fun _ -> ())
                           (self#mk_base_variable_reference vfptrInitVar))
                       vfsummaries;
	             self#set_variable_name vfptrInitVar vfptrVarName
	           end)
                 ~error:(fun _ -> ())
                 (self#mk_base_variable_reference thisVar))
         end
    | _ ->
       ch_error_log#add
         "class info ignored"
	 (LBLOCK [
              faddr#toPretty;
              STR ". Class-infos: ";
	      pretty_print_list
                (List.map (fun (c,_,_) -> c) classinfos)
                (fun s -> STR s)
		"[" ", " "]"])

  method set_argument_names (fintf: function_interface_t) =
    let stackpardata =
      List.map (fun p ->
          let (name, ty) = get_parameter_signature p in
          let offset = get_stack_parameter_offset p in
          (offset, name, ty))
        (get_stack_parameters fintf) in
    let regpardata =
      List.map (fun p ->
          let (name, ty) = get_parameter_signature p in
          let reg = get_register_parameter_register p in
          (reg, name, ty)) (get_register_parameters fintf) in
    begin
      List.iter (fun (offset_r, name, ty) ->
	  let memref = self#mk_local_stack_reference  in
          TR.tfold
          ~ok:(fun offset ->
	    let v =
              self#mk_memory_variable
                ~save_name:false memref (mkNumerical offset) in
            TR.tfold
              ~ok:(fun iv ->
	        let vname = name ^ "$" ^ (string_of_int offset) in
	        begin
	          self#set_variable_name iv vname;
	          if is_ptrto_known_struct ty then
	            self#set_pointedto_struct_field_names 1 iv vname ty
	        end)
              ~error:(fun e ->
                ch_error_log#add
                  ("set_argument_names:" ^ (string_of_int __LINE__))
                  (STR (String.concat "; " e)))
              (self#mk_initial_memory_value v))
          ~error:(fun e ->
            ch_error_log#add
              ("set_argument_names" ^ (string_of_int __LINE__))
              (STR (String.concat "; " e)))
          offset_r
        ) stackpardata;
      List.iter (fun (reg_r, name, ty) ->
          TR.tfold
            ~ok:(fun reg ->
	      let v = self#mk_initial_register_value ~level:0 reg in
	      let vname = name in
	      begin
	        self#set_variable_name v vname;
	        if is_ptrto_known_struct ty then
	          self#set_pointedto_struct_field_names 1 v vname ty
	      end)
            ~error:(fun e ->
              ch_error_log#add
                ("set_argument_names:" ^ (string_of_int __LINE__))
                (STR (String.concat "; " e)))
            reg_r
        ) regpardata
    end


  (* --------------------------------------------------- memory references -- *)

  method mk_unknown_memory_reference =
    varmgr#memrefmgr#mk_unknown_reference

  method mk_global_memory_reference =
    varmgr#memrefmgr#mk_global_reference

  method mk_local_stack_reference: memory_reference_int =
      varmgr#memrefmgr#mk_local_stack_reference

  method mk_realigned_stack_reference =
      varmgr#memrefmgr#mk_realigned_stack_reference

  method mk_base_variable_reference
           (v: variable_t): memory_reference_int traceresult =
    varmgr#make_memref_from_basevar v

  method mk_base_sym_reference
           (s: symbol_t): memory_reference_int traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      self#mk_base_variable_reference
      (self#get_variable s#getSeqNumber)

  (* --------------------------------------------------- program variables -- *)

  val chifvars = H.create 5
  val symchifvars = H.create 5

  (* Keep a separate map of symbolic variables per domain *)
  val dom_symchifvars = H.create 5

  method private add_chifvar
                   ?(atts = []) (v:assembly_variable_int) (vt:variable_type_t) =
    if H.mem chifvars v#index then
      H.find chifvars v#index
    else
      let vname = new symbol_t ~atts ~seqnr:v#index v#get_name in
      let chifvar = scope#mkVariable vname vt in
      begin
        H.add chifvars v#index chifvar;
        (if (List.length atts) > 0 then self#varmgr#set_av_attributes v#index atts);
        chifvar
      end

  method private mk_variable ?(atts = []) (v:assembly_variable_int) =
    self#add_chifvar ~atts v NUM_VAR_TYPE

  method private add_domain_symchifvar
                   (domain: string) (seqnr: int) (v: variable_t) =
    let dom_chifvar_entry =
      if H.mem dom_symchifvars domain then
        H.find dom_symchifvars domain
      else
        let entry = H.create 3 in
        let _ = H.add dom_symchifvars domain entry in
        entry in
    if H.mem dom_chifvar_entry seqnr then
      ()
    else
      H.add dom_chifvar_entry seqnr v

  (* create a SYM_VAR_TYPE variable for the same assembly variable *)
  method mk_symbolic_variable
           ?(domains: string list = [])(v: variable_t): variable_t =
    let name = v#getName in
    let seqnr = name#getSeqNumber in
    let symchifvar =
      if H.mem symchifvars seqnr then
        H.find symchifvars seqnr
      else
        let symchifvar = scope#mkVariable name SYM_VAR_TYPE in
        begin
          H.add symchifvars seqnr symchifvar;
          symchifvar
        end in
    begin
      List.iter
        (fun dom ->
          self#add_domain_symchifvar dom seqnr symchifvar) domains;
      symchifvar
    end

  method get_symbolic_num_variable(v: variable_t): variable_t traceresult =
    tprop
      (self#get_variable v#getName#getSeqNumber)
      (__FILE__ ^ ":" ^ (string_of_int __LINE__))

  method private has_chifvar index = H.mem chifvars index

  method get_variables = H.fold (fun _ v a -> v::a) chifvars []

  method get_sym_variables = H.fold (fun _ v a -> v::a) symchifvars []

  method get_domain_sym_variables (domain: string) =
    if H.mem dom_symchifvars domain then
      H.fold (fun _ v a -> v::a) (H.find dom_symchifvars domain) []
    else
      []

  method get_variable (index: int): variable_t traceresult =
    if H.mem chifvars index then
      Ok (H.find chifvars index)
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "No variable found with index: " ^ (string_of_int index)]

  method get_variable_type (var: variable_t): btype_t option =
    varmgr#get_variable_type var


  (* -------------------------------------------------------- transactions -- *)

  val mutable in_transaction = false
  val mutable constant_table = new NumericalCollections.table_t

  method get_scope = scope

  method start_transaction =
    begin
      scope#startTransaction ;
      in_transaction <- true
    end

  method end_transaction =
    let constant_assignments =
      constant_table#fold
        (fun a num tmp -> (ASSIGN_NUM (tmp, NUM num)) :: a) [] in
    begin
      scope#endTransaction ;
      in_transaction <- false ;
      constant_table <- new NumericalCollections.table_t ;
      List.rev constant_assignments
    end

  method mk_num_temp =
    if in_transaction then
      scope#requestNumTmpVariable
    else
      let _ = scope#startTransaction in
      let v = scope#requestNumTmpVariable in
      let _ = scope#endTransaction in
      v

  method mk_sym_temp = scope#requestSymTmpVariable

  method private mk_temp (t:variable_type_t):variable_t =
    if in_transaction then
      if is_numerical_type t then
        self#mk_num_temp
      else
        self#mk_sym_temp
    else
      let _ = self#start_transaction in
      let tmp =
        if is_numerical_type t then
          self#mk_num_temp
        else
          self#mk_sym_temp in
      let _ = self#end_transaction in
      tmp

  method request_num_constant (constant:numerical_t) =
    match constant_table#get constant with
    | Some v -> v
    | _ ->
       let tmp = self#mk_num_temp in
       begin constant_table#set constant tmp ; tmp end

  (* ------------------------------------------------ create new variables -- *)

  method mk_unknown_memory_variable (s:string) =
    self#mk_variable
      (varmgr#make_memory_variable (self#mk_unknown_memory_reference s) NoOffset)

  (* Eventually this function should be replaced with mk_offset_memory_variable *)
  method mk_memory_variable
           ?(save_name=true)
           ?(size=4)
           (memref: memory_reference_int)
           (offset: numerical_t) =
    if memref#is_unknown_reference then
      begin
        log_error_result __FILE__ __LINE__ ["unknown memory reference: tmp created"];
        self#mk_num_temp
      end
    else
      let optName = match memref#get_base with
        | BaseVar v when variable_names#has v#getName#getSeqNumber ->
	   Some (variable_names#get v#getName#getSeqNumber)
        | _ -> None in
      let offset =
        if offset#equal numerical_zero then
          NoOffset
        else
          ConstantOffset (offset, NoOffset) in
      let avar = varmgr#make_memory_variable ~size memref offset in
      let v = self#mk_variable avar in
      let _ = match optName with
	  Some name ->
	  let name = name ^ (memory_offset_to_string offset) in
	  if save_name && (not (variable_names#has v#getName#getSeqNumber)) then
	    self#set_variable_name v name
	  else ()
        | _ -> () in
      v

  method add_memory_offset
           (v:variable_t)
           (memoff: memory_offset_t): variable_t traceresult =
    if self#is_memory_variable v then
      tmap
        (fun av -> self#mk_variable av)
        (varmgr#add_memvar_offset v memoff)
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "variable " ^ (p2s v#toPretty) ^ " is not a memory variable"]

  method mk_offset_memory_variable
           ?(size=4)
           (memref: memory_reference_int)
           (offset: memory_offset_t): variable_t =
    if memref#is_unknown_reference then
      raise
        (BCH_failure
           (LBLOCK [STR "Unknown memory reference in mk_offset_memory_variable"]))
    else
      let avar = varmgr#make_memory_variable memref ~size offset in
      let var = self#mk_variable avar in
      let _ =
        ch_diagnostics_log#add
          "mk_offset_memory_variable"
          (LBLOCK [var#toPretty]) in
      var

  method mk_basevar_memory_variable
           ?(size=4)
           (basevar: variable_t)
           (offset: memory_offset_t): variable_t traceresult =
    let memref_r = self#mk_base_variable_reference basevar in
    TR.tmap
      (fun memref -> self#mk_offset_memory_variable ~size memref offset)
      memref_r

      (*
  method mk_index_offset_global_memory_variable
           ?(elementsize=4)
           (base: numerical_t)
           (offset: memory_offset_t): variable_t traceresult =
    let _ = self#mk_global_variable base in
    let addr_r = numerical_to_doubleword base in
    match addr_r with
    | Error e -> Error ("mk_index_offset_global_memory_variable" :: e)
    | Ok addr ->
       let var =
         self#mk_index_offset_memory_variable
           ~size:elementsize
           self#mk_global_memory_reference (ConstantOffset (base, offset)) in
       let _ =
         if has_symbolic_address_name addr then
           let ivar = self#mk_variable (varmgr#make_initial_memory_value var) in
           let sname = get_symbolic_address_name addr in
           let iname =
             match offset with
             | IndexOffset (v, _, NoOffset) ->
                if variable_names#has v#getName#getSeqNumber then
                  let ivname = variable_names#get v#getName#getSeqNumber in
                  "[" ^ ivname ^ "]"
                else
                  memory_offset_to_string offset
             | _ -> memory_offset_to_string offset in
           let vname = sname ^ iname in
           begin
             self#set_variable_name var vname;
             self#set_variable_name ivar (vname ^ "_in")
           end in
       Ok var
       *)

  method mk_gloc_variable
           (gloc: global_location_int) (offset: memory_offset_t): variable_t =
    let numgaddr = gloc#address#to_numerical in
    let gvar = self#mk_variable (varmgr#make_global_variable numgaddr) in
    let ivar = self#mk_variable (varmgr#make_initial_memory_value gvar) in
    begin
      self#set_variable_name gvar gloc#name;
      self#set_variable_name ivar (gloc#name ^ "_in");
      match offset with
      | NoOffset -> gvar
      | _ ->
         let gvar = varmgr#make_global_variable ~offset numgaddr in
         let gvar = self#mk_variable gvar in
         let ivar = self#mk_variable (varmgr#make_initial_memory_value gvar) in
         let name = gloc#name ^ (memory_offset_to_string offset) in
         begin
           self#set_variable_name gvar name;
           self#set_variable_name ivar (name ^ "_in");
           gvar
         end
    end

  method mk_global_variable_address (dw: doubleword_int): xpr_t traceresult =
    match memmap#containing_location dw with
    | Some gloc when dw#equal gloc#address ->
       let gvar =
         self#mk_variable (self#varmgr#make_global_variable dw#to_numerical) in
       let ivar = self#mk_variable (varmgr#make_initial_memory_value gvar) in
       begin
         self#set_variable_name gvar gloc#name;
         self#set_variable_name ivar (gloc#name ^ "_in");
         Ok (XOp ((Xf "addressofvar"), [XVar gvar]))
       end
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ dw#to_hex_string
              ^ " is not the address of a known global variable"]

  method mk_global_variable
           ?(size=4)
           ?(btype=t_unknown)
           (loc: location_int)
           (base: numerical_t): variable_t traceresult =
    let dw = numerical_mod_to_doubleword base in
    match memmap#containing_location dw with
    | Some gloc ->
       tmap
         ~msg:((elocm __LINE__) ^ "mk_global_variable")
         (fun offset ->
           let gvar =
             self#mk_variable
               (self#varmgr#make_global_variable
                  ~size ~offset gloc#address#to_numerical) in
           let ivar = self#mk_variable (varmgr#make_initial_memory_value gvar) in
           let name = gloc#name ^ (memory_offset_to_string offset) in
           begin
             self#set_variable_name gvar name;
             self#set_variable_name ivar (name ^ "_in");
             gvar
           end)
         (gloc#address_memory_offset
            ~tgtsize:(Some size) ~tgtbtype:btype loc (num_constant_expr base))
    | _ ->
       let _ = memmap#add_location ~size:(Some size) ~btype dw in
       Ok (self#mk_variable (self#varmgr#make_global_variable dw#to_numerical))

  method mk_stackslot_variable
           (stackslot: stackslot_int) (offset: memory_offset_t): variable_t =
    let atts: string list = if stackslot#is_loopcounter then ["lc"] else [] in
    let svar =
      self#mk_variable
        ~atts
        (self#varmgr#make_local_stack_variable
           ~offset (mkNumerical stackslot#offset)) in
    let name = stackslot#name ^ (memory_offset_to_string offset) in
    let _ =
      match atts with
      | [] -> ()
      | _ ->
         log_diagnostics_result
           ~msg:name
           ~tag:"mk_stackslot_variable:loop-counter variable"
           __FILE__ __LINE__
           ["offset: " ^ (memory_offset_to_string offset); p2s svar#toPretty] in
    begin
      self#set_variable_name svar name;
      log_diagnostics_result
        ~msg:name
        ~tag:"mk_stackslot_variable"
        __FILE__ __LINE__
        ["offset: " ^ (memory_offset_to_string offset); p2s svar#toPretty];
      svar
    end

  method mk_register_variable (register:register_t) =
    self#mk_variable (varmgr#make_register_variable register)

  method mk_flag_variable (flag: flag_t) =
    self#mk_variable (varmgr#make_flag_variable flag)

  method mk_cpu_register_variable (cpureg:cpureg_t) =
    self#mk_register_variable (CPURegister cpureg)

  method mk_fpu_register_variable (reg:int) =
    self#mk_register_variable (FloatingPointRegister reg)

  method mk_mmx_register_variable (reg:int) =
    self#mk_register_variable (MmxRegister reg)

  method mk_xmm_register_variable (reg:int) =
    self#mk_register_variable (XmmRegister reg)

  method mk_control_register_variable (reg:int) =
    self#mk_register_variable (ControlRegister reg)

  method mk_debug_register_variable (reg:int) =
    self#mk_register_variable (DebugRegister reg)

  method mk_double_register_variable (reg1:cpureg_t) (reg2:cpureg_t) =
    self#mk_register_variable (DoubleRegister (reg1, reg2))

  method mk_mips_register_variable (reg:mips_reg_t) =
    self#mk_register_variable (MIPSRegister reg)

  method mk_mips_special_register_variable (reg:mips_special_reg_t) =
    self#mk_register_variable (MIPSSpecialRegister reg)

  method mk_mips_fp_register_variable (index:int) =
    self#mk_register_variable (MIPSFloatingPointRegister index)

  method mk_arm_register_variable (reg:arm_reg_t) =
    self#mk_register_variable (ARMRegister reg)

  method mk_arm_double_register_variable (reg1: arm_reg_t) (reg2: arm_reg_t) =
    self#mk_register_variable (ARMDoubleRegister (reg1, reg2))

  method mk_arm_extension_register_variable (r: arm_extension_register_t) =
    self#mk_register_variable (ARMExtensionRegister r)

  method mk_arm_double_extension_register_variable
           (r1: arm_extension_register_t) (r2: arm_extension_register_t) =
    self#mk_register_variable (ARMDoubleExtensionRegister (r1, r2))

  method mk_arm_extension_register_element_variable
        (e: arm_extension_register_element_t) =
    self#mk_register_variable (ARMExtensionRegisterElement e)

  method mk_arm_special_register_variable (r: arm_special_reg_t) =
    self#mk_register_variable (ARMSpecialRegister r)

  method mk_pwr_gp_register_variable (index: int) =
    self#mk_register_variable (PowerGPRegister index)

  method mk_pwr_sp_register_variable (reg: pwr_special_reg_t) =
    self#mk_register_variable (PowerSPRegister reg)

  method mk_pwr_register_field_variable (f: pwr_register_field_t) =
    self#mk_register_variable (PowerCRField f)

  method mk_bridge_value (address:ctxt_iaddress_t) (argnr:int) =
    self#mk_variable (varmgr#make_bridge_value address argnr)

  method mk_frozen_test_value
    (var:variable_t) (taddr:ctxt_iaddress_t) (jaddr:ctxt_iaddress_t) =
    self#mk_variable (varmgr#make_frozen_test_value var taddr jaddr)

  method mk_special_variable (name:string) =
    self#mk_variable (varmgr#make_special_variable name)

  method mk_runtime_constant (name:string) =
    self#mk_variable (varmgr#make_runtime_constant name)

  method mk_return_value (address:ctxt_iaddress_t) =
    self#mk_variable (varmgr#make_return_value address)

  method mk_typecast_value
           (iaddr: ctxt_iaddress_t) (name: string) (ty: btype_t) (reg: register_t) =
    self#mk_variable (varmgr#make_typecast_value iaddr name ty reg)

  method mk_function_pointer_value
    (fname:string) (cname:string) (address:ctxt_iaddress_t) =
    self#mk_variable (varmgr#make_function_pointer_value fname cname address)

  method mk_calltarget_value (tgt:call_target_t) =
    self#mk_variable (varmgr#make_calltarget_value tgt)

  method mk_global_sideeffect_value
           ?(btype=None)
           (iaddr: ctxt_iaddress_t)
           (gaddr: doubleword_int)
           (arg: string) =
    self#mk_variable (varmgr#make_global_sideeffect_value ~btype iaddr arg gaddr)

  method mk_stack_sideeffect_value
           ?(btype=None)
           (iaddr: ctxt_iaddress_t)
           (offset: numerical_t)
           (arg: string) =
    self#mk_variable (varmgr#make_stack_sideeffect_value ~btype iaddr arg offset)

  method mk_side_effect_value (iaddr:ctxt_iaddress_t) (arg:string) =
    self#mk_variable (varmgr#make_side_effect_value iaddr "sev" arg)

  method mk_field_value (sname:string) (offset:int) (fname:string) =
    self#mk_variable (varmgr#make_field_value sname offset fname)

  method mk_symbolic_value (x:xpr_t) =
    match x with
    | XVar v -> v
    | _ -> self#mk_variable (varmgr#make_symbolic_value x)

  method mk_signed_symbolic_value (x: xpr_t) (s0: int) (sx: int) =
    self#mk_variable (varmgr#make_signed_symbolic_value x s0 sx)

  method private probe_global_var_field_values (v:variable_t) (iv:variable_t) =
    if varmgr#has_global_variable_address v then
      log_tfold
        (log_error "probe_global_var_field_values" "invalid global address")
        ~ok:(fun addr ->
          if has_symbolic_address_name addr then
            let vname = get_symbolic_address_name addr in
            let vtype = get_symbolic_address_type addr in
            let _ = self#set_variable_name v vname in
            let _ =
              if is_volatile vtype then
                chlog#add
                  "volatile type not initialized"
                  (LBLOCK [STR (btype_to_string vtype); STR " "; STR vname])
              else
                self#set_variable_name iv (vname ^ "_in") in
            if is_ptrto_known_struct vtype then
              self#set_pointedto_struct_field_names 1 iv vname vtype)
        ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
        (varmgr#get_global_variable_address v)

  method mk_initial_memory_value (v:variable_t):variable_t traceresult =
    if (self#is_memory_variable v) && (self#has_constant_offset v) then
      let iv = self#mk_variable (varmgr#make_initial_memory_value v) in
      let _ =
        if varmgr#is_global_variable v then
          self#probe_global_var_field_values v iv in
      Ok iv
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Variable is not suitable for initial memory value: "
             ^ v#getName#getBaseName]

  method mk_initial_register_value ?(level=0) (r:register_t) =
    self#mk_variable (varmgr#make_initial_register_value r level)


  (* -------------------------------------------- accessors and predicates -- *)

  method private nested_exprs_in_var (v: variable_t): xpr_t list =
    if self#is_symbolic_value v then
      TR.tfold
        ~ok:(fun x -> [x])
        ~error:(fun e ->
          begin
            log_error_result
              ~msg:("invalid symbolic value: " ^ v#getName#getBaseName)
              __FILE__ __LINE__ e;
            []
          end)
        (self#get_symbolic_value_expr v)

    else if self#is_memory_variable v then
      TR.tfold
        ~ok:(fun memoff ->
          List.map (fun v -> XVar v) (get_index_offset_variables memoff))
        ~error:(fun e ->
          begin
            log_error_result __FILE__ __LINE__ e;
            []
          end)
        (self#get_memvar_offset v)
    else
      []

  method variables_in_expr (expr: xpr_t): variable_t list =
    let s = new VariableCollections.set_t in
    let rec vs x =
      match x with
      | XVar v ->
         let xprs = self#nested_exprs_in_var v in
         begin
           s#add v;
           List.iter vs xprs
         end
      | XConst _ -> ()
      | XOp (_, l) -> List.iter vs l
      | XAttr (_, e) -> vs e in
    begin
      vs expr;
      s#toList
    end

  method has_initialized_string_value (v:variable_t) (offset:int) =
    H.mem initial_string_values (v#getName#getSeqNumber, offset)

  method get_initialized_string_value (v:variable_t) (offset:int) =
    let index = v#getName#getSeqNumber in
    if H.mem initial_string_values (index, offset) then
      H.find initial_string_values (index, offset)
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "initialized string value not found for ";
		v#toPretty;
                STR " at offset ";
                INT offset;
		STR " in " ; faddr#toPretty]))

  method private register_virtual_call
                   (v:variable_t) (s:function_interface_t) =
    let _ =
      chlog#add
        "register virtual call"
        (LBLOCK [
             faddr#toPretty;
             STR ": ";
             v#toPretty;
             STR ": ";
	     STR s.fintf_name]) in
    H.add virtual_calls v#getName#getSeqNumber s

  method is_virtual_call (v: variable_t) =
    H.mem virtual_calls v#getName#getSeqNumber

  method get_virtual_target (v: variable_t) =
    try
      H.find virtual_calls v#getName#getSeqNumber
    with
      Not_found ->
      raise
        (BCH_failure
           (LBLOCK [STR "No virtual target found for "; v#toPretty]))

  method get_frozen_variable
           (v: variable_t):
           (variable_t * ctxt_iaddress_t * ctxt_iaddress_t) traceresult =
    varmgr#get_frozen_variable v

  method private get_register_variables =
    List.filter varmgr#is_register_variable self#get_variables

  method private get_function_pointers =
    List.filter varmgr#is_function_pointer self#get_variables

  method get_local_variables =
    let is_local v =
      varmgr#is_local_variable v && varmgr#is_stack_variable v in
    List.filter is_local self#get_variables

  method get_external_memory_variables =
    let is_external v =
      self#is_memory_variable v
      && (not (self#is_volatile_variable v))
      && (not (self#is_unknown_memory_variable v))
      && ((not (self#is_local_variable v))
          || (self#is_stack_parameter_variable v)) in
    List.filter is_external self#get_variables

  method get_bridge_values_at (callsite:ctxt_iaddress_t) =
    List.filter (self#is_bridge_value_at callsite) self#get_variables

  method get_local_stack_variables =
    let is_local v = varmgr#is_local_variable v && varmgr#is_stack_variable v in
    List.filter is_local self#get_variables

  method get_selected_variables (filter: variable_t -> bool): variable_t list =
    List.filter filter self#get_variables

  method get_parent_stack_variables =
    List.filter varmgr#is_stack_parameter_variable self#get_variables

  method get_mips_argument_values =
    List.filter varmgr#is_initial_mips_argument_value self#get_variables

  method get_arm_argument_values =
    List.filter varmgr#is_initial_arm_argument_value self#get_variables

  method get_realigned_stack_variables =
    List.filter varmgr#is_realigned_stack_variable self#get_variables

  method get_stack_parameter_index (v: variable_t): int option =
    if self#is_initial_memory_value v then
      TR.tfold
        ~ok:(fun iv -> varmgr#get_stack_parameter_index iv)
        ~error:(fun e ->
          begin
            log_error_result __FILE__ __LINE__ e;
            None
          end)
        (varmgr#get_initial_memory_value_variable v)
    else
      varmgr#get_stack_parameter_index v

  method get_memvar_basevar (v:variable_t):variable_t traceresult =
    varmgr#get_memvar_basevar v

  method get_memval_basevar (v:variable_t): variable_t traceresult =
    varmgr#get_memval_basevar v

  method get_memvar_offset (v:variable_t): memory_offset_t traceresult =
    varmgr#get_memvar_offset v

  method has_variable_index_offset (v: variable_t): bool =
    varmgr#has_variable_index_offset v

  method get_memval_offset (v:variable_t): memory_offset_t traceresult =
    varmgr#get_memval_offset v

  method get_memvar_dependencies (v: variable_t): variable_t list =
    varmgr#get_memvar_dependencies v

  method get_constant_offsets (v: variable_t): numerical_t list traceresult =
    let offset_r =
      if self#is_initial_memory_value v then
        self#get_memval_offset v
      else if self#is_memory_variable v then
        self#get_memvar_offset v
      else
        Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
               ^ "Not a memory variable or initial memory value: "
               ^ v#getName#getBaseName] in
    TR.tbind
      (fun offset ->
        if is_constant_offset offset then
          get_constant_offsets offset
        else
          Error [
              __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable does not have constant offset: "
              ^ (p2s v#toPretty)])
      offset_r

  method get_total_constant_offset (v:variable_t): numerical_t traceresult =
    TR.tmap
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (List.fold_left (fun acc n -> acc#add n) numerical_zero)
      (self#get_constant_offsets v)

  method get_calltarget_value (v: variable_t): call_target_t traceresult =
    varmgr#get_calltarget_value v

  method get_register (v: variable_t): register_t traceresult =
    varmgr#get_register v

  method get_pointed_to_function_name (v: variable_t): string traceresult =
    varmgr#get_pointed_to_function_name v

  method get_call_site (v: variable_t): ctxt_iaddress_t traceresult =
    varmgr#get_call_site v

  method get_se_argument_descriptor (v: variable_t): string traceresult =
    varmgr#get_se_argument_descriptor v

  method get_global_sideeffect_target_address (v: variable_t): doubleword_result =
    varmgr#get_global_sideeffect_target_address v

  method is_global_sideeffect = varmgr#is_global_sideeffect

  method get_var_count = List.length self#get_variables

  method get_globalvar_count =
    List.length (List.filter self#is_global_variable self#get_variables)

  method get_returnvar_count =
    List.length (List.filter self#is_return_value self#get_variables)

  method get_sideeffvar_count =
    List.length (List.filter self#is_sideeffect_value self#get_variables)

  method is_global_variable (v: variable_t) =
    (varmgr#is_global_variable v) ||
      ((varmgr#is_initial_memory_value v) &&
         (tfold_default
            self#is_global_variable
            false
	    (varmgr#get_initial_memory_value_variable v)))

  method is_mutable_global_variable (v: variable_t): bool =
    (varmgr#is_global_variable v)
    && (not (fndata#is_const_global_variable (self#variable_name_to_string v)))

  method has_global_variable_address (v: variable_t): bool =
    varmgr#has_global_variable_address v

  method get_global_variable_address (v: variable_t): doubleword_result =
    if (varmgr#is_global_variable v) then
      if varmgr#has_global_variable_address v then
        varmgr#get_global_variable_address v
      else
        Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
               ^ "No constant numerical offset: "
               ^ v#getName#getBaseName]
    else if varmgr#is_initial_memory_value v then
      tbind
        ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
        (fun ivar ->
          if varmgr#has_global_variable_address ivar then
            self#get_global_variable_address ivar
          else
            Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                   ^ "Not a constant offset: "
                   ^ v#getName#getBaseName])
        (varmgr#get_initial_memory_value_variable v)
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Not a global variable or initial-value global variable: "
             ^ v#getName#getBaseName]

  method is_volatile_variable (v: variable_t) =
    if varmgr#has_global_variable_address v then
      tfold_default
        (fun addr ->
          if has_symbolic_address_name addr then
            let vtype = get_symbolic_address_type addr in
            is_volatile vtype
          else
            false)
        false
        (varmgr#get_global_variable_address v)
    else
      false

  method get_optreturn_value_capabilities
           (var: variable_t): (ctxt_iaddress_t * type_cap_label_t list) option =

    let memvar_caps (v: variable_t) =
      match self#get_optreturn_value_capabilities v with
      | Some (callsite, labels) ->
         tfold_default
           (fun offset ->
             if is_constant_offset offset then
               tfold_default
                 (fun num ->
                   Some (callsite,
                         Load :: (OffsetAccess (4, num#toInt)) :: labels))
                 None
                 (get_total_constant_offset offset)
             else
               None)
           None
           (self#get_memvar_offset v)
      | _ -> None in

    let memval_caps (v: variable_t) =
      match self#get_optreturn_value_capabilities v with
      | Some (callsite, labels) ->
         tfold_default
           (fun offset ->
             if is_constant_offset offset then
               tfold_default
                 (fun num ->
                   Some (callsite,
                         Load :: (OffsetAccess (4, num#toInt)) :: labels))
                 None
                 (get_total_constant_offset offset)
             else
               None)
           None
           (self#get_memval_offset v)
      | _ -> None in

    let aux (v: variable_t) =
      if self#is_return_value v then
        tfold_default
          (fun callsite -> Some (callsite, [])) None (self#get_call_site v)
      else if self#is_basevar_memory_variable v then
        tfold_default memvar_caps None (self#get_memvar_basevar v)
      else if self#is_basevar_memory_value v then
        tfold_default memval_caps None (self#get_memval_basevar v)
      else
        None in

    aux var

  method is_local_variable = varmgr#is_local_variable

  method is_function_pointer = varmgr#is_function_pointer

  method is_bridge_value = varmgr#is_bridge_value

  method is_bridge_value_at = varmgr#is_bridge_value_at

  method is_memory_variable = varmgr#is_memory_variable

  method is_basevar_memory_variable = varmgr#is_basevar_memory_variable

  method is_basevar_memory_value = varmgr#is_basevar_memory_value

  method is_calltarget_value = varmgr#is_calltarget_value

  method has_constant_offset (v:variable_t) = varmgr#has_constant_offset v

  method is_unknown_memory_variable = varmgr#is_unknown_memory_variable

  method is_unknown_base_memory_variable =
    varmgr#is_unknown_base_memory_variable

  method is_unknown_offset_memory_variable =
    varmgr#is_unknown_offset_memory_variable

  method get_memory_reference (v:variable_t): memory_reference_int traceresult =
    if self#is_initial_memory_value v then
      varmgr#get_memval_reference v
    else
      varmgr#get_memvar_reference v

  method is_stack_variable = varmgr#is_stack_variable

  method is_initial_stackpointer_value (v:variable_t) =
    varmgr#is_initial_stackpointer_value v

  method is_stack_parameter_variable (v:variable_t) =
    (varmgr#is_stack_parameter_variable v)

  method is_local_stack_variable = varmgr#is_local_stack_variable

  method is_stack_parameter_value (v:variable_t) =
    (self#is_initial_memory_value v)
    && (tfold_default
          (fun iv -> self#is_stack_parameter_variable iv)
          false
          (varmgr#get_initial_memory_value_variable v))

  method private get_argbasevar_with_offsets_aux
                   (v:variable_t)
                   (offsets:numerical_t list):
                   (variable_t * numerical_t list) option =
    if self#is_initial_memory_value v then
      TR.tfold
        ~ok:(fun iv ->
          if self#is_basevar_memory_variable iv then
            TR.tfold
              ~ok:(fun basevar ->
                TR.tfold
                  ~ok:(fun o ->
                    let newoffsets = o :: offsets in
                    if self#is_stack_parameter_variable basevar ||
                         self#is_initial_register_value basevar then
                      Some (basevar, newoffsets)
                    else
                      self#get_argbasevar_with_offsets_aux basevar newoffsets)
                  ~error:(fun e ->
                    begin self#log_dc_error_result __LINE__ e; None end)
                  (self#get_total_constant_offset iv))
              ~error:(fun e ->
                begin self#log_dc_error_result __LINE__ e; None end)
              (self#get_memvar_basevar iv)
          else
            None)
        ~error:(fun e ->
          begin self#log_dc_error_result __LINE__ e; None end)
        (varmgr#get_initial_memory_value_variable v)
    else
      None

  method get_argbasevar_with_offsets
           (v:variable_t): (variable_t * numerical_t list) option =
    self#get_argbasevar_with_offsets_aux v []

  method private get_globalbasevar_with_offsets_aux
                   (v:variable_t)
                   (offsets:numerical_t list):
                   (variable_t * numerical_t list) option =
    if self#is_initial_memory_value v then
      TR.tfold
        ~ok:(fun iv ->
          if self#is_basevar_memory_variable iv then
            TR.tfold
              ~ok:(fun basevar ->
                TR.tfold
                  ~ok:(fun o ->
                    let newoffsets = o :: offsets in
                    if self#is_global_variable basevar then
                      Some (basevar, newoffsets)
                    else
                      self#get_globalbasevar_with_offsets_aux basevar newoffsets)
                  ~error:(fun e ->
                    begin self#log_dc_error_result __LINE__ e; None end)
                  (self#get_total_constant_offset iv))
              ~error:(fun e->
                begin self#log_dc_error_result __LINE__ e; None end)
              (self#get_memvar_basevar iv)
          else
            None)
        ~error:(fun e ->
          begin self#log_dc_error_result __LINE__ e; None end)
        (varmgr#get_initial_memory_value_variable v)
    else
      None

  method get_globalbasevar_with_offsets
           (v:variable_t): (variable_t * numerical_t list) option =
    self#get_globalbasevar_with_offsets_aux v []

  method is_return_value = varmgr#is_return_value

  method is_sideeffect_value = varmgr#is_sideeffect_value

  method is_register_variable = varmgr#is_register_variable

  method is_stackpointer_variable = varmgr#is_stackpointer_variable

  method is_initial_register_value = varmgr#is_initial_register_value

  method is_initial_mips_argument_value = varmgr#is_initial_mips_argument_value

  method is_initial_arm_argument_value = varmgr#is_initial_arm_argument_value

  method is_function_initial_value = varmgr#is_function_initial_value

  method is_initial_memory_value = varmgr#is_initial_memory_value

  method is_initial_value (v:variable_t) =
    self#is_initial_memory_value v || self#is_initial_register_value v

  method get_init_value_variable (v:variable_t): variable_t traceresult =
    if self#is_initial_memory_value v then
      varmgr#get_initial_memory_value_variable v
    else if self#is_initial_register_value v then
      tbind
        ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ v#getName#getBaseName)
        (fun iv ->
          match iv with
          | CPURegister r -> Ok (self#mk_cpu_register_variable r)
          | MIPSRegister r -> Ok (self#mk_mips_register_variable r)
          | MIPSSpecialRegister r -> Ok (self#mk_mips_special_register_variable r)
          | ARMRegister r -> Ok (self#mk_arm_register_variable r)
          | ARMExtensionRegister r ->
             Ok (self#mk_arm_extension_register_variable r)
          | PowerGPRegister i -> Ok (self#mk_pwr_gp_register_variable i)
          | PowerSPRegister r -> Ok (self#mk_pwr_sp_register_variable r)
          | _ ->
             Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                    ^ "Not a cpu/mips/arm/pwr initial register value: "
                    ^ v#getName#getBaseName])
        (self#get_initial_register_value_register v)
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Variable is not an initial value: "
             ^ v#getName#getBaseName]

  method get_initial_register_value_register
           (v:variable_t): register_t traceresult =
    varmgr#get_initial_register_value_register v

  method is_frozen_test_value = varmgr#is_frozen_test_value

  method is_symbolic_value = varmgr#is_symbolic_value

  method is_signed_symbolic_value = varmgr#is_signed_symbolic_value

  method is_addressof_symbolic_value (v: variable_t) =
    if self#is_symbolic_value v then
      let symx_r = self#get_symbolic_value_expr v in
      TR.tfold_default
        (fun symx ->
          match symx with
          | XOp ((Xf "addressofvar"), _) -> true
          | _ -> false)
        false
        symx_r
    else
      false

  method get_addressof_symbolic_expr (v: variable_t): xpr_t traceresult =
    if self#is_addressof_symbolic_value v then
      let symx_r = self#get_symbolic_value_expr v in
      TR.tbind
        ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
        (fun symx ->
          match symx with
          | XOp ((Xf "addressofvar"), [x]) -> Ok x
          | _ ->
             Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                    ^ "Not an addressofvar symbolic expression: "
                    ^ (x2s symx)])
        symx_r
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Not a symbolic-value expression: "
             ^ (p2s v#toPretty)]

  method get_symbolic_value_expr (v: variable_t): xpr_t traceresult =
    if self#is_symbolic_value v then
      varmgr#get_symbolic_value_expr v
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Not a symbolic value expr: " ^ v#getName#getBaseName]

  method is_in_test_jump_range (v: variable_t) (a: ctxt_iaddress_t) =
    (varmgr#is_in_test_jump_range a v)

  method is_unknown_reference = varmgr#memrefmgr#is_unknown_reference

  method private write_xml_assembly_variable_id
                   (node: xml_element_int) (v: assembly_variable_int) =
    begin
      node#setAttribute "vn" v#get_name ;
      node#setIntAttribute "vx" v#index
    end

end


class function_info_t
        (faddr: doubleword_int)
        (fndata: function_data_int)
        (varmgr: variable_manager_int)
        (invio: invariant_io_int)
        (varinvio: var_invariant_io_int):function_info_int =
object (self)

  (* Function info permanent state: ------------------------------------------ *
   * These data items are saved and reloaded as part of the intermediate       *
   * analysis results.                                                         *
   * ------------------------------------------------------------------------- *)
  val env = new function_environment_t faddr fndata varmgr
  val constant_table = new VariableCollections.table_t          (* constants *)
  val calltargets = H.create 5                               (* call-targets *)

  val base_pointers = new VariableCollections.set_t         (* base-pointers *)
  val mutable stack_adjustment = None                    (* stack-adjustment *)
  val saved_registers = H.create 3            (* saved-registers -- not read *)

  val cc_user_to_setter = H.create 3                             (* cc-users *)
  val test_expressions = H.create 3                      (* test-expressions *)
  val test_variables = H.create 3                          (* test-variables *)

  (* val cvariable_types = H.create 3 *)     (* types of constant-value variables *)

  (* ------------------------------------------------------------------------- *)

  (* Function info transient state: ------------------------------------------ *
   * These data items are lost/recreated from one analysis run to the next     *
   * ------------------------------------------------------------------------- *)

  val instrbytes = H.create 5
  val jump_targets = H.create 5                           (* to be saved *)

  val mutable nonreturning = false
  val mutable user_summary = None     (* to be deprecated *)
  val mutable appsummary =
    let hexfaddr = faddr#to_hex_string in
    let lenfaddr = String.length hexfaddr in
    default_summary ("sub_" ^ (String.sub (faddr#to_hex_string) 2 (lenfaddr - 2)))

  val cc_setter_to_user = H.create 3                      (* to be saved ? *)
  val mutable complete = true

  val mutable dynlib_stub = None                (* call_target_t option *)
  val mutable sideeffects_changed = false
  val mutable call_targets_set = false
  val nonreturning_calls = new StringCollections.set_t
  val mutable invariants_to_be_reset = false
  val stackframe = mk_function_stackframe fndata varmgr
  val proofobligations =
    mk_proofobligations faddr (mk_xpodictionary varmgr#vard#xd)

  (* ------------------------------------------------------------------------- *)

  method private log_dc_error_result (line: int) (e: string list) =
    if BCHSystemSettings.system_settings#collect_data then
      self#log_error_result line e
    else
      ()

  method private log_error_result (line: int) (e: string list) =
    log_error_result ~msg:self#a#to_hex_string __FILE__ line e

  method stackframe = stackframe

  method xpod = self#proofobligations#xpod

  method proofobligations = proofobligations

  method set_instruction_bytes (ia:ctxt_iaddress_t) (b:string) =
    H.add instrbytes ia b

  method get_instruction_bytes (ia:ctxt_iaddress_t) =
    if H.mem instrbytes ia then
      H.find instrbytes ia
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No instruction bytes found for ";
                STR ia;
                STR " in function ";
                faddr#toPretty]))

  method sideeffects_changed = sideeffects_changed

  method call_targets_were_set = call_targets_set

  method get_address = faddr

  method a = faddr

  method get_function_data = functions_data#get_function self#get_address

  method env = env

  method finv = invio

  method fvarinv = varinvio

  val uselocs = H.create 5
  val usehighlocs = H.create 5

  method add_reaching_def
           (iaddr: string) (v: variable_t) (deflocs: symbol_t list) =
    begin
      let deflocs =
        if fndata#has_function_annotation then
          fndata#filter_deflocs iaddr v deflocs
        else
          deflocs in
      self#fvarinv#add_reaching_def iaddr v deflocs;
      List.iter (fun s ->
          if (List.length s#getAttributes) = 0 then
            let defloc = s#getBaseName in
            begin
              (if self#is_use_loc v iaddr then
                 self#fvarinv#add_use_loc defloc v iaddr);
              (if self#is_use_high_loc v iaddr then
                 self#fvarinv#add_use_high_loc defloc v iaddr)
            end) deflocs
    end

  method add_use_loc (v: variable_t) (iaddr: string) =
    let varix = v#getName#getSeqNumber in
    let entry =
      if H.mem uselocs varix then
        H.find uselocs varix
      else
        [] in
    H.replace uselocs varix (iaddr :: entry)

  method add_use_high_loc (v: variable_t) (iaddr: string) =
    let varix = v#getName#getSeqNumber in
    let entry =
      if H.mem usehighlocs varix then
        H.find usehighlocs varix
      else
        [] in
    H.replace usehighlocs varix (iaddr :: entry)

  method is_use_loc (v: variable_t) (iaddr: string) =
    let varix = v#getName#getSeqNumber in
    (H.mem uselocs varix) && (List.mem iaddr (H.find uselocs varix))

  method is_use_high_loc (v: variable_t) (iaddr: string) =
    let varix = v#getName#getSeqNumber in
    (H.mem usehighlocs varix) && (List.mem iaddr (H.find usehighlocs varix))

  method iinv (iaddr: ctxt_iaddress_t): location_invariant_int =
    invio#get_location_invariant iaddr

  method ivarinv (iaddr: ctxt_iaddress_t): location_var_invariant_int =
    varinvio#get_location_var_invariant iaddr

  method reset_invariants =
    if invariants_to_be_reset then
      begin
	invio#reset ;
	chlog#add "reset invariants" (STR faddr#to_hex_string);
      end

  method schedule_invariant_reset = invariants_to_be_reset <- true

  method were_invariants_reset = invariants_to_be_reset

  method get_name =
    if functions_data#has_function_name self#get_address then
      (functions_data#get_function self#get_address)#get_function_name
    else
      self#get_address#to_hex_string

  method set_incomplete = complete <- false
  method set_complete = complete <- true
  method is_complete = complete

  method set_stack_adjustment (a:int option) =
    match a with
    | Some n when n > 0 ->
       begin
         chlog#add
           "set stack adjustment"
           (LBLOCK [self#get_address#toPretty; STR ": "; INT n]);
         self#update_summary
           (function_summary_add_stack_adjustment self#get_summary n);
         stack_adjustment <- a
       end
    | Some n when n = 0 -> ()
    | Some n when n < 0 ->
       ch_error_log#add
         "unexpected stack adjustment"
         (LBLOCK [self#get_address#toPretty; STR ": "; INT n])
    | _ ->
       stack_adjustment <- a;

  method get_stack_adjustment = stack_adjustment

  method add_constant (v:variable_t) (c:numerical_t) = constant_table#set v c

  method has_constant (v:variable_t) =
    match constant_table#get v with Some _ -> true | _ -> false

  method get_constant (v:variable_t) =
    match constant_table#get v with
      Some c -> c
    | _ -> raise (Invocation_error "function_info#get_constant")

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * record register arguments                                                 *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method save_register
           (vmem: variable_t) (iaddr: ctxt_iaddress_t) (reg: register_t) =
    if self#env#is_stack_variable vmem then
      TR.tfold
        ~ok:(fun offset ->
          match offset with
          | ConstantOffset (n, NoOffset) ->
             self#stackframe#add_register_spill ~offset:n#toInt reg iaddr
          | _ ->
             log_error_result
               ~msg:"save_register:not a constant offset"
               __FILE__ __LINE__
               ["(" ^ (p2s self#get_address#toPretty) ^ "," ^ iaddr ^ "): ";
                (p2s vmem#toPretty) ^ " with " ^ (register_to_string reg)
                ^ " and offset " ^ (memory_offset_to_string offset)])
        ~error:(fun e ->
          log_error_result
            ~msg:"save_register"
            __FILE__ __LINE__
            (["(" ^ (p2s self#get_address#toPretty) ^ "," ^ iaddr ^ "): ";
              (p2s vmem#toPretty) ^ " with " ^ (register_to_string reg)] @ e))
        (self#env#get_memvar_offset vmem)
    else
      log_error_result
        ~msg:"save register:not a stack variable"
        __FILE__ __LINE__
        ["(" ^ (p2s self#get_address#toPretty) ^ "," ^ iaddr ^ "): ";
         "not a stack variable: "
         ^ (p2s vmem#toPretty) ^ " with " ^ (register_to_string reg)]

  method restore_register
           (memaddr: xpr_t) (iaddr:ctxt_iaddress_t) (reg:register_t) =
    match memaddr with
    | XOp (XMinus, [XVar v; offset]) ->
       if self#env#is_initial_stackpointer_value v then
         match offset with
         | XConst (IntConst n) ->
            self#stackframe#add_register_restore ~offset:n#neg#toInt reg iaddr
         | _ ->
            log_error_result
              ~msg:"restore register:not a constant offset"
              __FILE__ __LINE__
              ["(" ^ (p2s self#get_address#toPretty) ^ "," ^ iaddr ^ ")";
               (x2s memaddr)]
       else
         ()
    | _ ->
       ()

  method saved_registers_to_pretty =
    let p = ref [] in
    let _ =
      H.iter (fun _ s -> p := (LBLOCK [s#toPretty; NL]) :: !p) saved_registers in
    match !p with
      [] ->
       LBLOCK [
           STR (string_repeat "~" 80); NL; STR "No saved registers"; NL;
	   STR (string_repeat "~" 80); NL]
    | l ->
       LBLOCK [
           STR "Saved Registers"; NL; STR (string_repeat "~" 80); NL;
           LBLOCK l; NL;
	   STR (string_repeat "~" 80); NL]

  method set_nonreturning =
    if nonreturning then () else
      let fa = self#get_address in
      begin
	chlog#add "set nonreturning" (LBLOCK [fa#toPretty]);
	(functions_data#get_function fa)#set_non_returning;
	nonreturning <- true
      end

  method get_summary = appsummary

  method update_summary (fs: function_summary_int) = appsummary <- fs

  method private get_function_semantics =
    self#get_summary#get_function_semantics

  method set_bc_summary (fs: function_summary_int) =
    begin
      appsummary <- fs;
      env#set_argument_names fs#get_function_interface;
      chlog#add
        "set-bc-summary"
        (LBLOCK [
             function_interface_to_pretty fs#get_function_interface;
             STR " with function signature ";
             STR (btype_to_string
                    fs#get_function_interface.fintf_type_signature.fts_returntype)])
    end

  method read_xml_user_summary (node:xml_element_int) =
    try
      let summary = read_xml_function_summary node in
      begin
	user_summary <- Some summary;
	env#set_argument_names summary#get_function_interface;
	List.iter (fun p -> match p with
	| XXIncludes (ArgValue par, sc) ->
	  self#env#set_argument_structconstant par sc
	| _ -> ()) summary#get_preconditions;
	chlog#add "user function summary" (LBLOCK [self#get_address#toPretty])
      end
    with
    | XmlDocumentError (line, col, p)
    | XmlReaderError (line, col, p) ->
       let msg =
         LBLOCK [STR "function summary "; self#get_address#toPretty; p] in
	raise (XmlReaderError (line, col, msg))

  method set_unknown_java_native_method_signature =
    self#env#set_unknown_java_native_method_signature

  (* Note: this method may be out-of-sync with the current definition of
     function_interface *)
  method set_java_native_method_signature (api:java_native_method_api_t) =
    let _ = self#env#set_java_native_method_signature api in
    let args = api.jnm_signature#descriptor#arguments in
    let isStatic = api.jnm_static in
    let jthis = if isStatic then "this$obj" else "this$class" in
    let stackPars = [ (8, jthis, t_voidptr) ; (4, "jni$Env", t_voidptr) ] in
    let (_,_,stackPars) =
      List.fold_left (fun (count,off,pars) ty ->
          let name =
            (get_java_type_name_prefix ty) ^ "_" ^ (string_of_int count) in
          (count+1, off + (get_java_type_length ty),
           (off, name, (get_java_type_btype ty)) :: pars)) (3,12,stackPars) args in
    let mkparam (offset, name, btype) =
      let desc = if offset = 0 then "JNI interface pointer" else "" in
      let index = offset / 4 in
      let par = mk_indexed_stack_parameter ~btype ~desc offset index in
      modify_name_par name par in
    let fts = {
      fts_parameters = List.map mkparam stackPars;
      fts_varargs = false;
      fts_va_list = None;
      fts_returntype =
	(match api.jnm_signature#descriptor#return_value with
	| Some ty -> get_java_type_btype ty
	| _ -> t_void);
      fts_rv_roles = [];
      fts_stack_adjustment = Some (4 * (List.length stackPars));
      fts_calling_convention = "stdcall";
      fts_registers_preserved = []} in
    let fintf = {
        fintf_name = api.jnm_signature#name;
        fintf_jni_index = None;
        fintf_syscall_index = None;
        fintf_type_signature = fts;
        fintf_bctype = None;
        fintf_parameter_locations = [];
        fintf_returntypes = []
      } in
    let fsem = default_function_semantics in
    let fdoc = default_function_documentation in
    let summary = make_function_summary ~fintf ~sem:fsem ~doc:fdoc in
    appsummary <- summary;

  method summary_to_pretty = self#get_summary#toPretty

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * setters and users of condiditon codes; conditional jumps                 *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method connect_cc_user
           (user_addr:ctxt_iaddress_t) (setter_addr:ctxt_iaddress_t) =
    begin
      H.replace cc_setter_to_user setter_addr user_addr ;
      H.replace cc_user_to_setter user_addr setter_addr
    end

  method has_associated_cc_setter (user_address:ctxt_iaddress_t) =
    H.mem cc_user_to_setter user_address

  method get_associated_cc_setter (user_address:ctxt_iaddress_t) =
    if H.mem cc_user_to_setter user_address then
      H.find cc_user_to_setter user_address
    else
      raise (BCH_failure
               (LBLOCK [STR "function_info#get_associated_condition: ";
			STR user_address ]))

  method has_associated_cc_user (setter_address:ctxt_iaddress_t) =
    H.mem cc_setter_to_user setter_address

  method get_associated_cc_user (setter_address:ctxt_iaddress_t) =
    if H.mem cc_setter_to_user setter_address then
      H.find cc_setter_to_user setter_address
    else
      raise
        (BCH_failure
           (LBLOCK [STR "function_info#get_associated_jump: ";
                    STR setter_address ]))

  method set_test_expr (iaddr:ctxt_iaddress_t) (x:xpr_t) =
    H.replace test_expressions iaddr x

  method get_num_conditions_associated = H.length cc_user_to_setter

  method get_num_test_expressions = H.length test_expressions

  method get_test_expr (iaddr:ctxt_iaddress_t) =
    if H.mem test_expressions iaddr then
      H.find test_expressions iaddr
    else
      random_constant_expr

  method get_test_exprs =
    let result = ref [] in
    let _ = H.iter (fun ix v -> result := (ix,v) :: !result) test_expressions in
    !result

  method set_test_variables
           (test_iaddr: ctxt_iaddress_t)
           (vars: (variable_t * variable_t) list) =
    (* Multiple jump (or other use) sites may be using the same test, so we
       cannot just replace the set of test_variables, when a new set comes in.
     *)
    let entry =
      if H.mem test_variables test_iaddr then
        H.find test_variables test_iaddr
      else
        [] in
    let newentry =
      List.fold_left (fun acc (v1, v2) ->
          if (List.exists (fun (v1', v2') -> v1#equal v1' && v2#equal v2') acc) then
            acc
          else
            (v1, v2) :: acc) entry vars in
    H.replace test_variables test_iaddr newentry

  method get_test_variables (test_iaddr:ctxt_iaddress_t) =
    if H.mem test_variables test_iaddr then
      H.find test_variables test_iaddr
    else []

  method has_test_expr (iaddr:ctxt_iaddress_t) = H.mem test_expressions iaddr

  method private conditional_jump_state_to_pretty =
    let p = ref [] in
    begin
      H.iter (fun k v ->
	p := (LBLOCK [ STR k ; STR ": " ; pr_expr v ; NL ]) :: !p)
	test_expressions ;
      LBLOCK [ STR "Test expressions: " ; NL ; (LBLOCK !p) ; NL ]
    end

  method private write_xml_cc_users (node:xml_element_int) =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) cc_user_to_setter in
    node#appendChildren (List.map (fun (k,v) ->
      let cNode = xmlElement "user" in
      let set = cNode#setAttribute in
      begin set "src" k ; set "tgt" v ; cNode end ) !l)

  method private read_xml_cc_users (node:xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun cNode ->
      let get = cNode#getAttribute in
      H.replace cc_user_to_setter (get "src") (get "tgt")) (getcc "user")

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * call targets                                                             *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method set_call_target (iaddr:ctxt_iaddress_t) (ctinfo:call_target_info_int) =
    begin
      call_targets_set <- true;
      H.replace calltargets iaddr ctinfo
    end

  method get_call_target (i: ctxt_iaddress_t) =
    if H.mem calltargets i then
      H.find calltargets i
    else
      begin
        ch_error_log#add
          "call-target missing"
          (LBLOCK [
               STR "Function ";
               self#a#toPretty ;
               STR ": No call-target-info found at ";
               STR i]);
        mk_call_target_info
          (default_function_interface "unknown")
          default_function_semantics
          UnknownTarget
      end

  method has_call_target (i:ctxt_iaddress_t) =  H.mem calltargets i

  method get_callees =	H.fold (fun _ v a -> v::a) calltargets []

  method get_callees_located =
    H.fold (fun k v a -> (k,v)::a) calltargets []

  method get_call_count = H.length calltargets

  method get_call_category_count (cat:string) =
    H.fold
      (fun _ ctinfo acc ->
        if ctinfo#is_call_category cat then acc+1 else acc)
      calltargets 0


  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * base pointers                                                             *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method add_base_pointer (var:variable_t) =
    base_pointers#add var

  method get_base_pointers = base_pointers#toList

  method is_base_pointer (var:variable_t) = base_pointers#has var

  method base_pointers_to_pretty =
    if base_pointers#isEmpty then
      LBLOCK [
          STR (string_repeat "." 80);
          NL ;
          STR "No base pointers";
          NL;
	  STR (string_repeat "." 80);
          NL]
    else
      LBLOCK [
          STR (string_repeat "~" 80);
          NL;
          STR "Base pointers: ";
	  pretty_print_list
            base_pointers#toList env#variable_name_to_pretty "" ", " "";
	  NL;
          STR (string_repeat "~" 80);
          NL]

  method private write_xml_base_pointers (node:xml_element_int) =
    node#appendChildren (List.map (fun v ->
      let vNode = xmlElement "base" in
      begin
	vNode#setAttribute "vn" v#getName#getBaseName ;
	vNode#setIntAttribute "vx" v#getName#getSeqNumber ;
	vNode
      end) self#get_base_pointers)

  method private read_xml_base_pointers (node:xml_element_int) =
    List.iter (fun n ->
      let get = n#getAttribute in
      let geti = n#getIntAttribute in
      let var =
        new variable_t
          (new symbol_t ~seqnr:(geti "vx") (get "vn")) NUM_VAR_TYPE in
      self#add_base_pointer var) (node#getTaggedChildren "base")


  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * jump table targets                                                        *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method set_jumptable_target
           (jumpAddr:ctxt_iaddress_t)
           (base:doubleword_int)
           (jt:jumptable_int)
           (reg:register_t) =
    begin
      H.replace jump_targets jumpAddr (JumptableTarget (base,jt,reg));
      (if collect_diagnostics () then
         chlog#add
           "set jumptable target"
           (LBLOCK [
                STR jumpAddr;
                STR "; base: ";
                base#toPretty;
                STR "; on register: ";
                STR (register_to_string reg)]))
    end

  method set_offsettable_target
           (jumpAddr:ctxt_iaddress_t)
           (base:doubleword_int)
           (jt:jumptable_int)
           (db:data_block_int) =
    H.replace jump_targets jumpAddr (OffsettableTarget (base, jt, db))

  method set_global_jumptarget (jumpAddr: ctxt_iaddress_t) (v: variable_t) =
    if env#is_global_variable v then
      log_tfold
        (log_error "set_global_jumptarget" "invalid global address")
        ~ok:(fun gaddr ->
          H.replace
            jump_targets jumpAddr (JumpOnTerm (mk_global_parameter_term gaddr)))
        ~error:(fun _ -> ())
        (env#get_global_variable_address v)
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "set_global_jumptarget: ";
                STR "variable is not a global variable: ";
                v#toPretty]))

  method set_so_jumptarget
           (jumpAddr:ctxt_iaddress_t) (fname:string) (ctinfo:call_target_info_int) =
    begin
      track_function
        ~iaddr:jumpAddr self#a
        (LBLOCK [ STR "set so jumptarget: " ; STR fname ]) ;
      H.replace jump_targets jumpAddr (SOJumpTarget fname) ;
      self#set_call_target jumpAddr ctinfo
    end

  method set_dll_jumptarget
           (jumpAddr:ctxt_iaddress_t)
           (lib:string)
           (fname:string)
           (ctinfo:call_target_info_int) =
    begin
      track_function
        ~iaddr:jumpAddr self#a
        (LBLOCK [ STR "set dll jumptarget: " ; STR lib ;
                  STR  ", " ;  STR fname ]) ;
      H.replace jump_targets jumpAddr (DllJumpTarget (lib,fname)) ;
      self#set_call_target jumpAddr ctinfo
    end

  method is_dll_jumptarget (iaddr:ctxt_iaddress_t) =
    H.mem jump_targets iaddr &&
      (match H.find jump_targets iaddr with DllJumpTarget _ -> true | _ -> false)

  method get_dll_jumptarget (iaddr:ctxt_iaddress_t) =
    if H.mem jump_targets iaddr then
      match H.find jump_targets iaddr with
      | DllJumpTarget (lib,fname) -> (lib,fname)
      | _ ->
	 raise
           (BCH_failure
              (LBLOCK [
                   STR iaddr;
                   STR ": ";
		   STR "Jump target is not a dll target"]))
    else
      raise
        (BCH_failure
           (LBLOCK [STR iaddr; STR ": "; STR "No jump target found"]))

  method set_unknown_jumptarget (jumpAddr:ctxt_iaddress_t) =
    if H.mem jump_targets jumpAddr then () else
      H.add jump_targets jumpAddr UnknownJumpTarget

  method get_jump_target (jumpAddr:ctxt_iaddress_t) =
    if H.mem jump_targets jumpAddr then
      H.find jump_targets jumpAddr
    else
      UnknownJumpTarget

  method get_jumptable_jumps =
    H.fold (fun k v acc ->
      match v with JumptableTarget _ -> k :: acc | _ -> acc)
      jump_targets []

  method get_indirect_jumps_count = H.length jump_targets

  method get_unknown_jumps_count =
    H.fold (fun _ v acc ->
      match v with UnknownJumpTarget -> acc+1 | _ -> acc) jump_targets 0

  method get_dll_jumps_count =
    H.fold (fun _ v acc ->
      match v with DllJumpTarget _ -> acc+1 | _ -> acc) jump_targets 0

  method get_jumptable_count =
    H.fold (fun _ v acc ->
      match v with JumptableTarget _ -> acc+1 | _ -> acc) jump_targets 0

  method get_offsettable_count =
    H.fold (fun _ v acc ->
      match v with OffsettableTarget _ -> acc+1 | _ -> acc) jump_targets 0

  method get_global_jump_count =
    H.fold (fun _ v acc ->
        match v with
        | JumpOnTerm (ArgValue p) when is_global_parameter p -> acc+1
        | _ -> acc) jump_targets 0

  method get_argument_jump_count =
    H.fold (fun _ v acc ->
        match v with
        | JumpOnTerm (ArgValue p) when is_arg_parameter p -> acc+1
        | _ -> acc) jump_targets 0

  method has_jump_target (jumpAddr:ctxt_iaddress_t) =
    H.mem jump_targets jumpAddr &&
      (match H.find jump_targets jumpAddr with
       | UnknownJumpTarget -> false | _ -> true)

  method has_unknown_jump_target =
    H.fold (fun _ v acc ->
        acc
        || match v with
           | UnknownJumpTarget -> true
           | _ -> acc) jump_targets false

  method private write_xml_call_targets (node:xml_element_int) =
    let calltargets = H.fold (fun k v a -> (k, v)::a) calltargets [] in
    node#appendChildren
      (List.map
         (fun (k, v) ->
           let ctnode = xmlElement "ctinfo" in
           begin
             v#write_xml ctnode;
             ctnode#setAttribute "a" k;
             ctnode
           end) calltargets)

  method private read_xml_call_targets (node:xml_element_int) =
    List.iter (fun cnode ->
        let a = cnode#getAttribute "a" in
        let ctinfo = read_xml_call_target_info cnode in
        H.add calltargets a ctinfo) (node#getTaggedChildren "ctinfo")

  method private write_xml_constants (node:xml_element_int) =
    let var_to_xml (v,n) =
      let varNode = xmlElement "var" in
      let set = varNode#setAttribute in
      let seti = varNode#setIntAttribute in
      begin
	seti "id" v#getName#getSeqNumber ;
	set "name" v#getName#getBaseName ;
	set "value" n#toString ;
	varNode
      end in
    node#appendChildren (List.map var_to_xml constant_table#listOfPairs)

  method private read_xml_constants (node:xml_element_int) =
    List.iter (fun n ->
      let vn = n#getAttribute "name" in
      let seqnr = n#getIntAttribute "id" in
      let v = new variable_t (new symbol_t ~seqnr vn) NUM_VAR_TYPE in
      constant_table#set v (mkNumericalFromString (n#getAttribute "value")))
      (node#getTaggedChildren "var")

  method private write_xml_test_expressions (node:xml_element_int) =
    let l = ref [] in
    let _ = H.iter (fun k e -> l := (k,e) :: !l) test_expressions in
    let l = List.sort (fun (k1,_) (k2,_) -> Stdlib.compare k1 k2) !l in
    begin
      node#appendChildren (List.map (fun (k, e) ->
	let eNode = xmlElement "expr" in
	begin
	  varmgr#vard#xd#write_xml_xpr eNode e ;
	  eNode#setAttribute "addr" k ;
	  eNode
	end) l) ;
    end

  method private read_xml_test_expressions (node:xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun eNode ->
      let get = eNode#getAttribute in
      H.add
        test_expressions
        (get "addr")
        (varmgr#vard#xd#read_xml_xpr eNode))
      (getcc "expr")

  method private write_xml_test_variables (node:xml_element_int) =
    let aux (v,f) =
      let vNode = xmlElement "fvar" in
      let set = vNode#setAttribute in
      let seti = vNode#setIntAttribute in
      begin
	seti "vid" v#getName#getSeqNumber ;
	set "vn" v#getName#getBaseName ;
	seti "fid" f#getName#getSeqNumber ;
	set "fn" f#getName#getBaseName ;
	vNode
      end in
    let l = ref [] in
    begin
      H.iter (fun k vars ->
	let vNode = xmlElement "vars" in
	begin
	  vNode#setAttribute "addr" k ;
	  vNode#appendChildren (List.map aux vars) ;
	  l := vNode :: !l
	end) test_variables ;
      node#appendChildren !l ;
    end

  method private read_xml_test_variables (node:xml_element_int) =
    let make_variable seqnr name =
      new variable_t (new symbol_t ~seqnr name) NUM_VAR_TYPE in
    List.iter (fun aNode ->
      let address = aNode#getAttribute "addr" in
      let vars =
        List.map
          (fun vNode ->
	    let get = vNode#getAttribute in
	    let geti = vNode#getIntAttribute in
	    let v = make_variable (geti "vid") (get "vn") in
	    let f = make_variable (geti "fid") (get "fn") in
	    (v,f))  (aNode#getTaggedChildren "fvar") in
      H.add test_variables address vars) (node#getTaggedChildren "vars")

  method private write_xml_variable_names (node:xml_element_int) =
    self#env#variable_names#write_xml node

  method private read_xml_variable_names (node:xml_element_int) =
    self#env#variable_names#read_xml node

  method private write_xml_saved_registers (node:xml_element_int) =
    let savedregs = H.fold (fun _ v a -> v::a) saved_registers [] in
    node#appendChildren
      (List.map (fun s ->
           let n = xmlElement "sr" in
           begin
             s#write_xml n;
             n
           end) savedregs)

  method private write_xml_app_summary (node: xml_element_int) =
    let fsum = self#get_summary in
    begin
      write_xml_function_interface node fsum#get_function_interface;
      id#write_xml_function_semantics node fsum#get_function_semantics
    end

  method private read_xml_app_summary (node: xml_element_int) =
    let fintf = id#read_xml_function_interface node in
    let sem = id#read_xml_function_semantics node in
    let summary =
      make_function_summary ~fintf ~sem ~doc:default_function_documentation in
    appsummary <- summary

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let sumNode = xmlElement "summary" in
    let ccNode = xmlElement "cc-users" in
    let cNode = xmlElement "constants" in
    let tvNode = xmlElement "test-variables" in
    let teNode = xmlElement "test-expressions" in
    let jtNode = xmlElement "jump-targets" in
    let ctNode = xmlElement "call-targets" in
    let bpNode = xmlElement "base-pointers" in
    let vvNode = xmlElement "variable-names" in
    let srNode = xmlElement "saved-registers" in
    let sfNode = xmlElement "stackframe" in
    let espNode = xmlElement "stack-adjustment" in
    begin
      self#write_xml_app_summary sumNode;
      self#write_xml_constants cNode;
      self#write_xml_cc_users ccNode;
      self#write_xml_test_expressions teNode;
      self#write_xml_test_variables tvNode;
      (* self#write_xml_jump_targets jtNode ; *)
      self#write_xml_call_targets ctNode;
      self#write_xml_base_pointers bpNode;
      self#write_xml_variable_names vvNode;
      self#write_xml_saved_registers srNode;
      self#stackframe#write_xml sfNode;
      (match stack_adjustment with
       | Some i -> espNode#setIntAttribute "adj" i | _ -> ());
      append [
          sumNode;
          ccNode;
          tvNode;
          teNode;
          cNode;
	  ctNode;
          jtNode;
          bpNode;
          vvNode;
          srNode;
          sfNode;
          espNode]
    end

  method read_xml (node:xml_element_int) =
    let hasc = node#hasOneTaggedChild in
    try
      let getc = node#getTaggedChild in
      begin
	self#read_xml_constants (getc "constants") ;
        (if hasc "call-targets" then
           self#read_xml_call_targets (getc "call-targets")) ;
	(if hasc "cc-users" then self#read_xml_cc_users (getc "cc-users")) ;
	(if hasc "test-variables" then
	    self#read_xml_test_variables (getc "test-variables")) ;
	(if hasc "test-expressions" then
	    self#read_xml_test_expressions (getc "test-expressions")) ;
	(if hasc "base-pointers" then
	   self#read_xml_base_pointers (getc "base-pointers")) ;
        (if hasc "variable-names" then
           self#read_xml_variable_names (getc "variable-names")) ;
        (if hasc "stack-adjustment" then
           let espNode = getc "stack-adjustment" in
           if espNode#hasNamedAttribute "adj" then
             stack_adjustment <- Some (espNode#getIntAttribute "adj"));
        (if hasc "summary" then self#read_xml_app_summary (getc "summary"))
      end
    with
    | XmlDocumentError (line,col,p)
    | XmlReaderError (line,col,p) ->
       let msg =
         LBLOCK [
             STR "function info ";
             self#get_address#toPretty;
             STR ": ";
             p] in
      raise (XmlReaderError (line, col, msg))
    | Failure s ->
       pr_debug [
           STR "error in reading function info xml: ";
           STR s;
           STR " (";
	   self#get_address#toPretty;
           STR ")";
           NL]

  method state_to_pretty =
    LBLOCK [self#conditional_jump_state_to_pretty; NL]

  method save =
    let node = xmlElement "function-info" in
    let fname = self#get_address#to_hex_string in
    begin
      self#write_xml node;
      save_function_info_file fname node
    end

end


let function_infos = H.create 13


let load_finfo_userdata (finfo: function_info_int) (faddr: doubleword_int) =
  match load_userdata_function_file faddr#to_hex_string with
  | Some node ->
     finfo#read_xml_user_summary node
  | _ ->
     if functions_data#has_function_name faddr then
       let fname = (functions_data#get_function faddr)#get_function_name in
       if bcfiles#has_varinfo fname then
         let vinfo = bcfiles#get_varinfo fname in
         let bcsum = function_summary_of_bvarinfo vinfo in
         begin
           finfo#set_bc_summary bcsum;
           chlog#add
             "bc-function-summary"
             (LBLOCK [
                  STR fname;
                  STR ": ";
                  function_interface_to_pretty bcsum#get_function_interface])
         end
       else
         ()
     else
       let fname =
         let hexfaddr = faddr#to_hex_string in
         let lenfaddr = String.length hexfaddr in
         "sub_" ^ (String.sub (faddr#to_hex_string) 2 (lenfaddr - 2)) in
       if bcfiles#has_varinfo ~prefix:true fname then
         let vinfo = bcfiles#get_varinfo ~prefix:true fname in
         let bcsum = function_summary_of_bvarinfo vinfo in
         begin
           (if not (vinfo.bvname = fname) then
              if functions_data#has_function faddr then
                let fndata = functions_data#get_function faddr in
                begin
                  fndata#add_name vinfo.bvname;
                  chlog#add
                    "bc-function-summary (update name)"
                    (LBLOCK [STR vinfo.bvname; STR " from "; STR fname])
                end);
           finfo#set_bc_summary bcsum;
           chlog#add
             "bc-function-summary"
             (LBLOCK [
                  STR vinfo.bvname;
                  STR ": ";
                  function_interface_to_pretty bcsum#get_function_interface])
         end
       else
         ()


let load_function_info ?(reload=false) (faddr:doubleword_int) =
  let is_java_native_method () =
    let names = (functions_data#get_function faddr)#get_names in
    List.exists is_java_native_method_name names in
  if H.mem function_infos faddr#index && (not reload) then
    H.find function_infos faddr#index
  else if functions_data#has_function faddr then
    try
      let fname = faddr#to_hex_string in
      let xvard = load_function_vard_file fname in
      let varmgr = make_variable_manager faddr xvard in
      let invio = read_invs fname varmgr#vard in
      let varinvio = read_varinvs fname varmgr#vard in
      let fndata = functions_data#get_function faddr in
      let finfo = new function_info_t faddr fndata varmgr invio varinvio in
      let _ =
        match extract_function_info_file fname with
        | Some node -> finfo#read_xml node
        | _ -> () in
      let _ = load_finfo_userdata finfo faddr in
      let _ =
        match extract_inferred_function_arguments_from_summary_file
                faddr#to_hex_string with
        | _ -> () in
      let _ =
        if system_info#is_class_member_function faddr then
	  let classinfos = system_info#get_class_infos faddr in
	  finfo#env#set_class_member_variable_names classinfos in
      let _ =
        if is_java_native_method () then
	  let names =
            List.filter
              is_java_native_method_name
	      (functions_data#get_function faddr)#get_names in
	  match get_java_native_method_signature faddr#to_hex_string names with
	  | Some api -> finfo#set_java_native_method_signature api
	  | _ -> finfo#set_unknown_java_native_method_signature in
      begin
        H.replace function_infos faddr#index finfo;
        finfo
      end
    with
    | CHFailure p | BCH_failure p ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in loading function info for: ";
                 faddr#toPretty;
                 STR ": ";
                 p]))
  else
    raise
      (BCH_failure
         (LBLOCK [
              STR "Unable to load function info. ";
              faddr#toPretty;
              STR " is not a function entry point"]))


let get_function_info (faddr:doubleword_int) = load_function_info faddr


let get_function_infos () = Hashtbl.fold (fun _ v a -> v::a) function_infos []


let get_jni_calls () =
  let result =  ref [] in
  let table = H.create 3 in
  let add faddr iaddr jniindex =
    if H.mem table faddr#index then
      H.replace table faddr#index ((iaddr,jniindex) :: (H.find table faddr#index))
    else
      H.add table faddr#index [ (iaddr,jniindex) ] in
  let _ =
    List.iter (fun finfo ->
        List.iter (fun (iaddr,ctinfo) ->
            if ctinfo#is_jni_call then
              add finfo#get_address iaddr ctinfo#get_jni_index)
                  finfo#get_callees_located) (get_function_infos ()) in
  let _ =
    H.iter
      (fun k v ->
        result := (TR.tget_ok (index_to_doubleword k), v) :: !result) table in
  !result


let get_vars_metrics (env:function_environment_int) = {
    mvars_count = env#get_var_count;
    mvars_global = env#get_globalvar_count;
    mvars_args = 0;
    mvars_return = env#get_returnvar_count;
    mvars_sideeff = env#get_sideeffvar_count
}
