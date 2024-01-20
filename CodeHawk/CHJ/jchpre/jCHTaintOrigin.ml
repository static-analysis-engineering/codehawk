(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny Sipma

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
open CHPretty
open CHPrettyUtil

(* chutil *)
open CHIndexTable
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHInstructionInfo
open JCHPreAPI
open JCHPreSumTypeSerializer
open JCHXmlUtil

module H = Hashtbl


let use_one_top_target = ref true
let set_use_one_top_target b =
  use_one_top_target := b


let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c ->
    if !found then
      ()
    else if Char.code c = 10 then      (* NL *)
      ()
    else if (Char.code c) < 32 || (Char.code c) > 126 then
      found  := true) s in
  !found


let mk_constantstring (s:string):constantstring =
  if has_control_characters s then
    (hex_string s, true, String.length s)
  else
    (s,false, String.length s)


class taint_dictionary_t:taint_dictionary_int =
object (self)

  val string_table = mk_index_table "string-table"
  val symbol_table = mk_index_table "symbol-table"
  val symbol_list_table = mk_index_table "symbol_list_table"
  val variable_table = mk_index_table "variable-table"
  val variable_list_table = mk_index_table "variable-list-table"
  val method_target_table = mk_index_table "method-target-table"
  val taint_origin_table = mk_index_table "taint-origin-table"
  val taint_origin_list_table = mk_index_table "taint-origin-list-table"
  val variable_taints_table = mk_index_table "variable-taints-table"
  val tainted_variable_table = mk_index_table "tainted-variable-table"
  val tainted_variable_ids_table = mk_index_table "tainted-variable-ids-table"
  val taint_node_type_table = mk_index_table "taint-node-type-table"

  val mutable tables = []

  initializer
    tables <- [
      string_table;
      symbol_table;
      symbol_list_table;
      variable_table;
      variable_list_table;
      method_target_table;
      taint_origin_table;
      taint_origin_list_table;
      tainted_variable_table;
      tainted_variable_ids_table;
      taint_node_type_table;
   ]

  method index_string (s:string):int =
    let cs = mk_constantstring s in
    let (s,ishex,len) = cs in
    let x = if ishex then ["x"] else [] in
    let tags = if len = 0 then [] else [s] @ x in
    let args = [len] in
    string_table#add (tags,args)

  method get_string (index:int) =
    let (tags, args) = string_table#retrieve index in
    let (s, _, _) = if (List.length tags) > 0  && (List.length args) > 0 then
      (List.hd tags, List.length tags > 1, List.hd args)
    else if (List.length args) > 0 && (List.hd args) = 0 then    (* empty string *)
      ("", false, 0)
    else if (List.length args) > 0 then
      (" ", false, (List.hd args))                (* string of spaces of lengt n *)
    else
      raise
        (JCH_failure
           (LBLOCK [STR "Invalid string record: "; INT (List.hd args)])) in
    s

  method index_symbol (s:symbol_t) =
    let args =
      s#getSeqNumber
      :: (List.map self#index_string (s#getBaseName :: s#getAttributes)) in
    symbol_table#add ([],args)

  method private index_symbol_name (s:symbol_t) =
    let args =
      (-1) :: (List.map self#index_string (s#getBaseName :: s#getAttributes)) in
    symbol_table#add ([],args)

  method get_symbol (index:int) =
    let (_,args) = symbol_table#retrieve index in
    let a = a "symbol" args in
    let name = self#get_string (a 1) in
    let atts = List.map self#get_string (List.tl (List.tl args)) in
    let seqnr = (a 0) in
    new symbol_t ~atts ~seqnr name

  method index_symbol_list (l:symbol_t list) =
    symbol_list_table#add ([],List.map self#index_symbol l)

  method get_symbol_list (index:int) =
    let (_,args) = symbol_list_table#retrieve index in
    List.map self#get_symbol args

  method index_variable (v:variable_t) =
    let tags = [variable_type_mfts#ts v#getType] in
    let args = [self#index_symbol v#getName] in
    variable_table#add (tags,args)

  method get_variable (index:int) =
    let (tags,args) = variable_table#retrieve index in
    let t = t "variable" tags in
    let a = a "variable" args in
    let vtype = variable_type_mfts#fs (t 0) in
    let name = self#get_symbol (a 0) in
    new variable_t name vtype

  method index_variable_list (l:variable_t list) =
    variable_list_table#add ([],List.map self#index_variable l)

  method get_variable_list (index:int) =
    let (_,args) = variable_list_table#retrieve index in
    List.map self#get_variable args

  method index_method_target (tgt:method_target_int) =
    let key =
      ([],
       List.map (fun t ->
           t#get_class_method_signature#index) tgt#get_all_targets) in
    method_target_table#add key

  method get_method_target (index:int) =
    let (_,args) = method_target_table#retrieve index in
    let tgt = make_method_target () in
    let _ =
      List.iter
        (fun cmsix ->
          tgt#add_target (app#get_method (retrieve_cms cmsix))) args in
    tgt

  method index_taint_origin (t:taint_origin_type_t) =
    let tags = [taint_origin_type_mcts#ts t] in
    let key = match t with
      | T_ORIG_VAR (cmsix,var) -> (tags,[cmsix; self#index_variable var])
      | T_ORIG_FIELD (cfsix,infostring,callerix,pc) ->
         (tags,[cfsix; self#index_string infostring; callerix; pc])
      | T_ORIG_CALL (calleeix,infostring,callerix,pc) ->
         (tags,[calleeix; self#index_string infostring; callerix; pc])
      | T_ORIG_TOP_TARGET (mtgt,callerix,pc) ->
         (tags, [self#index_method_target mtgt; callerix; pc])
      | T_ORIG_STUB (stubix, callerix, pc) ->
         (tags, [stubix; callerix; pc]) in
    taint_origin_table#add key

  method get_taint_origin (index:int) =
    let (tags,args) = taint_origin_table#retrieve index in
    let t = t "taint-origin" tags in
    let a = a "taint-origin" args in
    match (t 0) with
    | "v" -> T_ORIG_VAR (a 0, self#get_variable (a 1))
    | "f" -> T_ORIG_FIELD (a 0, self#get_string (a 1), a 2, a 3)
    | "c" -> T_ORIG_CALL (a 0, self#get_string (a 1), a 2, a 3)
    | "t" -> T_ORIG_TOP_TARGET (self#get_method_target (a 0), a 1, a 2)
    | "s" -> T_ORIG_STUB (a 0, a 1, a 2)
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "taint-origin tag "; STR s; STR " not recognized"]))

  method index_taint_origin_list (l:taint_origin_type_t list) =
    taint_origin_list_table#add
      ([],List.sort_uniq Stdlib.compare (List.map self#index_taint_origin l))

  method get_taint_origin_list (index:int) =
    let (_,args) = taint_origin_list_table#retrieve index in
    List.map self#get_taint_origin args

  method index_taint_node_type (t:taint_node_type_t) =
    let tags = [taint_node_type_mcts#ts t] in
    let key = match t with
      | TN_FIELD cfsix -> (tags,[cfsix])
      | TN_OBJECT_FIELD (cmsix, var, cfsix, pc) ->
         (tags, [cmsix; self#index_variable var; cfsix; pc])
      | TN_VAR (cmsix, var, pc) -> (tags, [cmsix; self#index_variable var; pc])
      | TN_VAR_EQ (cmsix, var1, var2, syms) ->
         (tags,
          [cmsix;
           self#index_variable var1;
           self#index_variable var2;
           self#index_symbol_list syms])
      | TN_CALL (index, pc, callerix, calleeix, optvar, varlist) ->
         let varix =
           match optvar with Some v -> self#index_variable v | _ -> (-1) in
         (tags,
          [index;
           pc;
           callerix;
           calleeix;
           varix;
           self#index_variable_list varlist])
      | TN_UNKNOWN_CALL (index, pc, callerix, optvar, varlist) ->
         let varix =
           match optvar with Some v -> self#index_variable v | _ -> (-1) in
         (tags,[index; pc; callerix; varix; self#index_variable_list varlist])
      | TN_CONDITIONAL (cmsix, pc) -> (tags, [cmsix; pc])
      | TN_SIZE (cmsix, var, pc) -> (tags, [cmsix; self#index_variable var; pc])
      | TN_REF_EQUAL -> (tags, []) in
    taint_node_type_table#add key

  method get_taint_node_type (index:int) =
    let (tags, args) = taint_node_type_table#retrieve index in
    let t = t "taint-node-type" tags in
    let a = a "taint-node-type" args in
    let optvar i =
      match (a i) with (-1) -> None | k -> Some (self#get_variable k) in
    match (t 0) with
    | "f" -> TN_FIELD (a 0)
    | "o" -> TN_OBJECT_FIELD (a 0, self#get_variable (a 1), a 2, a 3)
    | "v" -> TN_VAR (a 0, self#get_variable (a 1), a 2)
    | "q" ->
       TN_VAR_EQ (
           a 0,
           self#get_variable (a 1),
           self#get_variable (a 2),
           self#get_symbol_list (a 3))
    | "c" ->
       TN_CALL (a 0, a 1, a 2, a 3, optvar 4, self#get_variable_list (a 5))
    | "u" ->
       TN_UNKNOWN_CALL (a 0, a 1, a 2, optvar 3, self#get_variable_list (a 4))
    | "j" -> TN_CONDITIONAL (a 0, a 1)
    | "s" -> TN_SIZE (a 0, self#get_variable (a 1), a 2)
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "taint-node-type tag "; STR s; STR " not recognized"]))

  method index_tainted_variable (d:tainted_variable_data_t) =
    tainted_variable_table#add
      ([],
       [self#index_variable d.tvar; self#index_taint_origin_list d.untrusted])

  method get_tainted_variable (index:int) =
    let (_,args) = tainted_variable_table#retrieve index in
    let a = a "tainted-variable" args in
    { tvar = self#get_variable (a 0);
      untrusted = self#get_taint_origin_list (a 1) }

  method index_tainted_variable_ids (ids:int list) =
    tainted_variable_ids_table#add ([],ids)

  method get_tainted_variable_ids (index:int) =
    snd (tainted_variable_ids_table#retrieve index)

  method write_xml_symbol ?(tag="isym") (node:xml_element_int) (s:symbol_t) =
    node#setIntAttribute tag (self#index_symbol s)

  method read_xml_symbol ?(tag="isym") (node:xml_element_int):symbol_t =
    self#get_symbol (node#getIntAttribute tag)

  method write_xml_variable ?(tag="ivar") (node:xml_element_int) (v:variable_t) =
    node#setIntAttribute tag (self#index_variable v)

  method read_xml_variable ?(tag="ivar") (node:xml_element_int):variable_t =
    self#get_variable (node#getIntAttribute tag)

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_string s)

  method read_xml_string ?(tag="istr") (node:xml_element_int):string =
    self#get_string (node#getIntAttribute tag)

  method write_xml_method_target
           ?(tag="imt") (node:xml_element_int) (tgt:method_target_int) =
    node#setIntAttribute tag (self#index_method_target tgt)

  method read_xml_method_target
           ?(tag="imt") (node:xml_element_int):method_target_int =
    self#get_method_target (node#getIntAttribute tag)

  method write_xml_taint_origin
           ?(tag="ito") (node:xml_element_int) (t:taint_origin_type_t) =
    node#setIntAttribute tag (self#index_taint_origin t)

  method read_xml_taint_origin
           ?(tag="ito") (node:xml_element_int):taint_origin_type_t =
    self#get_taint_origin (node#getIntAttribute tag)

  method write_xml_taint_origin_list
           ?(tag="itl") (node:xml_element_int) (l:taint_origin_type_t list) =
    node#setIntAttribute tag (self#index_taint_origin_list l)

  method read_xml_taint_origin_list
           ?(tag="ito") (node:xml_element_int):taint_origin_type_t list =
    self#get_taint_origin_list (node#getIntAttribute tag)

  method write_xml_tainted_variable
           ?(tag="itv") (node:xml_element_int) (d:tainted_variable_data_t) =
    node#setIntAttribute tag (self#index_tainted_variable d)

  method read_xml_tainted_variable
           ?(tag="itv") (node:xml_element_int):tainted_variable_data_t =
    self#get_tainted_variable (node#getIntAttribute tag)

  method write_xml_tainted_variable_ids
           ?(tag="itvids") (node:xml_element_int) (ids:int list) =
    node#setIntAttribute tag (self#index_tainted_variable_ids ids)

  method read_xml_tainted_variable_ids
           ?(tag="itvids") (node:xml_element_int):int list =
    self#get_tainted_variable_ids (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables;

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end

let taint_dictionary = new taint_dictionary_t


let taint_origin_type_to_pretty (t:taint_origin_type_t) =
  match t with
  | T_ORIG_VAR (cmsix, var) ->
     let cms = retrieve_cms cmsix in
     LBLOCK [
         STR "VAR ("; cms#to_abbreviated_pretty; STR ", "; var#toPretty; STR ")"]
  | T_ORIG_FIELD (cfsix, s, callerix, pc) ->
     let cfs = retrieve_cfs cfsix in
     let caller = retrieve_cms callerix in
     LBLOCK [
         STR ("FIELD (" ^ s ^ ", ");
         cfs#toPretty;
         STR ", ";
	 caller#to_abbreviated_pretty;
         STR ", ";
         INT pc;
         STR ")"]
  | T_ORIG_CALL (calleeix, s, callerix, pc) ->
     let caller = retrieve_cms callerix in
     let callee = retrieve_cms calleeix in
     LBLOCK [
         STR "CALL (";
         STR s;
         STR ", ";
         callee#to_abbreviated_pretty;
         STR ", ";
	 caller#to_abbreviated_pretty;
         STR ", ";
         INT pc;
         STR ")"]
  | T_ORIG_TOP_TARGET (t, callerix, pc) ->
     let caller = retrieve_cms callerix in
     LBLOCK [
         STR "TOP_TARGET (";
         t#toPretty;
         STR ", ";
	 caller#to_abbreviated_pretty;
         STR ", ";
         INT pc;
         STR ")"]
  | T_ORIG_STUB (stubix, callerix, pc) ->
     let stub = retrieve_cms stubix in
     let caller = retrieve_cms callerix in
     LBLOCK [
         STR "STUB (";
         stub#to_abbreviated_pretty;
         STR ", ";
	 caller#to_abbreviated_pretty;
         STR ", ";
         INT pc;
         STR ")"]


class taint_origin_t
  ~(index:int)
  ~(origin:taint_origin_type_t):taint_origin_int =
object (_: 'a)

  method get_origin = origin

  method get_index = index

  method compare (other: 'a) = Stdlib.compare index other#get_index

  method is_var_origin =
    match origin with T_ORIG_VAR _ -> true | _ -> false

  method is_field_origin =
    match origin with T_ORIG_FIELD _ -> true | _ -> false

  method is_call_origin =
    match origin with T_ORIG_CALL _ -> true | _ -> false

  method is_top_origin =
    match origin with T_ORIG_TOP_TARGET _ -> true | _ -> false

  method is_stub_origin =
    match origin with T_ORIG_STUB _ -> true | _ -> false

  method write_xml (node:xml_element_int) =
    taint_dictionary#write_xml_taint_origin node origin

  method toPretty = taint_origin_type_to_pretty origin

end


class taint_origin_set_t
 (index:int)
 (origins: taint_origin_type_t list):taint_origin_set_int =
object (self:'a)

  method compare (other: 'a) = Stdlib.compare index other#get_index

  method get_index = index

  method get_origins = origins

  method get_indices = List.map taint_dictionary#index_taint_origin origins

  method has_origin (t:taint_origin_int) =
    List.mem t#get_index self#get_indices

  method has_origin_index index = List.mem index self#get_indices

  method is_empty = match self#get_indices with [] -> true | _ -> false

  method write_xml (node:xml_element_int) =
    taint_dictionary#write_xml_taint_origin_list node origins

  method to_short_pretty =
    LBLOCK [INT index; STR "(s:"; INT (List.length origins); STR ")"]

  method to_pretty_inds = pp_list_int self#get_indices

  method toPretty =
    LBLOCK [pretty_print_list origins taint_origin_type_to_pretty "[" ", " "]"]

end


class tainted_variable_t
        ~(index:int)
        ~(data:tainted_variable_data_t):tainted_variable_int =
object (_: 'a)

  method getvariable = data.tvar

  method gettaint = (data.untrusted)

  method index = index

  method compare (other:'a) = Stdlib.compare index other#index

  method may_be_tainted = (List.length data.untrusted) > 0

  method write_xml (node:xml_element_int) =
    taint_dictionary#write_xml_tainted_variable node data

  method toPretty = LBLOCK [data.tvar#toPretty; STR ": untrusted (";
                             INT (List.length data.untrusted); STR ")"]

end


let _read_xml_tainted_variable (node:xml_element_int):tainted_variable_int =
  let data = taint_dictionary#read_xml_tainted_variable node in
  let index = taint_dictionary#index_tainted_variable data in
  new tainted_variable_t ~index ~data


let taint_origins = H.create 3
let taint_origin_sets = H.create 3
let tainted_variables = H.create 3


let add_taint_origin origin index =
  if H.mem taint_origins index then
    H.find taint_origins index
  else
    let t = new taint_origin_t ~index ~origin in
    begin
      H.add taint_origins index t;
      t
    end


let add_taint_origin_set ttypes index =
  if H.mem taint_origin_sets index then
    H.find taint_origin_sets index
  else
    let s = new taint_origin_set_t index ttypes in
    begin
      H.add taint_origin_sets index s;
      s
    end


let join_taint_origin_sets (s1:taint_origin_set_int) (s2:taint_origin_set_int) =
  let s = s1#get_origins @ s2#get_origins in
  let index = taint_dictionary#index_taint_origin_list s in
  let ttypes = taint_dictionary#get_taint_origin_list index in
  add_taint_origin_set ttypes index


let is_taint_origin_subset (s1:taint_origin_set_int) (s2:taint_origin_set_int) =
  let t1 = s1#get_origins in
  let t2 = s2#get_origins in
  List.for_all (fun x1 -> List.mem x1 t2) t1


let add_tainted_variable tvar index =
  if H.mem tainted_variables index then
    H.find tainted_variables index
  else
    let v = new tainted_variable_t ~index ~data:tvar in
    begin
      H.add tainted_variables index v;
      v
    end


let get_taint_origin index =
  if H.mem taint_origins index then
    H.find taint_origins index
  else
    let origin = taint_dictionary#get_taint_origin index in
    add_taint_origin origin index


let get_taint_origin_set index =
  if H.mem taint_origin_sets index then
    H.find taint_origin_sets index
  else
    let origins = taint_dictionary#get_taint_origin_list index in
    add_taint_origin_set origins index


let get_tainted_variable index =
  if H.mem tainted_variables index then
    H.find tainted_variables index
  else
    let tvar = taint_dictionary#get_tainted_variable index in
    add_tainted_variable tvar index


let mk_var_origin (procname:symbol_t) (v:variable_t) =
  let origin = T_ORIG_VAR (procname#getSeqNumber,v) in
  let index = taint_dictionary#index_taint_origin origin in
  add_taint_origin origin index


let mk_field_origin
      (finfo:field_info_int) (s:string) (caller:symbol_t) (pc:int) =
  let origin = T_ORIG_FIELD (finfo#get_index,s,caller#getSeqNumber,pc) in
  let index = taint_dictionary#index_taint_origin origin in
  add_taint_origin origin index


let mk_call_origin
      (minfo:method_info_int) (s:string) (caller:symbol_t) (pc:int) =
  let origin = T_ORIG_CALL (minfo#get_index,s,caller#getSeqNumber,pc) in
  let index = taint_dictionary#index_taint_origin origin in
  add_taint_origin origin index


let mk_top_target_origin (tgt:method_target_int) (caller:symbol_t) (pc:int) =
  let origin = T_ORIG_TOP_TARGET (tgt,caller#getSeqNumber,pc) in
  let index = taint_dictionary#index_taint_origin origin in
  add_taint_origin origin index


let mk_stub_origin (stub:symbol_t) (caller:symbol_t) (pc:int) =
  let origin = T_ORIG_STUB (stub#getSeqNumber,caller#getSeqNumber,pc) in
  let index = taint_dictionary#index_taint_origin origin in
  add_taint_origin origin index


let mk_taint_origin (origin:taint_origin_type_t) =
  let index = taint_dictionary#index_taint_origin origin in
  add_taint_origin origin index


let mk_taint_origin_set (l:taint_origin_int list) =
  let ttypes = List.map (fun t -> t#get_origin) l in
  let index = taint_dictionary#index_taint_origin_list ttypes in
  if H.mem taint_origin_sets index then
    H.find taint_origin_sets index
  else
    let s = new taint_origin_set_t index ttypes in
    begin H.add taint_origin_sets index s; s end


let mk_tainted_variable (tvar:tainted_variable_data_t) =
  let index = taint_dictionary#index_tainted_variable tvar in
  add_tainted_variable tvar index

let get_number_origins () = H.length taint_origins

let get_taint_origins () = taint_origins


let taint_origins_to_pretty () =
  let origins = H.fold (fun k v a -> (k,v) :: a) taint_origins [] in
  let origins = List.sort (fun (k1,_) (k2,_) -> Stdlib.compare k1 k2) origins in
  LBLOCK
    (List.map (fun (k,v) ->
         LBLOCK [fixed_length_pretty (INT k) 5; STR ": "; v#toPretty; NL])
       origins)
