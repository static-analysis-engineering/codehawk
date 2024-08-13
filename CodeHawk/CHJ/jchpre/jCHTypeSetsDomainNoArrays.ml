(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet and Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
open CHPretty
open CHCommon
open CHUtils
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHPreAPI
open JCHTypeSets


(* Suppress warnings on unused variables *)
[@@@warning "-27"]


module TypeCollections = CHCollections.Make
  (struct
     type t = value_type_t
     let compare = compare_value_types
     let toPretty = value_type_to_pretty
   end)

let type_dom_name = "type_sets"

(* Local variable table *)
let local_var_table = ref None

let ind_to_var = ref (new IntCollections.table_t)

let pc_to_load_var_to_type = ref (new IntCollections.table_t)

let pc_to_store_var_to_type = ref (new IntCollections.table_t)


let get_opcode (procId:int) (pc:int) =
  let cms = retrieve_cms procId in
  (app#get_method cms)#get_opcode pc


let add_load pc var ind (t: type_set_t) =
  !ind_to_var#set ind var;
  let var_table = new VariableCollections.table_t in
  var_table#set var t;
  !pc_to_load_var_to_type#set pc var_table


let add_store pc var ind t =
  !ind_to_var#set ind var;
  let var_table = new VariableCollections.table_t in
  var_table#set var t;
  !pc_to_store_var_to_type#set pc var_table


let _pp_var_table var_table =
  match var_table with
  | Some list ->
      let pp_var_table_line (start, len, name, vt, ind) =
	LBLOCK [
            INT start;
            STR " ";
            INT len;
            STR " ";
            STR name;
            STR " ";
            value_type_to_pretty vt;
            STR " ";
            INT ind;
            NL] in
      LBLOCK (List.map pp_var_table_line list)
  | None -> (STR "")


let set_local_var_info bytecode =
  begin
    local_var_table := bytecode#get_local_variable_table;
    pc_to_load_var_to_type := new IntCollections.table_t;
    pc_to_store_var_to_type := new IntCollections.table_t;
    ind_to_var := new IntCollections.table_t
  end


let get_type_from_var_table
      (var_table_opt: (int * int * string * value_type_t * int) list option)
      (local_ind: int) pc =
  match var_table_opt with
  | Some var_table ->
      begin
	let is_in first last pc =
	  pc >= first && pc <= last in
	let rec find list =
	  match list with
	  | (start, len, _name, vt, ind) :: rest_list ->
	      let first = start - 2 in
	      let last = start + len in
	      if ind = local_ind && is_in first last pc then
		Some vt
	      else find rest_list
	  | [] -> None in
	find var_table
      end
  | _ -> None


let get_type_from_table var ind pc =
  let name = var#getName#getBaseName in
  if name.[0] = 'r' && name.[1] <> 'e' then
    get_type_from_var_table !local_var_table ind pc
  else None


(* Result of the analysis. We are interested only in stack variables *)
let var_to_types = ref (new VariableCollections.table_t)


let add_to_var_to_types var type_set =
  if var#getName#getBaseName.[0] <> 'r' then
    !var_to_types#set var type_set


let reset_var_to_types () =
  var_to_types :=  new VariableCollections.table_t


(* Printing utilities for debugging *)
let op_args_to_pretty op_args : pretty_t =
  let arg_mode_to_string am =
    match am with
    | READ -> "READ"
    | WRITE -> "WRITE"
    | _ -> "READ_WRITE" in
  let pp_arg (s,v,am) : pretty_t =
    LBLOCK [
        STR ("("^s^" , ");
        v#toPretty;
	STR " , ";
        STR (arg_mode_to_string am);
	STR " )";
        NL] in
  pretty_print_list op_args pp_arg "" "" ""


let _operation_to_pretty op =
  LBLOCK [STR "operation "; op.op_name#toPretty;NL;
	   STR "op_args: "; NL; op_args_to_pretty op.op_args;
	   STR "end op_args"; NL]


(* Used to record the last assign. We postpone the action until
 * we know where where the assign is coming from.
 * For a copy stack assign - which are the assigns that are followed
 * by a dead_vars operation - copy the type. *)
let last_assign_vars = ref []


(* Domain for analysis of types.
 * prevs kepps track of dest -> src for assignments and stores
 * This is used to propagate back type information *)
class type_sets_domain_no_arrays_t proc_name proc prevs =
  object (self: 'a)

    inherit non_relational_domain_t
    method private get_object_vt =
      TObject
        (TClass
           (JCHDictionary.common_dictionary#make_class_name "java.lang.Object"))

    method private get_string_vt =
      TObject
        (TClass
           (JCHDictionary.common_dictionary#make_class_name "java.lang.String" ))

    method private get_class_vt =
      TObject
        (TClass
           (JCHDictionary.common_dictionary#make_class_name "java.lang.Class" ))

    method private get_throwable_vt =
      TObject
        (TClass
           (JCHDictionary.common_dictionary#make_class_name "java.lang.Throwable"))

    method private add_prev v prev =
      match prevs#get v with
      |	Some set -> set#add prev
      |	None -> prevs#set v (VariableCollections.set_of_list [prev])

    method private getValue' v : type_set_t =
      let v_value = self#getValue v in
      match v_value#getValue with
      | EXTERNAL_VALUE v -> v
      | TOP_VAL -> top_type_set
      |	BOTTOM_VAL -> bottom_type_set
      | _ ->
	 raise
           (CHFailure
              (LBLOCK [
                   STR "Type set expected. ";
                   v#toPretty;
                   STR ": ";
                   v_value#toPretty]))

    method private importValue v =
      match v#getValue with
      |	EXTERNAL_VALUE _ -> v
      |	TOP_VAL -> topNonRelationalDomainValue
      |	BOTTOM_VAL -> bottomNonRelationalDomainValue
      |	_ ->
         raise
           (JCH_failure
              (STR "JCHTypeSetsDomainNoArrays.importValue expected external_value_int"))

    method private set_type' table' t var =
      begin
        self#setValue
          table' var (new non_relational_domain_value_t (EXTERNAL_VALUE t));
        add_to_var_to_types var t
      end

    method special (_cmd: string) (_args: domain_cmd_arg_t list) = {< >}

    method private set_type_set table' type_set v =
      let old_value = self#getValue' v in
      let new_value = old_value#meet type_set in
      self#set_type' table' new_value v

    method private make_type_list vtype =
      match vtype with
      | TBasic Int2Bool ->
         [TBasic Bool; TBasic Byte; TBasic Short; TBasic Char; TBasic Int]
      | TBasic ByteBool -> [TBasic Bool; TBasic Byte]
      | TBasic Object -> [self#get_object_vt]
      | TObject (TArray vt) ->
	  let types = self#make_type_list vt in
	  List.map (fun t -> TObject (TArray t)) types
      | _ -> [vtype]

    method private set_type table' t v =
      let old_value = self#getValue' v in
      let this_value = mk_type_set (self#make_type_list t) in
      let new_value = old_value#meet this_value in
      self#set_type' table' new_value v

    method private set_not_const_type table' t v =
      self#set_type table' t v

    (* A numeric argument can take a smaller type *)
    method private set_arg_type table' t v =
      try
	let type_list =
	  match t with
	  | TBasic Int -> self#make_type_list (TBasic Int2Bool)
	  | TBasic Short -> [TBasic Bool; TBasic Byte; TBasic Short]
	  | TBasic Byte -> [TBasic Bool; TBasic Byte]
	  | TBasic Char -> [TBasic Bool; TBasic Byte; TBasic Char]
	  | _ -> self#make_type_list t in
	let new_type = mk_type_set type_list in
	let old_value = self#getValue' v in
	let new_value = old_value#meet (mk_type_set type_list) in
	if new_value#isBottom then
	  begin (* Something is wrong. Keep the info that was there *)
	    CHLogger.ch_error_log#add
              "type error in invocation"
	      (LBLOCK [
                   proc_name#toPretty;
                   STR " old_type: ";
                   old_value#toPretty;
                   STR " invocation type: ";
                   new_type#toPretty])
	  end
	else
          self#set_type' table' new_value v;
      with
      | _ ->
         pr_debug [STR "exception thrown in set_arg_type "; v#toPretty; NL];

    method private set_same_type table' vs =
      if List.length vs < 2 then
        ()
      else
	try
	  begin
	    let values = List.map self#getValue' vs in
	    let vl =
	      let add_val res vl = res#meet vl in
	      List.fold_left add_val top_type_set values in
	    List.iter (self#set_type' table' vl) vs
	  end
	with _ -> ()

    method private get_arg_var str args =
      let has_this_string (s, _, _) = s = str in
      try
	let (_, v, _) = List.find has_this_string args in v
      with
	Not_found ->
	raise
          (JCH_failure
             (LBLOCK [
                  STR "arg var ";
                  STR str;
                  STR " not found in ";
		  STR "JCHTypeSetsDomainNoArrays.get_arg_var"]))

    (* Set types for the arguments of an invocation from the signature of the
     * invoked function *)
    method private set_op_type_invoke table' msig args =
      (match msig#descriptor#return_value with
      | Some vt -> self#set_type table' vt (self#get_arg_var "return" args)
      | None -> ());
      let types = msig#descriptor#arguments in
      let args =
	let red_args =
          List.filter (fun (s,_,_) -> not (s = "return" || s = "throw")) args in
	if List.length red_args > List.length types then
          (* If the function is not static remove this *)
          List.tl red_args
        else
          red_args in
      let set_arg_type t (_,v,_) = self#set_arg_type table' t v in
      List.iter2 set_arg_type types args

    method private assign table' (v,w) =
      let wtype = self#getValue' w in
      begin
        self#set_type_set table' wtype v;
        self#add_prev v w;
        last_assign_vars := []
      end

    method !analyzeOperation
      ~(domain_name: string) ~(fwd_direction: bool) ~(operation: operation_t): 'a =
      match operation.op_name#getBaseName with
      |	"method-init" ->
	  let sig_vars =
	    try
	      let bindings = proc#getBindings in
	      let get_internal_var (s,_,_) =
		snd (List.find  (fun (s', _v') -> s#equal s') bindings) in
	      List.map get_internal_var proc#getSignature
	    with
	    | Not_found ->
	       raise
                 (JCH_failure
                    (LBLOCK [
                         STR "binding not found in JCHTypeSetsDomainNoArrays"])) in
	  let cms = retrieve_cms proc_name#getSeqNumber in
	  let mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber) in
	  let args =
	    let is_arg v  =
	      let name = v#getName#getBaseName in
	      name <> "exception" && name <> "return" in
	    List.filter is_arg sig_vars in
	  let descr = cms#method_signature#descriptor in
	  let arg_types =
	    let param_types = descr#arguments in
	    if mInfo#is_static then
              param_types
	    else
	      let class_type = TObject (TClass cms#class_name) in
	      class_type :: param_types in
	  let table' = table#clone in
	  List.iter2 (self#set_type table') arg_types args;
	  (match descr#return_value with
	  | Some vt ->
	     begin
	       try
		 let return =
                   List.find (fun v -> v#getName#getBaseName = "return") sig_vars in
		 self#set_type table' vt return
	       with
	       | Not_found ->
		  raise
                    (JCH_failure
                       (LBLOCK [
                            STR "JCHTypeSetsDomainNoArrays: ";
                            STR "return var not found for: ";
                            descr#toPretty;
                            STR " with return type: ";
                            value_type_to_pretty vt]))
	     end
	  | None -> ());
	  let exc =
	    try
	      List.find (fun v -> v#getName#getBaseName = "exception") sig_vars
	    with
	    | Not_found ->
	       raise
                 (JCH_failure
                    (LBLOCK [
                         STR "exception var not found in ";
			 STR "JCHTypeSetsDomainNoArrays"])) in
	  self#set_type table' self#get_throwable_vt exc;
	  {< table = table' >}
      |	"dead_vars" ->
	  let table' = table#clone in
	  self#assign table' (List.hd !last_assign_vars);
	  {< table = table' >}
      | "i"
      | "ii" -> self#set_op_type operation.op_name operation.op_args
      |	"e" -> {< >}
      | _ ->
	 raise
           (CHCommon.CHFailure
              (LBLOCK [
                   STR "Domain ";
                   STR domain_name;
                   STR " does not implement operation ";
                   operation.op_name#toPretty]))

    method private set_const_type table' jbt v =
      let new_type = mk_type_set (self#make_type_list (TBasic jbt)) in
      self#set_type' table' new_type v

    method private set_op_type opname args =
      let bcloc = get_bytecode_location proc_name#getSeqNumber opname#getSeqNumber in
      let instr_info = app#get_instruction bcloc in
      let table' = table#clone in
      let default () =
	last_assign_vars := [];
	{< table = table' >} in
      match instr_info#get_opcode with
      |	OpStore (Object , n) ->
	  let src1 = self#get_arg_var "src1" args in
	  let dst1 = self#get_arg_var "dst1" args in
	  self#add_prev dst1 src1;
	  let type_set = self#getValue' src1 in
	  self#set_type' table' type_set dst1;
	  let pc = opname#getSeqNumber in
	  add_store pc dst1 n type_set;
	  default ()
      |	OpStore (Long, _n) ->
	  let dst1 = self#get_arg_var "dst1" args in
	  let type_set = mk_type_set (self#make_type_list (TBasic Long)) in
	  self#set_type' table' type_set dst1;
	  default ()
      |	OpStore (Double, _n) ->
	  let dst1 = self#get_arg_var "dst1" args in
	  let type_set = mk_type_set (self#make_type_list (TBasic Double)) in
	  self#set_type' table' type_set dst1;
	  default ()
      |	OpStore (Float, _n) ->
	  let dst1 = self#get_arg_var "dst1" args in
	  let type_set = mk_type_set (self#make_type_list (TBasic Float)) in
	  self#set_type' table' type_set dst1;
	  default ()
      (* OpStore for integer types will store into an Int2Bool. The type can
         change *)
      |	OpStore (jbt, _n) ->
	  let src1 = self#get_arg_var "src1" args in
	  let src_type_set = self#getValue' src1 in
	  let dst1 = self#get_arg_var "dst1" args in
	  let type_set =
            (mk_type_set (self#make_type_list (TBasic jbt)))#meet src_type_set in
	  self#set_type' table' type_set dst1;
	  default ()
      |	OpLoad (jbt, n) ->
	  begin
	    let dst1 = self#get_arg_var "dst1" args in
	    self#set_not_const_type table' (TBasic jbt) dst1;
	    let pc = opname#getSeqNumber in
	    let src1 = self#get_arg_var "src1" args in
	    let type_set = self#getValue' src1 in
	    self#set_type' table' type_set dst1;  (* Added *)
	    let new_type_set =
	      (match get_type_from_table src1 n pc with
	      | Some (TBasic Object) -> type_set
	      | Some (TBasic t) -> mk_type_set (self#make_type_list (TBasic t))
	      | Some t ->
		 self#set_type table' t dst1;
                 (* Intersect the table type with other info *)
		  mk_type_set [t]
	      | None -> type_set) in
	    add_load pc src1 n new_type_set;
	    default ()
	  end
      | OpIInc _ ->
	 let t = mk_type_set [TBasic Int] in
         (* I am not sure that it should not be Int2Bool here *)
         begin
	   self#set_type' table' t (self#get_arg_var "src_dst" args);
      	   default ()
         end
      | OpAConstNull ->
         begin
	   self#set_type table' self#get_object_vt (self#get_arg_var "ref" args);
	   default ()
         end
      | OpStringConst _ ->
         begin
	   self#set_type table' self#get_string_vt (self#get_arg_var "ref" args);
	   default ()
         end
      | OpByteConst _
        | OpShortConst _
        | OpIntConst _ ->
         begin
	   self#set_const_type table' Int2Bool (self#get_arg_var "dst1" args);
	   default ()
         end
      | OpLongConst _ ->
         begin
	   self#set_const_type table' Long (self#get_arg_var "dst1" args);
	   default ()
         end
      | OpFloatConst _ ->
         begin
	   self#set_const_type table' Float (self#get_arg_var "dst1" args);
	   default ()
         end
      | OpDoubleConst _ ->
         begin
	   self#set_const_type table' Double (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpClassConst _ot ->
         begin
	   let new_type = mk_type_set [self#get_class_vt] in
	   self#set_type' table' new_type (self#get_arg_var "ref" args);
	   default ()
         end
      | OpAdd jbt
        | OpSub jbt
        | OpMult jbt
        | OpDiv jbt
        | OpRem jbt ->
	 let dst1 = self#get_arg_var "dst1" args in
	 let new_type = mk_type_set (self#make_type_list (TBasic jbt)) in
         begin
	   self#set_type_set table' new_type dst1;
	   default ()
         end
      | OpNeg jbt ->
	 let stype = self#getValue' (self#get_arg_var "src1" args) in
	 let new_type =
           stype#meet (mk_type_set (self#make_type_list (TBasic jbt))) in
         begin
	   self#set_type_set table' new_type (self#get_arg_var "dst1" args);
	   default ()
         end
      | OpIShl
        | OpIShr
        | OpIUShr
        | OpIAnd
        | OpIOr
        | OpIXor ->
         begin
	   self#set_type table' (TBasic Int2Bool) (self#get_arg_var "dst1" args);
	   default ()
         end
      | OpLShl
        | OpLShr
        | OpLUShr ->
         begin
	   self#set_not_const_type
             table' (TBasic Long) (self#get_arg_var "src1_1" args);
	   self#set_not_const_type
             table' (TBasic Int2Bool) (self#get_arg_var "src1_2" args);
	   self#set_type table' (TBasic Long) (self#get_arg_var "dst1" args);
	   default ()
         end
      | OpLAnd
        | OpLOr
        | OpLXor ->
         begin
	   self#set_not_const_type
             table' (TBasic Long) (self#get_arg_var "src1_1" args);
	   self#set_not_const_type
             table' (TBasic Long) (self#get_arg_var "src1_2" args);
	   self#set_type
             table' (TBasic Long) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpI2L ->
         begin
	   self#set_not_const_type
             table' (TBasic Int2Bool) (self#get_arg_var "src1" args);
	   let dst_type = mk_type_set [TBasic Long] in
	   self#set_type' table' dst_type (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpL2I ->
         begin
	   self#set_not_const_type
             table' (TBasic Long) (self#get_arg_var "src1" args);
	   self#set_type
             table' (TBasic Int) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpD2I ->
         begin
	   self#set_not_const_type
             table' (TBasic Double) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Int) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpF2I ->
         begin
	   self#set_not_const_type
             table' (TBasic Float) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Int) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpF2L ->
         begin
	   self#set_not_const_type
             table' (TBasic Float) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Long) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpD2L ->
         begin
	   self#set_not_const_type
             table' (TBasic Double) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Long) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpI2B ->
         begin
	   self#set_not_const_type table' (TBasic Int2Bool) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Byte) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpI2C ->
         begin
	   self#set_not_const_type
             table' (TBasic Int2Bool) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Char) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpI2S ->
         begin
	   self#set_not_const_type
             table' (TBasic Int2Bool) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Short) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpL2F ->
         begin
	   self#set_not_const_type
             table' (TBasic Long) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Float) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpD2F ->
         begin
	   self#set_not_const_type
             table' (TBasic Double) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Float) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpI2F ->
         begin
	   self#set_not_const_type
             table' (TBasic Int2Bool) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Float) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpF2D ->
         begin
	   self#set_not_const_type
             table' (TBasic Float) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Double) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpL2D ->
         begin
	   self#set_not_const_type
             table' (TBasic Long) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Double) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpI2D ->
         begin
	   self#set_not_const_type
             table' (TBasic Int2Bool) (self#get_arg_var "src1" args);
	   self#set_type table' (TBasic Double) (self#get_arg_var "dst1" args);
	   default ()
         end
      | OpCmpL
        | OpCmpFL
        | OpCmpFG
        | OpCmpDL
        | OpCmpDG ->
         begin
	   self#set_type table' (TBasic Int) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpIfCmpAEq _
        | OpIfCmpANe _ ->
	 let src1 = self#get_arg_var "src1" args in
	 let src2 = self#get_arg_var "src2" args in
         begin
	   self#set_same_type table' [src1; src2];
	   default ()
         end
      |	OpPutStatic (_, fsig)
        | OpPutField (_, fsig) ->
         begin
	   self#set_arg_type table' fsig#descriptor (self#get_arg_var "val" args);
	   default ()
         end
      |	OpGetStatic (_, fsig)
        | OpGetField (_, fsig) ->
         begin
	   self#set_type table' fsig#descriptor (self#get_arg_var "val" args);
	   default ()
         end
      |	OpArrayLength ->
         begin
	   self#set_type table' (TBasic Int) (self#get_arg_var "val" args);
	   default ()
         end
      |	OpArrayLoad jbt ->
	 let array = self#get_arg_var "array" args in
	 let elem = self#get_arg_var "val" args in
	 let atypes = self#getValue' array in
	 let jbt_type = mk_type_set (self#make_type_list (TBasic jbt)) in
	 let new_etypes = (mk_elem_type_set atypes)#meet jbt_type in
         begin
	   self#set_type_set table' new_etypes elem;
	   default ()
         end
      |	OpInvokeVirtual (ot, msig) ->
         begin
	   begin
	     match ot with
	     | TClass cn ->
		if cn#name = "java.lang.Object" && msig#name = "clone" then
		  begin
		    let arg0 = self#get_arg_var "arg0" args in
		    let ret = self#get_arg_var "return" args in
		    self#set_same_type table' [arg0; ret]
		  end
		else ()
	     | TArray _ -> ()
	   end;
	   self#set_op_type_invoke table' msig args;
	   default ()
         end
      |	OpInvokeStatic (_, msig)
        | OpInvokeSpecial (_, msig)
        | OpInvokeInterface (_, msig) ->
         begin
	   self#set_op_type_invoke table' msig args;
	   default ()
         end
      |	OpReturn Void -> default ()
      |	OpReturn t ->
         begin
	   self#set_type table' (TBasic t) (self#get_arg_var "src1" args);
	   default ()
         end
      |	OpNew cn ->
         begin
	   self#set_type table' (TObject (TClass cn)) (self#get_arg_var "ref" args);
	   default ()
         end
      |	OpNewArray t ->
         begin
	   self#set_type table' (TObject (TArray t)) (self#get_arg_var "ref" args);
	   default ()
         end
      |	OpAMultiNewArray (t, _n) ->
         begin
	   self#set_type table' (TObject t) (self#get_arg_var "ref" args);
	   default ()
         end
      |	OpCheckCast t ->
         begin
	   self#set_type table' (TObject t) (self#get_arg_var "dst1" args);
	   default ()
         end
      |	OpInstanceOf _t ->
         begin
	   self#set_type table' (TBasic Bool) (self#get_arg_var "val" args);
	   default ()
         end
      |	OpDup
        | OpDupX1
        | OpDupX2
        | OpDup2
        | OpDup2X1
        | OpDup2X2
        | OpSwap ->
         begin
	   List.iter (self#assign table') !last_assign_vars;
	   default ()
         end
      |	 _ -> default ()

    method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
      if bottom then self#mkBottom
      else
	let table' = table#clone in
	let default () = {< table = table' >} in
	match cmd with
	| ABSTRACT_VARS l ->
	    begin
	      self#abstractVariables table' l;
	      default ()
	    end
	| ASSERT TRUE ->
	    default ()
	| ASSERT FALSE ->
	    self#mkBottom
	| ASSIGN_NUM (v, NUM_VAR w)
	| ASSIGN_SYM (v, SYM_VAR w) ->
	   if w#getName#getBaseName = "exception" then
             self#assign table' (v, w)
	   else
             (* assign the same type only if it comes from a copy stack *)
             last_assign_vars := (v, w) :: !last_assign_vars;
	    default ()
	| ASSIGN_NUM (v, NUM _c) ->
           begin
	    (if v#isTmp then
	       self#set_type table' (TBasic Int) v);
	    default ();
           end
	| OPERATION op ->
	   self#analyzeOperation
             ~domain_name: type_dom_name ~fwd_direction: true ~operation: op
	| _ ->
	    default ()

  method private analyzeBwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then self#mkBottom
    else
      let table' = table#clone in
      let default () = {< table = table' >} in
      match cmd with
      | ABSTRACT_VARS l -> self#abstractVariables table' l;
	  default ()
      |	ASSIGN_NUM (x, _)
        | ASSIGN_SYM (x, _) -> self#abstractVariables table' [x];
	  default ()
      | ASSERT _ -> self#analyzeFwd' cmd
      | _ ->  default ()

end


let add_types_to_stack_layout system proc_name =
  let proc = system#getProcedure proc_name in
  let mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber) in
  let bytecode =
    match mInfo#get_method#get_implementation with
    | Native -> raise (JCH_failure (STR "expected bytecode"))
    | Bytecode bc -> bc in
  set_local_var_info bytecode;
  reset_var_to_types ();
  let pc_to_invariant = new IntCollections.table_t in
  let analyzer = CHAnalysisSetup.mk_analysis_setup () in
  let op_semantics ~(invariant: CHAtlas.atlas_t) ~(stable: bool)
    ~(fwd_direction: bool) ~context ~operation =
    match operation.op_name#getBaseName with
    | "v" ->
	(if fwd_direction && stable then
	  let pc = operation.op_name#getSeqNumber in
	  let type_dom = invariant#getDomain type_dom_name in
	  begin
	    pc_to_invariant#set pc type_dom
	  end);
	invariant
    | "method-init"
    | "dead_vars"
    | "i"
    | "ii" ->
	if fwd_direction then
	  invariant#analyzeFwd (OPERATION operation) (* (mk_type_dom_op operation) *)
	else
          invariant
    | _ -> invariant in
  begin
    analyzer#setOpSemantics op_semantics;
    analyzer#setStrategy
      {CHIterator.widening =
         (fun _ -> true, ""); CHIterator.narrowing = (fun _ -> true) };
    let prevs = new VariableCollections.table_t in
    let type_set_dom = new type_sets_domain_no_arrays_t proc_name proc prevs in
    analyzer#addDomain type_dom_name type_set_dom;
    analyzer#analyze_procedure ~do_loop_counters:false system proc;

    let last_vars =
      VariableCollections.set_of_list
        (List.flatten (List.map (fun s -> s#toList) prevs#listOfValues)) in
    let done_vars = new VariableCollections.set_t in
    let rec propagate_back v =
      let rec propagate_type t w =
        if not (done_vars#has v) then
	  begin
	    done_vars#add w;
	    match prevs#get w with
	    | Some set ->
	       let ws = set#toList in
	       if List.length ws = 1 then
	         begin
		   let prev_w = List.hd ws in
		   !var_to_types#set prev_w t;
		   propagate_type t prev_w
	         end
	       else List.iter propagate_back ws
	    | None -> ()
	  end in
      if not (done_vars#has v) then
        match !var_to_types#get v with
        | Some ts -> propagate_type ts v
        | None -> () in
    List.iter propagate_back last_vars#toList;

    let mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber) in
    let stack_layout = mInfo#get_method_stack_layout in
    let change_slot (_pc: int) (slot:logical_stack_slot_int)  =
      let var = slot#get_variable in
      match !var_to_types#get var with
      | Some type_set ->
	 slot#set_type (get_type_list_compact type_set)
      | None -> () in (* unreachable offset *)
    let change_stack (pc: int) (stack:op_stack_layout_int) =
      List.iter (change_slot pc) stack#get_slots in
    let pc_stack_layouts = stack_layout#get_pc_stack_layouts in
    List.iter (fun (i,s) -> change_stack i s) pc_stack_layouts;

    (* working with the indices rather than the names of the variables did not
     * work here.
     * There were cases when variables with same name had different indices *)
    let var_type_pcs =
      let var_type_pcs = ref [] in
      let add_loads pc table =
        let sw (var: variable_t) type_set =
	  let vname = var#getName#getBaseName in
	  let (same, others) =
	    List.partition (fun (vn, ts, _) ->
                vname = vn && ts#equal type_set) !var_type_pcs in
	  if List.length same = 0 then
	    var_type_pcs := (vname, type_set, [pc]) :: others
	  else
	    let (_, _ts, pcs) = List.hd same in
	    var_type_pcs := (vname, type_set, pc :: pcs) :: others in
        table#iter sw in
      !pc_to_load_var_to_type#iter add_loads;
      let code = bytecode#get_code in
      let add_stores pc table =
        let next_pc =
	  let i = ref (pc + 1) in
	  while !i < code#length && code#at !i = OpInvalid do
	    incr i;
	  done;
	  !i in
        add_loads next_pc table in
      !pc_to_store_var_to_type#iter add_stores;
      !var_type_pcs in

    let var_ind =
      let list = ref [] in
      !ind_to_var#iter
        (fun ind var -> list := (var#getName#getBaseName, ind) :: !list);
      !list in

    let local_v_table =
      match !local_var_table with
      | None ->
	 if var_type_pcs = [] then []
	 else
	   begin
	     let local_v_table = ref [] in
	     let var_type_pc_list =
	       let add var_pc_types (vname, types, pcs) =
		 (List.map (fun pc -> (vname, types, pc)) pcs) @ var_pc_types in
	       List.fold_left add [] var_type_pcs in
	     let ordered_var_type_pc_list =
	       let compare_triplets (vname1, _types1, pc1) (vname2, _types2, pc2) =
		 let n = compare vname1 vname2 in
		 if n = 0 then compare pc1 pc2
		 else n in
	       List.sort compare_triplets var_type_pc_list in
	     let (current_ind, current_types, current_pcs) =
	       let (vname, types, pc) = List.hd ordered_var_type_pc_list in
	       (ref (List.assoc vname var_ind), ref types, ref [pc]) in
	     let add_entry () =
	       let last = List.hd !current_pcs in
	       let first = List.hd (List.rev !current_pcs) in
	       let offset = last - first in
	       let type_list = get_type_list !current_types in
	       local_v_table :=
                 (first,
                  offset,
                  "unknown",
                  type_list,
                  !current_ind) :: !local_v_table in
	     let add_var (vname, types, pc) =
	       let ind = List.assoc vname var_ind in
	       if ind = !current_ind && types#equal !current_types then
		 current_pcs := pc :: !current_pcs
	       else
		 begin
		   add_entry ();
		   current_ind := ind;
		   current_types := types;
		   current_pcs := [pc]
		 end in
	     List.iter add_var (List.tl ordered_var_type_pc_list);
	     add_entry ();
	     !local_v_table
	   end
      | Some local_v_table ->
	 begin
	   let new_local_v_table =
             ref (List.map (fun (s, l, n, _t, i) ->
                      (s,l,n,bottom_type_set,i)) local_v_table) in
	   let add_var (vname, types, pcs) =
	     let ind = List.assoc vname var_ind in
	     let add outside_pcs pc =
	       let is_entry (s,l,_,_,i) = i = ind && pc >= s && pc <= s + l in
	       let (table_entries, rest_entries) =
                 List.partition is_entry !new_local_v_table in
	       if List.length table_entries = 0 then
                 pc :: outside_pcs
	       else
		 begin
		   let (s,l,n,prev_t,i) = List.hd table_entries in
		   new_local_v_table := (s,l,n,prev_t#join types,i) :: rest_entries;
		   outside_pcs
		 end in
	     let outside_pcs = List.fold_left add [] pcs in
	     if outside_pcs <> [] then
	       begin
		 let ordered_pcs = List.sort compare outside_pcs in
		 let first = List.hd pcs in
		 let last = List.hd (List.rev ordered_pcs) in
		 let offset = last - first in
		 new_local_v_table :=
                   (first, offset, "", types, ind) :: !new_local_v_table
	       end in
	   List.iter add_var var_type_pcs;
	   List.map (fun (s,l,n,ts,i) ->
               (s,l,n,get_type_list ts,i)) !new_local_v_table
	 end in
    stack_layout#set_local_variable_table local_v_table
  end


let rec implements_interface (cinfo:class_info_int) (cni: class_name_int) =
  try
    if cinfo#implements_interface cni then true
    else
      if cinfo#has_super_class then
        let cn = cinfo#get_super_class in
        let cn_info = JCHApplication.app#get_class cn in
        implements_interface cn_info cni
      else false
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "implements-interface"
        (LBLOCK [
             STR "implements-interface: ";
             cinfo#get_class_name#toPretty;
             STR " and ";
             cni#toPretty;
             STR ": ";
             p]);
      raise
        (JCH_failure
           (LBLOCK [
                STR "implements-interface: ";
                cinfo#get_class_name#toPretty;
                STR " and ";
                cni#toPretty;
                STR ": "; p]))
    end


let rec is_subinterface (cinfo:class_info_int) (cni: class_name_int) =
  try
    let interfaces = cinfo#get_interfaces in
    let cni_index = cni#index in
    if List.exists (fun i -> i#index = cni_index) interfaces then true
    else
      let is_sub i =
        let i_info = JCHApplication.app#get_class i in
        is_subinterface i_info cni in
      List.exists is_sub interfaces
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "is-subinterface"
        (LBLOCK [
             STR "is-subinterface ";
             cinfo#get_class_name#toPretty;
             STR " and ";
             cni#toPretty;
             STR ": ";
             p]);
      raise
        (JCH_failure
           (LBLOCK [
                STR "is-subinterface: ";
                cinfo#get_class_name#toPretty;
                STR " and ";
                cni#toPretty;
                STR ": ";
                p]))
    end


let is_subclass cn1 cn2 =
  try
    if cn1#name = cn2#name then
      true
    else if cn2#name = "java.lang.Object" then
      true
    else if cn1#name = "java.lang.Object" then
      cn2#name = "java.lang.Object"
    else
      begin
        let cn1_info = app#get_class cn1 in
        (* Not all classname have a corresponding class *)
        if cn1_info#is_missing then
          raise (JCH_failure (STR "missing class"));
        cn1#index =
          cn2#index
          || app#is_descendant cn1 cn2
          || implements_interface cn1_info cn2
          || (cn1_info#is_interface && is_subinterface cn1_info cn2)
      end
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "is-subclass"
        (LBLOCK [
             STR "is-subclass ";
             cn1#toPretty;
             STR " and ";
             cn2#toPretty;
             STR ": ";
             p]);
      raise
        (JCH_failure
           (LBLOCK [
                STR "is-subclass ";
                cn1#toPretty;
                STR " and ";
                cn2#toPretty;
                STR ": ";
                p]))
    end


class target_restrictor_t proc_name =
  object (self: 'a)
    inherit code_walker_t as super
    val pc_to_stack =
      let method_info = app#get_method (retrieve_cms proc_name#getSeqNumber) in
      let pc_stack_layouts =
        method_info#get_method_stack_layout#get_pc_stack_layouts in
      let table = new IntCollections.table_t in
      let _ = List.iter (fun (i,s) -> table#set i s) pc_stack_layouts in
      table

    method !walkCmd (cmd: (code_int, cfg_int) command_t) =
      match cmd with
      |	OPERATION op ->
	  begin
	    match op.op_name#getBaseName with
	    | "i"
	    | "ii" -> self#walkOperation op.op_name op.op_args
	    | _ -> super#walkCmd cmd
	  end
      |	_ -> super#walkCmd cmd

    method walkOperation opname _args =
      let opcode = get_opcode proc_name#getSeqNumber opname#getSeqNumber in
      let bcloc =
        get_bytecode_location proc_name#getSeqNumber opname#getSeqNumber in
      let iInfo = app#get_instruction bcloc in
      match opcode with
      |	OpInvokeVirtual (_, msig)
      |	OpInvokeSpecial (_, msig)
      |	OpInvokeInterface (_, msig) ->
	  begin
	    let pc = opname#getSeqNumber in
	    let obj_types =
	      let stack_layout = Option.get (pc_to_stack#get pc) in
	      let obj_index =
                stack_layout#get_size - (List.length msig#descriptor#arguments) in
	      let get_slot n =
		let slots = stack_layout#get_slots in
		let ordered_slots =
                  List.sort (fun s1 s2 ->
                      compare s1#get_level s2#get_level) slots in
		List.nth ordered_slots (pred n) in
	      (get_slot obj_index)#get_type in
	    let mtarget = iInfo#get_method_target () in
	    let minfos = mtarget#get_valid_targets in
	    let mcns = List.map (fun i -> i#get_class_name) minfos in
	    let add_type cns t =
	      match t with
	      | TObject TClass cn -> cn :: cns
	      | _ -> cns in
	    let cns = List.fold_left add_type [] obj_types in
	    let is_compatible mcn =
	      try
                List.exists (fun cn -> is_subclass cn mcn || is_subclass mcn cn) cns
	      with
              | _ -> true in
	    let new_mcns = List.filter is_compatible mcns in
	    if List.length mcns > List.length new_mcns then
	      begin
		mtarget#assert_invocation_objects new_mcns;
	      end
	  end
      |	_ -> ()

  end


(* Uses type info from stack layout to reduce the number of invocation targets *)
let restrict_targets system proc_name =
  let proc = system#getProcedure proc_name in
  let restrictor = new target_restrictor_t proc_name in
  restrictor#walkCode proc#getBody
