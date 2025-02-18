(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyrigth (c) 2020-2025 Henny B. Sipma

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
open CHSCC
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary


let dbg_on = ref false
let set_dbg_on () = dbg_on := true
let is_dbg_on () = !dbg_on

let pr__debug ls = if !dbg_on then pr_debug ls else ()

(* A few more pretty_t functions *)
let cfg_wto_to_pretty (c,w) =
  LBLOCK [STR "cfg: "; NL; c#toPretty; NL;
	   STR "wto:"; NL; pretty_print_wto [w]; NL]

let _cfg_wtos_to_pretty pairs =
  LBLOCK (List.map cfg_wto_to_pretty pairs)

let op_args_to_pretty op_args : pretty_t =
  let arg_mode_to_string am =
    match am with
    | READ -> "READ"
    | WRITE -> "WRITE"
    | _ -> "READ_WRITE" in
  let pp_arg (s,v,am) : pretty_t =
    LBLOCK [STR ("("^s^" , "); v#toPretty;
	     STR " , "; STR (arg_mode_to_string am);
	     STR " )"; NL] in
  pretty_print_list op_args pp_arg "" "" ""

let operation_to_pretty op =
  LBLOCK [STR "operation "; op.op_name#toPretty;NL;
	   STR "op_args: "; NL; op_args_to_pretty op.op_args;
	   STR "end op_args"; NL]

let pp_bool b =
  STR (if b then "true" else "false")

let bl = STR " "

let option_to_pretty opt =
  match opt with
  | Some o -> LBLOCK [STR "Some "; o#toPretty]
  | None -> STR "None"

let option_to_pretty_str opt =
  match opt with
  | Some o -> STR ("Some " ^ o)
  | None -> STR "None"


let postcond_preds_to_pretty preds =
  let postcond_pred_to_pretty pred =
    (JCHFunctionSummary.make_postcondition false pred)#toPretty in
  pretty_print_list preds postcond_pred_to_pretty "{" "\n" " }"

let precond_preds_to_pretty preds =
  pretty_print_list
    preds JCHFunctionSummary.precondition_predicate_to_pretty "{" "\n" " }"

let side_effects_to_pretty preds =
  pretty_print_list preds JCHFunctionSummary.sideeffect_to_pretty "{" "\n" " }"

(* pretty print for a proc name *)
let proc_name_pp proc_name =
  try
    (retrieve_cms proc_name#getSeqNumber)#toPretty
  with _ -> STR (proc_name#getBaseName)

(* pretty print for a set or table or list of proc names *)
let proc_set_pp set =
  pretty_print_list set#toList proc_name_pp "{" "; " "}"

let proc_table_pp (table: _ SymbolCollections.table_t) =
  let elts =
    table#fold (fun a k v -> ([proc_name_pp k; STR " -> "; NL;
				INDENT (5, v#toPretty); NL] @ a)) [] in
  LBLOCK [STR "{"; NL; INDENT (2, LBLOCK elts); STR "}"]

(* print table proc -> set or table that prints only if they are not empty *)
let proc_ltable_pp (table: _ SymbolCollections.table_t) =
  let add a k v =
    if v#size = 0 then
      a
    else
      [proc_name_pp k; STR " -> "; NL; INDENT (5, v#toPretty); NL] @ a in
  let elts = table#fold add [] in
  LBLOCK [STR "{"; NL; INDENT (2, LBLOCK elts); STR "}"]

let proc_list_pp proc_names =
  pretty_print_list proc_names proc_name_pp "{" ", " "}"

let dot_name proc_name =
  let cms = retrieve_cms proc_name#getSeqNumber in
  let name = cms#name in
  if name = "<init>" then "cc_init"
  else if name = "<clinit>" then "cl_init"
  else name

(* pretty print for the local variable table *)
let pp_var_table var_table =
  match var_table with
  | Some list ->
      let pp_var_table_line (start, len, name, vt, ind) =
	LBLOCK [INT start; bl; INT len; bl; STR name; bl;
                value_type_to_pretty vt; bl; INT ind; NL] in
      LBLOCK (List.map pp_var_table_line list)
  | None -> (STR "")

(* pretty print for pc -> invariant *)
let pp_pc_table pc_table =
  LBLOCK
    [STR "{";
     LBLOCK (
         List.map
	   (fun pc ->
             LBLOCK [STR "pc = ";
                     INT pc;
                     STR " -> "; NL;
		     INDENT (5, (Option.get (pc_table#get pc))#toPretty); NL])
	   (List.rev (pc_table#listOfKeys)));
     NL; STR "}"]


(* pretty print for a proc_name -> pc -> invariant *)
let pp_procpc_table sym_table =
  LBLOCK
    [STR "{";
     LBLOCK (
         List.map
	   (fun proc ->
             LBLOCK [
                 proc#toPretty;
                 STR ":"; NL;
		 INDENT (2, pp_pc_table (Option.get (sym_table#get proc))); NL])
	   sym_table#listOfKeys);
     NL; STR "}"]


class pretty_int_t i =
  object

    method int = i

    method toPretty = INT i
  end

class pretty_string_t s =
  object

    method str = s
    method toPretty = STR s
  end

class pretty_var_list_t (vs: variable_t list) =
  object
    method vars = vs
    method toPretty =
      pretty_print_list vs (fun v -> v#toPretty) "[" "," "]"
  end

class pretty_op_t o =
  object
    method op = o
    method toPretty = operation_to_pretty o
  end

(* converts pretty_p into a string *)
let string_of_pretty ls = string_printer#print (LBLOCK ls)

let string_of_sym sym = string_of_pretty [sym#toPretty]

let proc_name_str proc_name =
  let pp = (retrieve_cms proc_name#getSeqNumber)#toPretty in
  string_of_pretty [pp]

let pp_var_table_pred
      (table: <toPretty: pretty_t; ..> VariableCollections.table_t)
      pred: pretty_t =
  let sorted_vars =
    let vars = List.filter pred (table#listOfKeys) in
    let compare (v1: variable_t) (v2: variable_t) =
      compare (string_of_sym v1#getName) (string_of_sym v2#getName) in
    List.sort compare vars in
  let mk_pp k =
    let vl = Option.get (table#get k) in
    LBLOCK [k#toPretty;  STR " -> "; vl#toPretty; NL] in
  LBLOCK (List.map mk_pp sorted_vars)

let pp_assoc_list_vars ls =
  let pp_pair (v1, v2) =
    LBLOCK [STR "("; v1#toPretty; STR ", "; v2#toPretty; STR ")"] in
  pretty_print_list ls pp_pair "{" ", " "}"

let pp_assoc_list_ints ls =
  let pp_pair (i1, i2) = LBLOCK [STR "("; INT i1; STR ", "; INT i2; STR ")"] in
  pretty_print_list ls pp_pair "{" ", " "}"

let pp_assoc_list_var_int ls =
  let pp_pair (k, i) = LBLOCK [STR "("; k#toPretty; STR ", "; INT i; STR ")"] in
  pretty_print_list ls pp_pair "{" ", " "}"


(* Reads from file name a table int -> variable_t set *)
let read_int_to_var_set file_name =
  let in_channel = open_in file_name in
  let proc_to_set = new IntCollections.table_t in
  let length = in_channel_length in_channel in
  while pos_in in_channel < length do
    let (proc_name, list) (* : int * variable_t list *) =
      Marshal.from_channel in_channel in
    proc_to_set#set proc_name (VariableCollections.set_of_list list)
  done;
  close_in in_channel;
  proc_to_set

(* Reads from file name a table int -> int set *)
let read_int_to_int_set file_name =
  let in_channel = open_in file_name in
  let proc_to_set = new IntCollections.table_t in
  let length = in_channel_length in_channel in
  while pos_in in_channel < length do
    let (proc_name, list) (* : int * int list *) =
      Marshal.from_channel in_channel in
    proc_to_set#set proc_name (IntCollections.set_of_list list)
  done;
  close_in in_channel;
  proc_to_set

(* Reads from file name a table int -> (table variable_t -> variable_t) *)
let read_int_to_var_to_var file_name =
  let in_channel = open_in file_name in
  let proc_to_set = new IntCollections.table_t in
  let length = in_channel_length in_channel in
  while pos_in in_channel < length do
    let (proc_name, list) (* : int * (variable_t * variable_t) list *) =
      Marshal.from_channel in_channel in
    let table = new VariableCollections.table_t in
    let add_pair (v1, v2) = table#set v1 v2 in
    List.iter add_pair list;
    proc_to_set#set proc_name table
  done;
  close_in in_channel;
  proc_to_set

(* Reads from file name a table int -> string set *)
let read_int_to_string_set file_name =
  let in_channel = open_in file_name in
  let proc_to_set = new IntCollections.table_t in
  let length = in_channel_length in_channel in
  while pos_in in_channel < length do
    let (proc_name, list) (* : int * string list *) =
      Marshal.from_channel in_channel in
    proc_to_set#set proc_name (StringCollections.set_of_list list)
  done;
  close_in in_channel;
  proc_to_set

let jch_stats_log = CHLogger.mk_logger ()

let relational_op_to_string op =
  match op with
  | JEquals -> " = "
  | JLessThan -> " < "
  | JLessEqual -> " <= "
  | JGreaterThan -> " > "
  | JGreaterEqual -> " >= "
  | JNotEqual -> " <> "


let arithmetic_op_to_string op =
  match op with
  | JPlus -> " + "
  | JMinus -> " - "
  | JDivide ->" / "
  | JTimes -> " x "


let rec jterm_to_string jterm =
  match jterm with
  | JLocalVar (-1) -> "return"
  | JLocalVar i -> "r" ^ (string_of_int i)
  | JAuxiliaryVar s -> s
  | JLoopCounter i -> "loop_counter_" ^ (string_of_int i)
  | JConstant n -> (n#toString)
  | JBoolConstant b -> if b then "true" else "false"
  | JFloatConstant f -> string_of_float f
  | JStringConstant s -> s
  | JSize t -> "size (" ^ (jterm_to_string t) ^ ")"
  | JPower (t,n) -> "pow (" ^ (jterm_to_string t) ^ ", " ^ (string_of_int n) ^ ")"
  | JUninterpreted (name,terms) ->
     "un:"
     ^ name
     ^ " (" ^ (String.concat "," (List.map jterm_to_string terms))
     ^ ")"
  | JArithmeticExpr (op, t1, t2) ->
     (jterm_to_string t1) ^ (arithmetic_op_to_string op) ^ (jterm_to_string t2)
  | jterm -> JCHJTerm.jterm_to_string jterm

let relational_expr_to_string (op, t1, t2) =
  (jterm_to_string t1) ^ (relational_op_to_string op) ^ (jterm_to_string t2)

let pr__debug_large_table pp table =
  pr__debug [STR "{"; NL];
  List.iter (fun (k, v) ->
      pr__debug [INT k; STR " -> "]; pp v; pr__debug[NL]) table#listOfPairs;
  pr__debug [STR "}"; NL]
