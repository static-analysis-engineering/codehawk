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
open CHNumerical
open CHPretty  
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHJTerm

(* jchsys *)
open JCHPrintUtils

let max_num = mkNumerical 100000
let margin_num = mkNumerical 10 
let max_int_num = mkNumerical 2147483647
let max_long_num = mkNumericalFromString "9223372036854775807" 
let sym_max_int =
  JSymbolicConstant
    (TBasic Long, Some max_int_num, Some max_int_num, "max_int") 
let sym_max_long =
  JSymbolicConstant
    (TBasic Long, Some max_long_num, Some max_long_num, "max_long")

let make_sym_lc
      (cmsix:int) (hpc:int) (lb:numerical_t) (ub_opt:numerical_t option) =
  let lc_name = "lc_m_"^(string_of_int cmsix)^"@"^(string_of_int hpc) in
  JSymbolicConstant (TBasic Long, Some lb, ub_opt, lc_name)

let is_sym_lc (jterm:jterm_t) =
  match jterm with
  | JSymbolicConstant (_, _, _, name) ->
     (String.length name) > 5 && (String.sub name 0 5) = "lc_m_"
  | _ -> false

let make_sym_lp (cmsix:int) (hpc:int) (lb:numerical_t) =
  let lc_name = "lp_m_"^(string_of_int cmsix)^"@"^(string_of_int hpc) in
  JSymbolicConstant (TBasic Long, Some lb, None, lc_name)

let is_sym_lp (jterm:jterm_t) =
  match jterm with
  | JSymbolicConstant (_, _, _, name) ->
     (String.length name) > 5 && (String.sub name 0 5) = "lp_m_"
  | _ -> false

let make_sym_call (caller_ix:int) (pc:int) (lb:numerical_t) =
  let call_name = "call_"^(string_of_int caller_ix)^"@"^(string_of_int pc) in
  JSymbolicConstant (TBasic Long, Some lb, None, call_name)

let is_sym_call (jterm:jterm_t) =
  match jterm with
  | JSymbolicConstant (_, _, _, name) ->
     (String.length name) > 5 && (String.sub name 0 5) = "call_"
  | _ -> false

let make_sym_cost (cmsixs:int list) (lb:numerical_t) (pc:int) =
  let cost_name = ref "cost" in
  let add_cmsix cmsix =
    cost_name := !cost_name ^ "_" ^ (string_of_int cmsix) in
  begin
    List.iter add_cmsix cmsixs ;
    (if (List.length cmsixs) > 1 then
       cost_name := !cost_name ^ "_pc_" ^ (string_of_int pc)) ;
    JSymbolicConstant (TBasic Long, Some lb, None, !cost_name)
  end

let is_sym_cost (jterm:jterm_t) =
  match jterm with
  | JSymbolicConstant (_, _, _, name) ->
     (String.length name) > 5 && (String.sub name 0 5) = "cost_"
  | _ -> false

let rec is_sym_lc_or_call_term (jterm:jterm_t) =
  match jterm with
  | JSize jt -> is_sym_lc_or_call_term jt
  | JSymbolicConstant (_, _, _, name) ->
      if (String.length name) > 5 then
	let s = String.sub name 0 5 in
	s = "call_" || s = "lc_m_"
      else
        false
  | _ -> false 

let rec is_local_var (check_length:bool) (jterm:jterm_t) =
  match jterm with
  | JLocalVar _ -> true
  | JSize jt -> if check_length then is_local_var true jt else false 
  | _ -> false 

let cost_var = ref None
let set_cost_var v = cost_var := Some v
let get_cost_var () = Option.get !cost_var

let compare_num (n1:numerical_t) (n2:numerical_t) =
  n1#compare n2
    
let compare_tables
      (compare_keys:('a -> 'a -> int))
      (compare_elements:('b -> 'c -> int))
      (t1:< get: 'a -> 'b option; keys: < union : 'd -> < toList : 'a list; .. >; .. >; .. >)
      (t2:< get: 'a -> 'c option; keys : 'd; .. >):int =
  let sorted_keys = List.sort compare_keys (t1#keys#union t2#keys)#toList in
  let rec comp keys =
    match keys with
    | key :: rest_keys ->
	begin
	  match (t1#get key, t2#get key) with
	  | (None, None) ->
             raise (JCH_failure (STR "unexpected case"))
	  | (None, Some _) -> -1
	  | (Some _, None) -> 1
	  | (Some n1, Some n2) ->
	      let c = compare_elements n1 n2 in
	      if c = 0 then comp rest_keys else c
	end
    | [] -> 0 in
  comp sorted_keys

module JTermCollections = CHCollections.Make 
    (struct
      type t = jterm_t
      let compare j1 j2 = jterm_compare j1 j2
      let toPretty j = jterm_to_pretty j
    end)

module JTermTableCollections = CHCollections.Make
    (struct
      type t = numerical_t JTermCollections.table_t
      let compare = compare_tables jterm_compare compare_num
      let toPretty t = t#toPretty
    end)

let is_length (jterm:jterm_t) = 
  match jterm with
  | JSize _ -> true
  | _ -> false

let is_field (jterm:jterm_t) =
  match jterm with
  | JStaticFieldValue _ 
  | JObjectFieldValue _ -> true
  | _ -> false

let not_pos_jterms = new IntCollections.table_t
                   
let add_not_pos_jterm (cmix:int) (jterm:jterm_t) =
  let key = if is_field jterm then (-1) else cmix in
  match not_pos_jterms#get key with
  | Some set -> set#add jterm
  | _ ->
      let s = JTermCollections.set_of_list [jterm] in
      not_pos_jterms#set key s

let record_not_pos_jterms () =
  (match not_pos_jterms#get (-1) with
  | Some set ->
     chlog#add
       "not known to be positive "
       (LBLOCK[STR "fields "; set#toPretty; NL])
  | _ -> ()) ;
  let record_set (key, set) =
    if key != (-1) then 
      chlog#add
        "not known to be positive "
        (LBLOCK[STR "method "; INT key; set#toPretty; NL]) in
  List.iter record_set not_pos_jterms#listOfPairs

let is_const (jt:jterm_t) =
  match jt with
  | JConstant n -> true
  | _ -> false

let is_large_const (jt:jterm_t) =
  match jt with
  | JConstant n when n#gt max_num -> true
  | _ -> false

let is_pos_jterm (jt:jterm_t) = 	
  match jt with
  | JConstant n 
  | JSymbolicConstant (_, Some n, _, _) ->
      n#geq numerical_zero 
  | JSize _ -> true
  | _ -> JCHNumericAnalysis.is_pos_field jt 

let pp_list_jterm (jts:jterm_t list) =
  pretty_print_list jts jterm_to_pretty "{" "; " "}"

let rec no_local_vars (jterm:jterm_t) =
  match jterm with
  | JLocalVar _ -> false
  | JSize jt -> no_local_vars jt
  | _ -> true

let no_calls_or_lcs (lcs_to_keep:JTermCollections.set_t) (jterm:jterm_t) =
  match jterm with 
  | JSymbolicConstant _ ->
      if is_sym_call jterm then false 
      else if is_sym_lc jterm then
	if lcs_to_keep#has jterm then false
	else true
      else true
  | _ -> true

let no_cost_calls_or_lcs
      (lcs_to_keep:JTermCollections.set_t) (jterm:jterm_t) =
  match jterm with 
  | JSymbolicConstant _ ->
     if is_sym_cost jterm then
       false
     else if is_sym_call jterm then
       false 
      else if is_sym_lc jterm then
       if lcs_to_keep#has jterm then
         false
       else
         true
     else
       true
  | _ -> true

let no_loop_costs (jterm:jterm_t) =
  not (is_sym_lp jterm)
    
let remove_pc (jterm:jterm_t) =
  match jterm with 
  | JSymbolicConstant (t, lb, ub, name) ->
      if (String.length name) > 5 && (String.sub name 0 5) = "call_" then
	begin
	  let ind = String.index name '@' in
	  let new_name = String.sub name 0 ind in
	  JSymbolicConstant (t, lb, ub, new_name)
	end
      else
        jterm
  | _ -> jterm

let max_cost_analysis_time = ref 1.
let set_max_cost_analysis_time m = max_cost_analysis_time := m
    
exception JCH_cost_out_of_time of string
                                
let cost_time_limit = ref 1.
let start_cost_analysis () =  
  cost_time_limit := Sys.time () +. !max_cost_analysis_time

let check_cost_analysis_time (str:string) =
  if Sys.time () > !cost_time_limit then
    begin
      let str = "reached cost analysis time limit " ^ str in
      raise (JCH_cost_out_of_time str)
    end


