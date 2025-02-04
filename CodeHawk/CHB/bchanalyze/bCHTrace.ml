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
open CHLanguage
open CHPretty

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHBCTypeUtil
open BCHDoubleword
open BCHFunctionInfo
open BCHFunctionData
open BCHLibTypes
open BCHMemoryReference
open BCHSystemInfo

(* bchlibx86 *)
open BCHAssemblyFunctions
open BCHAssemblyInstructionAnnotations
open BCHLibx86Types

module H = Hashtbl
module TR = CHTraceResult


let get_fname (faddr:doubleword_int) =
  if functions_data#has_function_name faddr then
    (functions_data#get_function faddr)#get_function_name
  else
    faddr#to_hex_string


let get_xarg_indices (_finfo:function_info_int) (_x:xpr_t) = []


let var_is_referenced (_finfo:function_info_int) (x:xpr_t) (_v:variable_t) =
  let vars = variables_in_expr x in
  let aux (_xv:variable_t) = false in
  List.exists aux vars


let se_address_is_referenced
    (finfo:function_info_int) (floc:floc_int) (x:xpr_t) (v:variable_t) =
  if floc#is_address x then
    let (memref,memoffset) = floc#decompose_address x in
    if is_constant_offset memoffset then
      TR.tfold_default
        (fun offset ->
          let memv = finfo#env#mk_memory_variable memref offset in
          let memx = floc#rewrite_variable_to_external memv in
          var_is_referenced finfo memx v)
        false
        (get_total_constant_offset memoffset)
    else
      false
  else
    false


let get_callers (faddr:doubleword_int) =
  let callers = ref [] in
  let _ =
    assembly_functions#itera
      (fun _ f ->
        f#iter_calls (fun _iaddr floc ->
            if floc#has_call_target
               && floc#get_call_target#is_app_call
               && floc#get_call_target#get_app_address#equal faddr then
	callers := floc :: !callers
            else
              if floc#has_call_target
                 && floc#get_call_target#is_wrapped_app_call
	         && floc#get_call_target#get_wrapped_app_address#equal faddr then
	        callers := floc :: !callers
              else
                ())) in
  !callers


let get_callees (faddr:doubleword_int) =
  let callees = ref [] in
  let f = assembly_functions#get_function faddr#index in
  let _ = f#iter_calls (fun _ floc -> callees := floc :: !callees) in
  !callees


let get_app_callees (faddr:doubleword_int):doubleword_int list =
  List.fold_left (fun acc floc ->
    if floc#has_call_target && floc#get_call_target#is_app_call then
      floc#get_call_target#get_app_address :: acc
    else
      acc) [] (get_callees faddr)


let record_fpcallback_arguments (f:assembly_function_int) =
  let is_code_address n =
    try
      system_info#is_code_address
        (TR.tget_ok (numerical_to_doubleword n))
    with
    | Invalid_argument _ -> false in
  f#iter_calls (fun _ floc ->
    if floc#has_call_target && floc#get_call_target#is_signature_valid then
      List.iter (fun (p,x) ->
	if is_function_type p.apar_type then
	  match x with
	  | XConst (IntConst n) when is_code_address n ->
	     ignore
               (functions_data#add_function
                  (TR.tget_ok (numerical_to_doubleword n)))
	  | _ -> ()) floc#get_call_args)


let rec _trace_fwd faddr op =
  let fname =
    if functions_data#has_function_name faddr then
      (functions_data#get_function faddr)#get_function_name
    else
      faddr#to_hex_string in
  let finfo = get_function_info faddr in
  let callees = get_callees faddr in
  let _ =
    pr_debug [
        STR "--> Trace "; STR fname; STR " with operand "; INT op; NL] in
  List.iter (fun callee ->
      if callee#has_call_target && callee#get_call_target#is_signature_valid then
        let call_args = callee#get_call_args in
        List.iter (fun (p,e) ->
	    match p.apar_location with
	    | [StackParameter (par, _)] ->
	       let argIndices = get_xarg_indices finfo e in
	       if List.mem op argIndices then
	         begin
	           pr_debug [STR "    "; callee#l#toPretty; STR ": ";
			      (create_annotation callee)#toPretty; NL];
	           if callee#has_call_target
                      && callee#get_call_target#is_app_call then
		     let target = callee#get_call_target#get_app_address in
		     _trace_fwd target par
	         end
	    | _ -> ()) call_args
      else
        ()) callees


let rec _trace_bwd floc op =
  let fname = get_fname floc#l#f in
  let finfo = floc#f in
  let iann = create_annotation floc in
  let default () =
    pr_debug [STR "  "; iann#toPretty;  STR " in "; STR fname; NL] in
  if floc#has_call_target && floc#get_call_target#is_signature_valid then
    let (_,e) = List.nth floc#get_call_args (op-1) in
    let argIndices = get_xarg_indices finfo e in
    match argIndices with
    | [] -> default ()
    | _ ->
      let _ = default () in
      let _ =
        pr_debug [
            STR "Argument indices: ";
	    pretty_print_list argIndices (fun n -> INT n) "[" "," "]"; NL] in
      let callers = get_callers floc#l#f in
      List.iter
        (fun c -> List.iter (fun arg -> _trace_bwd c arg) argIndices) callers
  else
    default ()


let _get_lib_calls (libfun:string) =
  let flocs = ref [] in
  try
    let _ = assembly_functions#itera (fun _faddr f ->
      f#iter_calls (fun _ floc ->
	if floc#has_call_target && floc#get_call_target#is_dll_call then
	  let fname = floc#get_call_target#get_name in
	  if fname = libfun then
	    flocs := floc :: !flocs
	  else
	    ()
	else if floc#has_call_target
                && floc#get_call_target#is_app_call
                && floc#get_call_target#get_name = libfun then
	  flocs := floc :: !flocs
	else ())) in
    !flocs
  with
    BCH_failure p ->
      begin
	pr_debug [STR "Error in get_lib_calls: "; p; NL];
	!flocs
      end


let _get_jni_calls () =
  let flocs = ref [] in
  let _ = assembly_functions#itera (fun _faddr f ->
    f#iter_calls (fun _ floc ->
      if floc#has_call_target && floc#get_call_target#is_jni_call then
	flocs := floc :: !flocs
      else
	())) in
  !flocs


let _get_unresolved_calls () =
  let flocs = H.create 5 in
  let sym_printer = (fun s -> STR s#getBaseName) in
  let get_name faddr =
    let faddr = TR.tget_ok (string_to_doubleword faddr) in
    if functions_data#has_function_name faddr then
      (functions_data#get_function faddr)#get_function_name
    else
      faddr#to_hex_string in
  let _ = assembly_functions#itera (fun _faddr f ->
    f#iter_calls (fun _ _floc -> ())) in
  let fns = ref [] in
  let _ = H.iter (fun k v -> fns := (k,v) :: !fns) flocs in
  let fns = List.sort (fun (f1,_) (f2,_) -> Stdlib.compare f2 f1) !fns in
  let pp = ref [] in
  let _ =
    List.iter (fun (faddr, calls) ->
        let env =
          (get_function_info (TR.tget_ok (string_to_doubleword faddr)))#env in
        let xpr_formatter =
          make_xpr_formatter sym_printer env#variable_name_to_pretty in
        let ppp = ref [] in
        let calls = List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i2 i1) calls in
        let _ =
          List.iter (fun (iaddr,x) ->
              let p = LBLOCK [STR iaddr; STR "   "; xpr_formatter#pr_expr x; NL] in
              ppp := p :: !ppp) calls in
        let p = LBLOCK [STR (get_name faddr); NL; INDENT (3, LBLOCK !ppp); NL] in
        pp := p :: !pp) fns in
  LBLOCK !pp
