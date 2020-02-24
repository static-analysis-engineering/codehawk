(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Henny Sipma
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
open CHPretty
open CHUtils


(* Add a string to the attribute list of a symbol *) 
let add_attribute (s:symbol_t) (att:string):symbol_t =
  let sym = s#getBaseName in
  let seq = s#getSeqNumber in
  let atts = s#getAttributes in
  new symbol_t ~atts:(atts @ [ att ]) ~seqnr:seq sym

(* Return READ/READ_WRITE variables from a signature *)
let get_input_vars (bindings:bindings_t) (signature:signature_t):variable_t list =
  let is_input_var (sym,var) =
    let (_,_,m) = List.find (fun (s,_,_) -> sym#equal s) signature in
    match m with READ | READ_WRITE -> true | _ -> false in
  List.map (fun (_,v) -> v) (List.filter is_input_var bindings)

(* Return WRITE/READ_WRITE variables from a signature *)
let get_output_vars (bindings:bindings_t) (signature:signature_t):variable_t list =
  let is_output_var (sym,var) =
    let (_,_,m) = List.find (fun (s,_,_) -> sym#equal s) signature in
    match m with WRITE | READ_WRITE -> true | _ -> false in
  List.map (fun (_,v) -> v) (List.filter is_output_var bindings)


let is_last_opcode_for_line (i:int) (lt:(int * int list) list) =
  let last_opcodes = List.fold_right
      (fun (_,l) a ->
	match l with
	  [] -> a
	| _ -> (List.hd (List.rev l)) :: a) lt  [] in
  List.mem i last_opcodes


