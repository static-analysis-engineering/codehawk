(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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

(* bchlib *)
open BCHDoubleword
open BCHFunctionInfo
open BCHLibTypes
open BCHMemoryAccesses
open BCHPreFileIO


(* bchlibx86 *)
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHRecordMemoryAccesses
open BCHLibx86Types

module H = Hashtbl


class global_var_accesses_t:global_var_accesses_int =
object

  (* structure:
        function-address ->
          global-var -> (instr-address, memory-access) list  *)
  val table = H.create 3

  method initialize =
    assembly_functions#itera (fun faddr f ->
      let finfo = get_function_info faddr in
      let _ = record_memory_accesses f in
      let accesses = finfo#get_global_accesses in
      let ftable = H.create 5 in
      begin
	H.add table faddr#index ftable ;
	List.iter (fun (gvar,l) -> H.add ftable gvar#index l) accesses
      end)

  (* returns a list of
       (global-var,
          (function-address,
             (instr-address, memory-access) list ) )   *)
  method get_accesses =
    let gtable = H.create 3 in
    let result = ref [] in
    let add faddr gvtable = 
      let addg gvar l =
	let entry = if H.mem gtable gvar then H.find gtable gvar else [] in
	H.replace gtable gvar ( (index_to_doubleword faddr,l) :: entry) in 
      H.iter addg gvtable in
    let _ = H.iter add table in
    let _ = H.iter (fun k v -> result := (k,v) :: !result) gtable in
    List.map (fun (k,v) -> (index_to_doubleword k, v))
      (List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) !result)

  (* returns a list of
      (global-var, (instr-address, memory-access) list ) *)
  method get_function_accesses (faddr:doubleword_int) =
    let result = ref [] in
    if H.mem table faddr#index then
      let _ = H.iter (fun k v -> result := (k,v) :: !result) (H.find table faddr#index) in
      List.map (fun (k,v) -> (index_to_doubleword k,v))
	(List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) !result)
    else
      []

  (* return a list of
       (function-address, (instr-address, memory-access list))  *)
  method get_gvar_accesses (gvar:doubleword_int) =
    let result = ref [] in
    let _ = H.iter (fun k v -> 
      if H.mem v gvar#index then result := (k,H.find v gvar#index) :: !result) table in
    List.map  (fun (k,v) -> (index_to_doubleword k, v))
      (List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) !result)

end  
      

let global_var_accesses = new global_var_accesses_t
