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
open CHNumerical

(* chutil *)
open CHLogger

(* bchlib *)
open BCHDoubleword
open BCHConstantDefinitions
open BCHLibTypes

module B = Big_int_Z

let exp2 p  = B.power_int_positive_int 2 p
let e16 = exp2 16


class immediate_t (signed:bool) (size_in_bytes:int) (big_val:B.big_int):immediate_int =
object (self: 'a)

  val signed = signed
  val size_in_bytes = size_in_bytes
  val big_val = big_val

  method equal (other:'a) = B.eq_big_int self#to_big_int other#to_big_int

  (* =============================================================== Predicates *)

  method is_doubleword = size_in_bytes = 4

  (* =============================================================== Converters *)

  method to_big_int = big_val

  method to_numerical = mkNumerical_big big_val

  method to_int = try Some (B.int_of_big_int big_val) with Failure _ -> None

  method to_doubleword = big_int_to_doubleword big_val
    
  (* ============================================================= Transformers *)

  method sign_extend (size:int) = {< size_in_bytes = size >}

  method to_unsigned = 
    if B.ge_big_int big_val B.zero_big_int then
      {< signed = false >}
    else
      {< signed = false ; big_val = B.add_big_int big_val (exp2 (8*size_in_bytes)) >}

  (* ========================================================== Pretty printing *)

  method to_string = 
    let v = self#to_doubleword in
    if has_symbolic_name v then get_symbolic_name v else B.string_of_big_int big_val

  method to_hex_string = 
    let abs_val = B.abs_big_int big_val in
    let dw = big_int_to_doubleword abs_val in
    if B.lt_big_int big_val B.zero_big_int then
      "-" ^ dw#to_hex_string
    else
      dw#to_hex_string

  method toPretty = STR self#to_hex_string
end

let make_immediate = new immediate_t

let immediate_from_int i = new immediate_t true 0 (B.big_int_of_int i)
let imm1 = immediate_from_int 1
let imm0 = immediate_from_int 0

