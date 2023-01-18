(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHTraceResult

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHConstantDefinitions
open BCHLibTypes

module H = Hashtbl
module B = Big_int_Z
module TR = CHTraceResult


let exp2 p  = B.power_int_positive_int 2 p
let e8 = exp2 8
let e16 = exp2 16
let e32 = exp2 32
let e64 = exp2 64


let signedimmranges = H.create 4
let unsignedimmranges = H.create 4
let _ =
  List.iter (fun i ->
      begin
        H.add
          signedimmranges
          i
          (let p = (8 * i) - 1 in
           let e = exp2 p in
           (B.minus_big_int e, B.sub_big_int e B.unit_big_int));
        H.add
          unsignedimmranges
          i
          (let p = 8 * i in
           let e = exp2 p in
           (B.zero_big_int, B.sub_big_int e B.unit_big_int))
      end) [1; 2; 4; 8]


let signed_imm_range (i: int): (B.big_int * B.big_int) TR.traceresult =
  if H.mem signedimmranges i then
    Ok (H.find signedimmranges i)
  else
    Error ["Immediate: byte size not supported: " ^ (string_of_int i)]


let unsigned_imm_range (i: int): (B.big_int * B.big_int) TR.traceresult =
  if H.mem unsignedimmranges i then
    Ok (H.find unsignedimmranges i)
  else
    Error ["Immediate: byte size not supported: " ^ (string_of_int i)]


class immediate_t
        (signed:bool) (size_in_bytes:int) (big_val:B.big_int):immediate_int =
object (self: 'a)

  val signed = signed

  val size_in_bytes = size_in_bytes

  val big_val = big_val

  method equal (other:'a) = B.eq_big_int self#to_big_int other#to_big_int

  (* ============================================================= Predicates *)

  method is_doubleword = size_in_bytes = 4

  method is_quadword = size_in_bytes = 8

  (* ============================================================= Converters *)

  method to_big_int = big_val

  method to_numerical = mkNumerical_big big_val

  method to_doubleword =
    if size_in_bytes <= 4 then
      let dwimm = (TR.tget_ok (self#sign_extend 4))#to_unsigned in
      Some (TR.tget_ok (numerical_to_doubleword dwimm#to_numerical))
    else
      None

  method to_int =
    try Some (B.int_of_big_int big_val) with Failure _ -> None

  (* =========================================================== Transformers *)

  method sign_extend (size: int): 'a traceresult =
    if size >= size_in_bytes && H.mem signedimmranges size then
      Ok {< size_in_bytes = size >}
    else
      Error [
          "Immediate:sign_extend:from:"
          ^ (string_of_int size_in_bytes)
          ^ " to:"
          ^ (string_of_int size)]

  method to_unsigned = 
    if B.ge_big_int big_val B.zero_big_int then
      {< signed = false >}
    else
      {< signed = false ;
         big_val = B.add_big_int big_val (exp2 (8*size_in_bytes)) >}

  (* ======================================================== Pretty printing *)

  method to_string = B.string_of_big_int big_val

  method to_hex_string =
    if size_in_bytes <= 4 then
      let numval = self#to_numerical in
      if signed then
        TR.tget_ok (numerical_to_signed_hex_string numval)
      else
        TR.tget_ok (numerical_to_hex_string numval)
    else
      if not signed then
        let (hi, lo) = B.quomod_big_int big_val e32 in
        if B.eq_big_int hi B.zero_big_int then
          let dwlo = TR.tget_ok (big_int_to_doubleword lo) in
          dwlo#to_hex_string
        else
          let dwhi = TR.tget_ok (big_int_to_doubleword hi) in
          let dwlo = TR.tget_ok (big_int_to_doubleword lo) in
          dwhi#to_hex_string ^ dwlo#to_fixed_length_hex_string
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Size for immediate not supported: ";
                INT size_in_bytes]))

  method toPretty =
    try
      STR self#to_hex_string
    with
    | BCH_failure p ->
       begin
         ch_error_log#add
           "immediate value inconsistent"
           (LBLOCK [
                STR (B.string_of_big_int big_val);
                STR "; size in bytes: ";
                INT size_in_bytes;
                STR " (";
                p;
                STR ")"]);
         STR (B.string_of_big_int big_val)
       end

end


let make_immediate
      (signed: bool) (size_in_bytes: int) (big_val: B.big_int): immediate_result =
  let immrange =
    if signed then
      signed_imm_range size_in_bytes
    else
      unsigned_imm_range size_in_bytes in
  TR.tbind
    ~msg:"make_immediate"
    (fun (low, high) ->
      if B.le_big_int low big_val && B.le_big_int big_val high then
        Ok (new immediate_t signed size_in_bytes big_val)
      else
        Error [
            "Immediate value out-of-range: "
            ^ (B.string_of_big_int big_val)
            ^ "(low: "
            ^ (B.string_of_big_int low)
            ^ "; high: )"
            ^ (B.string_of_big_int high)
            ^ ")"])
    immrange


let signed_immediate_from_int ?(size=4) (i: int) =
  make_immediate true size (B.big_int_of_int i)

let imm0 = TR.tget_ok (signed_immediate_from_int 0)
let imm1 = TR.tget_ok (signed_immediate_from_int 1)


