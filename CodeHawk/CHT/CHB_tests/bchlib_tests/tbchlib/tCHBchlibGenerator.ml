(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* bchlib *)
open BCHDoubleword

module G = TCHGenerator
module BA = TCHBchlibAssertion


let msb_classifier =
  (fun dw -> if dw#to_int > BA.e31 then "msbset" else "msbnotset")


let msb_pair_classifier =
  (fun (dw1, dw2) ->
    let b1 = if dw1#to_int >= BA.e31 then "Y" else "N" in
    let b2 = if dw2#to_int >= BA.e31 then "Y" else "N" in
    "msb" ^ b1 ^ b2)


let doubleword =
  ((fun r ->
    let l = G.make_int 1 9 in
    let (gen_hex, _) = G.number_hex l in
    let s = "0x" ^ (gen_hex r) in
    string_to_doubleword s),
   (fun dw -> dw#to_hex_string))


let doubleword_pair =
  ((fun r ->
    let (gen_d, _) = doubleword in
    (gen_d r, gen_d r)),
   (fun (dw1, dw2) -> (dw1#to_hex_string ^ "," ^ dw2#to_hex_string)))
