(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023  Aarno Labs, LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerTypes


let oim5 (v: int): int = v + 1

let rindex (v: int): int = if v < 8 then v else v + 16

let arindex (v: int): int = v + 8

let d8_sign_extend (d8: int) = if d8 >= 128 then d8 - 256 else d8


(* SCI8(F, SCL, UI8) format  (VLEPEM, page 3-5)
   if SCL = 0 then imm_value <- (24)F || UI8 else
   if SCL = 1 then imm_value <- (16)F || UI8 || (8)F else
   if SCL = 2 then imm_value <- (8)F || UI8 || (16)F
   else imm_value <- UI8 || (24)F

   From: VLEPEM, page 3-5
 *)
let sci8 (f: int) (scl: int) (ui8: int) =
  if f = 0 then
    match scl with
    | 0 -> ui8
    | 1 -> ui8 lsl 8
    | 2 -> ui8 lsl 16
    | 3 -> ui8 lsl 24
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Unexpected value for SCL in SCI8: "; INT scl]))
  else
    match scl with
    | 0 -> (16777215 lsl 8) + ui8
    | 1 -> (65535 lsl 16) + (ui8 lsl 8) + 255
    | 2 -> (255 lsl 24) + (ui8 lsl 16) + 65535
    | 3 -> (ui8 lsl 24) + 16777215
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Unexpected value SCL in SCI8: "; INT scl]))
