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

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types

(* bchlibmips32 *)
open BCHMIPSTypes

(* bchlibarm32 *)
open BCHARMTypes

(* bchlibpower32 *)
open BCHPowerTypes


val add_no_lineq: string -> unit

val analyze_all: bool ref
val analyze: float -> unit

val analyze_x86_function:
  doubleword_int -> assembly_function_int -> int -> unit

val analyze_mips_function:
  doubleword_int -> mips_assembly_function_int -> int -> unit

val analyze_mips: float -> unit

val analyze_arm_function:
  doubleword_int -> arm_assembly_function_int -> int -> unit

val analyze_arm: float -> unit


val analyze_pwr_function:
  doubleword_int -> pwr_assembly_function_int -> int -> unit

val analyze_pwr: float -> unit
