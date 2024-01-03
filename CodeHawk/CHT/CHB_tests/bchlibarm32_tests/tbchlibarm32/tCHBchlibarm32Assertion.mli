(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2024  Aarno Labs LLC

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

(* xprlib *)
open XprTypes

(* bchlibarm32 *)
open BCHARMTypes

   
val equal_jumptable_targets:
  ?msg:string
  -> expected:(string * int list) list
  -> received:arm_jumptable_int
  -> unit
  -> unit


val equal_cfg_edges:
  ?msg:string
  -> expected:(string * string) list
  -> received:(string * string) list
  -> unit
  -> unit


val equal_chif_conditionxprs:
  ?msg:string
  -> expected:string
  -> received:xpr_t list
  -> unit
  -> unit


val equal_arm_conditional_expr:
  ?msg:string
  -> expected:string
  -> received: xpr_t option
  -> unit
  -> unit


val equal_instrxdata_conditionxprs:
  ?msg: string
  -> expected:string
  -> received:xpr_t list
  -> index:int
  -> unit
  -> unit


val equal_instrxdata_tags:
  ?msg: string
  -> expected:string
  -> received:string list
  -> indices:int list
  -> unit
  -> unit


val equal_dictionary_key:
  ?msg: string
  -> expected:(string list * int)
  -> received:(string list * int list)
  -> unit
  -> unit
