(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* extchlib *)
open CHPretty

(* cchlib *)
open CCHBasicTypes

val constant_to_string: constant -> string

val location_to_pretty: location -> pretty_t
val location_line_to_string: location -> string

val storage_to_string: storage -> string
val int_type_to_string   : ikind -> string
val binop_to_print_string: binop -> string
val unop_to_print_string : unop -> string

val typ_to_pretty   : typ -> pretty_t
val exp_to_pretty   : exp -> pretty_t
val lval_to_pretty  : lval -> pretty_t
val offset_to_pretty: offset -> pretty_t

val instr_to_pretty : instr -> pretty_t

val enuminfo_to_pretty: enuminfo -> pretty_t
val compinfo_to_pretty: compinfo -> pretty_t
val varinfo_to_pretty : varinfo -> pretty_t
