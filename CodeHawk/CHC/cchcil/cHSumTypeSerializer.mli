(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
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

(* cil *)
open Cil
   
class type ['a] sumtype_string_converter_int =
  object
    method to_string: 'a -> string
    method from_string: string -> 'a
  end


val ikind_serializer: ikind sumtype_string_converter_int
val fkind_serializer: fkind sumtype_string_converter_int
val unop_serializer: unop sumtype_string_converter_int
val binop_serializer: binop sumtype_string_converter_int

val storage_serializer: storage sumtype_string_converter_int

val exp_serializer: exp sumtype_string_converter_int
val typ_serializer: typ sumtype_string_converter_int
val attrparam_serializer: attrparam sumtype_string_converter_int
val constant_serializer: constant sumtype_string_converter_int
val offset_serializer: offset sumtype_string_converter_int
val typsig_serializer: typsig sumtype_string_converter_int

val label_serializer: label sumtype_string_converter_int
val stmtkind_serializer: stmtkind sumtype_string_converter_int
val instr_serializer: instr sumtype_string_converter_int
