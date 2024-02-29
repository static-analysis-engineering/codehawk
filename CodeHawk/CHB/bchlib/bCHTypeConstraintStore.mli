(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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
   

val mk_type_constraint_store: unit -> type_constraint_store_int

val mk_intvalue_type_constant: int -> type_constant_t option

val mk_data_address_load_typevar:
      ?size:int -> ?offset:int -> doubleword_int -> type_variable_t

val mk_data_address_store_typevar:
      ?size:int -> ?offset:int -> doubleword_int -> type_variable_t

val mk_gvar_type_var: doubleword_int -> type_variable_t

val mk_function_return_typevar: doubleword_int -> type_variable_t

val mk_function_return_load_typevar:
  ?size:int -> ?offset:int -> doubleword_int -> type_variable_t

val mk_function_return_store_typevar:
  ?size:int -> ?offset:int -> doubleword_int -> type_variable_t
  
val mk_regparam_typevar: doubleword_int -> register_t -> type_variable_t

val mk_regparam_load_typevar:
      ?size:int -> ?offset:int -> doubleword_int -> register_t -> type_variable_t

val mk_regparam_load_array_typevar:
      ?size:int -> ?offset:int -> doubleword_int -> register_t -> type_variable_t
  
val mk_regparam_store_typevar:
      ?size:int -> ?offset:int -> doubleword_int -> register_t -> type_variable_t

val mk_regparam_store_array_typevar:
      ?size:int -> ?offset:int -> doubleword_int -> register_t -> type_variable_t
  
val mk_stackaddress_typevar: doubleword_int -> int -> type_variable_t
