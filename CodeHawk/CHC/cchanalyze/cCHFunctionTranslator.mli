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

(* chlib *)
open CHLanguage

(* cchlib *)
open CCHBasicTypes

(* cchanalyze *)
open CCHAnalysisTypes
	
val get_num_translator:
  c_environment_int -> orakel_int -> operations_provider_int -> function_translator_int
  
val get_interval_translator:
  c_environment_int -> orakel_int -> operations_provider_int -> function_translator_int
  
val get_valueset_translator: 
  c_environment_int -> orakel_int -> operations_provider_int -> function_translator_int

val get_symbolicsets_translator: 
  c_environment_int -> orakel_int -> operations_provider_int -> function_translator_int

val get_sym_pointersets_translator:
  c_environment_int -> orakel_int -> operations_provider_int -> function_translator_int

val get_statesets_translator:
  c_environment_int -> orakel_int -> operations_provider_int -> function_translator_int

