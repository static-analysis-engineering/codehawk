(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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
open CHIntervals
open CHLanguage
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

class int_field_manager_t :
  object ('a)

    method get_all_non_private_fields : (field_info_int * interval_t list) list
    method get_all_num_fields : field_info_int list
    method get_field_intervals : field_info_int -> interval_t list
    method is_const_field : field_info_int -> bool
    method is_dt_field : class_name_int -> field_signature_int -> bool
    method project_out : field_info_int -> unit
    method put_field :
	     symbol_t
             -> field_info_int
             -> interval_t
             -> interval_t list
             -> bool
             -> variable_t
             -> unit
    method record_field : instruction_info_int -> unit
    method reset : unit
    method start : unit
    method set_unknown_fields : JCHProcInfo.jproc_info_t -> unit
    method toPretty : pretty_t

  end

val int_field_manager : int_field_manager_t
