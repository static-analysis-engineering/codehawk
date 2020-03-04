(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

open Big_int_Z

(* chlib *)
open CHIntervals
open CHLanguage
open CHPretty

   
class interval_array_t : 
  int -> 
  object ('a)
    method augment : int -> int -> interval_t -> 'a
    method get_arrays : interval_t array array 
    method clone : 'a
    method copy : 'a
    method copy_set : int -> interval_t -> 'a
    method copy_set_typed : int -> interval_t -> 'a
    method get : int -> interval_t
    method get_type_interval : int -> interval_t
    method get_singletons : (int * big_int) list
    method get_singletons_that_changed : 'a -> 
      (int * interval_t) list * (int * interval_t) list 
    method is_discrete : int -> bool 
    method iteri :  (int -> interval_t -> unit) -> unit
    method join' : int -> 'a -> 'a
    method join : 'a -> 'a
    method make : int ->  interval_t -> 'a
    method make_from_types : int -> 'a
    method make_bottom_intervals : int -> 'a
    method make_top_intervals : int -> 'a
    method meet : 'a -> bool -> 'a
    method project_out : int list -> 'a
    method pr__debug_large_interval_array :
             JCHNumericInfo.numeric_info_t -> string -> variable_t list -> unit
    method remap : int -> (int * int) list -> 'a
    method remove : int list -> 'a
    method remove_entries : int -> int list -> 'a
    method restrict_to_type :int list -> 'a
    method set : int -> interval_t -> unit
    method set_type_intervals :
             JCHProcInfo.jproc_info_t -> variable_t list -> 'a
    method set_type_intervals_and_restrict :
             JCHProcInfo.jproc_info_t -> variable_t list -> 'a
    method to_pretty : variable_t list -> pretty_t
    method toPretty : pretty_t
    method widening' : 'a -> 'a
    method widening : 'a -> 'a

  end

val make_top_intervals : int -> interval_array_t 
val make_from_types : JCHProcInfo.jproc_info_t -> variable_t list -> interval_array_t 

val dbg : bool ref
