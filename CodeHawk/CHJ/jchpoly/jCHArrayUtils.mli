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
open CHLanguage
open CHPretty

val dbg : bool ref
  
val remove_0_rows_m : big_int array array -> big_int array array
  
val for_all_ind_a:
  (int -> big_int -> bool) -> big_int array -> int -> int -> bool

val for_all_a : (int -> big_int -> bool) -> big_int array -> bool
val exists_a : (int -> 'a -> bool) -> 'a array -> bool 
val equal_a : big_int array -> big_int array -> bool 
val find_gcd_a : big_int array -> big_int
val find_mult_a : big_int array -> big_int
val find_lcm_a : big_int array -> big_int
val copy_m : big_int array array -> big_int array array
val swap_rows_m : big_int array -> int -> int -> unit
val equal_m : big_int array array -> big_int array array -> bool

val find_indep_sols_m :
  big_int array array
  -> int
  -> int array
  -> big_int array array * big_int array array
  
val find_cols_used_m : big_int array array -> int array
val get_common_col_used_a : int array -> int array -> int
  
val find_ineq_sols_m :
  bool
  -> big_int array array
  -> big_int array array
  -> big_int array array * big_int array array * bool
  
val remove_trivial_rows : big_int array array -> big_int array array
  
val minimize_m :
  big_int array array
  -> big_int array array
  -> (big_int array array * big_int array array) option
  
val find_eq_from_sol_a : big_int array * big_int array -> big_int array
  
val find_eqs_from_sols_m :
  big_int array array * big_int array array -> big_int array array
  
val implies_eq: big_int array array -> big_int array -> bool
  
val implies_constraint :
  big_int array array
  -> big_int array array
  -> big_int array
  -> bool -> bool * (big_int array array * big_int array array) option
  
val implies_constraint_error :
  big_int array array
  -> big_int array array
  -> big_int array
  -> bool
  -> unit
  
val add_rows_m :
  big_int array array -> big_int array list -> big_int -> big_int array array
  
val remove_row_m : big_int array array -> int -> big_int array array
val remove_rows_m : big_int array array -> int list -> big_int array array
val add_col_a : big_int array -> int -> big_int -> big_int array
val add_col_m : big_int array array -> int -> big_int -> big_int array array
val remove_col_a : big_int array -> int -> big_int array
val remove_col_m : big_int array array -> int -> big_int array array
val remove_cols_m : big_int array array -> int list -> big_int array array
val get_used_cols_a : big_int array -> int list

val pp_with_vars_m:
  big_int array array -> variable_t list ->string ->  pretty_t
  
val has_row :  big_int array array ->  big_int array -> bool
