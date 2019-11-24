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

(* ============================================================================== *
 * Adapted from CIL                                                               *
 * ============================================================================== *)

(* chlib *)
open CHNumerical

(* xprlib *)
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

val zero: exp
val one: exp

val make_constant_exp: numerical_t -> exp

val binop_to_xop: binop -> xop_t
val exp_to_xpr: exp -> xpr_t option  (* constants only *)
  
val is_relational_operator: binop -> bool
val reverse_relational_operator: binop -> binop

val is_signed_type  : ikind -> bool
val is_bool_type    : ikind -> bool
val is_unsigned_type: ikind -> bool
val is_character_type: ikind -> bool

val get_integer_promotion: typ -> typ -> typ

val ikind_size_leq : ikind -> ikind -> bool
val const_fits_kind: constant -> ikind -> bool
val int_fits_kind  : numerical_t -> ikind -> bool
val float_fits_kind: float -> fkind -> bool
val enum_fits_kind : string -> ikind -> bool

val has_const_attribute: typ -> bool

val is_not_zero: exp -> bool

val is_safe_int_cast: ikind -> ikind -> bool
val get_safe_upperbound: ikind -> numerical_t
val get_safe_lowerbound: ikind -> numerical_t
val get_safe_bit_width : ikind -> int
val get_required_minimum_bit_width: int -> int

val type_of_tgt_exp  : cfundeclarations_int -> exp -> typ
val type_of_exp      : cfundeclarations_int -> exp -> typ
val type_of_lval     : cfundeclarations_int -> lval -> typ
val type_of_offset   : cfundeclarations_int -> typ -> offset -> typ
val returntype_of_exp: cfundeclarations_int -> exp -> typ

val is_integral_type: typ -> bool
val is_pointer_type : typ -> bool
val is_string_type  : typ -> bool
val is_array_type   : typ -> bool
val is_void_type    : typ -> bool
val is_struct_type  : typ -> bool
val is_void_ptr_type: typ -> bool
val is_function_type: typ -> bool
val is_float_type   : typ -> bool
val is_unsigned_integral_type: typ -> bool
val is_volatile_type: typ -> bool

val is_constant_string: exp -> bool
val is_enum_constant  : string -> exp -> bool

val get_field_offset: offset -> string * int
val add_offset: offset -> offset -> offset
val get_field_lval_exp: exp -> string * int
val is_field_offset: offset -> bool
val is_constant_offset: offset -> bool
val is_field_lval_exp: exp -> bool

val exp_has_repeated_field: exp -> bool

val size_of_type    : cfundeclarations_int -> typ -> xpr_t
val size_of_exp_type: cfundeclarations_int -> exp -> xpr_t

val max_size_of_type: cfundeclarations_int -> typ -> xpr_t
val max_size_of_exp_type: cfundeclarations_int -> exp -> xpr_t

val range_of_type: cfundeclarations_int -> typ -> type_range_int

val byte_offset_of_field: cfundeclarations_int -> fieldinfo -> xpr_t

val get_pointer_expr_target_type: cfundeclarations_int -> exp -> typ

val update_type: (string,string) Hashtbl.t -> (int,int) Hashtbl.t -> typ -> typ
