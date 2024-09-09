(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
 * Adapted from the automatically generated machdep file in CIL                   *
 * ============================================================================== *)

module B = Big_int_Z
module H = Hashtbl

(* chlib *)
open CHCommon
open CHLanguage
open CHNumerical
open CHPretty

(* xprlib *)
open Xprt
open XprTypes

(* cchlib *)
open CCHLibTypes

let mkvar s =
  XVar (new variable_t (new symbol_t ~atts:["symsize"] s) NUM_VAR_TYPE)


class type_range_t (lb:numerical_t) (ub:numerical_t):type_range_int =
object
  method min = lb
  method max = ub
end

let typeranges = H.create 7

let addrange (width:int) (signed:bool)  =
  let b_one = B.big_int_of_int 1 in
  let maxm1 = B.power_int_positive_int 2 (width-1) in
  let maxm = B.mult_int_big_int 2 maxm1 in
  let lb =
    if signed then
      new numerical_t (B.minus_big_int maxm1)
    else
      numerical_zero in
  let ub =
    if signed then
      mkNumerical_big (B.sub_big_int maxm1 b_one)
    else
      mkNumerical_big (B.sub_big_int maxm b_one) in
  H.add typeranges (width,signed) (new type_range_t lb ub)


let _ =
  begin
    addrange 1 false;
    addrange 8 false;
    addrange 8 true;
    addrange 16 false;
    addrange 16 true;
    addrange 32 false;
    addrange 32 true;
    addrange 64 false;
    addrange 64 true
  end


let get_type_range (width:int) (signed:bool):type_range_int =
  try
    H.find typeranges (width,signed)
  with
  | Not_found ->
     raise
       (CHFailure
          (LBLOCK [
               STR "No type range found for ";
               STR (if signed then "signed" else "unsigned");
               STR " width of "; INT width]))


let ic1 = int_constant_expr 1
let ic2 = int_constant_expr 2
let ic4 = int_constant_expr 4
let ic8 = int_constant_expr 8
let ic16 = int_constant_expr 16
let ic32 = int_constant_expr 32


let symbolic_sizes = {
  sizeof_short  = mkvar "sizeof_short";
  sizeof_int    = mkvar "sizeof_int";
  sizeof_bool   = mkvar "sizeof_bool";
  sizeof_long   = mkvar "sizeof_long";
  sizeof_int128 = mkvar "sizeof_int128";

  sizeof_longlong = mkvar "sizeof_longlong";
  sizeof_ptr      = mkvar "sizeof_ptr";
  sizeof_enum     = mkvar "sizeof_enum";
  sizeof_float    = mkvar "sizeof_float";
  sizeof_double   = mkvar "sizeof_double";

  sizeof_longdouble = mkvar "sizeof_longdouble";
  sizeof_complex_float = mkvar "sizeof_complex_float";
  sizeof_complex_double = mkvar "sizeof_complex_double";
  sizeof_complex_longdouble = mkvar "sizeof_complex_longdouble";

  sizeof_void       = mkvar "sizeof_void";
  sizeof_fun        = mkvar "sizeof_fun";

  alignof_short     = mkvar "alignof_short";
  alignof_int       = mkvar "alignof_int";
  alignof_bool      = mkvar "alignof_bool";
  alignof_long      = mkvar "alignof_long";
  alignof_int128    = mkvar "alignof_int128";

  alignof_longlong  = mkvar "alignof_longlong";
  alignof_ptr       = mkvar "alignof_ptr";
  alignof_enum      = mkvar "alignof_enum";
  alignof_float     = mkvar "alignof_float";

  alignof_double     = mkvar "alignof_double";
  alignof_longdouble = mkvar "alignof_longdouble";
  alignof_complex_float = mkvar "alignof_complex_float";
  alignof_complex_double = mkvar "alignof_complex_double";
  alignof_complex_longdouble = mkvar "alignof_complex_longdouble";

  alignof_str        = mkvar "alignof_str";
  alignof_fun        = mkvar "alignof_fun";
  alignof_aligned    = mkvar "alignof_aligned"
  }


(* sizes in bytes for linux server, from cil output *)
let linux_64_machine_sizes = {
    sizeof_short  = ic2;
    sizeof_int    = ic4;
    sizeof_bool   = ic1;
    sizeof_long   = ic8;
    sizeof_int128 = ic16;

    sizeof_longlong = ic8;
    sizeof_ptr      = ic8;
    sizeof_enum     = ic4;
    sizeof_float    = ic4;
    sizeof_double   = ic8;
    sizeof_longdouble = ic16;
    sizeof_complex_float = ic8;
    sizeof_complex_double = ic16;
    sizeof_complex_longdouble = ic32;

    sizeof_void       = ic1;
    sizeof_fun        = ic1;

    alignof_short  = ic2;
    alignof_int    = ic4;
    alignof_bool   = ic1;
    alignof_long   = ic8;
    alignof_int128 = ic16;

    alignof_longlong = ic8;
    alignof_ptr      = ic8;
    alignof_enum     = ic4;
    alignof_float    = ic4;
    alignof_double     = ic8;
    alignof_longdouble = ic16;
    alignof_complex_float = ic8;
    alignof_complex_double = ic16;
    alignof_complex_longdouble = ic32;

    alignof_str        = ic1;
    alignof_fun        = ic1;
    alignof_aligned    = ic16
  }


(* sizes in bytes for linux 32 bits, derived from 64 bits *)
let linux_32_machine_sizes = {
    sizeof_short  = ic2;
    sizeof_int    = ic4;
    sizeof_bool   = ic1;
    sizeof_long   = ic4;
    sizeof_int128 = ic16;

    sizeof_longlong = ic8;
    sizeof_ptr      = ic4;
    sizeof_enum     = ic4;
    sizeof_float    = ic4;
    sizeof_double   = ic8;
    sizeof_longdouble = ic8;
    sizeof_complex_float = ic8;
    sizeof_complex_double = ic16;
    sizeof_complex_longdouble = ic16;

    sizeof_void       = ic1;
    sizeof_fun        = ic1;

    alignof_short  = ic2;
    alignof_int    = ic4;
    alignof_bool   = ic1;
    alignof_long   = ic4;
    alignof_int128 = ic16;

    alignof_longlong = ic8;
    alignof_ptr      = ic4;
    alignof_enum     = ic4;
    alignof_float    = ic4;
    alignof_double     = ic8;
    alignof_longdouble = ic8;
    alignof_complex_float = ic8;
    alignof_complex_double = ic16;
    alignof_complex_longdouble = ic16;

    alignof_str        = ic1;
    alignof_fun        = ic1;
    alignof_aligned    = ic8
  }


let linux_16_machine_sizes = {
    sizeof_short  = ic2;
    sizeof_int    = ic2;
    sizeof_bool   = ic1;
    sizeof_long   = ic4;
    sizeof_int128 = ic16;

    sizeof_longlong = ic4;
    sizeof_ptr      = ic2;
    sizeof_enum     = ic2;
    sizeof_float    = ic2;
    sizeof_double   = ic4;
    sizeof_longdouble = ic4;
    sizeof_complex_float = ic4;
    sizeof_complex_double = ic8;
    sizeof_complex_longdouble = ic8;

    sizeof_void       = ic1;
    sizeof_fun        = ic1;

    alignof_short  = ic2;
    alignof_int    = ic2;
    alignof_bool   = ic1;
    alignof_long   = ic4;
    alignof_int128 = ic16;

    alignof_longlong = ic4;
    alignof_ptr      = ic2;
    alignof_enum     = ic2;
    alignof_float    = ic2;
    alignof_double     = ic4;
    alignof_longdouble = ic4;
    alignof_complex_float = ic4;
    alignof_complex_double = ic8;
    alignof_complex_longdouble = ic8;

    alignof_str        = ic1;
    alignof_fun        = ic1;
    alignof_aligned    = ic4
  }


let max_sizes = {        (* sizes in bytes *)
  sizeof_int   = 64;
  sizeof_float = 64;
  sizeof_void  = 64;
  sizeof_ptr   = 64;
  sizeof_fun   = 64;
  sizeof_enum  = 64
  }
