(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHPretty

(* bchlib *)
open BCHBCTypes


val attributes_to_string: b_attributes_t -> string

val b_attrparam_to_string: b_attrparam_t -> string

val location_line_to_string: b_location_t -> string

val storage_to_string: bstorage_t -> string

val location_to_pretty: b_location_t -> pretty_t

val float_representation_to_string: frepresentation_t -> string

val int_type_to_string: ikind_t -> string

val float_type_to_string: fkind_t -> string

val btype_to_string: btype_t -> string

val tname_to_string: tname_t -> string

val btype_to_pretty: btype_t -> pretty_t

val exp_to_string: bexp_t -> string

val compinfo_to_pretty: bcompinfo_t -> pretty_t

val enuminfo_to_pretty: benuminfo_t -> pretty_t

val varinfo_to_pretty: bvarinfo_t -> pretty_t

val fieldinfo_to_pretty: bfieldinfo_t -> pretty_t

val offset_to_pretty: boffset_t -> pretty_t

val instr_to_pretty: binstr_t -> pretty_t
