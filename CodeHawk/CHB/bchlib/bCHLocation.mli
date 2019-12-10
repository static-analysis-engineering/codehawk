(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

val make_location:
  ?ctxt:context_t list  (* context: outer context first *)
  -> base_location_t    (* address of inner function, instruction address *)
  -> location_int

(* create a location with the same context but different instruction address *)
val make_i_location:
  location_int          (* original location *)
  -> doubleword_int     (* new instruction address *)
  -> location_int       (* new location, identical to original except for instruction address *)

(* create a location with a new context preprended *)
val make_c_location:
  location_int           (* original location *)
  -> context_t           (* new context to be prepended *)
  -> location_int        (* new location with new context prepended *)

val ctxt_string_to_location:
  doubleword_int      (* outer function address *)
  -> ctxt_iaddress_t  (* string that represents the base location and context *)
  -> location_int

val add_ctxt_to_ctxt_string:
  doubleword_int      (* outer function address *)
  -> ctxt_iaddress_t  (* string thta represents the context, outer context first *)
  -> context_t        (* new context to be prepended *)
  -> ctxt_iaddress_t

val ctxt_string_to_string: ctxt_iaddress_t -> string
val is_iaddress: ctxt_iaddress_t -> bool
val symbol_to_ctxt_string: symbol_t -> ctxt_iaddress_t
val ctxt_string_to_symbol: string -> ?atts:string list -> ctxt_iaddress_t -> symbol_t

