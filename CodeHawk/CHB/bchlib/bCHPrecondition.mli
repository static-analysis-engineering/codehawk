(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes


(** Function precondition on the function interface *)

(** {1 Xml reading/writing}*)

(** [read_xml_par_preconditions node thisf] returns the precondition
    predicates that are encoded in the xml node [node] for the function
    identified with [thisf]*)
val read_xml_par_preconditions:
  xml_element_int -> bterm_t -> fts_parameter_t list -> xxpredicate_t list


(** [read_xml_precondition_xxpredicate node thisf pars] returns the
    precondition predicates that are encoded in the xml node [node] for
    the function identified with [thisf] and parameters [pars].*)
val read_xml_precondition_xxpredicate:
  xml_element_int -> bterm_t -> fts_parameter_t list -> xxpredicate_t list


val read_xml_precondition:
  xml_element_int -> bterm_t -> fts_parameter_t list -> xxpredicate_t list


val read_xml_preconditions:
  xml_element_int -> bterm_t -> fts_parameter_t list -> xxpredicate_t list
