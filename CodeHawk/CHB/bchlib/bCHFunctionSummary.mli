(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


(** Function summary containing signature, semantics, and documentation.

    These summaries are used both for library functions and application
    functions. They can originate from:
    - the function summaries in bchsummaries (in xml),
    - constructed from a function prototype read in via a c file,
    - created by the function-info based on analysis results.
 *)


(** [make_function_summary fintf sem doc] returns a function summary with
    function signature [fintf], function semantics [sem] and function
    documentation [doc].*)
val make_function_summary:
  fintf:function_interface_t
  -> sem:function_semantics_t
  -> doc:function_documentation_t
  -> function_summary_int


(** [function_summary_of_bvarinfo vinfo] returns a function summary from
    a function prototype [vinfo] (typically read in from a c file), with
    default (empty) semantics and default (empty) documentation.*)
val function_summary_of_bvarinfo: bvarinfo_t -> function_summary_int


(** Returns an empty documentation data structure.*)
val default_function_documentation: function_documentation_t


(** [default_summary name] returns a function summary with signature
    [name()], empty semantics, and empty documentation.*)
val default_summary: string -> function_summary_int


(** [function_summary_add_stack_adjustment fsum adj] returns a function summary
    that is identical to [fsum] except for the stack adjustment and calling
    convention in the function type signature, which are set to [adj] and
    'stdcall', respectively.*)
val function_summary_add_stack_adjustment:
  function_summary_int -> int -> function_summary_int


(** [read_xml_function_summary xnode] constructs a function summary from
    its xml reprsentation in [xnode].*)
val read_xml_function_summary: xml_element_int -> function_summary_int
