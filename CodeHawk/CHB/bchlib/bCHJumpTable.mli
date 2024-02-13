(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

val make_jumptable:
  ?end_address: doubleword_int option
  -> start_address:doubleword_int
  -> targets:doubleword_int list
  -> unit
  -> jumptable_int traceresult


val make_indexed_jumptable:
  start_address: doubleword_int
  -> end_address: doubleword_int
  -> indexed_targets: (doubleword_int * int list) list
  -> default_target: doubleword_int
  -> jumptable_int traceresult


val split_jumptable:
  jumptable:jumptable_int
  -> sizes:(int list)
  -> jumptable_int list

val read_xml_jumptable: xml_element_int -> jumptable_int traceresult

val find_jumptables   :
  is_code_address:(doubleword_int -> bool)
  -> read_only_section_strings:(doubleword_int * string) list
  -> jumptable_int list

val create_jumptable:
  base:doubleword_int
  -> section_base:doubleword_int
  -> is_code_address:(doubleword_int -> bool)
  -> section_string:string -> jumptable_int option
