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

type diagnostic_report_t = {
    dr_filename: string ;
    dr_fname: string ;
    dr_isppo: bool ;
    dr_po_id: int ;
    dr_predicate_tag: string ;
    dr_predicate: string ;
    dr_diagnostics: string list
  }

val record_missing_summary : string -> string -> int -> int -> unit

val record_postcondition_request: string -> string -> string -> int -> int -> unit

val report_rfi: diagnostic_report_t -> unit

val report_investigate: diagnostic_report_t -> unit

val display_missing_summaries: unit -> unit

val display_postcondition_requests: unit -> unit

val display_diagnostic_reports: unit -> unit

val display_investigations: unit -> unit
