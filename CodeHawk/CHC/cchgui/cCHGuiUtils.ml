(* =============================================================================
   CodeHawk C Analyzer 
   Author: Andrew McGraw
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
open CHPretty

(* chutil *)
open CHPrettyUtil

(* cchlib *)
open CCHUtilities

let callback_print_exn f () =
  try f () with
    | CHCommon.CHFailure s ->
        let _ = pr_debug [ STR "CHCommon.CHFailure ( " ; s ; STR " ) " ; NL ] in
        raise (CHCommon.CHFailure s)
    | CCHUtilities.CCHFailure s ->
        let _ = pr_debug [ STR "CCHUtilities.CCHFAilure ( " ; s ; STR " ) " ; NL ] in
        raise (CCHUtilities.CCHFailure s)
    | CHXmlDocument.XmlDocumentError (line, col, p) ->
        let _ = pr_debug [ STR "XmlDocumentError ( " ; INT line ; STR "," ; INT col ; STR ") " ; p ; NL ] in
        raise (CHXmlDocument.XmlDocumentError(line, col, p))
    | e -> raise e


let percent_to_string n d =
  if d = 0 then "N/A" else
    Printf.sprintf "%3.0f" ((float_of_int n) /. (float_of_int d) *. 100.0)
