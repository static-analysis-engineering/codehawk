(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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

(* bchlib *)
open BCHBCTypes


let get_format_archetype
      (attrs: b_attributes_t) (index: int): BCHLibTypes.formatstring_type_t option =
  List.fold_left (fun acc attr ->
      match acc with
      | Some _ -> acc
      | _ ->
         match attr with
         | Attr (("format" | "chk_format"), params) ->
            (match params with
             | [ACons ("printf", []); AInt fmtrefindex; AInt _]
               | [ACons ("printf", []); AInt fmtrefindex] ->
                if index = fmtrefindex then
                  Some BCHLibTypes.PrintFormat
                else
                  None
             | [ACons ("scanf", []); AInt fmtrefindex; AInt _]
               | [ACons ("scanf", []); AInt fmtrefindex] ->
                if index = fmtrefindex then
                  Some BCHLibTypes.ScanFormat
                else
                  None
             | _ -> None)
         | _ -> None) None attrs
