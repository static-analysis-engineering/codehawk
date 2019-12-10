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
open CHLogger
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open Xprt
open XprXml

(* bchlib *)
open BCHApiParameter
open BCHBTerm
open BCHDoubleword
open BCHFunctionApi
open BCHFunctionStub
open BCHLibTypes
open BCHBTerm
open BCHUtilities
open BCHXmlUtil

module P = Pervasives

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

(* ----------------------------------------------------------------- printing *)

let rec call_target_to_pretty (tgt:call_target_t) =
  match tgt with
  | StubTarget s -> LBLOCK [ STR "stub:" ; function_stub_to_pretty s ]
  | StaticStubTarget (dw,s) ->
     LBLOCK [ STR "staticstub(" ; dw#toPretty ; STR "):" ; function_stub_to_pretty s ]
  | AppTarget a -> LBLOCK [ STR "app:" ; a#toPretty ]
  | InlinedAppTarget (a,name) ->
    LBLOCK [ STR "app:" ; a#toPretty ; STR " (inlined:" ; STR name ; STR ")" ]
  | WrappedTarget (a,_,wtgt,_) ->
    LBLOCK [ STR "wrapped: " ; a#toPretty ; STR " -> " ; 
	     call_target_to_pretty wtgt; STR ")" ]
  | IndirectTarget (t,tgts) ->
    LBLOCK [ STR "indirect targets on:" ; bterm_to_pretty t ;
	     pretty_print_list tgts call_target_to_pretty "{" ", " "}" ]
  | VirtualTarget a  -> LBLOCK [ STR "vrt:" ; STR (function_api_to_prototype_string a) ]
  | UnknownTarget -> LBLOCK [ STR "unknown" ]


(* --------------------------------------------------------------- comparison *)

let rec call_target_compare (t1:call_target_t) (t2:call_target_t) =
  match (t1,t2) with
  | (StubTarget t1, StubTarget t2) -> function_stub_compare t1 t2
  | (StubTarget _, _) -> -1
  | (_, StubTarget _) -> 1
  | (StaticStubTarget (a1,t1), StaticStubTarget (a2,t2)) ->
     let l0 = a1#compare a2 in if l0 = 0 then function_stub_compare t1 t2 else l0
  | (StaticStubTarget _, _) -> -1
  | (_, StaticStubTarget _) -> 1
  | (AppTarget a1,AppTarget a2) -> a1#compare a2
  | (AppTarget _, _) -> -1
  | (_, AppTarget _) -> 1
  | (InlinedAppTarget (a1,_),InlinedAppTarget (a2,_)) -> a1#compare a2
  | (InlinedAppTarget _,_) -> -1
  | (_, InlinedAppTarget _) -> 1
  | (WrappedTarget (a1,fapi1,tgt1,_),WrappedTarget (a2,fapi2,tgt2,_)) -> 
    let l1 = a1#compare a2 in
    if l1 = 0 then 
      let l2 = function_api_compare fapi1 fapi2 in
      if l2 = 0 then call_target_compare tgt1 tgt2
      else l2
    else l1
  | (WrappedTarget _, _) -> -1
  | (_, WrappedTarget _) -> 1
  | (VirtualTarget a1, VirtualTarget a2) -> function_api_compare a1 a2
  | (VirtualTarget _, _) -> -1
  | (_, VirtualTarget _) -> 1
  | (IndirectTarget (t1,tl1), IndirectTarget (t2,tl2)) ->
    let l1 = bterm_compare t1 t2 in
    if l1 = 0 then list_compare tl1 tl2 call_target_compare else l1
  | (IndirectTarget _, _) -> -1
  | (_, IndirectTarget _) -> 1
  | (UnknownTarget, UnknownTarget) -> 0


