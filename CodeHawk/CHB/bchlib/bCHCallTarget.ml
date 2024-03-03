(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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
open BCHFunctionInterface
open BCHFunctionStub
open BCHLibTypes
open BCHBTerm


let rec call_target_to_pretty (tgt:call_target_t) =
  match tgt with
  | StubTarget s -> LBLOCK [STR "stub:"; function_stub_to_pretty s]
  | StaticStubTarget (dw,s) ->
     LBLOCK [STR "staticstub("; dw#toPretty; STR "):"; function_stub_to_pretty s]
  | AppTarget a -> LBLOCK [STR "app:"; a#toPretty]
  | InlinedAppTarget (a,name) ->
    LBLOCK [STR "app:"; a#toPretty; STR " (inlined:"; STR name ; STR ")"]
  | WrappedTarget (a,_,wtgt,_) ->
     LBLOCK [
         STR "wrapped: ";
         a#toPretty;
         STR " -> ";
         call_target_to_pretty wtgt;
         STR ")"]
  | IndirectTarget (t,tgts) ->
     LBLOCK [
         STR "indirect targets on:";
         (match t with Some t -> bterm_to_pretty t | None -> STR "?");
	 pretty_print_list tgts call_target_to_pretty "{" ", " "}"]
  | VirtualTarget a  ->
     LBLOCK [STR "vrt:"; STR (function_interface_to_prototype_string a)]
  | CallbackTableTarget (dw, offset) ->
     LBLOCK [STR "cbt:"; dw#toPretty; STR "@"; INT offset]
  | UnknownTarget -> LBLOCK [STR "unknown"]
