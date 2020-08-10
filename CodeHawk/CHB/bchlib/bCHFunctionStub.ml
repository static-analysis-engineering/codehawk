(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma

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
open BCHLibTypes
open BCHUtilities

module P = Pervasives

let function_stub_to_string (s:function_stub_t) =
  match s with
  | SOFunction name -> name
  | DllFunction (dll,name) -> "(" ^ dll ^ ":" ^ name ^ ")"
  | JniFunction i -> "jni(" ^ (string_of_int i) ^ ")"
  | LinuxSyscallFunction i -> "linux_syscall(" ^ (string_of_int i) ^ ")"
  | PckFunction (lib,pckgs,name) ->
     "(" ^ lib ^ ":" ^  (String.concat "::" pckgs)  ^ ":" ^ name

let function_stub_to_pretty (s:function_stub_t) =
  match s with
  | SOFunction name -> STR name
  | DllFunction (dll,name) ->
     LBLOCK [ STR "(" ; STR  dll ; STR ":" ;  STR name ; STR ")" ]
  | JniFunction i -> LBLOCK [ STR "jni(" ; INT i ; STR ")" ]
  | LinuxSyscallFunction i ->
     LBLOCK [ STR "linux_syscall(" ; INT i ; STR ")" ]
  | PckFunction (lib,pckgs,name) ->
    LBLOCK [ STR "lib:" ; STR lib ; STR ":" ;
	     pretty_print_list pckgs (fun s -> STR s) "" "::" "" ; STR name ;
	     STR " (static)" ]

let function_stub_compare (s1:function_stub_t)  (s2:function_stub_t) =
  match (s1,s2) with
  | (SOFunction n1, SOFunction n2) -> P.compare n1 n2
  | (SOFunction _, _) -> -1
  | (_, SOFunction _) -> 1
  | (DllFunction (l1,n1), DllFunction (l2,n2)) ->
     let l0 = P.compare l1 l2 in if l0 = 0 then P.compare n1 n2 else l0
  | (DllFunction _, _) -> -1
  | (_, DllFunction _) -> 1
  | (JniFunction i1, JniFunction i2) -> P.compare i1 i2
  | (JniFunction _, _) -> -1
  | (_, JniFunction _) -> 1
  | (LinuxSyscallFunction i1, LinuxSyscallFunction i2) -> P.compare i1 i2
  | (LinuxSyscallFunction _, _) -> -1
  | (_, LinuxSyscallFunction _) -> 1
  | (PckFunction (lib1,p1,n1),PckFunction (lib2,p2,n2)) ->
     let l0 = P.compare lib1 lib2 in
     if l0 = 0 then
       let l1 = list_compare p1 p2 P.compare in
       if l1 = 0 then P.compare n1 n2
       else l1
     else l0
