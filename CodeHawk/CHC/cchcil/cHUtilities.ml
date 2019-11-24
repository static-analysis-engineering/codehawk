(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
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

open Cil
open CHPrettyPrint

exception CCFailure of pretty_t

(* Return the suffix of s that starts at the n'th character of s *)
let string_suffix (s:string) (n:int):string = 
  try
    String.sub s n ((String.length s) - n)
  with
    Invalid_argument _ ->
    let len = String.length s in
    let msg = "String.sub s " ^ (string_of_int n)
              ^ " on string of length " ^ (string_of_int len) in
    raise (Invalid_argument msg)
    
    
let string_starts_with (s:string) (p:string) =
  let slen = String.length s in
  let plen = String.length p in
  if slen < plen then
    false
  else
    (String.sub s 0 plen) = p
  
(* Replace character c with string r in string s *)
let rec string_replace (c:char) (r:string) (s:string):string =
  try
    let i = String.index s c in
    let prefix = String.sub s 0 i in
    let suffix = string_replace c r (String.sub s (i+1) ((String.length s) - i -1)) in
    prefix ^ r ^ suffix
  with Not_found -> s
                  
(* Replace substring o with string r in string s *)
let rec string_replace_string (o:string) (r:string) (s:string) =
  if (String.length s) < (String.length o) then
    s
  else if string_starts_with s o then
    r ^ (string_replace_string o r (string_suffix s (String.length o)))
  else
    (String.sub s 0 1) ^ (string_replace_string o r (string_suffix s 1))
  
(* Returns a list of strings that form the components separated by the separator;
   without the separator itself included *)
let string_nsplit (separator:char) (s:string):string list =
  let result = ref [] in
  let len = String.length s in
  let start = ref 0 in
  begin
    while !start < len do
      let s_index = try String.index_from s !start separator with Not_found -> len in
      let substring = String.sub s !start (s_index - !start) in
      begin
	result := substring :: !result ;
	start := s_index + 1
      end 
    done;
    List.rev !result
  end
  
  
