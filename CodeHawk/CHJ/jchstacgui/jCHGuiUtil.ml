(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* jchpre *)
open JCHPreAPI

let get_variable_name (mInfo:method_info_int) (pc:int) (v:variable_t) =
  let get_register_index (v: variable_t) = 
    let name = v#getName#getBaseName in
    if name.[0] = 'r' && name.[1] <> 'e' then 
      int_of_string (Str.string_after name 1)
    else -1 in
  let is_loop_counter v = 
      let vname = v#getName#getBaseName in
      String.length vname > 2 && vname.[0] == 'l' && vname.[1] = 'c'  in
  if is_loop_counter v then
    "loopcounter_"
    ^ v#getName#getBaseName
    ^ "_"
    ^ (string_of_int v#getName#getSeqNumber)
  else if mInfo#has_local_variable_table then
      let index = get_register_index v in
      if index = (-1) then
	v#getName#getBaseName
      else
	if mInfo#has_local_variable_name index pc then
	  mInfo#get_local_variable_name index pc
	else
	  v#getName#getBaseName
  else
    v#getName#getBaseName

