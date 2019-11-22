(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Anca Browne
   -----------------------------------------------------------------------------
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
  ============================================================================== *)

(* chlib *)
open CHPretty

type external_value_exchange_format_t =
  | EVX_STRING of string
  | EVX_LIST of external_value_exchange_format_t list
              
let rec evx_to_pretty evx =
  match evx with
  | EVX_STRING s -> STR s
  | EVX_LIST l -> pretty_print_list l evx_to_pretty "[" "; " "]"
                
class type external_value_int =
  object ('a)
       
    method kind: string
    method marshal: external_value_exchange_format_t
    method isTop: bool
    method isBottom: bool
    method leq: 'a -> bool
    method equal: 'a -> bool
    method join: 'a -> 'a
    method meet: 'a -> 'a
    method widening: 'a -> 'a
    method narrowing: 'a -> 'a
    method toPretty: pretty_t
         
  end
  
