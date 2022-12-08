(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes

(* bchlibpe *)
open BCHLibPETypes

module H = Hashtbl
module TR = CHTraceResult


class string_table_t:string_table_int  =
object (self)
  val table = H.create 23

  method reset = H.clear table

  method add (dw:doubleword_int) (s:string)  = 
    if H.mem table dw#index then () else H.add table dw#index s

  method has (dw:doubleword_int) = H.mem table dw#index

  method get (dw:doubleword_int) =
    if self#has dw then
      H.find table dw#index
    else
      begin
	ch_error_log#add "invocation error"
	  (LBLOCK [
               STR "Address ";
               dw#toPretty;
               STR " could not be found in string_table"]);
	raise (Invocation_error "string_table_t#get")
      end

  method get_strings = 
    H.fold (fun k v a -> (TR.tget_ok (index_to_doubleword k), v) :: a) table []

  method toPretty =
    H.fold (fun k v a ->
        LBLOCK [
            a;
            NL;
            STR (TR.tget_ok (index_to_doubleword k))#to_fixed_length_hex_string;
            STR "  ";
            STR v])
      table (STR "")
    
end


let string_table = new string_table_t
let wide_string_table = new string_table_t
