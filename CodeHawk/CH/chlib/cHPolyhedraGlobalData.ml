(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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

class global_data_t maxnbdims maxnbrows =
  let dec = 2 in
    (* Strict inequalities are not implemented *)
  let maxcolumns = dec + maxnbdims in
object
  
  val _strict: bool = false (* Strict inequalities are not implemented *)
    
  val _dec: int = dec
    
  val _maxnbdims: int = maxnbdims
    
  val _maxnbrows: int = maxnbrows

  val _maxcolumns: int = maxcolumns

  val _cst = 1
    
    
  method strict = _strict

  method dec = _dec

  method maxnbdims = _maxnbdims

  method maxnbrows = _maxnbrows

  method maxcolumns = _maxcolumns

  method cst = _cst
    
end

let pGD: global_data_t ref = ref (new global_data_t 20 10000)

let is_some v =
  match v with
    | Some _ -> true
    | None -> false

let is_none v = not(is_some v)

type tbool_t =
  | Tbool_bottom
  | Tbool_true
  | Tbool_false
  | Tbool_top

