(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
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

(* tchlib *)
open TCHTestApi


(* Predefined reducers *)

let unit () = []


let bool _ = []


let int (x: int) = [-2; -1; 0; 1; 2; x / 2]


let string (x: string) =
  if x != "" then
    let len = String.length x in
    let len2 = (len + 1) / 2 in
    let s1 = String.sub x 0 len2 in
    let s2 = String.sub x len2 (len - len2) in
    [""; s1; s2]
  else
    []


let list (x: 'a list) =
  match x with
  | head :: tail ->
     let rec split acc (n: int) = function
       | (hd :: tl) as l ->
          if n = 0 then
            [[]; [head]; List.rev acc; tail; l]
          else
            split (hd :: acc) (pred n) tl
       | [] -> [[]; [head]; List.rev acc; tail] in
     split [] (((List.length x) + 1) / 2) x
  | [] -> []
              
