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

module U = TCHUtils

exception Failed of failure_t


let fail (x: string) (y: string) (z: string) =
  let f = {expected_value = x; actual_value = y; fmessage = z} in
  raise (Failed f)


let fail_msg = fail "" ""


let default_printer _ = ""


let equal ?(eq=(=)) ?(prn=default_printer) ?(msg="") (x: 'a) (y: 'a) =
  if not (eq x y) then fail (prn x) (prn y) msg


let not_equal ?(eq=(=)) ?(prn=default_printer) ?(msg="") (x: 'a) (y: 'a) =
  if (eq x y) then fail (prn x) (prn y) msg


let same ?(prn=default_printer) ?(msg="") (x: 'a) (y: 'a) =
  if not (x == y) then fail (prn x) (prn y) msg


let not_same ?(prn=default_printer) ?(msg="") (x: 'a) (y: 'a) =
  if x == y then fail (prn x) (prn y) msg


let make_equal (eq: 'a -> 'a -> bool) (prn: 'a -> string) = equal ~eq ~prn


let make_equal_list
      (eq: 'a -> 'a -> bool)
      (prn: 'a -> string)
      ?(msg="")
      (x: 'a list)
      (y: 'a list) =
  let rec iter i x y =
    match (x, y) with
    | (hd_x :: tl_x, hd_y :: tl_y) ->
       if eq hd_x hd_y then
         iter (succ i) tl_x tl_y
       else
         let fm = Printf.sprintf "%s (at index %d)" msg i in
         fail (prn hd_x) (prn hd_y) fm
    | (_ :: _, [])
      | ([], _ :: _) ->
       let fm = Printf.sprintf "%s (lists of different sizes)" msg in
       fail_msg fm
    | ([], []) -> () in
  iter 0 x y


let equal_string = make_equal (=) U.string_of_string


let raises ?(msg="") (f: unit -> 'a) =
  let exn = try begin ignore (f ()); false end with _ -> true in
  if not exn then fail "any exception" "no exception" msg
