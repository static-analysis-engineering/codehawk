(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma

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

(* cchlib *)
open CCHBasicTypes
open CCHUtilities

module B = Big_int_Z


let zero = Const (CInt (Int64.zero, IInt, None))

let unknown_location = {file = "unknown"; line = (-1); byte = (-1)}

let call_sink = {file = "callsink"; line = (-1); byte = (-1)}

let mk_int_constant i = CInt (Int64.of_int i, IInt, None)

let mk_disequality e1 e2 = BinOp (Ne, e1, e2, TInt (IChar, []))

let mk_equality e1 e2 = BinOp (Eq, e1, e2, TInt (IChar, []))

let mk_logical_and e1 e2 = BinOp (LAnd, e1, e2, TInt (IChar, []))


let exp_is_zero (x:exp) =
  match x with
  | Const (CInt (i64, _, _)) ->
     B.eq_big_int (B.big_int_of_int64 i64) B.zero_big_int
  | _ -> false


let char_const_to_int (c: char) : constant =
  let c' = Char.code c in
  let value =
    if c' < 128  then
      Int64.of_int c'
    else
      Int64.of_int (c' - 256) in
  CInt(value, IInt, None)


let char_const_to_big c =
  match char_const_to_int c with
  | CInt (i64, _, _) -> B.big_int_of_int64 i64
  | _ ->
     raise
       (CCHFailure
	  (LBLOCK [ STR "Unable to parse char constant "; STR "CChr " ]))


let mk_location_string (loc:location) =
  loc.file ^ "_" ^ (string_of_int loc.line) ^ "_" ^ (string_of_int loc.byte)
