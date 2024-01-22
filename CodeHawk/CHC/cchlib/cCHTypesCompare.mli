(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* cchlib *)
open CCHBasicTypes


val list_compare: 'a list -> 'b list -> ('a -> 'b -> int) -> int

val pair_compare:
  ('a * 'b) -> ('a * 'b) -> ('a -> 'a -> int) -> ('b -> 'b -> int) -> int

val triple_compare:
  ('a * 'b * 'c)
  -> ('a * 'b * 'c)
  -> ('a -> 'a -> int)
  -> ('b -> 'b -> int)
  -> ('c -> 'c -> int)
  -> int

val location_compare: location -> location -> int

val offset_compare: offset -> offset -> int

val varuse_compare: varuse -> varuse -> int

val fielduse_compare: fielduse -> fielduse -> int

val constant_compare: constant -> constant -> int

val typ_compare :
  ?ctable:(int,int)Hashtbl.t -> ?constr:(int,int)Hashtbl.t -> typ -> typ -> int

val exp_compare : exp -> exp -> int

val lval_compare: lval -> lval -> int

val enuminfo_structural_compare: enuminfo -> enuminfo -> int

val compinfo_structural_compare:
  (int,int) Hashtbl.t  -> compinfo -> compinfo -> (int * (int,int) Hashtbl.t)

val compinfo_compare: compinfo -> compinfo -> int

val varinfo_compare: varinfo -> varinfo -> int
