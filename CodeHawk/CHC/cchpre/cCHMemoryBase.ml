(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* cchpre *)
open CCHPreTypes


let memory_base_compare (b1:memory_base_t) (b2:memory_base_t) =
  match (b1,b2) with
  | (CNull i1, CNull i2) -> Stdlib.compare i1 i2
  | (CNull _, _) -> -1
  | (_,  CNull _) -> 1
  | (CStringLiteral i1, CStringLiteral i2) -> Stdlib.compare i1 i2
  | (CStringLiteral _, _) -> -1
  | (_, CStringLiteral _) -> 1
  | (CStackAddress v1, CStackAddress v2) ->
     Stdlib.compare v1#getName#getSeqNumber v2#getName#getSeqNumber
  | (CStackAddress _, _) -> -1
  | (_, CStackAddress _) -> 1
  | (CGlobalAddress v1, CGlobalAddress v2) ->
     Stdlib.compare v1#getName#getSeqNumber v2#getName#getSeqNumber
  | (CGlobalAddress _, _) -> -1
  | (_, CGlobalAddress _) -> 1
  | (CBaseVar v1, CBaseVar v2) ->
     Stdlib.compare v1#getName#getSeqNumber v2#getName#getSeqNumber
  | (CBaseVar _,_) -> -1
  | (_, CBaseVar _) -> 1
  | (CUninterpreted s1, CUninterpreted s2) -> Stdlib.compare s1 s2


let memory_base_to_string (b:memory_base_t) =
  match b with
  | CNull i -> "NULL(" ^ (string_of_int i) ^ ")"
  | CStringLiteral s ->
     "addrof-" ^ (string_of_int (String.length s)) ^ "-char-string"
  | CStackAddress v ->
     "addrof_localvar_"
     ^ v#getName#getBaseName
     ^ "_"
     ^ (string_of_int v#getName#getSeqNumber)
  | CGlobalAddress v -> "addrof_globalvar_" ^ v#getName#getBaseName
  | CBaseVar v -> "addr_in_" ^ v#getName#getBaseName
  | CUninterpreted s -> "uninterpreted_" ^ s


let memory_base_to_pretty (b:memory_base_t) = STR (memory_base_to_string b)
