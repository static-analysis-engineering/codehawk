(* =============================================================================
   CodeHawk C Analyzer
   Author: Alexander Bakst
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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

(* chlib*)
open CHLanguage
open CHPretty

type t =
  | True 
  | Unknown
  | VarInt of (int * int option * int option) (* vid; val *)
  | VarNull of int

let unknown_cstr = "unkown"
let null_var_cstr = "null-var"
let var_int_cstr = "var-int"
let true_cstr = "tt"
let encode_bound = function
| None -> "inf"
| Some i -> string_of_int i

let decode_bound = function
| "inf" -> None
| s -> Some(int_of_string s)

let from_symbol (sym: symbol_t): t option =
  match sym#getSymbol with
  | [s] ->
    begin 
      match String.split_on_char ':' s with
      | [k; v] when k = null_var_cstr -> Some (VarNull (int_of_string v))
      | [k; v; l; u] when k = var_int_cstr -> 
        let lb = decode_bound l in
        let ub = decode_bound u in
        Some (VarInt (int_of_string v, lb, ub))
      | [k] when k = true_cstr -> Some True
      | [k] when k = unknown_cstr -> Some Unknown
      | _ -> None (* these should throw*)
    end
  | _ -> None

let to_symbol: t -> symbol_t = function
  | True -> new symbol_t true_cstr
  | VarNull i -> new symbol_t (null_var_cstr ^ ":" ^ string_of_int i)
  | VarInt (v, l, u) -> 
    let lb = encode_bound l in
    let ub = encode_bound u in
    new symbol_t (var_int_cstr ^ ":" ^ string_of_int v ^ ":" ^ lb ^ ":" ^ ub)
  | Unknown -> new symbol_t unknown_cstr

let to_pretty = function
| Unknown -> STR "?"
| True -> STR "T"
| VarNull i -> LBLOCK [ STR "Null("; INT i; STR ")" ]
| VarInt (v, l, u) -> 
  LBLOCK [ STR "VarRange("; INT v; STR ", "; STR (encode_bound l); STR ", "; STR (encode_bound u);  STR ")"]
