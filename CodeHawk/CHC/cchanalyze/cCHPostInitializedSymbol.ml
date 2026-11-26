(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
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

(* Encoding (see the .mli for the semantics):
   symbol: base name "post-initialized", attributes
     [callee name; callee vid; call line; argument index;
      return-value variable index; prior-state variable index; condition]
   with condition "tt" (unconditional), "in:<lb>:<ub>" (bounds "inf" when
   absent), or "ne:<c>". *)

(* chlib *)
open CHLanguage
open CHPretty

type condition_t =
  | Always
  | InRange of int option * int option
  | NotEqual of int

type t = {
    pi_callee: string;
    pi_callee_vid: int;
    pi_line: int;
    pi_arg: int;            (* argument index (starting at 1) *)
    pi_rv_index: int;       (* -1 if there is no condition *)
    pi_prior_index: int;    (* -1 if there is no condition *)
    pi_condition: condition_t
  }

let basename = "post-initialized"

let encode_bound = function None -> "inf" | Some i -> string_of_int i

let decode_bound = function "inf" -> None | s -> Some (int_of_string s)

let condition_to_string (c: condition_t) =
  match c with
  | Always -> "tt"
  | InRange (lb, ub) -> "in:" ^ (encode_bound lb) ^ ":" ^ (encode_bound ub)
  | NotEqual c -> "ne:" ^ (string_of_int c)

let condition_from_string (s: string): condition_t option =
  match String.split_on_char ':' s with
  | ["tt"] -> Some Always
  | ["in"; l; u] -> Some (InRange (decode_bound l, decode_bound u))
  | ["ne"; c] -> Some (NotEqual (int_of_string c))
  | _ -> None

let to_symbol (p: t): symbol_t =
  new symbol_t
    ~atts:[p.pi_callee;
           string_of_int p.pi_callee_vid;
           string_of_int p.pi_line;
           string_of_int p.pi_arg;
           string_of_int p.pi_rv_index;
           string_of_int p.pi_prior_index;
           condition_to_string p.pi_condition]
    basename

let is_post_initialized_symbol (s: symbol_t) = s#getBaseName = basename

let from_symbol (s: symbol_t): t option =
  if is_post_initialized_symbol s then
    match s#getAttributes with
    | [callee; vid; line; argix; rvix; priorix; cond] ->
       (try
          (match condition_from_string cond with
           | Some c ->
              Some {
                  pi_callee = callee;
                  pi_callee_vid = int_of_string vid;
                  pi_line = int_of_string line;
                  pi_arg = int_of_string argix;
                  pi_rv_index = int_of_string rvix;
                  pi_prior_index = int_of_string priorix;
                  pi_condition = c }
           | None -> None)
        with Failure _ -> None)
    | _ -> None
  else
    None

(* The success outcome as a condition on the return value, given the error
   postconditions (error discriminator); None if the error outcome cannot
   be expressed (more than one discriminator, or a discriminator that is
   not a comparison of the return value with a constant). *)
let success_condition
      (epcs: CCHLibTypes.xpredicate_t list): condition_t option =
  let open CCHBasicTypes in
  let open CCHLibTypes in
  match epcs with
  | [] -> Some Always
  | [XRelationalExpr (op, ReturnValue, NumConstant n)] ->
     (match (try Some n#toInt with _ -> None) with
      | None -> None
      | Some c ->
         (match op with
          | Lt -> Some (InRange (Some c, None))
          | Le -> Some (InRange (Some (c + 1), None))
          | Gt -> Some (InRange (None, Some c))
          | Ge -> Some (InRange (None, Some (c - 1)))
          | Eq -> Some (NotEqual c)
          | Ne -> Some (InRange (Some c, Some c))
          | _ -> None))
  | _ -> None

(* the postcondition the symbol stands for *)
let postcondition (p: t): CCHLibTypes.xpredicate_t =
  let open CCHLibTypes in
  XInitialized
    (ArgAddressedValue (ArgValue (ParFormal p.pi_arg, ArgNoOffset), ArgNoOffset))

let to_pretty (p: t) =
  LBLOCK [
      STR basename; STR "("; STR p.pi_callee; STR "@";
      INT p.pi_line; STR ", "; STR (condition_to_string p.pi_condition);
      STR ")"]
