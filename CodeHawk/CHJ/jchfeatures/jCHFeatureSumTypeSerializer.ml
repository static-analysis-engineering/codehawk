(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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

(* chutil *)
open CHSumTypeSerializer

(* jchfeatures *)
open JCHFeaturesAPI


class fxpr_mcts_t:[fxpr_t] mfts_int =
object

  inherit [fxpr_t] mcts_t "fxpr_t"

  method! ts (x:fxpr_t) =
    match x with
    | FXVar _ -> "v"
    | FXField _ -> "f"
    | FXArrayElem _ -> "a"
    | FXConst _ -> "c"
    | FXOp _ -> "x"
    | FXFunctionCall _ -> "fc"
    | FXAttr _ -> "s"
    | FXMultiple _ -> "m"
    | FXException -> "e"
    | FXNull -> "n"
    | FXUnknown -> "u"

end

let fxpr_mcts:fxpr_t mfts_int =  new fxpr_mcts_t


class fxfeature_mcts_t:[fxfeature_t] mfts_int =
object

  inherit [fxfeature_t] mcts_t "fxfeature_t"

  method! ts (f:fxfeature_t) =
    match f with
    | FXCondition _ -> "c"
    | FXAssignment _ -> "a"
    | FXProcedureCall _ -> "p"
    | FXReturn _ -> "r"
    | FXThrow _ -> "t"

  method! tags = ["a"; "c"; "p"; "r"; "t"]

end

let fxfeature_mcts:fxfeature_t mfts_int = new fxfeature_mcts_t
