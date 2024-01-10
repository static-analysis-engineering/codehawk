(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs, LLC

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

(* bchlibpower32 *)
open BCHPowerTypes


let pwr_itype_mfts: pwr_instruction_type_t mfts_int =
  mk_mfts
    "pwr_instruction_type_t"
    [(PWR, "p"); (VLE16, "v"); (VLE32, "w")]


class pwr_opkind_mcts_t: [pwr_operand_kind_t] mfts_int =
object

  inherit [pwr_operand_kind_t] mcts_t "pwr_oeprand_kind_t"

  method! ts (k: pwr_operand_kind_t) =
    match k with
    | PowerGPReg _ -> "g"
    | PowerSpecialReg _ -> "s"
    | PowerRegisterField _ -> "f"
    | PowerConditionRegisterBit _ -> "c"
    | PowerImmediate _ -> "i"
    | PowerAbsolute _ -> "a"
    | PowerIndReg _ -> "ir"
    | PowerIndexedIndReg _ -> "xr"

  method! tags = ["a"; "c"; "f"; "g"; "i"; "ir"; "s"; "xr"]

end

let pwr_opkind_mcts: pwr_operand_kind_t mfts_int = new pwr_opkind_mcts_t


class pwr_branch_prediction_mcts_t: [pwr_branch_prediction_t] mfts_int =
object

  inherit [pwr_branch_prediction_t] mcts_t "pwr_branch_prediction_t"

  method! ts (p: pwr_branch_prediction_t) =
    match p with
    | BPNone -> "n"
    | BPPlus _ -> "p"
    | BPMinus _ -> "m"

  method! tags = ["m"; "n"; "p"]

end

let pwr_branch_prediction_mcts: pwr_branch_prediction_t mfts_int =
  new pwr_branch_prediction_mcts_t
