(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(** Serialization of sum types *)

(* chlib *)
open CHCommon

(* chutil *)
open CHPrettyUtil
open CHSumTypeSerializer

(* xprlib *)
open XprTypes

   
let xop_mfts:xop_t mfts_int  =
  mk_fn_mfts
    "xop_t"
    [(XNeg, "neg");
     (XBNot, "bnot");
     (XLNot, "lnot");
     (XPlus, "plus");
     (XMinus, "minus");
     (XMult, "mult");
     (XDiv, "div");
     (XMod, "mod");
     (XPow, "pow");
     (XShiftlt, "shiftlt");
     (XShiftrt, "shiftrt");
     (XLsr, "lsr");
     (XAsr, "asr");
     (XLsl, "lsl");
     (XLt, "lt");
     (XGt, "gt");
     (XLe, "le");
     (XGe, "ge");
     (XEq, "eq");
     (XNe, "ne");
     (XSubset, "subset");
     (XDisjoint, "disjoint");
     (XBAnd, "band");
     (XBXor,"bxor");
     (XBOr, "bor");
     (XBNor, "bnor");
     (XLAnd, "land");
     (XLOr, "lor");
     (XXlsb, "lsb");
     (XXlsh, "lsh");
     (XXbyte, "xbyte");
     (XNumJoin, "numjoin");
     (XNumRange, "range")]
    (fun x ->
      match x with
      | Xf f -> "xf_" ^ f
      | _ ->
         raise
           (CHFailure
              (LBLOCK [
                   STR "internal error in xop_t sumtype";
                   STR " serializer"])))
    (fun s ->
      match (nsplit '_' s) with
      | ["xf"; f] -> Xf f
      | _ ->
         raise
           (CHFailure
              (LBLOCK [
                   STR "String ";
                   STR s;
                   STR " not recognized as a valid xop_t type"])))


class xcst_mcts: [xcst_t] mfts_int =
object

  inherit [xcst_t] mcts_t "xcst_t"  

  method! ts (c:xcst_t) =
    match c with
    | SymSet _ -> "ss"
    | IntConst _ -> "ic"
    | BoolConst _ -> "bc"
    | XRandom -> "r"
    | XUnknownInt -> "ui" 
    | XUnknownSet -> "us"

  method! tags = [ "bc"; "ic"; "r"; "ss"; "ui"; "us" ]

end


let xcst_mcts = new xcst_mcts


class xpr_mcts_t: [xpr_t] mfts_int =
object

  inherit [xpr_t] mcts_t "xpr_t"

  method! ts (x:xpr_t) =
    match x with
    | XVar _ -> "v"
    | XConst _ -> "c"
    | XOp _ -> "x"
    | XAttr _ -> "a"

  method! tags = [ "a"; "c"; "v"; "x" ]

end
                             
let xpr_mcts = new xpr_mcts_t  
