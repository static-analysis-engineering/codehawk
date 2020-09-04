(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma

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
open CHLanguage
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHSumTypeSerializer

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSTypes

let mips_fp_format_mfts: mips_fp_format_t mfts_int =
  mk_mfts "mips_format_t"
          [ (FPSingle,"f"); (FPDouble,"d"); (FPFixedWord,"w"); (FPFixedLong,"l");
            (FPPair,"p") ]

class mips_instr_format_mcts_t: [ mips_instr_format_t ] mfts_int =
object

  inherit [ mips_instr_format_t ] mcts_t "mips_instr_format_t"

  method ts (f:mips_instr_format_t) =
    match f with
    | SyscallType _ -> "sc"
    | RSyncType _ -> "rs"
    | RBreakType _ -> "rb"
    | RType _ -> "r"
    | R2Type _ -> "r2"
    | R3Type _ -> "r3"
    | IType _ -> "i"
    | JType _ -> "j"
    | FPMCType _ -> "fpmc"
    | FPRType _ -> "fpr"
    | FPRIType _ -> "fpri"
    | FPCompareType _ -> "fpc"
    | FPICCType _ -> "fpicc"
    | FormatUnknown _ -> "unknown"

  method tags =
    [ "r" ; "i" ; "j" ; "fpmc" ; "fpmc" ; "fpr" ; "fpri" ;  "fpc" ; "fpicc" ;
      "r2" ; "r3"; "rb"; "rs"; "unknown" ]

end

let mips_instr_format_mcts:mips_instr_format_t mfts_int = new mips_instr_format_mcts_t

class mips_opkind_mcts_t: [ mips_operand_kind_t ] mfts_int =
object

  inherit [ mips_operand_kind_t ] mcts_t "mips_operand_kind_t"

  method ts (k:mips_operand_kind_t) =
    match k with
    | MIPSReg _ -> "r"
    | MIPSSpecialReg _ -> "s"
    | MIPSFPReg _ -> "f"
    | MIPSIndReg _ -> "i"
    | MIPSAbsolute _ -> "a"
    | MIPSImmediate _ -> "m"

  method tags = [ "a" ; "f" ; "i" ; "m" ; "r" ; "s" ]

end

let mips_opkind_mcts:mips_operand_kind_t mfts_int = new mips_opkind_mcts_t
