(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023  Aarno Labs, LLC

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

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHFunctionData
open BCHLibTypes
open BCHSystemInfo

(* bchpower32 *)
open BCHPowerTypes

(* Reference: NXP-VLEPEM *)


class type ['a] opcode_formatter_int =
  object
    method ops: string -> pwr_operand_int list -> 'a
    method int_ops: string -> int list -> 'a
    method no_ops: string -> 'a
    method ops_bc: string -> pwr_operand_int -> pwr_operand_int list -> 'a
    method conditional_branch:
             pwr_instruction_type_t -> int -> int -> pwr_operand_int -> 'a
    method enable: string -> bool -> 'a
  end


type 'a opcode_record_t ={
    mnemonic: string;
    operands: pwr_operand_int list;
    ida_asm: 'a
  }


let mnemonic_oe_rc (s: string) (oe: bool) (rc: bool): string =
  match (oe, rc) with
  | (false, false) -> s
  | (false, true) -> s ^ "."
  | (true, false) -> s ^ "o"
  | (true, true) -> s ^ "o."


let mnemonic_bp (s: string) (bp: pwr_branch_prediction_t) =
  match bp with
  | BPNone -> s
  | BPPlus _ -> s ^ "+"
  | BPMinus _ -> s ^ "-"


let mnemonic_bpp (s: string) (bph: bool) (bpt: bool): string =
  match (bph, bpt) with
  | (false, false) -> s
  | (false, true) -> s ^ "+"
  | (true, false) -> s ^ "-"
  | (true, true) -> s ^ "+"


let get_record (opc: pwr_opcode_t) =
  match opc with
  | Add (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "add" oe rc
       | VLE16 -> "se_add"
       | _ -> "xxxx_add" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; so; ov];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [rd; rb]
         | _ -> f#ops mnemonic [rd; ra; rb])
     }

  | AddCarrying (pit, rc, oe, rd, ra, rb, cr, so, ov, ca) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "addc" oe rc
       | _ -> "xxxx_addc" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; so; ov; ca];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | AddExtended (pit, rc, oe, rd, ra, rb, cr, so, ov, ca) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "adde" oe rc
       | _ -> "xxxx_adde" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; so; ov; ca];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | AddImmediate (pit, s, op2, op16, rc, rd, ra, simm, cr) ->
     let mnemonic = match pit with
       | PWR -> "addi"
       | VLE16 -> "se_addi"
       | VLE32 ->
          (match (s, op2, op16, rc) with
           | (false, false, true, false) -> "e_add16i"
           | (false, true, false, true) -> "e_add2i."
           | (true, true, false, false) -> "e_add2is"
           | (false, false, false, false) -> "e_addi"
           | (false, false, false, true) -> "e_addi."
           | _ -> "xxxx_addi") in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; simm; cr];
       ida_asm = (fun f ->
         match pit with
         | PWR -> f#ops mnemonic [rd; ra; simm]
         | VLE16 -> f#ops mnemonic [rd; simm]
         | VLE32 ->
            if op2 then
              f#ops mnemonic [rd; simm]
            else
              f#ops mnemonic [rd; ra; simm])
     }

  | AddImmediateCarrying (pit, rc, rd, ra, simm, cr, ca) ->
     let mnemonic = match pit with
       | PWR -> if rc then "addic." else "addic"
       | VLE32 -> if rc then "e_addic." else "e_addic"
       | _ -> "xxxx_addic" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; simm; cr; ca];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; simm])
     }

  | AddMinusOneExtended (pit, rc, oe, rd, ra, cr, ca, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "addme" oe rc
       | _ -> "xxxx_addme" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; cr; ca; so; ov];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra])
     }

  | AddZeroExtended (pit, rc, oe, rd, ra, cr, ca, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "addze" oe rc
       | _ -> "xxxx_addze" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; cr; ca; so; ov];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra])
     }

  | And (pit, rc, ra, rs, rb, cr) ->
     let mnemonic = match pit with
       | VLE16 -> if rc then "se_and." else "se_and"
       | PWR -> if rc then "and." else "and"
       | _ -> "xxxx_and" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra; rb]
         | _ -> f#ops mnemonic [ra; rs; rb])
     }

  | AndComplement (pit, rc, ra, rs, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "andc." else "andc"
       | VLE16 -> "se_andc"
       | _ -> "xxxx_andc" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra; rb]
         | _ -> f#ops mnemonic [ra; rs; rb])
     }

  | AndImmediate (pit, shifted, op2, rc, ra, rs, uimm, cr) ->
     let mnemonic = match pit with
       | PWR -> if shifted then "andis." else "andi."
       | VLE16 -> "se_andi"
       | VLE32 when op2 && rc -> if shifted then "e_and2is." else "e_and2i."
       | VLE32 when op2 -> if shifted then "e_and2is" else "e_and2i"
       | VLE32 -> if rc then "e_andi." else "e_andi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; uimm; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra; uimm]
         | VLE32 when op2 -> f#ops mnemonic [ra; uimm]
         | _ -> f#ops mnemonic [ra; rs; uimm])
     }

  | BitClearImmediate (pit, rx, ui5) ->
     let mnemonic = match pit with
       | VLE16 -> "se_bclri"
       | _ -> "xxxx_bclri" in
     {
       mnemonic = mnemonic;
       operands = [rx; ui5];
       ida_asm = (fun f -> f#ops mnemonic [rx; ui5])
     }

  | BitGenerateImmediate (pit, rx, ui5) ->
     let mnemonic = match pit with
       | VLE16 -> "se_bgeni"
       | _ -> "xxxx_bgeni" in
     {
       mnemonic = mnemonic;
       operands = [rx; ui5];
       ida_asm = (fun f -> f#ops mnemonic [rx; ui5])
     }

  | BitMaskGenerateImmediate (pit, rx, ui5) ->
     let mnemonic = match pit with
       | VLE16 -> "se_bmaski"
       | _ -> "xxxx_bmaski" in
     {
       mnemonic = mnemonic;
       operands = [rx; ui5];
       ida_asm = (fun f -> f#ops mnemonic [rx; ui5])
     }

  | BitSetImmediate (pit, rx, ui5) ->
     let mnemonic = match pit with
       | VLE16 -> "se_bseti"
       | _ -> "xxxx_bseti" in
     {
       mnemonic = mnemonic;
       operands = [rx; ui5];
       ida_asm = (fun f -> f#ops mnemonic [rx; ui5])
     }

  | BitTestImmediate (pit, rx, uimm, cr) ->
     let mnemonic = match pit with
       | VLE16 -> "se_btsti"
       | _ -> "xxxx_btsti" in
     {
       mnemonic = mnemonic;
       operands = [rx; uimm; cr];
       ida_asm = (fun f -> f#ops mnemonic [rx; uimm])
     }

  | Branch (pit, tgt) ->
     let mnemonic = match pit with
       | PWR -> "b"
       | VLE16 -> "se_b"
       | VLE32 -> "e_b" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#ops mnemonic [tgt])
     }

  | BranchConditional (pit, aa, bo, bi, bd) ->
     let mnemonic = match pit with
       | PWR -> "bc"
       | VLE32 -> "e_bc"
       | VLE16 -> "se_bc" in
     {
       mnemonic = mnemonic;
       operands = [bd];
       ida_asm = (fun f -> f#conditional_branch pit bo bi bd)
     }

  | BranchConditionalLinkRegister (pit, bo, bi, bh, lr) ->
     let mnemonic = match pit with
       | PWR -> "bclr"
       | _ -> "xxxx_bclr" in
     {
       mnemonic = mnemonic;
       operands = [lr];
       ida_asm = (fun f -> f#int_ops mnemonic [bo; bi; bh])
     }

  | BranchConditionalLinkRegisterLink (pit, bo, bi, bh, lr) ->
     let mnemonic = match pit with
       | PWR -> "bclrl"
       | _ -> "xxxx_bclrl" in
     {
       mnemonic = mnemonic;
       operands = [lr];
       ida_asm = (fun f -> f#int_ops mnemonic [bo; bi; bh])
     }

  | BranchCountRegister (pit, tgt) ->
     let mnemonic = match pit with
       | PWR -> "bctr"
       | VLE16 -> "se_bctr"
       | _ -> "xxxx_bctr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | BranchCountRegisterLink (pit, tgt) ->
     let mnemonic = match pit with
       | VLE16 -> "se_bctrl"
       | _ -> "xxxx_bctr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | BranchLink (pit, tgt, lr) ->
     let mnemonic = match pit with
       | PWR -> "bl"
       | VLE16 -> "se_bl"
       | VLE32 -> "e_bl" in
     {
       mnemonic = mnemonic;
       operands = [tgt; lr];
       ida_asm = (fun f -> f#ops mnemonic [tgt])
     }

  | BranchLinkRegister (pit, tgt) ->
     let mnemonic = match pit with
       | VLE16 -> "se_blr"
       | PWR -> "blr"
       | _ -> "xxxx_blr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | BranchLinkRegisterLink (pit, tgt) ->
     let mnemonic = match pit with
       | VLE16 -> "se_blrl"
       | _ -> "xxxx_blr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | CBranchDecrementNotZero (pit, aa, bo, bi, bp, bd, ctr) ->
     let mnemonic = match pit with
       | PWR -> "bdnz"
       | VLE16 -> "se_bdnz"
       | VLE32 -> "e_bdnz" in
     {
       mnemonic = mnemonic;
       operands = [bd];
       ida_asm = (fun f -> f#ops mnemonic [bd])
     }

  | CBranchDecrementZero (pit, aa, bo, bi, bp, bd, ctr) ->
     let mnemonic = match pit with
       | PWR -> "bdz"
       | VLE16 -> "se_bdz"
       | VLE32 -> "e_bdz" in
     {
       mnemonic = mnemonic;
       operands = [bd];
       ida_asm = (fun f -> f#ops mnemonic [bd])
     }

  | CBranchEqual (pit, aa, bo, bi, bp, cr, bd) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "beq" bp
       | VLE16 -> "se_beq"
       | VLE32 -> "e_beq" in
     {
       mnemonic = mnemonic;
       operands = [cr; bd];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [bd])
     }

  | CBranchEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "beqlr" bp
       | VLE16 -> "se_beqlr"
       | VLE32 -> "e_beqlr" in
     {
       mnemonic = mnemonic;
       operands = [cr; lr];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [])
     }

  | CBranchGreaterEqual (pit, aa, bo, bi, bp, cr, bd) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "bge" bp
       | VLE16 -> "se_bge"
       | VLE32 -> "e_bge" in
     {
       mnemonic = mnemonic;
       operands = [cr; bd];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [bd])
     }

  | CBranchGreaterEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "bgelr" bp
       | VLE16 -> "se_bgelr"
       | VLE32 -> "e_bgelr" in
     {
       mnemonic = mnemonic;
       operands = [cr; lr];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [])
     }

  | CBranchGreaterThan (pit, aa, bo, bi, bp, cr, bd) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "bgt" bp
       | VLE16 -> "se_bgt"
       | VLE32 -> "e_bgt" in
     {
       mnemonic = mnemonic;
       operands = [cr; bd];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [bd])
     }

  | CBranchGreaterThanLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "bgtlr" bp
       | VLE16 -> "se_bgtlr"
       | VLE32 -> "e_bgtlr" in
     {
       mnemonic = mnemonic;
       operands = [cr; lr];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [])
     }

  | CBranchLessEqual (pit, aa, bo, bi, bp, cr, bd) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "ble" bp
       | VLE16 -> "se_ble"
       | VLE32 -> "e_ble" in
     {
       mnemonic = mnemonic;
       operands = [cr; bd];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [bd])
     }

  | CBranchLessEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "blelr" bp
       | VLE16 -> "se_blelr"
       | VLE32 -> "e_blelr" in
     {
       mnemonic = mnemonic;
       operands = [cr; lr];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [])
     }

  | CBranchLessThan (pit, aa, bo, bi, bp, cr, bd) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "blt" bp
       | VLE16 -> "se_blt"
       | VLE32 -> "e_blt" in
     {
       mnemonic = mnemonic;
       operands = [cr; bd];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [bd])
     }

  | CBranchLessThanLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "bltlr" bp
       | VLE16 -> "se_bltlr"
       | VLE32 -> "e_bltlr" in
     {
       mnemonic = mnemonic;
       operands = [cr; lr];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [])
     }

  | CBranchNotEqual (pit, aa, bo, bi, bp, cr, bd) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "bne" bp
       | VLE16 -> "se_bne"
       | VLE32 -> "e_bne" in
     {
       mnemonic = mnemonic;
       operands = [cr; bd];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [bd])
     }

  | CBranchNotEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_bp "bnelr" bp
       | VLE16 -> "se_bnelr"
       | VLE32 -> "e_bnelr" in
     {
       mnemonic = mnemonic;
       operands = [cr; lr];
       ida_asm = (fun f -> f#ops_bc mnemonic cr [])
     }

  | ClearLeftShiftLeftWordImmediate (pit, rc, ra, rs, mb, sh, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "clrlslwi." else "clrlslwi"
       | _ -> "xxxx_clrlslwi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; mb; sh];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; mb; sh])
     }

  (* Simplified mnemonic, VLEPIM, Table A-23 *)
  | ClearLeftWordImmediate (pit, rc, ra, rs, mb) ->
     let mnemonic = match pit with
       | PWR -> if rc then "clrlwi." else "clrlwi"
       | VLE32 -> "e_clrlwi"
       | _ -> "xxxx_clrlwi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; mb];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; mb])
     }

  (* Simplified mnemonic, VLEPIM, Table A-23 *)
  | ClearRightWordImmediate (pit, rc, ra, rs, me, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "clrrwi." else "clrrwi"
       | VLE32 -> "e_clrrwi"
       | _ -> "xxxx_clrrwi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; me];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; me])
     }

  | CompareImmediate (pit, op16, cr, ra, simm) ->
     let mnemonic = match pit with
       | PWR -> "cmpwi"
       | VLE16 -> "se_cmpi"
       | VLE32 -> if op16 then "e_cmp16i" else "e_cmpi" in
     {
       mnemonic = mnemonic;
       operands = [cr; ra; simm];
       ida_asm = (fun f ->
         match pit with
         | PWR -> f#ops mnemonic [cr; ra; simm]
         | VLE32 -> f#ops mnemonic (if op16 then [ra; simm] else [cr; ra; simm])
         | VLE16 -> f#ops mnemonic [ra; simm])
     }

  | CompareLogical (pit, cr, ra, rb) ->
     let mnemonic = match pit with
       | PWR -> "cmplw"   (* in 32 bit, cmplw is the default version *)
       | VLE16 -> "se_cmpl"
       | VLE32 -> "cmplw" in
     {
       mnemonic = mnemonic;
       operands = [cr; ra; rb];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra; rb]
         | _ -> f#ops mnemonic [cr; ra; rb])
     }

  | CompareLogicalImmediate (pit, op16, cr, ra, uimm) ->
     let mnemonic = match pit with
       | PWR -> "cmplwi"
       | VLE16 -> "se_cmpli"
       | VLE32 -> if op16 then "e_cmpl16i" else "e_cmpli" in
     {
       mnemonic = mnemonic;
       operands = [cr; ra; uimm];
       ida_asm = (fun f ->
         match pit with
         | PWR -> f#ops mnemonic [cr; ra; uimm]
         | VLE16 -> f#ops mnemonic [ra; uimm]
         | VLE32 ->
            f#ops mnemonic (if op16 then [ra; uimm] else [cr; ra; uimm]))
     }

  | CompareWord (pit, cr, ra, rb) ->
     let mnemonic = match pit with
       | PWR -> "cmpw"
       | VLE16 -> "se_cmp"
       | _ -> "xxxx_cmpw" in
     {
       mnemonic = mnemonic;
       operands = [cr; ra; rb];
       ida_asm = (fun f ->
         if cr#is_default_cr then
           f#ops mnemonic [ra; rb]
         else
           f#ops mnemonic [cr; ra; rb])
     }

  | ComplementRegister (pit, rc, ra, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> "not"
       | VLE16 -> "se_not"
       | _ -> "xxxx_not" in
     {
       mnemonic = mnemonic;
       operands = [ra; rb; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra]
         | _ -> f#ops mnemonic [ra; rb])
     }

  | ConditionRegisterNot (pit, crd, cra) ->
     let mnemonic = match pit with
       | PWR -> "crnot"
       | _ -> "xxxx_crnot" in
     {
       mnemonic = mnemonic;
       operands = [crd; cra];
       ida_asm = (fun f -> f#ops mnemonic [crd; cra])
     }

  | ConditionRegisterOr (pit, crd, cra, crb) ->
     let mnemonic = match pit with
       | PWR -> "cror"
       | VLE32 -> "e_cror"
       | _ -> "xxxx_cror" in
     {
       mnemonic = mnemonic;
       operands = [crd; cra; crb];
       ida_asm = (fun f -> f#ops mnemonic [crd; cra; crb])
     }

  | CountLeadingZerosWord (pit, rc, ra, rs, cr0) ->
     let mnemonic = match pit with
       | PWR -> "cntlzw"
       | _ -> "xxxx_cntlzw" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; cr0];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs])
     }

  | DivideWord (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "divw" oe rc
       | _ -> "xxxx_divw" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; so; ov];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | DivideWordUnsigned (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "divwu" oe rc
       | _ -> "xxxx_divwu" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; so; ov];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | ExtendSignByte (pit, rc, ra, rs, cr) ->
     let mnemonic = match pit with
       | PWR -> "extsb"
       | VLE16 -> "se_extsb"
       | _ -> "xxxx_extsb" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra]
         | _ -> f#ops mnemonic [ra; rs])
     }

  | EnforceInOrderExecutionIO (pit, mo) ->
     let mnemonic = match pit with
       | PWR -> "eieio"
       | _ -> "xxxx_eieio" in
     {
       mnemonic = mnemonic;
       operands = [mo];
       ida_asm = (fun f -> f#ops mnemonic [mo]);
     }

  | ExtendSignHalfword (pit, rc, ra, rs, cr) ->
     let mnemonic = match pit with
       | PWR -> "extsh"
       | VLE16 -> "se_extsh"
       | _ -> "xxxx_extsh" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra]
         | _ -> f#ops mnemonic [ra; rs])
     }

  | ExtendZeroByte (pit, dst) ->
     let mnemonic = match pit with
       | VLE16 -> "se_extzb"
       | _ -> "xxxx_extzb" in
     {
       mnemonic = mnemonic;
       operands = [dst];
       ida_asm = (fun f -> f#ops mnemonic [dst])
     }

  | ExtendZeroHalfword (pit, dst) ->
     let mnemonic = match pit with
       | VLE16 -> "se_extzh"
       | _ -> "xxxx_extzh" in
     {
       mnemonic = mnemonic;
       operands = [dst];
       ida_asm = (fun f -> f#ops mnemonic [dst])
     }

  | ExtractRightJustifyWordImmediate (pit, rc, ra, rs, n, b, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "extrwi." else "extrwi"
       | VLE32 -> "e_extrwi"
       | _ -> "xxxx_extrwi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; n; b];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; n; b])
     }

  | InsertRightWordImmediate (pit, rc, ra, rs, sh, mb, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "insrwi." else "insrwi"
       | VLE32 -> "e_insrwi"
       | _ -> "xxxx_insrwi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; sh; mb; cr];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; sh; mb])
     }

  | InstructionSynchronize (pit) ->
     let mnemonic = match pit with
       | PWR -> "isync"
       | VLE16 -> "se_isync"
       | _ -> "xxxx_isync" in
     {
       mnemonic = mnemonic;
       operands = [];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | IntegerSelect (pit, rd, ra, rb, crb) ->
     let mnemonic = match pit with
       | PWR -> "isel"
       | _ -> "xxxx_isel" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; crb];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb; crb])
     }

  | IntegerSelectEqual (pit, rd, ra, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> "iseleq"
       | _ -> "xxxx_iseleq" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | IntegerSelectGreaterThan (pit, rd, ra, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> "iselgt"
       | _ -> "xxxx_iselgt" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | IntegerSelectLessThan (pit, rd, ra, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> "isellt"
       | _ -> "xxxx_isellt" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | LoadByteZero (pit, update, rd, ra, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "lbzu" else "lbz"
       | VLE16 -> "se_lbz"
       | VLE32 -> if update then "e_lbzu" else "e_lbz" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [rd; mem])
     }

  | LoadByteZeroIndexed (pit, update, rd, ra, rb, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "lbzux" else "lbzx"
       | _ -> "xxxx_lbzx" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; mem];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | LoadHalfwordZero (pit, update, rd, ra, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "lhzu" else "lhz"
       | VLE16 -> "se_lhz"
       | VLE32 -> if update then "e_lhzu" else "e_lhz" in
     let mnemonic = if update then mnemonic ^ "u" else mnemonic in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [rd; mem])
     }

  | LoadImmediate (pit, signed, shifted, rd, imm) ->
     let mnemonic = match pit with
       | PWR -> if shifted then "lis" else "li"
       | VLE16 -> "se_li"
       | VLE32 -> if shifted then "e_lis" else "e_li" in
     {
       mnemonic = mnemonic;
       operands = [rd; imm];
       ida_asm = (fun f -> f#ops mnemonic [rd; imm])
     }

  | LoadMultipleVolatileGPRWord (pit, ra, mem) ->
     let mnemonic = match pit with
       | VLE32 -> "e_lmvgprw"
       | _ -> "xxxx_lmvgprw" in
     {
       mnemonic = mnemonic;
       operands = [ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [mem])
     }

  | LoadMultipleVolatileSPRWord (pit, ra, mem, cr, lr, ctr, xer) ->
     let mnemonic = match pit with
       | VLE32 -> "e_lmvsprw"
       | _ -> "xxxx_lmvsprw" in
     {
       mnemonic = mnemonic;
       operands = [ra; mem; cr; lr; ctr; xer];
       ida_asm = (fun f -> f#ops mnemonic [mem])
     }

  | LoadMultipleVolatileSRRWord (pit, ra, mem, srr0, srr1) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_lmvsrrw"
       | _ -> "xxxx_lmvsrrw" in
     {
       mnemonic = mnemonic;
       operands = [ra; mem; srr0; srr1];
       ida_asm = (fun f -> f#ops mnemonic [mem])
     }

  | LoadMultipleWord (pit, rd, ra, mem) ->
     let mnemonic = match pit with
       | PWR -> "lmw"
       | VLE32 -> "e_lmw"
       | _ -> "xxxx_lmw" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [rd; mem])
     }

  | LoadWordZero (pit, update, rd, ra, mem) ->
     let mnemonic =
       match pit with
       | PWR -> if update then "lwzu" else "lwz"
       | VLE32 -> if update then "e_lwzu" else "e_lwz"
       | VLE16 -> "se_lwz" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [rd; mem])
     }

  | LoadWordZeroIndexed (pit, update, rd, ra, rb, mem) ->
     let mnemonic =
       match pit with
       | PWR -> if update then "lwzux" else "lwzx"
       | _ -> "xxxx_lwzx" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; mem];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | MemoryBarrier (pit, mo) ->
     let mnemonic =
       match pit with
       | PWR -> "mbar"
       | _ -> "xxxx_mbar" in
     {
       mnemonic = mnemonic;
       operands = [mo];
       ida_asm = (fun f -> f#ops mnemonic [mo])
     }

  | MoveConditionRegisterField (pit, crfd, crs) ->
     let mnemonic =
       match pit with
       | PWR -> "mcrf"
       | VLE32 -> "e_mcrf"
       | _ -> "xxxx_mcrf" in
     {
       mnemonic = mnemonic;
       operands = [crfd; crs];
       ida_asm = (fun f -> f#ops mnemonic [crfd; crs])
     }

  | MoveFromAlternateRegister (pit, rx, ary) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_mfar"
       | _ -> "xxxx_mfar" in
     {
       mnemonic = mnemonic;
       operands = [rx; ary];
       ida_asm = (fun f -> f#ops mnemonic [rx; ary])
     }

  | MoveFromConditionRegister (pit, rd, cr) ->
     let mnemonic = match pit with
       | PWR -> "mfcr"
       | _ -> "xxxx_mfcr" in
     {
       mnemonic = mnemonic;
       operands = [rd; cr];
       ida_asm = (fun f -> f#ops mnemonic [rd])
     }

  | MoveFromCountRegister (pit, rx, ctr) ->
     let mnemonic = match pit with
       | PWR -> "mfctr"
       | VLE16 -> "se_mfctr"
       | _ -> "xxxx_mfctr" in
     {
       mnemonic = mnemonic;
       operands = [rx; ctr];
       ida_asm = (fun f -> f#ops mnemonic [rx])
     }

  | MoveFromExceptionRegister (pit, rd, xer) ->
     let mnemonic = match pit with
       | PWR -> "mfxer"
       | _ -> "xxxx_mfxer" in
     {
       mnemonic = mnemonic;
       operands = [rd; xer];
       ida_asm = (fun f -> f#ops mnemonic [rd])
     }

  | MoveFromLinkRegister (pit, rd, lr) ->
     let mnemonic = match pit with
       | PWR -> "mflr"
       | VLE16 -> "se_mflr"
       | _ -> "xxxx_mflr" in
     {
       mnemonic = mnemonic;
       operands = [rd; lr];
       ida_asm = (fun f -> f#ops mnemonic [rd])
     }

  | MoveFromMachineStateRegister (pit, rd, msr) ->
     let mnemonic = match pit with
       | PWR -> "mfmsr"
       | _ -> "xxxx_mfmsr" in
     {
       mnemonic = mnemonic;
       operands = [rd; msr];
       ida_asm = (fun f -> f#ops mnemonic [rd])
     }

  | MoveFromSpecialPurposeRegister (pit, rd, sprn) ->
     let mnemonic = match pit with
       | PWR -> "mfspr"
       | _ -> "xxxx_mfspr" in
     {
       mnemonic = mnemonic;
       operands = [rd; sprn];
       ida_asm = (fun f -> f#ops mnemonic [rd; sprn])
     }

  | MoveRegister (pit, rc, ra, rs) ->
     let mnemonic = match pit with
       | PWR -> if rc then "mr." else "mr"
       | VLE16 -> "se_mr"
       | _ -> "xxxx_mr" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs])
     }

  | MoveToAlternateRegister (pit, arx, ry) ->
     let mnemonic = match pit with
       | VLE16 -> "se_mtar"
       | _ -> "xxxx_mtar" in
     {
       mnemonic = mnemonic;
       operands = [arx; ry];
       ida_asm = (fun f -> f#ops mnemonic [arx; ry])
     }

  | MoveToConditionRegister (pit, cr, rs) ->
     let mnemonic =
       match pit with
       | PWR -> "mtcr"
       | _ -> "xxxx_mtcr" in
     {
       mnemonic = mnemonic;
       operands = [cr; rs];
       ida_asm = (fun f -> f#ops mnemonic [rs])
     }

  | MoveToConditionRegisterFields (pit, crm, rs) ->
     let mnemonic =
       match pit with
       | PWR -> "mtcrf"
       | _ -> "xxxx_mtcrf" in
     {
       mnemonic = mnemonic;
       operands = [crm; rs];
       ida_asm = (fun f -> f#ops mnemonic [crm; rs])
     }

  | MoveToCountRegister (pit, ctr, rs) ->
     let mnemonic =
       match pit with
       | PWR -> "mtctr"
       | VLE16 -> "se_mtctr"
       | _ -> "xxxx_mtctr" in
     {
       mnemonic = mnemonic;
       operands = [ctr; rs];
       ida_asm = (fun f -> f#ops mnemonic [rs])
     }

  | MoveToExceptionRegister (pit, xer, rs) ->
     let mnemonic = match pit with
       | PWR -> "mtxer"
       | _ -> "xxxx_mtxer" in
     {
       mnemonic = mnemonic;
       operands = [xer; rs];
       ida_asm = (fun f -> f#ops mnemonic [rs])
     }

  | MoveToLinkRegister (pit, lr, rs) ->
     let mnemonic = match pit with
       | PWR -> "mtlr"
       | VLE16 -> "se_mtlr"
       | _ -> "xxxx_mtlr" in
     {
       mnemonic = mnemonic;
       operands = [lr; rs];
       ida_asm = (fun f -> f#ops mnemonic [rs])
     }

  | MoveToMachineStateRegister (pit, msr, rs) ->
     let mnemonic =
       match pit with
       | PWR -> "mtmsr"
       | _ -> "xxxx_mtmsr" in
     {
       mnemonic = mnemonic;
       operands = [msr; rs];
       ida_asm = (fun f -> f#ops mnemonic [rs])
     }

  | MoveToSpecialPurposeRegister (pit, sprn, rs) ->
     let mnemonic = match pit with
       | PWR -> "mtspr"
       | _ -> "xxxx_mtspr" in
     {
       mnemonic = mnemonic;
       operands = [sprn; rs];
       ida_asm = (fun f -> f#ops mnemonic [sprn; rs])
     }

  | MultiplyHighWordUnsigned (pit, rc, rd, ra, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> "mulhwu"
       | _ -> "xxxx_mulhwu" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | MultiplyLowImmediate (pit, op2, rd, ra, simm) ->
     let mnemonic = match pit with
       | PWR -> "mulli"
       | VLE32 -> if op2 then "e_mull2i" else "e_mulli"
       | _ -> "xxxx_mulli" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; simm];
       ida_asm = (fun f ->
         match pit with
         | VLE32 when op2 -> f#ops mnemonic [rd; simm]
         | _ -> f#ops mnemonic [rd; ra; simm])
     }

  | MultiplyLowWord (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "mullw" oe rc
       | VLE16 -> "se_mullw"
       | _ -> "xxxx_mullw" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; so; ov];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [rd; rb]
         | _ -> f#ops mnemonic [rd; ra; rb])
     }

  | Negate (pit, rc, oe, rd, ra, cr, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "neg" oe rc
       | VLE16 -> "se_neg"
       | _ -> "xxxx_neg" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; cr; so; ov];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [rd]
         | _ -> f#ops mnemonic [rd; ra])
     }

  | Or (pit, rc, ra, rs, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "or." else "or"
       | VLE16 -> "se_or"
       | _ -> "xxxx_or" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra; rb]
         | _ -> f#ops mnemonic [ra; rs; rb])
     }

  | OrImmediate (pit, rc, shifted, op2, ra, rs, uimm, cr) ->
     let mnemonic = match pit with
       | PWR -> if shifted then "oris" else "ori"
       | VLE32 ->
          (match (rc, shifted, op2) with
           | (false, false, false) -> "e_ori"
           | (true, false, false) -> "e_ori."
           | (false, false, true) -> "e_or2i"
           | (false, true, true) -> "e_or2is"
           | _ -> "xxxx_ori")
       | _ -> "xxxx_ori" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; uimm];
       ida_asm =
         (fun f ->
           match pit with
           | PWR -> f#ops mnemonic [ra; rs; uimm]
           | VLE32 ->
              f#ops mnemonic (if op2 then [ra; uimm] else [ra; rs; uimm])
           | _ -> f#ops mnemonic [ra; rs; uimm])
     }

  | ReturnFromDebugInterrupt (pit, msr, dsr0, dsr1) ->
     let mnemonic = match pit with
       | PWR -> "rfdi"
       | VLE16 -> "se_rfdi"
       | _ -> "xxxx_rfdi" in
     {
       mnemonic = mnemonic;
       operands = [msr; dsr0; dsr1];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | ReturnFromInterrupt (pit, msr, sr0, sr1) ->
     let mnemonic = match pit with
       | PWR -> "rfi"
       | VLE16 -> "se_rfi"
       | _ -> "xxxx_rfi" in
     {
       mnemonic = mnemonic;
       operands = [msr; sr0; sr1];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | ReturnFromMachineCheckInterrupt (pit, msr, mcsr0, mcsr1) ->
     let mnemonic = match pit with
       | PWR -> "rfmci"
       | VLE16 -> "se_rfmci"
       | _ -> "xxxx_rfmci" in
     {
       mnemonic = mnemonic;
       operands = [msr; mcsr0; mcsr1];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | RotateLeftWord (pit, rc, ra, rs, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "rotlw." else "rotlw"
       | VLE32 -> if rc then "e_rlw." else "e_rlw"
       | _ -> "xxxx_rlw" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb; cr];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; rb])
     }

  | RotateLeftWordImmediateAndMask (pit, rc, ra, rs, sh, mb, me, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "rlwinm." else "rlwinm"
       | VLE32 -> "e_rlwinm"
       | _ -> "xxxx_rlwinm" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; sh; mb; me; cr];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; sh; mb; me])
     }

  | ShiftLeftWord (pit, rc, ra, rs, rb, cr) ->
     let mnemonic = match pit with
       | VLE16 -> "se_slw"
       | PWR -> if rc then "slw." else "slw"
       | _ -> "xxxx_slw" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb; cr];
       ida_asm =
         (fun f ->
           match pit with
           | VLE16 -> f#ops mnemonic [ra; rb]
           | _ -> f#ops mnemonic [ra; rs; rb])
     }

  | ShiftLeftWordImmediate (pit, rc, ra, rs, sh, cr) ->
     let mnemonic = match pit with
       | PWR -> "slwi"
       | VLE16 -> "se_slwi"
       | VLE32 -> if rc then "e_slwi." else "e_slwi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; sh; cr];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; sh])
     }

  | ShiftRightAlgebraicWord (pit, rc, ra, rs, rb, cr, ca) ->
     let mnemonic = match pit with
       | PWR -> if rc then "sraw." else "sraw"
       | VLE16 -> "se_sraw"
       | _ -> "xxxx_sraw" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb; cr; ca];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra; rb]
         | _ -> f#ops mnemonic [ra; rs; rb])
     }

  | ShiftRightAlgebraicWordImmediate (pit, rc, ra, rs, sh, cr, ca) ->
     let mnemonic = match pit with
       | PWR -> if rc then "srawi." else "srawi"
       | VLE16 -> "se_srawi"
       | VLE32 -> "e_srawi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; sh; cr; ca];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; sh])
     }

  | ShiftRightWord (pit, rc, ra, rs, rb, cr) ->
     let mnemonic = match pit with
       | VLE16 -> "se_srw"
       | PWR -> if rc then "srw." else "srw"
       | _ -> "xxxx_srw" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [rs; rb]
         | _ -> f#ops mnemonic [ra; rs; rb])
     }

  | ShiftRightWordImmediate (pit, rc, ra, rs, sh, cr) ->
     let mnemonic = match pit with
       | VLE16 -> "se_srwi"
       | VLE32 -> if rc then "e_srwi." else "e_srwi"
       | _ -> "xxxx_srwi" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; sh; cr];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [ra; sh]
         | _ -> f#ops mnemonic [ra; rs; sh])
     }

  | StoreByte (pit, update, rs, ra, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "stbu" else "stb"
       | VLE16 -> "se_stb"
       | VLE32 -> if update then "e_stbu" else "e_stb" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [rs; mem])
     }

  | StoreByteIndexed (pit, update, rs, ra, rb, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "stbux" else "stbx"
       | _ -> "xxxx_stbx" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; rb; mem];
       ida_asm = (fun f -> f#ops mnemonic [rs; ra; rb])
     }

  | StoreHalfword (pit, update, rs, ra, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "sthu" else "sth"
       | VLE16 -> "se_sth"
       | VLE32 -> if update then "e_sthu" else "e_sth" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [rs; mem])
     }

  | StoreHalfwordIndexed (pit, update, rs, ra, rb, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "sthux" else "sthx"
       | _ -> "xxxx_sthx" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; rb; mem];
       ida_asm = (fun f -> f#ops mnemonic [rs; ra; rb])
     }

  | StoreMultipleWord (pit, rs, ra, ea) ->
     let mnemonic = match pit with
       | PWR -> "stmw"
       | VLE32 -> "e_stmw"
       | _ -> "xxxx_stmw" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [rs; ea])
     }

  | StoreMultipleVolatileGPRWord (pit, ra, ea) ->
     let mnemonic = match pit with
       | VLE32 -> "e_stmvgprw"
       | _ -> "xxxx_stmvgprw" in
     {
       mnemonic = mnemonic;
       operands = [ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [ea])
     }

  | StoreMultipleVolatileSPRWord (pit, ra, mem, cr, lr, ctr, xer) ->
     let mnemonic = match pit with
       | VLE32 -> "e_stmvsprw"
       | _ -> "xxxx_stmvsprw" in
     {
       mnemonic = mnemonic;
       operands = [mem; ra; cr; lr; ctr; xer];
       ida_asm = (fun f -> f#ops mnemonic [mem])
     }

  | StoreMultipleVolatileSRRWord (pit, ra, mem, srr0, srr1) ->
     let mnemonic = match pit with
       | VLE32 -> "e_stmvsrrw"
       | _ -> "xxxx_stmvsrrw" in
     {
       mnemonic = mnemonic;
       operands = [ra; mem; srr0; srr1];
       ida_asm = (fun f -> f#ops mnemonic [mem])
     }

  | StoreWord (pit, update, rs, ra, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "stwu" else "stw"
       | VLE16 -> "se_stw"
       | VLE32-> if update then "e_stwu" else "e_stw" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; mem];
       ida_asm = (fun f -> f#ops mnemonic [rs; mem])
     }

  | StoreWordIndexed (pit, update, rs, ra, rb, mem) ->
     let mnemonic = match pit with
       | PWR -> if update then "stwux" else "stwx"
       | VLE16 -> "se_stwx"
       | VLE32 -> "e_stwx" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; rb; mem];
       ida_asm = (fun f -> f#ops mnemonic [rs; ra; rb])
     }

  | Subtract (pit, rx, ry) ->
     let mnemonic = match pit with
       | VLE16 -> "se_sub"
       | _ -> "xxxx_sub" in
     {
       mnemonic = mnemonic;
       operands = [rx; ry];
       ida_asm = (fun f -> f#ops mnemonic [rx; ry])
     }

  | SubtractFrom (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "subf" oe rc
       | VLE16 -> "se_subf"
       | _ -> "xxxx_subf" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; so; ov];
       ida_asm = (fun f ->
         match pit with
         | VLE16 -> f#ops mnemonic [rd; rb]
         | _ -> f#ops mnemonic [rd; ra; rb])
     }

  | SubtractFromCarrying (pit, rc, oe, rd, ra, rb, cr, ca, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "subfc" oe rc
       | _ -> "xxxx_subfc" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; ca; so; ov];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | SubtractFromExtended (pit, rc, oe, rd, ra, rb, cr, ca, so, ov) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "subfe" oe rc
       | _ -> "xxxx_subfe" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; rb; cr; ca; so; ov];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; rb])
     }

  | SubtractFromImmediateCarrying (pit, rc, rd, ra, simm, cr, ca) ->
     let mnemonic = match pit with
       | PWR -> "subfic"
       | VLE32 -> if rc then "e_subfic." else "e_subfic"
       | _ -> "xxxx_subfic" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; simm; cr; ca];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra; simm])
     }

  | SubtractFromZeroExtended (pit, rc, oe, rd, ra, cr, so, ov, ca) ->
     let mnemonic = match pit with
       | PWR -> mnemonic_oe_rc "subfze" oe rc
       | _ -> "xxxx_subfze" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; cr; so; ov; ca];
       ida_asm = (fun f -> f#ops mnemonic [rd; ra])
     }

  | SubtractImmediate (pit, rc, rd, ra, imm, cr) ->
     let mnemonic = match pit with
       | PWR -> "subi"
       | VLE16 -> if rc then "se_subi." else "se_subi"
       | _ -> "xxxx_subi" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; imm; cr];
       ida_asm =
         (fun f ->
           match pit with
           | VLE16 -> f#ops mnemonic [rd; imm]
           | _ -> f#ops mnemonic [rd; ra; imm])
     }

  | TLBWriteEntry pit ->
     let mnemonic = match pit with
       | PWR -> "tlbwe"
       | _ -> "xxxx_tlbwe" in
     {
       mnemonic = mnemonic;
       operands = [];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }

  | WriteMSRExternalEnableImmediate (pit, enable, msr) ->
     let mnemonic = match pit with
       | PWR -> "wrteei"
       | _ -> "xxxx_wrteei" in
     {
       mnemonic = mnemonic;
       operands = [msr];
       ida_asm = (fun f -> f#enable mnemonic enable)
     }

  | Xor (pit, rc, ra, rs, rb, cr) ->
     let mnemonic = match pit with
       | PWR -> if rc then "xor." else "xor"
       | _ -> "xxxx_xor" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; rb; cr];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; rb])
     }

  | XorImmediate (pit, rc, shifted, ra, rs, uimm, cr) ->
     let mnemonic = match pit with
       | PWR -> if shifted then "xoris" else "xori"
       | VLE32 -> if rc then "e_xori." else "e_xori"
       | _ -> "xxxx_xori" in
     {
       mnemonic = mnemonic;
       operands = [ra; rs; uimm];
       ida_asm = (fun f -> f#ops mnemonic [ra; rs; uimm])
     }

  | NoOperation -> {
      mnemonic = "nop";
      operands = [];
      ida_asm = (fun f -> f#no_ops "nop")
    }
  | OpInvalid | NotCode _ -> {
      mnemonic = "invalid";
      operands = [];
      ida_asm = (fun f -> f#no_ops "invalid")
    }
  | OpcodeIllegal i -> {
      mnemonic = "ILLEGAL";
      operands = [];
      ida_asm = (fun f -> f#no_ops ("ILLEGAL: " ^ (string_of_int i)))
    }
  | OpcodeUndefined s -> {
      mnemonic = "UNDEFINED";
      operands = [];
      ida_asm = (fun f -> f#no_ops ("UNDEFINED: " ^ s))
    }
  | OpcodeUnpredictable s -> {
      mnemonic = "UNPREDICTABLE";
      operands = [];
      ida_asm = (fun f -> f#no_ops ("UNPREDICTABLE: " ^ s))
    }
  | NotRecognized (name, dw) -> {
      mnemonic = "not_recognized";
      operands = [];
      ida_asm =
        (fun f -> f#no_ops ("not_recognized " ^ name ^ ":" ^ dw#to_hex_string))
    }


class string_formatter_t (width: int): [string] opcode_formatter_int =
object (self)

  method ops (s: string) (operands: pwr_operand_int list) =
    let s = (fixed_length_string s width) in
    let (_, result) =
      List.fold_left
        (fun (isfirst, a) op ->
          if isfirst then
            (false, s ^ " " ^ op#toString)
          else
            (false, a ^ ", " ^ op#toString)) (true, s) operands in
    result

  method int_ops (s: string) (ops: int list): 'a =
    let s = (fixed_length_string s width) in
    let (_, result) =
      List.fold_left
        (fun (isfirst, a) op ->
          if isfirst then
            (false, s ^ " " ^ (string_of_int op))
          else
            (false, a ^ "," ^ (string_of_int op))) (true, s) ops in
    result

  method no_ops (s: string) = s

  method ops_bc (s: string) (cr: pwr_operand_int) (ops: pwr_operand_int list) =
    if cr#is_default_cr then
      match ops with
      | [] -> self#no_ops s
      | _ -> self#ops s ops
    else
      self#ops s (cr::ops)

  method enable (s: string) (b: bool) =
    let s = (fixed_length_string s width) in
    if b then s ^ " 1" else s ^ " 0"

  method conditional_branch
           (pit: pwr_instruction_type_t)
           (bo: int)
           (bi: int)
           (tgt: pwr_operand_int) =
    let prefix = match pit with
      | PWR -> "b"
      | VLE16 -> "se_b"
      | VLE32 -> "e_b" in
    (fixed_length_string (prefix ^ "c") width)
    ^ " "
    ^ (string_of_int bo)
    ^ ","
    ^ (string_of_int bi)
    ^ ","
    ^ tgt#toString
end


let pwr_opcode_to_string ?(width=12) (opc: pwr_opcode_t) =
  let formatter = new string_formatter_t width in
  let default () = (get_record opc).ida_asm formatter in
  default ()
                  

let pwr_opcode_name (opc: pwr_opcode_t) = (get_record opc).mnemonic
