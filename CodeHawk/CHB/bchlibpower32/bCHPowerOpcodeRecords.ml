(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs, LLC

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
    method ops: string -> power_operand_int list -> 'a
    method no_ops: string -> 'a
  end


type 'a opcode_record_t ={
    mnemonic: string;
    operands: power_operand_int list;
    ida_asm: 'a
  }


let get_record (opc: power_opcode_t) =
  match opc with
  | AddImmediate (pit, shifted, rc, dst, src, imm) ->
     let mnemonic =
       match (pit, rc, shifted) with
       | (PWR, false, false) -> "addi"
       | (PWR, true, false) -> "addis"
       | (VLE16, false, false) -> "se_addi"
       | (VLE32, false, false) -> "e_addi"
       | (VLE32, false, true) -> "e_addi."
       | _ -> "xxxx_addi" in
     {
       mnemonic = mnemonic;
       operands = [dst; src; imm];
       ida_asm = (fun f -> f#ops mnemonic [dst; src; imm])
     }
  | And (pit, rx, ry) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_and"
       | _ -> "xxxx_and" in
     {
       mnemonic = mnemonic;
       operands = [rx; ry];
       ida_asm = (fun f -> f#ops mnemonic [rx; ry])
     }
  | BitGenerateImmediate (pit, dst, imm) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_bgeni"
       | _ -> "xxxx_bgeni" in
     {
       mnemonic = mnemonic;
       operands = [dst; imm];
       ida_asm = (fun f -> f#ops mnemonic [dst; imm])
     }
  | BitMaskGenerateImmediate (pit, dst, imm) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_bmaski"
       | _ -> "xxxx_bmaski" in
     {
       mnemonic = mnemonic;
       operands = [dst; imm];
       ida_asm = (fun f -> f#ops mnemonic [dst; imm])
     }
  | BitSetImmediate (pit, dst, imm) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_bseti"
       | _ -> "xxxx_bseti" in
     {
       mnemonic = mnemonic;
       operands = [dst; imm];
       ida_asm = (fun f -> f#ops mnemonic [dst; imm])
     }
  | BranchCountRegister (pit, tgt) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_bctr"
       | _ -> "xxxx_bctr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }
  | BranchCountRegisterLink (pit, tgt) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_bctrl"
       | _ -> "xxxx_bctr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }
  | BranchLinkRegister (pit, tgt) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_blr"
       | _ -> "xxxx_blr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }
  | BranchLinkRegisterLink (pit, tgt) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_blrl"
       | _ -> "xxxx_blr" in
     {
       mnemonic = mnemonic;
       operands = [tgt];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }
  | CompareImmediate (pit, src, imm) ->
     let mnemonic =
       match pit with
       | PWR -> "cmpi"
       | VLE16 -> "se_cmpi"
       | VLE32 -> "e_cmpi" in
     {
       mnemonic = mnemonic;
       operands = [src; imm];
       ida_asm = (fun f -> f#ops mnemonic [src; imm])
     }
  | CompareLogical (pit, src1, src2) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_cmpl"
       | _ -> "xxxx_cmpl" in
     {
       mnemonic = mnemonic;
       operands = [src1; src2];
       ida_asm = (fun f -> f#ops mnemonic [src1; src2])
     }
  | CompareLogicalImmediate (pit, src, imm) ->
     let mnemonic =
       match pit with
       | PWR -> "cmpli"
       | VLE16 -> "se_cmpli"
       | VLE32 -> "e_cmpli" in
     {
       mnemonic = mnemonic;
       operands = [src; imm];
       ida_asm = (fun f -> f#ops mnemonic [src; imm])
     }
  | ExtendZeroHalfword (pit, dst) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_extzh"
       | _ -> "xxxx_extzh" in
     {
       mnemonic = mnemonic;
       operands = [dst];
       ida_asm = (fun f -> f#ops mnemonic [dst])
     }
  | InstructionSynchronize (pit) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_isync"
       | _ -> "xxxx_isync" in
     {
       mnemonic = mnemonic;
       operands = [];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }
  | LoadByteZeroUpdate (pit, rd, ra, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_lbzu"
       | _ -> "xxxx_lbzu" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [rd; ea])
     }
  | LoadHalfwordZero (pit, dst, ea) ->
     let mnemonic =
       match pit with
       | PWR -> "lhz"
       | VLE16 -> "se_lhz"
       | VLE32 -> "e_lhz" in
     {
       mnemonic = mnemonic;
       operands = [dst; ea];
       ida_asm = (fun f -> f#ops mnemonic [dst; ea])
     }
  | LoadImmediate (pit, shifted, dst, src) ->
     let mnemonic =
       match (pit, shifted) with
       | (PWR, false) -> "li"
       | (PWR, true) -> "lis"
       | (VLE16, false) -> "se_li"
       | (VLE32, false) -> "e_li"
       | (VLE32, true) -> "e_lis"
       | _ -> "xxxx_li" in
     {
       mnemonic = mnemonic;
       operands = [dst; src];
       ida_asm = (fun f -> f#ops mnemonic [dst; src])
     }
  | LoadMultipleVolatileGPRWord (pit, ra, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_lmvgprw"
       | _ -> "xxxx_lmvgprw" in
     {
       mnemonic = mnemonic;
       operands = [ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [ea])
     }
  | LoadMultipleVolatileSPRWord (pit, ra, cr, lr, ctr, xer, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_lmvsprw"
       | _ -> "xxxx_lmvsprw" in
     {
       mnemonic = mnemonic;
       operands = [ra; cr; lr; ctr; xer; ea];
       ida_asm = (fun f -> f#ops mnemonic [ea])
     }
  | LoadMultipleVolatileSRRWord (pit, ra, srr0, srr1, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_lmvsrrw"
       | _ -> "xxxx_lmvsrrw" in
     {
       mnemonic = mnemonic;
       operands = [ra; srr0; srr1; ea];
       ida_asm = (fun f -> f#ops mnemonic [ea])
     }
  | LoadMultipleWord (pit, rd, ra, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_lmw"
       | _ -> "xxxx_lmw" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [rd; ea])
     }
  | LoadWordZero (pit, dst, ea) ->
     let mnemonic =
       match pit with
       | PWR -> "lwz"
       | VLE16 -> "se_lwz"
       | VLE32 -> "e_lwz" in
     {
       mnemonic = mnemonic;
       operands = [dst; ea];
       ida_asm = (fun f -> f#ops mnemonic [dst; ea])
     }
  | LoadWordZeroUpdate (pit, rd, ra, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_lwzu"
       | _ -> "xxxx_lwzu" in
     {
       mnemonic = mnemonic;
       operands = [rd; ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [rd; ea])
     }
  | MoveFromAlternateRegister (pit, dst, src) ->
     let mnemonic =
       match pit with
       | PWR -> "mfar"
       | VLE16 -> "se_mfar"
       | _ -> "xxxx_mfar" in
     {
       mnemonic = mnemonic;
       operands = [src; dst];
       ida_asm = (fun f -> f#ops mnemonic [dst; src])
     }
  | MoveFromLinkRegister (pit, dst, lr) ->
     let mnemonic =
       match pit with
       | PWR -> "mflr"
       | VLE16 -> "se_mflr"
       | _ -> "xxxx_mflr" in
     {
       mnemonic = mnemonic;
       operands = [dst; lr];
       ida_asm = (fun f -> f#ops mnemonic [dst])
     }
  | MoveRegister (pit, dst, src) ->
     let mnemonic =
       match pit with
       | PWR -> "mr"
       | VLE16 -> "se_mr"
       | _ -> "xxxx_mr" in
     {
       mnemonic = mnemonic;
       operands = [src; dst];
       ida_asm = (fun f -> f#ops mnemonic [dst; src])
     }
  | MoveToCountRegister (pit, ctr, src) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_mtctr"
       | _ -> "xxxx_mtctr" in
     {
       mnemonic = mnemonic;
       operands = [ctr; src];
       ida_asm = (fun f -> f#ops mnemonic [src])
     }
  | MoveToLinkRegister (pit, lr, src) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_mtlr"
       | _ -> "xxxx_mtlr" in
     {
       mnemonic = mnemonic;
       operands = [lr; src];
       ida_asm = (fun f -> f#ops mnemonic [src])
     }
  | NotRegister (pit, reg) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_not"
       | _ -> "xxxx_not" in
     {
       mnemonic = mnemonic;
       operands = [reg];
       ida_asm = (fun f -> f#ops mnemonic [reg])
     }
  | Or (pit, rx, ry) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_or"
       | _ -> "xxxx_or" in
     {
       mnemonic = mnemonic;
       operands = [rx; ry];
       ida_asm = (fun f -> f#ops mnemonic [rx; ry])
     }
  | ReturnFromInterrupt (pit, msr) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_rfi"
       | _ -> "xxxx_rfi" in
     {
       mnemonic = mnemonic;
       operands = [msr];
       ida_asm = (fun f -> f#no_ops mnemonic)
     }
  | ShiftLeftWordImmediate (pit, dst, src, imm) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_slwi"
       | VLE32 -> "e_slwi"
       | _ -> "xxxx_slwi" in
     {
       mnemonic = mnemonic;
       operands = [src; dst; imm];
       ida_asm = (fun f -> f#ops mnemonic [dst; src; imm])
     }
  | ShiftRightAlgebraicWordImmediate (pit, dst, src, imm) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_srawi"
       | VLE32 -> "e_srawi"
       | _ -> "xxxx_srawi" in
     {
       mnemonic = mnemonic;
       operands = [src; dst; imm];
       ida_asm = (fun f -> f#ops mnemonic [dst; src; imm])
     }
  | StoreByteUpdate (pit, rs, ra, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_stbu"
       | _ -> "xxxx_stbu" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [rs; ea])
     }
  | StoreHalfword (pit, dst, ea) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_sth"
       | _ -> "xxxx_sth" in
     {
       mnemonic = mnemonic;
       operands = [dst; ea];
       ida_asm = (fun f -> f#ops mnemonic [dst; ea])
     }
  | StoreMultipleWord (pit, rs, ra, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_stmw"
       | _ -> "xxxx_stmw" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [rs; ea])
     }
  | StoreMultipleVolatileGPRWord (pit, ra, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_stmvgprw"
       | _ -> "xxxx_stmvgprw" in
     {
       mnemonic = mnemonic;
       operands = [ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [ea])
     }
  | StoreMultipleVolatileSPRWord (pit, ra, cr, lr, ctr, xer, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_stmvsprw"
       | _ -> "xxxx_stmvsprw" in
     {
       mnemonic = mnemonic;
       operands = [ra; cr; lr; ctr; xer; ea];
       ida_asm = (fun f -> f#ops mnemonic [ea])
     }
  | StoreMultipleVolatileSRRWord (pit, ra, srr0, srr1, ea) ->
     let mnemonic =
       match pit with
       | VLE32 -> "e_stmvsrrw"
       | _ -> "xxxx_stmvsrrw" in
     {
       mnemonic = mnemonic;
       operands = [ra; srr0; srr1; ea];
       ida_asm = (fun f -> f#ops mnemonic [ea])
     }
  | StoreWord (pit, dst, ea) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_stw"
       | _ -> "xxxx_stw" in
     {
       mnemonic = mnemonic;
       operands = [dst; ea];
       ida_asm = (fun f -> f#ops mnemonic [dst; ea])
     }
  | StoreWordUpdate (pit, rs, ra, ea) ->
     let mnemonic =
       match pit with
     | VLE32 -> "e_stwu"
     | _ -> "xxxx_stwu" in
     {
       mnemonic = mnemonic;
       operands = [rs; ra; ea];
       ida_asm = (fun f -> f#ops mnemonic [rs; ea])
     }
  | Subtract (pit, dst, src) ->
     let mnemonic =
       match pit with
       | VLE16 -> "se_sub"
       | _ -> "xxxx_sub" in
     {
       mnemonic = mnemonic;
       operands = [dst; src];
       ida_asm = (fun f -> f#ops mnemonic [dst; src])
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

  method ops (s: string) (operands: power_operand_int list) =
    let s = (fixed_length_string s width) in
    let (_, result) =
      List.fold_left
        (fun (isfirst, a) op ->
          if isfirst then
            (false, s ^ " " ^ op#toString)
          else
            (false, a ^ ", " ^ op#toString)) (true, s) operands in
    result

  method no_ops (s: string) = s
end


let power_opcode_to_string ?(width=12) (opc: power_opcode_t) =
  let formatter = new string_formatter_t width in
  let default () = (get_record opc).ida_asm formatter in
  default ()
                  
