(* =============================================================================
   CodeHawk Binary Analyzer
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

(* =============================================================================
   The implementation in this file is based on the documents:

   Intel 64 and IA-32 Architectures Software Developer's Manual, September 2010
   Volume 2A: Instruction Set Reference, A-M
   Volume 2B: Instruction Set Reference, N-Z
   ============================================================================= *)

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHOperand


let pxc0 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md, reg, rm) = decompose_modrm modrm in
  let op1 = get_rm_byte_operand md rm ch RW in
  let op2 = read_immediate_signed_byte_operand ch in
  match reg with

  (* C0/0 ib --- ROL r/m8,imm8 --- Rotate 8 bits r/m8 left imm8 times
     C0/1 ib --- ROR r/m8,imm8 --- Rotate 8 bits r/m8 right imm8 times
     C0/2 ib --- RCL r/m8,imm8 --- Rotate 9 bits (CF,r/m8) left imm8 times
     C0/3 ib --- RCR r/m8,imm8 --- Rotate 9 bits (CF,r/m8) right imm8 times
     C0/4 ib --- SHL r/m8,imm8 --- Multiply r/m8 by 2 imm8 times
     C0/5 ib --- SHR r/m8,imm8 --- Unsigned divide r/m8 by 2, imm8 times
     C0/7 ib --- SAR r/m8,imm8 --- Signed divide r/m8 by 2, imm8 times

     Shl and Sal are the same instruction; both are listed under C0/4. No
     instruction is listed for C0/6. Similar for C1.

     If another instruction exists for C0/6 with a different form, reading of
     op1 and op2 needs to be localized to the individual instructions. Same
     for C1.
   *)

  | 0 -> Rol (op1, op2)
  | 1 -> Ror (op1, op2)
  | 2 -> Rcl (op1, op2)
  | 3 -> Rcr (op1, op2)
  | 4 -> Shl (op1, op2)
  | 5 -> Shr (op1, op2)
  | 7 -> Sar (op1, op2)
  | _ -> Unknown

let pxc1 opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md, reg, rm) = decompose_modrm modrm in
  let op1 = get_rm_def_operand opsize_override md rm ch RW in
  let op2 = read_immediate_signed_byte_operand ch in
  match reg with

  (* C1/0 ib --- ROL r/m32,imm8 --- Rotate 32 bits r/m32 left imm8 times
     C1/1 ib --- ROR r/m32,imm8 --- Rotate 32 bits r/m32 right imm8 times
     C1/2 ib --- RCL r/m32,imm8 --- Rotate 33 bits (CF,r/m32) left imm8 times
     C1/3 ib --- RCR r/m32,imm8 --- Rotate 33 bits (CF,r/m32) right imm8 times
     C1/4 ib --- SHL r/m32,imm8 --- Multiply r/m32 by 2 imm8 times
     C1/5 ib --- SHR r/m32,imm8 --- Unsigned divide r/m32 by 2 imm8 times
     C1/7 ib --- SAR r/m32,imm8 --- Signed divide r/m32 by 2 imm8 times     *)

  | 0 -> Rol (op1, op2)
  | 1 -> Ror (op1, op2)
  | 2 -> Rcl (op1, op2)
  | 3 -> Rcr (op1, op2)
  | 4 -> Shl (op1, op2)
  | 5 -> Shr (op1, op2)
  | 7 -> Sar (op1, op2)
  | _ -> Unknown

(* ===========================================================================
 * C4: 3-byte avx instruction
 * =========================================================================== *)
let pxc4 (ch:pushback_stream_int) =
  let avx1 = ch#read_byte in
  let avx2 = ch#read_byte in
  let opc = ch#read_byte in
  let (_, mm) = decompose_avx_rxb avx1 in
  let (_, xreg, lpp) = decompose_avx_lpp avx2 in
  match opc with

  | 0x00 ->
     begin
       match (mm,lpp) with

       (* VEX.NDS.128.66.0F38.WIG 00 /r --- VPSHUFB xmm1,xmm2,xmm3/m128 ---
          Shuffle bytes in xmm2 according to contents of xmm3/m128
        *)

       | (2, 1) ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD WR in
	  let op3 = xmm_register_op xreg RD in
	  VPackedShuffle ("b", op2, op3, Some op1)

       | _ -> Unknown

    end

  | 0x0f ->
     begin
       match (mm,lpp) with

      (* VEX.NDS.128.66.0F3A.WIG 0F /r ib --- VPALIGNR xmm1,xmm2,xmm3/m128,imm8
         Concatenate xmm2 and xmm3/m128, extract byte aligned result shifted
         to the right by constant value in imm8 and result is stored in xmm1
       *)

       | (3, 1) ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD WR in
	  let op3 = xmm_register_op xreg RD in
	  let op4 = read_immediate_unsigned_byte_operand ch in
	  VPackedAlignRight (op2, op3, op1, op4)

       | _ -> Unknown

    end

  | _ -> Unknown


(* ===========================================================================
 * C5: 2-byte avx instruction
 * =========================================================================== *)
let pxc5 (ch:pushback_stream_int) =
  let avx1 = ch#read_byte in
  let opc = ch#read_byte in
  let (_,xreg,lpp) = decompose_avx_lpp avx1 in
  match opc with
    (* VEX.128.66.0F.WIG 6F /r --- VMOVDQA xmm1,xmm2/m128 ---
       Move aligned packed integer values from xmm2/mem to xmm1

       VEX.128.F3.0F.WIG 6F /r --- VMOVDQU xmm1,xmm2/m128 ---
       Move unaligned packed integer values from xmm2/m128 to xmm1

       VEX.128.66.0F.WIG 7F /r --- VMOVDQA xmm1/m128,xmm2 ---
       Move aligned packed integer values from xmm2 to xmm1/mem

       VEX.128.F3.0F.WIG 7F /r --- VMOVDQU xmm1/m128,xmm2 ---
       Move unaligned packed integer values from xmm2 to xmm1/m128
     *)
  | 0x6f ->
     begin
       match (xreg,lpp)  with

       | (0, 1) ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD WR in
	  VMovdq (true, op2, op1)

       | (0, 2) ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD WR in
	  VMovdq (false, op2, op1)

       | _ -> Unknown

    end

  (* VEX.NDD.128.66.0F.WIG 72 /2 ib --- VPSRLD xmm1, xmm2, imm8    ---
     Shift doublewords in xmm2 right by imm8 while shifting in 0s

     VEX.NDD.128.66.0F.WIG 72 /6 ib --- VPSLLD xmm1, xmm2, imm8
     Shift doublewords in xmm2 left by imm8 while shifting in 0s
   *)

  | 0x72 ->
     let modrm = ch#read_byte in
     let (md, reg, rm) = decompose_modrm modrm in
     begin
       match reg with

       | 2 ->
          let op1 = get_rm_operand md rm ~size:16 ch RD in
	  let op2 = xmm_register_op xreg WR in
	  let op3 = read_immediate_unsigned_byte_operand ch in
	  VPackedShift ("rl", 4, op2, op1, op3)

       | 6 ->
          let op1 = get_rm_operand md rm ~size:16 ch RD in
	  let op2 = xmm_register_op xreg WR in
	  let op3 = read_immediate_unsigned_byte_operand ch in
	  VPackedShift ("ll", 4, op2, op1, op3)

       | _ -> Unknown

    end


    (* VEX.NDD.128.66.0F.WIG 73 /3 ib --- VPSRLDQ xmm1, xmm2, imm8   ---
       Shift xmm2 right by imm8 bytes while shifting in 0s

       VEX.NDD.128.66.0F.WIG 73 /6 ib --- VPSLLQ xmm1, xmm2, imm8    ---
       Shift quadwords in xmm2 left by imm8 while shifting in 0s

       VEX.NDD.128.66.0F.WIG 73 /7 ib --- VPSLLDQ xmm1, xmm2, imm8   ---
       Shift xmm2 left by imm8 bytes while shifting in 0s and store result in
       xmm1
     *)

  | 0x73 ->
     let modrm = ch#read_byte in
     let (md, reg, rm) = decompose_modrm modrm in
     begin
       match reg with

       | 3 ->
          let op1 = get_rm_operand md rm ~size:16 ch RD in
	  let op2 = xmm_register_op xreg WR in
	  let op3 = read_immediate_unsigned_byte_operand ch in
	  VPackedShift ("rl", 16, op2, op1, op3)

       | 6 ->
          let op1 = get_rm_operand md rm ~size:16 ch RD in
	  let op2 = xmm_register_op xreg WR in
	  let op3 = read_immediate_unsigned_byte_operand ch in
	  VPackedShift ("ll", 8, op2, op1, op3)

       | 7 ->
          let op1 = get_rm_operand md rm ~size:16 ch RD in
	  let op2 = xmm_register_op xreg WR in
	  let op3 = read_immediate_unsigned_byte_operand ch in
	  VPackedShift ("ll", 16, op2, op1, op3)

       | _ -> Unknown

     end

  | 0x7f ->
     begin
       match (xreg, lpp) with

       | (0,1) ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 WR RD in
	  VMovdq (true, op1, op2)

       | (0, 2) ->
          let (op1,op2) = get_modrm_xmm_operands ch 16 WR RD in
	  VMovdq (false, op1, op2)

       | _ -> Unknown

    end

  | 0x77 ->
     begin
       match (xreg,lpp) with

       (* VEX.256.0F.WIG 77  --- VZEROALL --- zero all YMM registers *)

       | (0, 4) -> VZeroAll

       | _ -> Unknown

    end

  (* VEX.NDS.128.66.0F.WIG EB /r --- VPOR xmm1, xmm2, xmm3/m128
     Bitwise OR of xmm2/m128 and xmm3
   *)

  | 0xeb ->
     begin
       match lpp with
       | 1 ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD RW in
	  let op3 = xmm_register_op xreg RD in
	  VPackedOp ("or", 16, op2, op3, op1)

       | _ -> Unknown

    end

  (* VEX.NDS.128.66.0F.WIG EF /r --- VPXOR xmm1, xmm2, xmm3/m128 ---
     Bitwise XOR of xmm3/m128 and xmm2
   *)

  | 0xef ->
     begin
       match lpp with
       | 1 ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD RW in
	  let op3 = xmm_register_op xreg RD in
	  VPackedOp ("xor", 16, op2, op3, op1)

       | _ -> Unknown

    end

  (* VEX.NDS.128.66.0F.WIG FC /r --- VPADDB xmm1,xmm2,xmm3/m128 ---
     Add packed byte integers from xmm3/m128 and xmm2
   *)

  | 0xfc ->
     begin
       match lpp with
       | 1 ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD WR in
	  let op3 = xmm_register_op xreg RD in
	  VPackedAdd (false, false, 1, op2, op3, op1)

       | _ -> Unknown

    end

  (* VEX.NDS.128.66.0F.WIG FD /r --- VPADDW xmm1,xmm2,xmm3/m128 ---
     Add packed word integers from xmm3/m128 and xmm2
   *)

  | 0xfd ->
     begin
       match lpp with
       | 1 ->
          let (op1, op2) = get_modrm_xmm_operands ch 16 RD WR in
	  let op3 = xmm_register_op xreg RD in
	  VPackedAdd (false, false, 2, op2, op3, op1)

       | _ -> Unknown

    end

  (* VEX.NDS.128.66.0F.WIG FE /r --- VPADDD xmm1,xmm2,xmm3/m128 ---
     Add packed doubleword integers from xmm3/m128 and xmm2
   *)

  | 0xfe ->
    begin
      match lpp with
      | 1 ->
         let (op1, op2) = get_modrm_xmm_operands ch 16 RD WR in
	 let op3 = xmm_register_op xreg RD in
	 VPackedAdd (false, false, 4, op2, op3, op1)

      | _ -> Unknown

    end

  | _ -> Unknown


let pxc6 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md, reg, rm) = decompose_modrm modrm in
  match reg with

  (* C6/0 --- MOV r/m8,imm8 ---- Move imm8 to r/m8   *)

  | 0 ->
     let op1 = get_rm_byte_operand md rm ch WR in
     let op2 = read_immediate_unsigned_byte_operand ch in
     Mov (1, op1, op2)

  | _ -> Unknown


let pxc7 opsize_override (ch:pushback_stream_int) =
  let opsize = if opsize_override then 2 else 4 in
  let modrm = ch#read_byte in
  let (md, reg, rm) = decompose_modrm modrm in
  match reg with

  (* C7/0 --- MOV r/m32,imm32 ----- Move imm32 to r/m32  *)

  | 0 ->
     let op1 = get_rm_def_operand opsize_override md rm ch WR in
     let op2 = read_immediate_unsigned_operand opsize ch in
     Mov (opsize, op1, op2)

  | _ -> Unknown
