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

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHDisassemblyUtils


let px80 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md, reg, rm) = decompose_modrm modrm in
  let read_operands mode =
    let op1 = get_rm_byte_operand md rm ch mode in
    let op2 = read_immediate_signed_byte_operand ch in
    (op1, op2) in
  match reg with

  (* 80/0 ib --- ADD r/m8,imm8 ---- Add imm8 to r/m8
     80/1 ib --- OR  r/m8,imm8 ---- r/m8 OR r8
     80/2 ib --- ADC r/m8,imm8 ---- Add with carry imm8 to r/m8
     80/3 ib --- SBB r/m8,imm8 ---- Subtract with borrow imm8 from r/m8
     80/4 ib --- AND r/m8,imm8 ---- r/m8 AND r8
     80/5 ib --- SUB r/m8,imm8 ---- Subtract imm8 from r/m8
     80/6 ib --- XOR r/m8,imm8 -----r/m8 XOR r8
     80/7 ib --- CMP r/m8,imm8 ---- Compare imm8 with r/m8 *)

  | 0 ->  let (op1, op2) = read_operands RW in Add (op1, op2)
  | 1 ->  let (op1, op2) = read_operands RW in LogicalOr (op1, op2)
  | 2 ->  let (op1, op2) = read_operands RW in AddCarry (op1, op2)
  | 3 ->  let (op1, op2) = read_operands RW in SubBorrow (op1, op2)
  | 4 ->  let (op1, op2) = read_operands RW in LogicalAnd (op1, op2)
  | 5 ->  let (op1, op2) = read_operands RW in Sub (op1, op2)
  | 6 ->  let (op1, op2) = read_operands RW in Xor (op1, op2)
  | 7 ->  let (op1, op2) = read_operands RD in Cmp (op1, op2)

  | _ ->
    begin
      ch_error_log#add
        "disassembly"
        (STR ("Error in px80. reg value: " ^ (string_of_int reg)));
      raise
        (BCH_failure
           (STR ("Error in px80. reg value: " ^ (string_of_int reg))))
    end


let px81 opsize_override (ch:pushback_stream_int) =
  let opsize = if opsize_override then 2 else 4 in
  let modrm = ch#read_byte in
  let (md, reg, rm) = decompose_modrm modrm in
  let read_operands mode =
    let op1 = get_rm_def_operand opsize_override md rm ch mode in
    let op2 = read_immediate_signed_operand opsize ch in
    (op1, op2) in
  match reg with

  (* 81/0 id --- ADD r/m32,imm32 ---- Add imm32 to r/m32
     81/1 id --- OR  r/m32,imm32 ---- r/m32 OR r32
     81/2 id --- ADC r/m32,imm32 ---- Add with CF imm32 to r/m32
     81/3 id --- SBB r/m32,imm32 ---- Subtract with borrow imm32 from r/m32
     81/4 id --- AND r/m32,imm32 ---- r/m32 AND r32
     81/5 id --- SUB r/m32,imm32 ---- subtract imm32 from r/m32
     81/6 id --- XOR r/m32,imm32 ---- r/m32 XOR r32
     81/7 id --- CMP r/m32,imm32 ---- compare imm32 with r/m32    *)

  | 0 ->  let (op1, op2) = read_operands RW in Add (op1, op2)
  | 1 ->  let (op1, op2) = read_operands RW in LogicalOr (op1, op2)
  | 2 ->  let (op1, op2) = read_operands RW in AddCarry (op1, op2)
  | 3 ->  let (op1, op2) = read_operands RW in SubBorrow (op1, op2)
  | 4 ->  let (op1, op2) = read_operands RW in LogicalAnd (op1, op2)
  | 5 ->  let (op1, op2) = read_operands RW in Sub (op1, op2)
  | 6 ->  let (op1, op2) = read_operands RW in Xor (op1, op2)
  | 7 ->  let (op1, op2) = read_operands RD in Cmp (op1, op2)

  | _ ->
    begin
      ch_error_log#add
        "disassembly"
        (STR ("Error in px81. reg value: " ^ (string_of_int reg)));
      raise
        (BCH_failure
           (STR ("Error in px81. reg value: " ^ (string_of_int reg))))
    end


let px83 opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md, reg, rm) = decompose_modrm modrm in
  let read_operands mode =
    let op1 = get_rm_def_operand opsize_override md rm ch mode in
    let op2 = (read_immediate_signed_byte_operand ch)#sign_extend 4 in
    (op1, op2) in

  match reg with

  (* 83/0 ib --- ADD r/m32,imm8 ----
     Add sign-extended imm8 to r/m32

     83/1 ib --- OR  r/m32,imm8 ----
     r/m32 or imm8 (sign-extended)

     83/2 ib --- ADC r/m32,imm8 ----
     Add with CF sign extended imm8 into r/m32

     83/3 ib --- SBB r/m32,imm8 ----
     Subtract with borrow sign-extended imm8 from r/m32

     83/4 ib --- AND r/m32,imm8 ----
     r/m32 AND imm8 (sign-extended)

     83/5 ib --- SUB r/m32,imm8 ----
     Subtract sign-extended imm8 from r/m32

     83/6 ib --- XOR r/m32,imm8 ----
     r/m32 XOR imm8 (sign-extended)

     83/7 ib --- CMP r/m32,imm8 ----
     Compare sign-extended imm8 with r/m32
   *)

  | 0 ->  let (op1, op2) = read_operands RW in Add (op1, op2)
  | 1 ->  let (op1, op2) = read_operands RW in LogicalOr (op1, op2)
  | 2 ->  let (op1, op2) = read_operands RW in AddCarry (op1, op2)
  | 3 ->  let (op1, op2) = read_operands RW in SubBorrow (op1, op2)
  | 4 ->  let (op1, op2) = read_operands RW in LogicalAnd(op1, op2)
  | 5 ->  let (op1, op2) = read_operands RW in Sub (op1, op2)
  | 6 ->  let (op1, op2) = read_operands RW in Xor (op1, op2)
  | 7 ->  let (op1, op2) = read_operands RD in Cmp (op1, op2)

  | _ ->
    begin
      ch_error_log#add
        "disassembly"
        (STR ("Error in px83: " ^ (string_of_int reg)));
      raise
        (BCH_failure
           (STR ("Error in px83. reg value: " ^ (string_of_int reg))))
    end


let px8f (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* 8F/0 --- POP r/m32 ---- Pop top of stack into m32, increment stack pointer *)

  | 0 -> let op = get_rm_operand md rm ch WR in Pop (4, op)

  | _ -> Unknown
