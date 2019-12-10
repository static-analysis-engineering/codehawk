(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHOperand
open BCHX86Opcodes


let pxd0 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with
    
  (* D0/0 --- ROL r/m8,1 --- Rotate 8 bits r/m8 left, once
     D0/1 --- ROR r/m8,1 --- Rotate 8 bits r/m8 right, once
     D0/2 --- RCL r/m8,1 --- Rotate 9 bits (CF,r/m8) left once
     D0/3 --- RCR r/m8,1 --- Rotate 9 bits (CF,r/m8) right once
     D0/4 --- SHL r/m8,1 --- Multiply r/m8 by 2, once
     D0/5 --- SHR r/m8,1 --- Unsigned divide r/m8 by 2, once
     D0/6 --- SAL r/m8,1 --- Multiply r/m8 by 2, once          (not documented, encountered in use)
     D0/7 --- SAR r/m8,1 --- Signed divide r/m8 by 2, once 

     The shift arithmetic right (SAR) instruction shifts the bits of the
     destination (first) operand to the right. For each shift count the
     least significant bit of the destination operand is shifted into the
     CF flag, and the most significant bit is set or cleared to correspond
     with the sign of the original value in the destination operand.

     Shl and Sal are the same operation (both are listed under D0/4);
     no instruction is listed for D0/6. Similar for D1, D2, and D3.
*)

  | 0 -> let op = get_rm_byte_operand md rm ch RW in Rol (op,imm1_operand)
  | 1 -> let op = get_rm_byte_operand md rm ch RW in Ror (op,imm1_operand)
  | 2 -> let op = get_rm_byte_operand md rm ch RW in Rcl (op,imm1_operand)
  | 3 -> let op = get_rm_byte_operand md rm ch RW in Rcr (op,imm1_operand)
  | 4 -> let op = get_rm_byte_operand md rm ch RW in Shl (op,imm1_operand)
  | 5 -> let op = get_rm_byte_operand md rm ch RW in Shr (op,imm1_operand)
  | 6 -> let op = get_rm_byte_operand md rm ch RW in Shl (op,imm1_operand)
  | 7 -> let op = get_rm_byte_operand md rm ch RW in Sar (op,imm1_operand)

  | _ -> Unknown

let pxd1 opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* D1/0 --- ROL r/m32,1 ---- Rotate 32 bits left once
     D1/1 --- ROR r/m32,1 ---- Rotate 32 bits right once
     D1/2 --- RCL r/m32,1 ---- Rotate 33 bits (CF,r/m32) left once
     D1/3 --- RCR r/m32,1 ---- Rotate 33 bits (CF,r/m32) right once
     D1/4 --- SHL r/m32,1 ---- Multiply r/m32 by 2, once
     D1/5 --- SHR r/m32,1 ---- Unsigned divide r/m32 by 2, once
     D1/6 --- SAL r/m32,1 ---- Multiply r/m32 by 2, once (not documented, encountered in use)
     D1/7 --- SAR r/m32,1 ---- Signed divide r/m32 by 2, once *)

  | 0 -> let op = get_rm_def_operand opsize_override md rm ch RW in Rol(op,imm1_operand)
  | 1 -> let op = get_rm_def_operand opsize_override md rm ch RW in Ror(op,imm1_operand)
  | 2 -> let op = get_rm_def_operand opsize_override md rm ch RW in Rcl(op,imm1_operand)
  | 3 -> let op = get_rm_def_operand opsize_override md rm ch RW in Rcr(op,imm1_operand)
  | 4 -> let op = get_rm_def_operand opsize_override md rm ch RW in Shl(op,imm1_operand)
  | 5 -> let op = get_rm_def_operand opsize_override md rm ch RW in Shr(op,imm1_operand)
  | 6 -> let op = get_rm_def_operand opsize_override md rm ch RW in Shl(op,imm1_operand)
  | 7 -> let op = get_rm_def_operand opsize_override md rm ch RW in Sar(op,imm1_operand)

  | _ -> Unknown

let pxd2 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* D2/0 --- ROL r/m8,CL ---- Rotate 8 bits r/m8 left CL times
     D2/1 --- ROR r/m8,CL ---- Rotate 8 bits r/m8 right CL times
     D2/2 --- RCL r/m8,CL ---- Rotate 9 bits (CF,r/m8) left CL times
     D2/3 --- RCR r/m8,CL ---- Rotate 9 bits (CF,r/m8) right CL times
     D2/4 --- SHL r/m8,CL ---- Multiply r/m8 by 2, CL times    
     D2/5 --- SHR r/m8,CL ---- Unsigned divide r/m8 by 2, CL times
     D2/6 --- SHL r/m8,CL ---- Multiply r/m8 by 2, CL times (undocumented)
     D2/7 --- SAR r/m8,CL ---- Signed divide r/m8 by 2, CL times
   *)

  | 0 -> let op = get_rm_byte_operand md rm ch RW in Rol (op,cl_r RD)
  | 1 -> let op = get_rm_byte_operand md rm ch RW in Ror (op,cl_r RD)
  | 2 -> let op = get_rm_byte_operand md rm ch RW in Rcl (op,cl_r RD)
  | 3 -> let op = get_rm_byte_operand md rm ch RW in Rcr (op,cl_r RD)
  | 4 -> let op = get_rm_byte_operand md rm ch RW in Shl (op,cl_r RD)
  | 5 -> let op = get_rm_byte_operand md rm ch RW in Shr (op,cl_r RD)
  | 6 -> let op = get_rm_byte_operand md rm ch RW in Shl (op,cl_r RD)
  | 7 -> let op = get_rm_byte_operand md rm ch RW in Sar (op,cl_r RD)

  | _ -> Unknown


let pxd3 opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* D3/0 --- ROL r/m32, CL ---- Rotate 32 bits r/m32 left CL times
     D3/1 --- ROR r/m32, CL ---- Rotate 32 bits r/m32 right CL times
     D3/2 --- RCL r/m32, CL ---- Rotate 33 bits (CF,r/m32) left CL times
     D3/3 --- RCR r/m32, CL ---- Rotate 33 bits (CF,r/m32) right CL times
     D3/4 --- SHL r/m32, CL ---- Multiply r/m32 by 2, CL times
     D3/5 --- SHR r/m32, CL ---- Unsigned divide r/m32 by 2, CL times 
     D3/6 --- SHL r/m32, CL ---- Multiply r/m32 by 2, CL times (not documented)
     D3/7 --- SAR r/m32, CL ---- Signed divide r/m32 by 2, CL times
   *)

  | 0 -> let op = get_rm_def_operand opsize_override md rm ch RW in Rol (op,cl_r RD)
  | 1 -> let op = get_rm_def_operand opsize_override md rm ch RW in Ror (op,cl_r RD)
  | 2 -> let op = get_rm_def_operand opsize_override md rm ch RW in Rcl (op,cl_r RD)
  | 3 -> let op = get_rm_def_operand opsize_override md rm ch RW in Rcr (op,cl_r RD)
  | 4 -> let op = get_rm_def_operand opsize_override md rm ch RW in Shl (op,cl_r RD)
  | 5 -> let op = get_rm_def_operand opsize_override md rm ch RW in Shr (op,cl_r RD)
  | 6 -> let op = get_rm_def_operand opsize_override md rm ch RW in Shl (op,cl_r RD) 
  | 7 -> let op = get_rm_def_operand opsize_override md rm ch RW in Sar (op,cl_r RD)

  | _ -> Unknown 

let pxd8 opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  match modrm with

  (* D8 C0+i --- FADD ST(0),ST(i) -- Add st(0) to st(i) and store result in st(0) *)

  | 0xc0 | 0xc1 | 0xc2 | 0xc3 | 0xc4 | 0xc5 | 0xc6 | 0xc7 ->
    Fadd (false, true, 10, fpu_register_op 0 RW, fpu_register_op (modrm - 0xc0) RD)

  (* D8 C8+i --- FMUL ST(0),ST(i) --- Multiply ST(0) by ST(i) and store result in ST(0) *)

  | 0xc8 | 0xc9 | 0xca | 0xcb | 0xcc | 0xcd | 0xce | 0xcf ->
    Fmul (false, true, 10, fpu_register_op 0 RW, fpu_register_op (modrm - 0xc8) RD)
    
  (* D8 D0+ ---- FCOM ST(i) --- Compare ST(0) with ST(i)  
     D8 D8+ ---- FCOMP ST(i) -- Compare ST(0) with ST(i) and pop register stack *)

  | 0xd0 | 0xd1 | 0xd2 | 0xd3 | 0xd4 | 0xd5 | 0xd6 | 0xd7 ->
    Fcom (0, true, 10, fpu_register_op (modrm - 0xd0) RD)

  | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
    Fcom (1, true, 10, fpu_register_op (modrm - 0xd8) RD)

  (* D8 E0+i ---- FSUB ST(0),ST(i)  --- Subtract ST(i) from ST(0) and store result in ST(0) *)

  | 0xe0 | 0xe1 | 0xe2 | 0xe3 | 0xe4 | 0xe5 | 0xe6 | 0xe7 ->
    Fsub (false, true, 10, fpu_register_op 0 RW, fpu_register_op (modrm - 0xe0) RD)

  (* D8 E8+i ---- FSUBR ST(0),ST(i) --- Subtract ST(0) from ST(i) and store result in ST(0) *)

  | 0xe8 | 0xe9 | 0xea | 0xeb | 0xec | 0xed | 0xee | 0xef ->
    Fsubr (false, true, 10, fpu_register_op 0 RW, fpu_register_op (modrm - 0xf0) RD)

  (* D8 F0+i ---- FDIV ST(0),ST(i) --- Divide ST(0) by ST(i) and store result in ST(0)  *)

  | 0xf0 | 0xf1 | 0xf2 | 0xf3 | 0xf4 | 0xf5 | 0xf6 | 0xf7 ->
    Fdiv (false, true, 10, fpu_register_op 0 RW, fpu_register_op (modrm - 0xf0) RD)

  (* D8 F8+i ---- FDIVR ST(i),ST(0) --- Divide ST(i) by ST(0) and store result in ST(0) *)

  | 0xf8 | 0xf9 | 0xfa | 0xfb | 0xfc | 0xfd | 0xfe | 0xff ->
    Fdivr (false, true, 10, fpu_register_op 0 RW, fpu_register_op (modrm - 0xf8) RD)

  | _ ->
      let (md,reg,rm) = decompose_modrm modrm in
      match reg with

      (* D8/0 ---- FADD m32fp ---- Add m32fp to st(0) and store result in st(0) 
         D8/1 ---- FMUL m32fp ---- Multiply ST(0) by m32fp and store result in ST(0) *)

      | 0 -> let op = get_rm_operand md rm ch RD in 
	     Fadd (false, true, 4, fpu_register_op 0 RW, op)
	       
      | 1 -> let op = get_rm_operand md rm ch RD in	
	     Fmul (false, true, 4, fpu_register_op 0 RW, op)

      (* D8/2 ---- FCOM m32fp ---- Compare ST(0) with m32fp
	 D8/3 ---- FCOMP m32fp --- Compare ST(0) with m32fp and pop register stack *)

      | 2 -> let op = get_rm_operand md rm ch RD in Fcom (0,true,4, op)
      | 3 -> let op = get_rm_operand md rm ch RD in Fcom (1,true,4, op)

      (* D8/4 ---- FSUB m32fp ---- Subtract m32fp from ST(0) and store result in ST(0) 
	 D8/5 ---- FSUBR m32fp ---- Subtract ST(0) from m32fp and store result in ST(0)
         D8/6 ---- FDIV m32fp ---- Divide ST(0) by m32fp and store result in ST(0) 
	 D8/7 ---- FDIVR m32fp ---- Divide m32fp by ST(0) and store result in ST(0) *)

      | 4 -> let op = get_rm_operand md rm ch RD in Fsub  (false,true,4,fpu_register_op 0 RW, op)
      | 5 -> let op = get_rm_operand md rm ch RD in Fsubr (false,true,4,fpu_register_op 0 RW, op)
      | 6 -> let op = get_rm_operand md rm ch RD in Fdiv  (false,true,4,fpu_register_op 0 RW, op)
      | 7 -> let op = get_rm_operand md rm ch RD in Fdivr (false,true,4,fpu_register_op 0 RW,op)

      | _ -> Unknown

let pxd9 opsize_override (ch:pushback_stream_int) = 
  let modrm = ch#read_byte in
  match modrm with

  (* D9 C0+i  ---- FLD ----- Push ST(i) onto the FPU register stack     *)

  | 0xc0 | 0xc1 | 0xc2 | 0xc3 | 0xc4 | 0xc5 | 0xc6 | 0xc7 -> 
    FLoad (true, 10, fpu_register_op (modrm - 0xc0) RD)

  (* D9 C8+i  ---- FXCH ---- Exchange the contents of ST(0) and ST(i)   *)

  | 0xc8 | 0xc9 | 0xca | 0xcb | 0xcc | 0xcd | 0xce | 0xcf -> 
    Fxch (fpu_register_op (modrm - 0xc8) RW)

  (* D9 E0 ---- FCHS ---- Complement sign of st(0) 
     D9 E1 ---- FABS ---- Replace st(0) with its absolute value 
     D9 E4 ---- FTST ---- Compare ST(0) with 0.0.
     D9 E5 -----FXAM ---- Examines the contents of ST(0) register *)

  | 0xe0 -> FStackOp ("fchs", "complement sign of ST(0)")
  | 0xe1 -> FStackOp ("fabs", "replace ST(0) with absolute value of ST(0)")
  | 0xe4 -> FStackOp ("ftst", "compare ST(0) with 0.0")
  | 0xe5 -> FStackOp ("fxam", "classify value or number in ST(0)")

  (* D9 E8 ---- FLD1 ---- Push +1.0 onto the FPU register stack
     D9 E9 ---- FLDL2T -- Push log_2 10 onto the FPU register stack
     D9 EA ---- FLDL2E -- Push log_2 e onto the FPU register stack
     D9 EB ---- FLDPI --- Push pi onto the FPU register stack
     D9 EC ---- FLDLG2 -- Push log_10 2 onto the FPU register stack
     D9 ED ---- FLDLN2 -- Push log_e 2 onto the FPU register stack
     D9 EE ---- FLDZ ---- Push +0.0 onto the FPU register stack  *)

  | 0xe8 -> FLoadConstant ("1", "+1.0")
  | 0xe9 -> FLoadConstant ("l2t", "log_2 of 10")
  | 0xea -> FLoadConstant ("l2e", "log_2 of e")
  | 0xeb -> FLoadConstant ("pi", "pi") 
  | 0xec -> FLoadConstant ("lg2", "log_10 of 2")
  | 0xed -> FLoadConstant ("ln2", "log_e of 2")
  | 0xee -> FLoadConstant ("z", "+0.0")

  (* D9 F0 ---- F2XM1 --- Replace ST(0) with 2^(st(0))-1  
     D9 F1 ---- FYL2X --- Replace ST(1) with (ST(1) ∗ log2ST(0)) and pop the register stack.
     D9 F2 ---- FPTAN --- Replace ST(0) with its approximate tangent and push 1 onto 
                          the FPU stack
     D9 F3 ---- FPATAN -- Replace ST(1) with arctan(ST(1)/ST(0)) and pop the register stack

     D9 F5 ---- FPREM1 -- Replace ST(0) with the IEEE remainder obtained from dividing 
                          ST(0) by ST(1).

     D9 F6 ---- FDECSTP - Decrement TOP field in FPU status word

     D9 F7 ---- FINCSTP - Increment the TOP field in the FPU status register.

     D9 F9 ---- FYL2XP1 - Replace ST(1) with ST(1) ∗ log2(ST(0) + 1.0) and pop the register 
                          stack
     D9 FA ---- FSQRT --- Computes square root of ST(0) and stores the result in ST(0) 
     D9 FB ---- FSINCOS - Compute the sine and cosine of ST(0); replace ST(0) with 
                          the approximate sine, and push the approximate cosine onto 
                          the register stack
     D9 FC ---- FRNDINT -- Round ST(0) to an integer
     D9 FE ---- FSIN  --- Replace ST(0) with its sine
     D9 FF ---- FCOS  --- Replace ST(0) with its cosine
  *)

  | 0xf0 -> FStackOp ("f2xm1", "replace ST(0) with 2^(ST(0)-1)")
  | 0xf1 -> FStackOp ("fyl2x", "replace ST(1) with (ST(1) ∗ log2ST(0)) and pop")
  | 0xf2 -> FStackOp ("fptan", "replace ST(0) with its tangent and push 1")
  | 0xf3 -> FStackOp ("fpatan", "replace ST(1) with arctan(ST(1)/ST(0)) and pop")
  | 0xf5 -> FStackOp ("fprem1", "replace ST(1) with IEEE remainder ST(0)/ST(1)")
  | 0xf6 -> FStackOp ("fdecstp", "decrement TOP field in FPU status word")
  | 0xf7 -> FStackOp ("fincstp", "increment the TOP field in the FPU status register")
  | 0xf9 -> FStackOp ("fyl2xp1", "replace ST(1) with ST(1) ∗ log2(ST(0) + 1.0) and pop")
  | 0xfa -> FStackOp ("fsqrt", "replace ST(0) with its square root")
  | 0xfb -> FStackOp ("fsincos", "replace ST(0) with its sine and push the cosine")
  | 0xfc -> FStackOp ("frndint", "round ST(0) to an integer")
  | 0xfe -> FStackOp ("fsin" , "replace ST(0) with its sine")
  | 0xff -> FStackOp ("fcos" , "replace ST(0) with its cosine") 

  | _ ->
      let (md,reg,rm) = decompose_modrm modrm in
      match reg with

      (* D9/0 --- FLD m32fp --- push mf32p onto the FPU register stack      
	 D9/2 --- FST m32fp --- Copy st(0) to m32fp
	 D9/3 --- FSTP mf32p -- Copy st(0) to m32fp and pop register stack   
	 D9/4 --- FLDENV m14/28byte --- Load FPU environment from m15byte or m28byte
	 D9/5 --- FLDCW m2byte -- Load FPU control word from m2byte       
	 D9/6 --- FNSTENV m14/28byte --- Store FPU environment to m14byte or m28byte
	 without checking for pending unmasked floating point exceptions
	 D9/7 --- FNSTCW m2byte - Store FPU control word to m2byte without checking
         for pending unmasked floating point exceptions   *)
	
      | 0 -> let op = get_rm_operand md rm ch RD in FLoad  (true,4,op)
      | 2 -> let op = get_rm_operand md rm ch WR in FStore (false, true, 4, op)
      | 3 -> let op = get_rm_operand md rm ch WR in FStore (true, true, 4, op)
      | 4 -> let size = if opsize_override then 14 else 28 in
	     let op = get_rm_operand md rm ~size ch WR in 
	     FLoadState ("env",size,op)

      | 5 -> let op = get_rm_word_operand md rm ch RD in FLoadState ("cw",2,op)
      | 6 -> let size = if opsize_override then 14 else 28 in
	     let op = get_rm_operand md rm ~size ch WR in 
	     FStoreState ("env",false,size,op)
	       
      | 7 -> let op = get_rm_word_operand md rm ch WR in FStoreState ("cw",false, 2, op)
	  
      | _ -> Unknown


let pxda opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  match modrm with 

  (* DA E9 ---- FUCOMPP ---- Compare ST(0) with ST(1) and pop register twice       *)

  | 0xe9 -> Fucom (2, fpu_register_op 1 RD)

  | _ ->
      let (md,reg,rm) = decompose_modrm modrm in
      match reg with
	
      (* DA/0 --- FIADD m32int  --- Add m32int to st(0) and store result in st(0) 
	 DA/1 --- FIMUL m32int  --- Multiply ST(0) by m32int and store result in ST(0) 
	 DA/2 --- FICOM m32int  --- Compare ST(0) with m32int
	 DA/3 --- FICOMP m32int --- Compare ST(0) with m32int and pop stack register
	 DA/4 --- FISUB m32int  --- Subtract m32int from ST(0) and store result in ST(0) 
	 DA/5 --- FISUBR m32int --- Subtract ST(0) from m32int and store result in ST(0)
         DA/6 --- FIDIV m32int  --- Divide ST(0) by m32int and store result in ST(0) 
         DA/7 --- FIDIVR m32int --- Divide m32int by ST(0) and store result in ST(0) *)

      | 0 -> let op = get_rm_operand md rm ch RD in 
	     Fadd  (false,false,4,fpu_register_op 0 RW, op)

      | 1 -> let op = get_rm_operand md rm ch RD in 
	     Fmul  (false,false,4,fpu_register_op 0 RW, op)
	       
      | 2 -> let op = get_rm_operand md rm ch RD in 
	     Fcom  (0,false,4,op)

      | 3 -> let op = get_rm_operand md rm ch RD in
	     Fcom  (1,false,4,op)

      | 4 -> let op = get_rm_operand md rm ch RD in 
	     Fsub  (false,false,4,fpu_register_op 0 RW, op)

      | 5 -> let op = get_rm_operand md rm ch RD in 
	     Fsubr (false,false,4,fpu_register_op 0 RW, op)

      | 6 -> let op = get_rm_operand md rm ch RD in 
	     Fdiv  (false,false,4,fpu_register_op 0 RW, op)
	       
      | 7 -> let op = get_rm_operand md rm ch RD in 
	     Fdivr (false,false,4,fpu_register_op 0 RW, op)

      | _ -> Unknown


let pxdb opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in 
  match modrm with
  (* DB C8+i -- FCMOVNE ST(0),ST(i) -- move if not equal (ZF = 0) *)


  (* DB E2 --- FNCLEX --- clear floating point exception flags without checking
                          pending  unmasked floating point exceptions         
     DB E3 --- FNINIT --- Initialize FPU without checking for pending unmasked floating
		          point exceptions                                              *)

  | 0xe2 -> Fclex false
  | 0xe3 -> Finit false

  (* DB E8+i ---- FUCOMI ST(0),ST(i) --- Compare ST(0) with ST(i) and set EFlags *)

  | 0xe8 | 0xe9 | 0xea | 0xeb | 0xec | 0xed | 0xee | 0xef ->
    Fcomi (false,true, fpu_register_op (modrm - 0xe8) RD)

  (* DB F0+i ---- FCOMI ST(0),ST(i) --- Compare ST(0) with ST(i) and set EFlags *)
      
  | 0xf0 | 0xf1 | 0xf2 | 0xf3 | 0xf4 | 0xf5 | 0xf6 | 0xf7 ->
    Fcomi (false,false, fpu_register_op (modrm - 0xf0) RD)

  | _ ->
      let (md,reg,rm) = decompose_modrm modrm in
      match reg with
	
      (* DB/0 --- FILD m32int --- Push m32int onto the FPU register stack     
	 DB/2 --- FIST m32int --- Store ST(0) in m32 int                      
	 DB/3 --- FISTP m32int -- Store st(0) in m32int and pop register stack 
	 DB/5 --- FLD m80fp   --- Push m80fp onto the FPU register stack         
         DB/7 --- FSTP m80fp  --- Copy ST(0) to m80fp and pop register stack *)

      | 0 -> let op = get_rm_operand md rm ch RD in FLoad  (false,4,op) 
      | 2 -> let op = get_rm_operand md rm ch WR in FStore (false, false, 4, op)
      | 3 -> let op = get_rm_operand md rm ch WR in FStore (true , false, 4, op)
      | 5 -> let op = get_rm_operand md rm ~size:10 ch RD in FLoad  (true,10, op)
      | 7 -> let op = get_rm_operand md rm ~size:10 ch WR in FStore (true, true, 10, op)

      | _ -> Unknown


let pxdc opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  match modrm with

  (* DC C0+i ---- FADD ST(i),ST(0) ---- Add st(i) to st(0) and store result in st(i)  *)

  | 0xc0 | 0xc1 | 0xc2 | 0xc3 | 0xc4 | 0xc5 | 0xc6 | 0xc7 ->
    Fadd (false, true, 10, fpu_register_op (modrm - 0xc0) RW, fpu_register_op 0 RD)

  (* DC C8+i ---- FMUL ST(i),ST(0) --- Multiply ST(i) by ST(0) and store result in ST(i) *)

  | 0xc8 | 0xc9 | 0xca | 0xcb | 0xcc | 0xcd | 0xce | 0xcf ->
    Fmul (false, true, 10, fpu_register_op (modrm - 0xc8) RW, fpu_register_op 0 RD)

  (* DC E0+i ---- FSUBR ST(i),ST(0) --- Subtrach ST(i) from ST(0) and store result in ST(i) *)
			
  | 0xe0 | 0xe1 | 0xe2 | 0xe3 | 0xe4 | 0xe5 | 0xe6 | 0xe7 ->
    Fsubr (false, true, 10, fpu_register_op (modrm - 0xe0) RW, fpu_register_op 0 RD)

  (* DC E8+i ---- FSUB ST(i),ST(0)  --- Subtract ST(0) from ST(i) and store result in ST(i) *)

  | 0xe8 | 0xe9 | 0xea | 0xeb | 0xec | 0xed | 0xee | 0xef ->
    Fsub (false, true, 10, fpu_register_op (modrm - 0xe8) RW, fpu_register_op 0 RD)

  (* DC F0+i ---- FDIVR ST(i),ST(0) --- Divide ST(0) by ST(i) and store result in ST(i)  *)

  | 0xf0 | 0xf1 | 0xf2 | 0xf3 | 0xf4 | 0xf5 | 0xf6 | 0xf7 ->
    Fdivr (false, true, 10, fpu_register_op (modrm - 0xf0) RW, fpu_register_op 0 RD)

  (* DC F8+i ---- FDIV  ST(i),ST(0) --- Divide ST(i) by ST(0) and store result in ST(i) *)

  | 0xf8 | 0xf9 | 0xfa | 0xfb | 0xfc | 0xfd | 0xfe | 0xff ->
    Fdiv (false, true, 10, fpu_register_op (modrm - 0xf8) RW, fpu_register_op 0 RD)

  | _ ->
    let (md,reg,rm) = decompose_modrm modrm in
    match reg with
      
     (* DC/0 --- FADD m64fp  --- Add m64fp to ST(0) and store result in ST(0) 
        DC/1 --- FMUL m64fp  --- Multiply st(0) by m64fp and store result in st(0) 
	DC/2 --- FCOM  m64fp --- Compare ST(0) with m64fp
	DC/3 --- FCOMP m64fp --- Compare st(0) with m64fp  and pop register stack 
	DC/4 --- FSUB m64fp  --- Subtract m64fp from st(0) and store result in st(0)
	DC/5 --- FSUBR m64fp --- Subtract st(0) from m64fp and store result in st(0)
	DC/6 --- FDIV m64fp  --- Divide st(0) by m64fp and store result in st(0)       
        DC/7 --- FDIVR m64fp --- Divide m64fp by ST(0) and store result in ST(0)    *)
     
     | 0 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fadd (false,true,8,fpu_register_op 0 RW, op)

     | 1 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fmul (false,true,8,fpu_register_op 0 RW, op)
	      
     | 2 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fcom (0,true,8, op)
	      
     | 3 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fcom (1,true,8, op)

     | 4 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fsub  (false,true,8,fpu_register_op 0 RW, op)

     | 5 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fsubr (false,true,8,fpu_register_op 0 RD, op)

     | 6 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fdiv  (false,true,8,fpu_register_op 0 RW, op)  
	      
     | 7 -> let op = get_rm_operand md rm ~size:8 ch RD in 
	    Fdivr (false,true,8,fpu_register_op 0 RW, op)
     
     | _ -> Unknown


let pxdd opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  match modrm with

  (* DD D0+i ---- FST ST(i) --- Copy ST(0) to ST(i) *)

  | 0xd0 | 0xd1 | 0xd2 | 0xd3 | 0xd4 | 0xd5 | 0xd6 | 0xd7 ->
    FStore (false, true, 10, fpu_register_op (modrm - 0xd0) WR)

  (* DD D8+i ---- FSTP ST(i) ---- Copy ST(0) to ST(i) and pop register stack *)

  | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
    FStore (true, true, 10, fpu_register_op (modrm - 0xd8) WR)

  (* DD E0+i ---- FUCOM ST(i),ST(0) ---- Unordered comparison of ST(0) with ST(i)   
     DD E8+i ---- FUCOM ST(i),ST(0) ---- Unordered comparison of ST(0) with ST(i) 
                                         and pop register stack   *)

  | 0xe0 | 0xe1 | 0xe2 | 0xe3 | 0xe4 | 0xe5 | 0xe6 | 0xe7 -> 
    Fucom (0, fpu_register_op (modrm - 0xe0) RD)

  | 0xe8 | 0xe9 | 0xea | 0xeb | 0xec | 0xed | 0xee | 0xef -> 
    Fucom (1, fpu_register_op (modrm - 0xe8) RD)

  | _ ->
    let (md,reg,rm) = decompose_modrm modrm in
    match reg with
	
    (* DD/0 --- FLD m64fp  --- Push m64fp onto FPU register stack                
       DD/2 --- FST  m64fp --- Copy ST(0) to m64fp 
       DD/3 --- FSTP m64fp --- Copy ST(0) to m64fp and pop register               *)
      
    | 0 -> let op = get_rm_operand md rm ~size:8 ch RD in FLoad  (true,8,op)
    | 2 -> let op = get_rm_operand md rm ~size:8 ch WR in FStore (false, true, 8, op)				
    | 3 -> let op = get_rm_operand md rm ~size:8 ch WR in FStore (true , true, 8, op)

    (* DD/4 ---- FRSTOR m94/128byte --- Load FPU state from m94byte or m108byte  *)

    | 4 -> let op = get_rm_operand md rm ~size:16 ch RD in FRestoreState op

    (* DD/6  --- FNSAVE m94/128byte --- Store FPU environment to m94byte or m108byte 
                                        without checking for pending unmasked 
                                        floating- point exceptions. Then 
                                        re-initialize the FPU                     *)

    | 6 -> let op = get_rm_operand md rm ~size:16 ch WR in FSaveState (false, op)
					
    (* DD/7 --- FNSTW m2byte --- Store FPU status word at m2byte without checking for
                                   pending unmasked floating point exceptions           *)

    | 7 -> let op = get_rm_word_operand md rm ch WR in FStoreState ("sw",false, 2,op)
						    
    | _ -> Unknown

let pxde opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  match modrm with

  (* DE C0+i --- FADDP ST(i),ST(0) --- Add st(0) to st(i), store result in st(i)
                                       and pop the register stack               *)

  | 0xc0 | 0xc1 | 0xc2 | 0xc3 | 0xc4 | 0xc5 | 0xc6 | 0xc7 ->
    Fadd (true, true, 10, fpu_register_op (modrm - 0xc0) RW, fpu_register_op 0 RD)

  (* DE C8+i --- FMULP ST(i),ST(0) --- Multiply ST(i) by ST(0) and store result
                                       in ST(i) and pop the register stack      *)

  | 0xc8 | 0xc9 | 0xca | 0xcb | 0xcc | 0xcd | 0xce | 0xcf ->
    Fmul (true, true, 10, fpu_register_op (modrm - 0xc8) RW, fpu_register_op 0 RD)

  (* DE D9 ---- FCOMPP ---- Compare ST(0) with ST(1) and pop register stack twice *)

  | 0xd9 -> Fcom (2, true, 10, fpu_register_op 1 RD)

  (* DE E0+i --- FSUBRP ST(i),ST(0) --- Subtract ST(i) from ST(0), store result in
                                        ST (i) and pop the register stack          *)

  | 0xe0 | 0xe1 | 0xe2 | 0xe3 | 0xe4 | 0xe5 | 0xe6 | 0xe7 ->
    Fsubr (true, true, 10, fpu_register_op (modrm - 0xe0) RW, fpu_register_op 0 RD)

  (* DE E8+i --- FSUBP ST(i),ST(0) --- Subtract ST(0) from ST(i), store result in
                                       ST(i) and pop register stack                *)

  | 0xe8 | 0xe9 | 0xea | 0xeb | 0xec | 0xed | 0xee | 0xef ->
    Fsub (true, true, 10, fpu_register_op (modrm - 0xe8) RW, fpu_register_op 0 RD)

  (* DE F0+i ---- FDIVRP ST(i),ST(0) --- Divide ST(0) by ST(i), store the result in
                                         ST(i) and pop register stack               *)

  | 0xf0 | 0xf1 | 0xf2 | 0xf3 | 0xf4 | 0xf5 | 0xf6 | 0xf7 ->
    Fdivr (true, true, 10, fpu_register_op (modrm - 0xf0) RW, fpu_register_op 0 RD)

  (* DE F8+i ---- FDIVP ST(i),ST(0) --- Divide ST(i) by ST(0), store the result in 
                                        ST(i) and pop register stack                *)

  | 0xf8 | 0xf9 | 0xfa | 0xfb | 0xfc | 0xfd | 0xfe | 0xff ->
    Fdiv (true, true, 10, fpu_register_op (modrm - 0xf8) RW, fpu_register_op 0 RD)

  | _ ->
    let (md,reg,rm) = decompose_modrm modrm in
    match reg with

     (* DE/0 --- FIADD m16int --- Add m16int to st(0) and store result in st(0)  
	DE/1 --- FIMUL m16int --- Multiiply ST(0) by m16int and store result in ST(0)  
	DE/2 --- FICOM m16int --- Compare ST(0) with m16int
	DE/3 --- FICOMP m16int -- Compare ST(0) with m16int and pop stack register
	DE/4 --- FISUB m16int --- Subtract m16int from ST(0) and store result int ST(0)   
	DE/5 --- FISUBR m16int --- Subtract st(0) from m16int and store result  in st(0)  *) 
      
    | 0 -> let op = get_rm_operand md rm ~size:2 ch RD in 
	   Fadd  (false,false,2,fpu_register_op 0 RW, op)

    | 1 -> let op = get_rm_operand md rm ~size:2 ch RD in
	   Fmul  (false,false,2,fpu_register_op 0 RW, op)

    | 2 -> let op = get_rm_operand md rm ~size:2 ch RD in 
	   Fcom  (0,false,2,op)

    | 3 -> let op = get_rm_operand md rm ~size:2 ch RD in 
	   Fcom  (1,false,2,op)
	     
    | 4 -> let op = get_rm_operand md rm ~size:2 ch RD in 
	   Fsub  (false,false,2,fpu_register_op 0 RW, op)
	     
    | 5 -> let op = get_rm_operand md rm ~size:2 ch RD in 
	   Fsubr (false,false,2,fpu_register_op 0 RW,op)
     
    (* DE/6 ---- FIDIV m16int ---- Divide ST(0) by m16int and store result in ST(0)
       
       Note: this instruction seems to be superceded by DE F0+i : FDIVRP ST(i),ST(0)  *)

    | 6 -> let op = get_rm_operand md rm ~size:2 ch RD in 
	   Fdiv (false,false, 2, fpu_register_op 0 RW, op)
     
    (* DE/7 ---- FIDVR m16int ---- Divide m16int by ST(0) and store result  in ST(0)  
       
       Note: this instruction seems to be superceded by DE F8+i : FDIVP ST(i),ST(0) *)
     
    | 7 -> let op = get_rm_operand md rm ~size:2 ch RD in 
	   Fdivr (true,true,2,fpu_register_op 0 RW,op)
     
    | _ -> Unknown


let pxdf opsize_override (ch:pushback_stream_int) = 
  let modrm = ch#read_byte in
  match modrm with

  (* DF E0 --- FNSTW AX --- Store FPU status word in AX without checking for pending
                            unmasked floating point exceptions                       *)

  | 0xe0 -> FStoreState("sw",false, 2, ax_r WR)

  (* DF E8+i --- FUCOMIP ST(0),ST(i) --- Compare ST(0) with ST(i), check for ordered values,
                                         set EFlags, and pop register stack *)

  | 0xe8 | 0xe9 | 0xea | 0xeb | 0xec | 0xed | 0xee | 0xef ->
    Fcomi (true, true, fpu_register_op (modrm - 0xe8) RD)

  (* DF F0+i --- FCOMIP ST(0),ST(i)  --- Compare ST(0) with ST(i), set EFlags, and pop
                                         register stack                                  *)

  | 0xf0 | 0xf1 | 0xf2 | 0xf3 | 0xf4 | 0xf5 | 0xf6 | 0xf7 ->
    Fcomi (true, false, fpu_register_op (modrm - 0xf0) RD)

  | _ ->
    let (md,reg,rm) = decompose_modrm modrm in
    match reg with
      
      (* DF/0 --- FILD  m16int --- Push m16int onto FPU register stack
	 DF/2 --- FIST  m16int --- Store ST(0) in m16int
         DF/3 --- FISTP m16int --- Store ST(0) in m16int and pop register stack
         DF/5 --- FILD  m64int --- Push m64int onto FPU register stack    
         DF/7 --- FISTP m64int --- Store st(0) in m64int and pop register stack *)	

      | 0 -> let op = get_rm_word_operand md rm ch RD in FLoad (false,2,op)
      | 2 -> let op = get_rm_word_operand md rm ch RD in FStore (false,false,2,op)
      | 3 -> let op = get_rm_word_operand md rm ch WR in FStore (true ,false,2,op)
      | 5 -> let op = get_rm_operand ~size:8 md rm ch RD in FLoad (false,8,op)
      | 6 -> let op = get_rm_operand ~size:10 md rm ch WR in Fbstp op
      | 7 -> let op = get_rm_operand ~size:8 md rm ch WR in FStore (true,false,8, op)
	  
      | _ -> Unknown
