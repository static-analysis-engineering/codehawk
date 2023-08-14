(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
   ============================================================================= 
*)

(* bchlib *)
open BCHCPURegisters
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHOperand
open BCHX86Opcodes


let pxf20f (ch:pushback_stream_int) =
  let b2 = ch#read_byte in
  match b2 with

  (* F2 0F 10/r --- MOVSD xmm1,xmm2/m64 --- Move scalar double-prec floating-point value 
                                            from xmm2/m64 to xmm1 register
     F2 0F 11/r --- MOVSD xmm2/m64,xmm1 --- Move scalar double-prec floating-point value 
                                            from xmm1 register to xmm2/m64   
     F2 0F 12/r --- MOVDDUP xmm1,xmm2/m64 - Move one double-prec floating-point value from
                                            the lower 64-bit xmm2/m64 to xmm1 and duplicate
  *)

  | 0x10 -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmMove("",true,false,op2,op1)

  | 0x11 -> let (op1,op2) = get_modrm_xmm_operands ch 8 WR RD in 
	    FXmmMove("",true,false,op1,op2)

  | 0x12 -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmMove("dup",true,false,op2,op1)

  (* F2 OF 2A/r --- CVTSI2SD xmm,r/m32 --- Convert one signed doubleword integer from r/m32
                                           to one double-precision floating-point value    *)

  | 0x2a -> let (op1,op2) = get_modrm_sized_operands ch 4 RD 16 WR in
	    FConvert (false,"si","sd",op2,op1)

   (* F2 0F 2C/r --- CVTTSD2SI r32,xmm/m64 - Convert one double-precision floating-point value
                                             from xmm/m64 to one signed doubleword integer in r32
                                             using truncation  
      F2 0F 2D/r --- CVTSD2SI r32,xmm/m64 -- Convert one double-prec floating-point value from
                                             xmm/m64 to one signed doubleword integer r32         *)

  | 0x2c -> let (op1,op2) = get_modrm_xmm_reg_operands ch 8 RD WR in 
	    FConvert (true,"sd", "si",op2,op1)

  | 0x2d -> let (op1,op2) = get_modrm_xmm_reg_operands ch 8 RD WR in 
	    FConvert (false,"sd","si",op2,op1)

  (* F2 0F 2F/r --- COMISS xmm1,xmm2/m32 --- Compare low single-prec floating-point values
                                             in xmm1 and xmm2/m32 and set the EFLAGS       *)

  | 0x2f -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in
	    FXmmOp ("comi",true,true,op2,op1)

  (* F2 0F 51/r --- SQRTSD xmm1,xmm2/m64 -- Computes the square root of the low double-prec
                                            floating-point value in xmm2/m64
     F2 0F 58/r --- ADDSD xmm1,xmm2/m64 --- Add the low double-precision floating-point 
                                            value from xmm2/m64 to xmm1
     F2 0F 59/r --- MULSD xmm1,xmm2/m64 --- Multiply the low double-precision floating-point 
                                            value in xmm2/m64 by low double-precision 
                                            floating-point value in xmm1                 *)

  | 0x51 -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmOp ("sqrt",true,false,op2,op1)

  | 0x58 -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmOp ("add",true,false,op2,op1)

  | 0x59 -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmOp ("mul",true,false,op2,op1)
   
  (* F2 0F 5A/r --- CVTSD2SS xmm1,xmm2/m64 --- Convert one double-precision floating-point value
                                               in xmm2/m64 to one single-precision floating-point
                                               value in xmm1                                    *)

  | 0x5a -> let (op1,op2) = get_modrm_xmm_operands ch  8 RD WR in 
	    FConvert (false,"sd","ss",op2, op1)

  (* F2 0F 5C/r --- SUBSD xmm1,xmm2/m64 --- Subtract the low double-precision
                                            floating-point value in xmm2/m64 from xmm1  
     F2 0F 5D/r --- MINSD xmm1,xmm2/m64 --- Return the minimum scalar double-prec floating-point
                                            value between xmm2/m64 and xmm1
     F2 0F 5E/r --- DIVSD xmm1,xmm2/m64 --- Divide low double-precision floating-point value in
                                            xmm1 by low double-precision floating-point value in
                                            xmm2.m64                                        
     F2 0F 5F/r --- MAXSD xmm1,xmm2/m64 --- Return the maximum scalar double-prec floating-point
                                            value between xmm2/m64 and xmm1
 *)

  | 0x5c -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmOp ("sub",true,false,op2,op1)

  | 0x5d -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmOp ("min",true,false,op2,op1)

  | 0x5e -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmOp ("div",true,false,op2,op1)
	      
  | 0x5f -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD WR in 
	    FXmmOp ("max",true,false,op2,op1)

  (* F2 0F 70/r ib --- PSHUFLW xmm1,xmm2/m128,imm8 --- Shuffle the low words in xmm2/m128 
                                                       based on the encoding in imm8 and 
                                                       store the result in xmm1   *)

  | 0x70 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedShuffle ("lw",op2,op1,Some op3)

  (* F2 0F 7C/r --- HADDPS xmm1,xmm2/m128 --- Horizontal add packed single-prec 
                                              floating-point values from xmm2/m128 to xmm1
     F2 0F 7D/r --- HSUBPS xmm1,xmm2/m128 --- Horizontal subtract packed single-prec
                                              floating-point values from xmm2/m128 to xmm1  *)

  | 0x7c -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("hadd",false,true,op2,op1)
	      
  | 0x7d -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("hsub",false,true,op2,op1)

  (* F2 0F C2/r --- CMPSD xmm1,xmm2/m64,imm8 -- Compare low double-prec floating-point value
                                                in xmm2/m64 and xmm1 using imm8 as comparison
                                                predicate                                     *)

  | 0xc2 -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD RW in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    FXmmCompare (true,false,op2,op1,op3)

  (* F2 0F D0/r --- ADDSUBPS xmm1,xmm2/m128 --- Add/subtract single-precision floating-point
                                                values from xmm2/m128 to xmm1     *)

  | 0xd0 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("addsub",false,true,op2,op1)

  (* F2 0F E6/r --- CVTPD2DQ xmm1,xmm2/m128 --- Convert two packed double-prec floating-point
                                                values from xmm2/m128 to two packed signed
                                                doubleword integers in xmm1                     *)

  | 0xe6 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in
	    FConvert (false,"pd","dq",op2,op1)

  | _ -> Unknown


let rec pxf2 dseg eseg opsize_override (ch:pushback_stream_int) (base:doubleword_int)=
  let opsize = if opsize_override then 2 else 4 in
  let b2 = ch#read_byte in
  match b2 with

  | 0x0f -> pxf20f ch

  (* F2 66 ----- opsize override  *)

  | 0x66 -> pxf2 dseg eseg true ch base

  (* F2 jcc instruction MPX bnd short jumps: TODO: add separate opcode *)
          
  | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77
  | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f ->
    let cc = index_to_condition_code (b2 - 0x70) in
    begin
      try
	let op = read_target8_operand base ch in Jcc (cc,op)
      with
	Invalid_argument s -> InconsistentInstr s
    end

  (* F2 A4 --- REPNE MOVS m8 m8   --- not documented
     F2 A5 --- REPNE MOVS m32 m32 --- not documented  
     Note: as these instructions don't set a flag we assume their behavior is identical
     to that of REP MOVS
 *)

  | 0xa4 -> RepNeMovs (1, es_edi ~seg:eseg ~size:1 WR, ds_esi ~seg:dseg ~size:1 RD)
  | 0xa5 -> RepNeMovs (opsize, es_edi ~seg:eseg ~size:opsize WR, ds_esi ~seg:dseg ~size:opsize RD)

  (* F2 A6 --- REPNE CMPS m8  --- Find matching bytes in ES:[EDI] and DS:[ESI]
     F2 A7 --- REPNE CMPS m32 --- Find matching doublewords in ES:[EDI] and DS:[EDI] *)

  | 0xa6 -> RepNeCmps (1, es_edi ~seg:eseg ~size:1 RD, ds_esi ~seg:dseg ~size:1 RD)
  | 0xa7 -> RepNeCmps (opsize, es_edi ~seg:eseg ~size:opsize RD, ds_esi ~seg:dseg ~size:opsize RD)

  (* F2 AA --- REPNE STOS m8  --- not documented
     F2 AB --- REPNE STOS m32 --- not documented
     Note: as these instructions don't set a flag we assume their behavior is identical
     to that of REP STOS
  *)

  | 0xaa -> RepNeStos (1, es_edi ~seg:eseg ~size:1 WR)
  | 0xab -> RepNeStos (opsize, es_edi ~seg:eseg ~size:opsize WR)

  (* F2 AE --- REPNE SCAS m8 --- Find AL starting at ES:[EDI]   
     F2 AF --- REPNE SCAS m32 -- Find EAX starting at ES:[EDI]        *)

  | 0xae -> RepNeScas (1, es_edi ~seg:eseg ~size:1 RD)
  | 0xaf -> RepNeScas (opsize, es_edi ~seg:eseg ~size:opsize RD)

  (* F2 C2 --- BND RET imm16 (MPX mode 
     F2 C3 --- BND RETN --- Return (MPX mode) *)

  | 0xc2 -> let imm = ch#read_i16 in BndRet (Some imm)
  | 0xc3 -> BndRet None

  (* F2 E8 cd --- CALL rel32 --- Call near, relative, displacement
                              relative to next instruction      
                   MPX version; TODO: create separate instruction *)

  | 0xe8 -> 
    begin
      try
	let op = read_target32_operand base ch in DirectCall op
      with
	Invalid_argument s ->
	  InconsistentInstr ("Direct call with address problem " ^ s)
    end

  (* E9 cd --- JMP rel32 --- Jump near relative, RIP = RIP + 32bit disp 
               MPX version; TODO: create separate instruction *)

  | 0xe9 -> 
    begin
      try
	let op = read_target32_operand base ch in DirectJmp op
      with
	Invalid_argument s ->
	  InconsistentInstr ("Direct jmp with address problem " ^ s)
    end

  | _ -> Unknown


let pxf30f1e (ch: pushback_stream_int) =
  let b3 = ch#read_byte in
  match b3 with

  (* F3 0F 1E FB --- ENDBR32 --- Terminate an Indirect Branch in 32-bit and
                                   Compatibility mode *)
  | 0xfb -> TerminateBranch32

  | _ -> Unknown


let pxf30fa7 (ch:pushback_stream_int) =
  let b3 = ch#read_byte in
  match b3 with

 (* F3 0F A7 C0 --- repz xstore-rng
    F3 0F A7 C8 --- repz xcrypt-ecb
    F3 0F A7 D0 --- repz xcrypt-cbc
    F3 0F A7 E0 --- repz xcrypt-cfb
    F3 0F A7 E8 --- repz xcrypt-ofb
 *)
  | 0xc0 -> XStoreRng
  | 0xc8 -> XCrypt "Ecb"
  | 0xd0 -> XCrypt "Cbc"
  | 0xe0 -> XCrypt "Cfb"
  | 0xe8 -> XCrypt "Ofb"

  | _ -> Unknown


let pxf30f (ch:pushback_stream_int) =
  let b2 = ch#read_byte in
  match b2 with

  (* F3 0F 10/r --- MOVSS xmm1,xmm2/m32 --- Move scalar single-precision floating-point
                                            value from xmm2/m32 to xmm1 register
     F3 0F 11/r --- MOVSS xmm2/m32,xmm1 --- Move scalar single-precision floating-point
                                            value from xmm1 register to xmm2/m32
     F3 0F 12/r --- MOVSLDUP xmm1,xmm2/m128 -- Move two single-prec floating-point values
                                               from the lower 32-bit of each qword in
                                               xmm2/m128 to xmm1 and duplicate each 32-bit
                                               operand to the higher 32-bits of each qword
     F3 0F 16/r --- MOVSHDUP xmm1,xmm2/m128 -- Move two single-prec floating-point values
                                               from the higher 32-bits of each qword in
                                               xmm2/m128 to xmm1 and duplicat each 32-bit
                                               operand to the lower 32-bits of each qword

     Moves a scalar single-precision floating-point value from the source operand 
     (second operand) to the destination operand (first operand). The source and 
     destination operands can be XMM registers or 32-bit memory locations. This 
     instruction can be used to move a single-precision floating-point value to and 
     from the low doubleword of an XMM register and a 32-bit memory location, or to 
     move a single-precision floating-point value between the low doublewords of 
     two XMM registers.
   *)

  | 0x1e -> pxf30f1e ch

  | 0x10 -> let (op1,op2) = get_modrm_xmm_operands ch 4  RD WR in 
	    FXmmMove ("",true,true,op2,op1)

  | 0x11 -> let (op1,op2) = get_modrm_xmm_operands ch 4  WR RD in 
	    FXmmMove ("",true,true,op1,op2)

  | 0x12 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FXmmMove ("hdup",true,true,op2,op1)

  | 0x16 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FXmmMove ("ldup",true,true,op2,op1)

  (* F3 OF 2A/r --- CVTSI2SS xmm,r/m32 --- Convert one signed doubleword integer from r/m32
                                           to one single-precision floating-point value   
     F3 0F 2C/r --- CVTTSS2SI r32,xmm/m32 -- Convert one single-prec floating-point value from
                                             xmm/m32 to one signed doubleword integer in r32
                                             using truncation  
     F3 0F 2D/r --- CVTSS2SI r32,xmm/m32 --- Convert one single-precision floating-point value
                                             from xmm/m32 to one signed doubleword integer in r32 *)

  | 0x2a -> let (op1,op2) = get_modrm_sized_operands ch 4 RD 16 WR in 
	    FConvert (false,"si","ss",op2,op1)

  | 0x2c -> let (op1,op2) = get_modrm_xmm_reg_operands ch 4 RD WR in 
	    FConvert (true,"ss","si",op2,op1)

  | 0x2d -> let (op1,op2) = get_modrm_xmm_reg_operands ch 4 RD WR in 
	    FConvert (false,"ss","si",op2,op1)

  (* F3 0F 51/r --- SQRTSS xmm1,xmm2/m32 --- Computes square root of the low single-precision
                                             floating-point value in xmm2/m32 and stores the
                                             result in xmm1 *)

  | 0x51 -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("sqrt",true,true,op2,op1)

  (* F3 0F 52/r --- RSQRTSS xmm1,xmm2/m32 - Computes the reciprocals of the square root of the
                                            low single-prec floating-point value in xmm2/m32
     F3 0F 53/r --- RCPSS xmm1,xmm2/m32 --- Computes the reciprocals of the scalar single-prec
                                            floating-point values in xmm2/m32
     F3 0F 58/r --- ADDSS xmm1,xmm2/m32 --- Add the low single-precision floating-point
                                            value from xmm2/m32 to xmm1
     F3 0F 59/r --- MULSS xmm1,xmm2/m32 --- Multiply the low single-precision floating-point
                                            value in xmm2/m32 by the low single-precision
                                            floating-point value in xmm1                        *)

  | 0x52 -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("rsqrt",true,true,op2,op1)

  | 0x53 -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("rcp",true,true,op2,op1)

  | 0x58 -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("add",true,true,op2,op1)

  | 0x59 -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("mul",true,true,op2,op1)

  (* F3 0F 5A/r --- CVTSS2SD xmm1,xmm2/m32 --- Convert one single-precision floating-point value
                                               in xmm2/m32 to one double-precision floating-point
                                               value in xmm1  

     F3 0F 5B/r --- CVTTPS2DQ xmm1,xmm2/m128 -- Convert four single-prec floating-point values
                                                from xmm2/m128 to four signed doubleword integers
                                                in xmm1 using truncation                          *)

  | 0x5a -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD WR in 
	    FConvert (false,"ss","sd",op2,op1)

  | 0x5b -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FConvert (true,"ps","dq",op2,op1)

  (* F3 0F 5C/r --- SUBSS xmm1,xmm2/m32 --- Subtract the lower single-precision floating-point
                                            value in xmm2/m32 from xmm1
     F3 0F 5D/r --- MINSS xmm1,xmm2/m32 --- Return the minimum scalar single-precision
                                            floating-point value between xmm2/m32 and xmm1
     F3 0F 5E/r --- DIVSS xmm1,xmm2/m32 --- Divide low single-precision floating-point value
                                            in xmm1 by low single-precision floating-point value 
                                            in xmm2/m32
     F3 0F 5F/r --- MAXSS xmm1,xmm2/m32 --- Return the maximum scalar single-precision
                                            floating-point value between xmm2/m32 and xmm1
  *)

  | 0x5c -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("sub",true,true,op2,op1)

  | 0x5d -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("min",true,true,op2,op1)

  | 0x5e -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("div",true,true,op2,op1)

  | 0x5f -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in 
	    FXmmOp ("max",true,true,op2,op1)

  (* F3 0F 6F/r --- MOVDQU xmm1, xmm2/m128 --- move unaligned double quadword from 
                                               xmm2/m128 to xmm1 *)

  | 0x6f -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Movdq (false,op2,op1) 

  (* F3 0F 70/r ib --- PSHUFHW xmm1,xmm2/m128,imm8 --- Shuffle the high words in xmm2/m128 
                                                       based on the encoding in imm8 and 
                                                       store the result in xmm1          *)

  | 0x70 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedShuffle ("hw",op2,op1,Some op3)

   (* F3 0F 7E/r --- MOVQ xmm1,xmm2/m64 --- Move quadword from xmm2/m64 to xmm1           *)

  | 0x7e -> let (op1,op2) = get_modrm_double_quadword_operands ch RD WR in 
	    Movdw (8, op2,op1)

   (* F3 0F 7F/r --- MOVDQU xmm2/m128, xmm1 --- Move unaligned double quadword from 
                                                xmm1 to xmm2/m128 *)

  | 0x7f -> let (op1,op2) = get_modrm_xmm_operands ch 16 RW RD in Movdq (false,op1,op2)

  | 0xa7 -> pxf30fa7 ch

  (* F3 OF BC/r --- TZCNT r32, r/m32 --- Count the number of trailing zero bits *)

  | 0xbc ->
     let (op1, op2) = get_modrm_operands ch RW RD in
     CountTrailingZeroBits (op1, op2)

  (* F3 0F C2/r --- CMPSS xmm1,xmm2/m32, imm8 --- Compare low single-precision floating-point
                                                  value in xmm2/m32 and xmm1 using imm8 as
                                                  comparison predicate                     *)

  | 0xc2 -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RW in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    FXmmCompare (true,true,op2,op1,op3)

  (* F3 0F E6 --- CVTDQ2PD xmm1,xmm2/m128 --- Convert two packed signed doubleword integers
                                              from xmm2/m128 to two packed double-prec
                                              floating-point values in xmm1                 *)

  | 0xe6 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FConvert (false,"dq","pd",op2,op1)

  | _ -> Unknown


let rec pxf3 dseg eseg opsize_override (ch:pushback_stream_int) =
  let opsize = if opsize_override then 2 else 4 in
  let b2 = ch#read_byte in
  match b2 with

  | 0x0f -> pxf30f ch

  (* F3 66 --- opsize override *)

  | 0x66 -> pxf3 dseg eseg true ch

  (* F3 6C ---- REP INS m8,DX  --- Input ECX bytes from port DX into ES:[EDI]
   * F3 6D ---- REP INS m32,DX --- Input ECX doublewords from port DX into ES:[EDI]   *)

  | 0x6c -> RepIns (1, es_edi ~seg:eseg ~size:1 WR)
  | 0x6d -> RepIns (opsize, es_edi ~seg:eseg ~size:opsize WR)

  (* F3 6E ---- REP OUTS m8,DX  --- Input ECX bytes from DS:[ESI] to port DX
   * F3 6F ---- REP OUTS m32,DX --- Input ECX doublewords from DS:[ESI] to port DX  *)

  | 0x6e -> RepOuts (1, ds_esi ~seg:eseg ~size:1 WR)
  | 0x6f -> RepOuts (opsize, ds_esi ~seg:eseg ~size:opsize WR)

  (* F3 90 --- PAUSE --- Spin Loop Hint  
     Gives hint to processor that improves performance of spin-wait loops *)

  | 0x90 -> Pause    

  (* F3 A4 --- REP MOVS m8  m8  --- Move ECX bytes from DS:[ESI] to ES:[EDI]
     F3 A5 --- REP MOVS m32 m32 --- Move ECX double words from DS:[ESI] to ES:[EDI]  *)

  | 0xa4 -> RepMovs (1, es_edi  ~seg:eseg ~size:1 WR, ds_esi ~seg:dseg ~size:1 RD)
  | 0xa5 -> RepMovs (opsize, es_edi ~seg:eseg ~size:opsize WR, ds_esi ~seg:dseg ~size:opsize RD)
   
  (* F3 A6 --- REPE CMPS m8 ---      Find nonmatching bytes in ES:[EDI] and DS:[ESI]
     F3 A7 --- REPE CMPS m32 m32 --- Find nonmatching doublewords in ES:[EDI] and DS:[ESI] *)
  
  | 0xa6 -> RepECmps (1, es_edi ~seg:eseg ~size:1 RD, ds_esi ~seg:dseg ~size:1 RD)
  | 0xa7 -> RepECmps (opsize, es_edi ~seg:eseg ~size:opsize RD, ds_esi ~seg:dseg ~size:opsize RD)

  (* F3 AA --- REP STOS m8  --- Fill ECX bytes at ES:[EDI] with AL
     F3 AB --- REP STOS m32 --- Fill ECX doublewords at ES:[EDI] with EAX *)

  | 0xaa -> RepStos (1, es_edi ~seg:eseg ~size:1 WR)
  | 0xab -> RepStos (opsize, es_edi ~seg:eseg ~size:opsize WR)

  (* F3 AC --- REP LODS m8  --- Load ECX bytes from DS:[ESI] into AL
   * F3 AD --- REP LODS m32 --- Load ECX doublewords from DS:[ESI] into EAX   *)
    
  | 0xac -> RepLods (1, ds_esi ~seg:dseg ~size:1 RD)
  | 0xad -> RepLods (opsize, ds_esi ~seg:dseg ~size:opsize RD)

  (* F3 AE --- REPE SCAS m8  --- Find non-AL byte starting at ES:[EDI]
     F3 AF --- REPE SCAS m32 --- Find non-EAX doubleword starting at ES:[EDI]   *)

  | 0xae -> RepEScas (1, es_edi ~seg:eseg ~size:1 RD)
  | 0xaf -> RepEScas (opsize, es_edi ~seg:eseg ~size:opsize RD)

  (* F3 C3 --- REPZ RET --- undocumented *)

  | 0xc3 -> RepzRet

  | _ -> Unknown


let pxf6 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with
    
  (* F6/0 ib --- TEST r/m8,imm8 --- AND imm8 with r/m8, set SF,ZF,PF according to result
     F6/1 ib --- TEST r/m8,imm8 --- AND imm8 with r/m8, set SF,ZF,PF according to result
                                    (undocumented)                                     *)

  | 0 
  | 1 -> let op1 = get_rm_byte_operand md rm ch RD in
	 let op2 = read_immediate_signed_byte_operand ch in
	 Test (op1, op2)

  (* F6/2    --- NOT r/m8  --- Reverse each bit of r/m8

     Performs a bitwise NOT operation (each 1 is set to 0, and each 0 is set to 1) on the
     destination operand and stores the result in the destination operand location. 

     F6/3    --- NEG r/m8  --- Two's complement negate r/m8  

     Replaces the value of the destination operand with its two's complement. (This operation
     is equivalen to subtracting the operand from 0.
   *)

  | 2 -> let op = get_rm_byte_operand md rm ch RW in OnesComplementNegate op
  | 3 -> let op = get_rm_byte_operand md rm ch RW in TwosComplementNegate op

  (* F6/4 --- MUL r/m8  --- Unsigned multiply: AX <- AL * r/m8
     F6/5 --- IMUL r/m8 --- AX <- AL * r/m8                        *)

  | 4 -> let op = get_rm_byte_operand md rm ch RD in Mul  (1,ax_r WR, al_r RD, op)
  | 5 -> let op = get_rm_byte_operand md rm ch RD in IMul (1,ax_r WR, al_r RD, op)

  (* F6/6 --- DIV r/m8 --- Unsigned divide:  AL,AH <- AX / r/m8
     F6/7 --- IDIV r/m8 -- Signed divide: AL,AH <- AX / r/m8           
                           with result stored in AL <- Quotient, AH <- Remainder   *)

  | 6 -> let op = get_rm_byte_operand md rm ch RD in Div  (1, al_r WR, ah_r WR, ax_r RD, op)
  | 7 -> let op = get_rm_byte_operand md rm ch RD in IDiv (1, al_r WR, ah_r WR, ax_r RD, op)

  | _ -> Unknown

let pxf7 opsize_override (ch:pushback_stream_int) =
  let opsize = if opsize_override then 2 else 4 in
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* F7/0 --- TEST r/m32 -- AND imm32 with r/m32, set SF,ZF,PF according to result    
     F7/1 --- TEST r/m32 -- AND imm32 with r/m32, set SF,ZF,PF according to result 
                            (undocumented)                                          *)   

  | 0
  | 1 -> let op1 = get_rm_def_operand opsize_override md rm ch RD in
	 let op2 = read_immediate_signed_operand opsize ch in
	 Test (op1, op2 )

  (* F7/2 --- NOT r/m32 --- One's complement negate r/m 32 
     F7/3 --- NEG r/m32 --- Two's complement negate r/m 32 *)

  | 2 -> let op = get_rm_def_operand opsize_override md rm ch RW in OnesComplementNegate op
  | 3 -> let op = get_rm_def_operand opsize_override md rm ch RW in TwosComplementNegate op

  (* F7/4 --- MUL r/m32 ---- Unsigned multiply EDX:EAX <- EAX * r/m32  
     F7/5 --- IMUL r/m32 --- Signed multiply EDX:EAX <- EAX * r/m32     *)

  | 4 ->
     let op = get_rm_def_operand opsize_override md rm ch RD in
     if opsize_override then
       Mul (2, dx_ax_r WR,ax_r RD, op)
     else
       Mul (4, edx_eax_r WR, eax_r RD, op)

  | 5 ->
     let op = get_rm_def_operand opsize_override md rm ch RD in 
     if opsize_override then
       IMul (2, dx_ax_r WR,ax_r RD, op )
     else
       IMul (4, edx_eax_r WR, eax_r RD, op)

  (* F7/6 --- DIV r/m32 --- Unsigned divide EDX:EAX by r/m32 with
                            result stored in EAX <- quotient,
                            EDX <- remainder 

     F7/7 --- IDIV r/m32 -- Signed divide EDX:EAX by r/m32 with result
                            stored in EAX <- quotient, EDX <- remainder *)

  | 6 ->
     let op = get_rm_def_operand opsize_override md rm ch RD in
     if opsize_override then
       Div (2, ax_r WR, dx_r WR, dx_ax_r RD, op)
     else
       Div (4, eax_r WR, edx_r WR, edx_eax_r RD, op)

  | 7 ->
     let op = get_rm_def_operand opsize_override md rm ch RD in
     if opsize_override then
       Div (2, ax_r WR, dx_r WR, dx_ax_r RD, op)
     else
       Div (4, eax_r WR, edx_r WR, edx_eax_r RD, op)

  | _ -> Unknown


let pxfe (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* FE/0 --- INC r/m8 ---- Increment r/m8 by 1 
     FE/1 --- DEC r/m8 ---- Decrement r/m8 by 1 *)

  | 0 -> let op = get_rm_byte_operand md rm ch RW in Increment op
  | 1 -> let op = get_rm_byte_operand md rm ch RW in Decrement op

  | _ -> Unknown


let pxff seg_override opsize_override (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  let opsize = if opsize_override then 2 else 4 in
  match reg with

  (* FF/0 --- INC r/m32 ---- Increment r/m doubleword by 1 
     FF/1 --- DEC r/m32 ---- Decrement r/m doubleword by 1 *)

  | 0 -> let op = get_rm_def_operand opsize_override md rm ch RW in Increment op

  | 1 -> let op = get_rm_def_operand opsize_override md rm ch RW in Decrement op

  (* FF/2 --- CALL r/m32 --- Call near, absolute indirect, address given in r/m32 *)
  (* FF/3 --- CALL m16:16 / m16:32 ---
     Call far, absolute indirect address given in m16:16 / m16:32 *)

  | 2 -> let op = get_rm_def_operand opsize_override md rm ch RD in IndirectCall op
  | 3 -> let op = get_rm_def_operand opsize_override md rm ch RD in IndirectCall op

  (* FF/4 --- JMP r/m32  --- Jump near, absolute indirect, address given in r/m32 *)

  | 4 -> let op = get_rm_def_operand opsize_override md rm ch RD in IndirectJmp op

  (* FF/6 --- PUSH r/m32 --- Push r/m32 *)

  | 6 -> let op = get_rm_operand md rm ~seg_override:seg_override ~size:opsize ch RD in 
	 Push (opsize,op)

  | _ -> Unknown
