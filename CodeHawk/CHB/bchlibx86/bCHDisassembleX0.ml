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
open BCHLibTypes

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHOperand
open BCHX86Opcodes

let px0f01 (ch:pushback_stream_int) = 
  let b3 = ch#read_byte in
  let (md,reg,rm) = decompose_modrm b3 in
  match b3 with

  (* 0F 01 D0 --- XGETBV --- Reads an extended control register specified by ECX into
                             EDX:EAX  
     (Currently, only XCR0 is supported; all other values of ECX are reserved and will
      cause a #GP(0)                                                                     *)

  | 0xd0 -> XGetBV

  (* 0F 01/1 --- SIDT --- Store Interrupt Descriptor Table Register *)

  | _ ->
     begin
       match reg with
       | 1 -> let op = get_rm_operand md rm ch WR in StoreIDTR op
       | _ -> Unknown
     end


let px0f18 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* 0F 18/0 --- PREFETCHNTA m8 -- move data from m8 closer to the processor using NTA hint 
     0F 18/1 --- PREFETCHT0 m8 --- move data from m8 closer to the processor using T0 hint
     0F 18/2 --- PREFETCHT1 m8 --- move data from m8 closer to the processor using T1 hint
     0F 18/3 --- PREFETCHT2 m8 --- move data from m8 closer to the processor using T2 hint   *)

  | 0 -> let op = get_rm_operand md rm ch RD in Prefetch ("nta", op)
  | 1 -> let op = get_rm_operand md rm ch RD in Prefetch ("t0", op)
  | 2 -> let op = get_rm_operand md rm ch RD in Prefetch ("t1", op)
  | 3 -> let op = get_rm_operand md rm ch RD in Prefetch ("t2", op)

  | _ -> Unknown

let px0f38 (ch:pushback_stream_int) =
  let b3 = ch#read_byte in
  match b3 with
    
  (* 0F 38 00/r --- PSHUFB mm1,mm2/m64 --- Shuffle bytes in mm1 according to contents
                                           of mm2/m64                                  *)
    
  | 0x00 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShuffle ("b",op2,op1,None)

  (* OF 38 0B/r --- PMULHRSW mm1,mm2/m64 -- Multiply 16-bit signed words, scale and round
                                            signed doublewords, pack high 16 bits to mm1   *)

  | 0x0b -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedMultiply ("hrsw",op2,op1)
							     
  (* 0F 38 1C/r --- PABSB mm1,mm2/m64   --- Compute absolute value of byte mm2/m64  
                                            and store unsigned result in mm1
     0F 38/1D/r --- PABSW mm1,mm2/m64   --- Compute absolute value of 16-bit integers
                                            in mm2/m64 and store unsigned result in mm1
     0F 38/1E/r --- PABSD mm1,mm2/m64   --- Compute absolute value of 32-bit integers
                                            in mm2/m64 and store unsigned result in mm1
  *)
		
  | 0x1c -> let (op1,op2) = get_modrm_mm_operands ch 8 RD WR in PackedOp ("abs",1,op2,op1)
  | 0x1d -> let (op1,op2) = get_modrm_mm_operands ch 8 RD WR in PackedOp ("abs",2,op2,op1)
  | 0x1e -> let (op1,op2) = get_modrm_mm_operands ch 8 RD WR in PackedOp ("abs",4,op2,op1)
							     
  | _ -> Unknown

let px0f3a (ch:pushback_stream_int) =
  let b3 = ch#read_byte in
  match b3 with

  (* 0F 3A 0F --- PALIGNR mm1,mm2/m64,imm8 --- Concatenate destination and source
                                               operands, extract byte-aligned result
                                               shifted to the right by imm8 into mm1  *)

  | 0x0f -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedAlignRight (op2,op1,op3)
      
  | _ -> Unknown

let px0f3f (ch:pushback_stream_int) =
  let b3 = ch#read_byte in
  match b3 with
  
  (* 0F 3F 07 0B --- VPCEXT: illegal opcode trapped by VirtualPC virtual machine; used
                     by malware to detect the presence of virtual machines            *)

  | 0x07 ->
    let b4 = ch#read_byte in
    begin
      match b4 with
      | 0x0b -> MiscOp("vpcext 0x07 0x0B")
      | _ -> Unknown
    end
  | _ -> Unknown

let px0f71 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with
    
  (* 0F 71/2 ib --- PSRLW mm,imm8 --- Shift words in mm right by imm8 while shifting in 0s
     0F 71/4 ib --- PSRAW mm,imm8 --- Shift words in mm right by imm8 while shifting in sign bits
     0F 71/6 ib --- PSLLW mm,imm8 --- Shift words in mm left by imm8 while shifting in 0s   *)

  | 2 -> let op1 = get_rm_operand md rm ~size:8 ch RW in
	 let op2 = read_immediate_unsigned_byte_operand ch in
	 PackedShift ("rl",2, op1, op2)

  | 4 -> let op1 = get_rm_operand md rm ~size:8 ch RW in
	 let op2 = read_immediate_unsigned_byte_operand ch in
	 PackedShift ("ra",2, op1, op2)

  | 6 -> let op1 = get_rm_operand md rm ~size:8 ch RW in
	 let op2 = read_immediate_unsigned_byte_operand ch in
	 PackedShift ("ll",2, op1, op2)
					 
  | _ -> Unknown

let px0f72 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* 0F 72/2 ib --- PSRLD mm,imm8 --- Shift doublewords in mm right by imm8 while shifting in 0s
     0F 72/4 ib --- PSRAD mm,imm8 --- Shift doublewords in mm right by imm8 while shifting in 
                                      sign bits
     0F 72/6 ib --- PSLLD mm,imm8 --- Shift doublewords in mm left by imm8 while shifting in 0s  *)

  | 2 -> let op1 = get_rm_operand md rm ~size:8 ch RW in
	 let op2 = read_immediate_unsigned_byte_operand ch in
	 PackedShift ("rl",4, op1, op2)

  | 4 -> let op1 = get_rm_operand md rm ~size:8 ch RW in
	 let op2 = read_immediate_unsigned_byte_operand ch in
	 PackedShift ("ra",4, op1, op2)
	   
  | 6 -> let op1 = get_rm_operand md rm ~size:8 ch RW in
	 let op2 = read_immediate_unsigned_byte_operand ch in
	 PackedShift ("ll",4, op1, op2)

  | _ -> Unknown

let px0f73 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with
    
  (* 0F 73/2 ib --- PSRLQ mm,imm8 --- Shift mm right by imm8 while shifting in 0s
     0F 73/6 ib --- PSLLQ mm,imm8 --- Shift quadword in mm left by imm8 while shifting in 0s *)
    
  | 2 ->  let op1 = get_rm_operand md rm ~size:8 ch RW in
	  let op2 = read_immediate_unsigned_byte_operand ch in
	  PackedShift ("rl",8, op1, op2)

  | 6 ->  let op1 = get_rm_operand md rm ~size:8 ch RW in
	  let op2 = read_immediate_unsigned_byte_operand ch in
	  PackedShift ("ll",8, op1, op2)

  | _ -> Unknown

let px0fae (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* 0F AE/0 --- FXSAVE m512byte  --- Save the x87 FPU, MMX, XMM, and MXCSR register 
                                      state to m512byte. 
     0F AE/1 --- FXRSTOR m512byte --- Restore the x87 FPU, MMX, XMM, and MXCSR register 
                                      state from m512byte.                             *)

  | 0 -> let op = get_rm_operand md rm ~size:64 ch WR in FXSave op
  | 1 -> let op = get_rm_operand md rm ~size:64 ch RD in FXRestore op

  (* 0F AE/2 --- LDMXCSR m32 -- Load MXCSR register from m32
     0F AE/3 --- STMXCSR m32 -- Store contents of MXCSR register to m32        
     0F AE/7 --- CLFLUSH m8 --- Flushes cache line containing m8  
     0F AE/7 --- SFENCE ------- Serializes store operations                *)

  | 2 -> let op = get_rm_operand md rm ch RD in Ldmxcsr op
  | 3 -> let op = get_rm_operand md rm ch WR in Stmxcsr op

  | 7 -> let op = get_rm_byte_operand md rm ch RD in FlushCacheLine op

  | _ -> Unknown


let px0fba (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  let (md,reg,rm) = decompose_modrm modrm in
  match reg with

  (* OF BA/4 ib --- BT  r/m32,imm8 --- Store selected bit in CF flag   
     0F BA/5 ib --- BTS r/m32,imm8 --- Store selected bit in CF flag and set
     0F BA/6 ib --- BTR r/m32,imm8 --- Store selected bit in CF flag and clear      
     OF BA/7 ib --- BTC r/m32,imm8 --- Store selected bit in CF flag and complement *)

  | 4 -> 
      let op1 = get_rm_operand md rm ch RD in
      let op2 = read_immediate_signed_byte_operand ch in
      BitTest (op1, op2)

  | 5 ->
      let op1 = get_rm_operand md rm ch RW in
      let op2 = read_immediate_signed_byte_operand ch in
      BitTestAndSet (op1, op2)

  | 6 ->
      let op1 = get_rm_operand md rm ch RW in
      let op2 = read_immediate_signed_byte_operand ch in
      BitTestReset (op1, op2)

  | 7 ->
      let op1 = get_rm_operand md rm ch RW in
      let op2 = read_immediate_signed_byte_operand ch in
      BitTestComplement (op1, op2)

  | _ -> Unknown

let px0fc7 (ch:pushback_stream_int) =
  let modrm = ch#read_byte in
  match modrm with
  (*  0F C7 C8 01 00 --- illegal opcode, trapped by VirtualPC virtual machine; 
                         used by malware to detect presence of virtual machine *)
  | 0xc8 ->
    let y1 = ch#read_byte in
    begin
      match y1 with
      | 0x01 -> 
	let y2 = ch#read_byte in
	begin
	  match y2 with
	  | 0x00 -> MiscOp("vmcpuid")
	  | _ -> Unknown
	end
      | _ -> Unknown
    end
  | _ ->
    let (md,reg,rm) = decompose_modrm modrm in
    match reg with

  (* 0F c7/1 --- CMPXCHG8B m64 --- Compare EDX:EAX with m64. If equal, set ZF and 
     load ECX:EBX into m64. Else, clear ZF and load 
     m64 into EDX:EAX.                             

     Note: some of these encodings are not valid and cause a processor exception,
     except when run in VirtualPC, which traps these exceptions, see
     Peter Ferrie, Attacks on Virtual Machine Emulators                      *)

    | 1 -> let op = get_rm_operand md rm ~size:8 ch WR in 
	   let opsrc = double_register_op Ecx Ebx 8 RD in
	   let opdst = double_register_op Edx Eax 8 WR in
	   CmpExchange8B(op,opdst,opsrc)

  (* 0F C7/6 --- Randomize the operand; new instruction added in 2012 
     Documented in 
     Intel(R) 64 and IA-32 Architectures  Software Developer's Manual
     Documentation Changes, August 2012                                  *)

    | 6 -> let op = get_rm_operand md rm ch WR in RdRandomize op

    | _ -> Unknown

let px0f base opsize_override (ch:pushback_stream_int) =
  let opsize = if opsize_override then 2 else 4 in
  let b2 = ch#read_byte in
  match b2 with

  | 0x01 -> px0f01 ch

  (* 0F 05 --- SYSCALL --- Fast System Call 
                           Fast call to privilege level 0 system procedures.      *)

  | 0x05 -> SysCall

  (* 0F 06 --- CLTS --- Clear TS flag in CR0 *)

  | 0x06 -> ClearTaskSwitchedFlag

  (* 0F 07 --- SYSRET --- Return to compatibility mode from fast system call      *)

  | 0x07 -> SysReturn

  (* 0F 0B --- UD2 --- Undefined instruction *)

  | 0x0b -> UndefinedInstruction

  (* 0F 0E --- FEMMS --- Clear MMX state *)

  | 0x0e -> MiscOp "femms"

  (* 0F 10/r --- MOVUPS xmm1,xmm2/m128 --- Move packed single precision floating-point values
                                           from xmm2/m128 to xmm1
     0F 11/r --- MOVUPS xmm2/m128,xmm1 --- Move packed single precision floating-point values
                                           from xmm1 to xmm2/m128                           
     0F 12/r --- MOVHLPS xmm1,xmm2 --- Move two packed single-precision floating-point values
                                       from high quadword of xmm2 to low quadword of xmm1  
     0F 12/r --- MOVLPS xmm,m64    --- Move two packed single-prec floating-point values
                                       from m64 to low quadword of xmm
     0F 13/r --- MOVLPS m64,xmm    --- Move two packed single-prec floating-point values
                                       from low quadword of xmm to m64                    *)

  | 0x10 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FXmmMove ("u",false,true,op2,op1)

  | 0x11 -> let (op1,op2) = get_modrm_xmm_operands ch 16 WR RD in 
	    FXmmMove ("u",false,true,op1,op2)

  | 0x12 -> let (op1,op2) = get_modrm_xmm_operands ch 8  RD WR in 
	    FXmmMove ("hl",false,true,op2,op1)

  | 0x13 -> let (op1,op2) = get_modrm_xmm_operands ch 8  WR RD in 
	    FXmmMove ("l",false,true,op1,op2)

  (* 0F 14/r --- UNPCKLPS xmm1,xmm2/m128 --- Unpacks and Interleaves single-precision 
                                             floating-point values from low quadwords 
                                             of xmm1 and xmm2/mem into xmm             *)

  | 0x14 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RW RD in
	    FXmmOp ("unpacklps",true,false,op1,op2)

  (* 0F 16/r --- MOVLHPS xmm1,xmm2 --- Move two packed single-prec floating-point value
                                       from low quadword of xmm2 to high quadword of xmm1
     0F 16/r --- MOVHPS xmm,m64    --- Move two packed single-prec floating-point values
                                       from m64 to high quadword of xmm
     0F 17/r --- MOVHPS m64,xmm    --- Move two packed single-prec floating-point values
                                       from high quadword of xmm to m64
  *)

  | 0x16 -> let (op1,op2) = get_modrm_xmm_operands ch 8  RD WR in 
	    FXmmMove ("lh",false,true,op2,op1)

  | 0x17 -> let (op1,op2) = get_modrm_xmm_operands ch 8  WR RD in 
	    FXmmMove ("h",false,true,op1,op2)

  | 0x18 -> px0f18 ch

  (* 0F 1F 00                      -- 3-byte nop 
   * 0F 1F 40 00                   -- 4-byte nop
   * 0F 1F 44 00 00                -- 5-byte nop 
   * 0F 1F 80 00 00 00 00          -- 7-byte nop
   * 0F 1F 84 00 00 00 00 00       -- 8-byte nop 
   *)

  | 0x1F ->
     let opc3 = ch#read_byte in
     begin
       match opc3 with
       | 0x00 -> MultiByteNop 3
       | 0x40 ->
          let opc4 = ch#read_byte in
          begin
            match opc4 with
            | 0x00 -> MultiByteNop 4
            | _ -> Unknown
          end
       | 0x44 ->
          let opc4 = ch#read_byte in
          begin
            match opc4 with
            | 0x00 ->
               let opc5 = ch#read_byte in
               begin
                 match opc5 with
                 | 0x00 -> MultiByteNop 5
                 | _ -> Unknown
               end
            | _ -> Unknown
          end
       | 0x80 ->
          let opc4 = ch#read_byte in
          begin
            match opc4 with
            | 0x00 ->
               let opc5 = ch#read_byte in
               begin
                 match opc5 with
                 | 0x00 ->
                    let opc6 = ch#read_byte in
                    begin
                      match opc6 with
                      | 0x00 ->
                         let opc7 = ch#read_byte in
                         begin
                           match opc7 with
                           | 0x00 -> MultiByteNop 7
                           | _ -> Unknown
                         end
                      | _ -> Unknown
                    end
                 | _ -> Unknown
               end
            | _ -> Unknown
          end
       | 0x84 ->
          let opc4 = ch#read_byte in
          begin
            match opc4 with
            | 0x00 ->
               let opc5 = ch#read_byte in
               begin
                 match opc5 with
                 | 0x00 ->
                    let opc6 = ch#read_byte in
                    begin
                      match opc6 with
                      | 0x00 ->
                         let opc7 = ch#read_byte in
                         begin
                           match opc7 with
                           | 0x00 ->
                              let opc8 = ch#read_byte in
                              begin
                                match opc8 with
                                | 0x00 -> MultiByteNop  8
                                | _ -> Unknown
                              end
                           | _ -> Unknown
                         end
                      | _ -> Unknown
                    end
                 | _ -> Unknown
               end
            | _ -> Unknown
          end
       | _ -> Unknown
     end

  (* 0F 20/r --- MOV r32,CRx  --- Move control register to r32 
     0F 21/r --- MOV r32,DRx  --- Move debug register to r32
     0F 22/r --- MOV CRx, r32 --- Move r32 to control register 
     0F 23/r --- MOV DRx, r32 --- Move r32 to debug register
  *)

  | 0x20 -> let (op1,op2) = get_modrm_cr_operands ch RD WR in Mov(4,op2,op1)
  | 0x21 -> let (op1,op2) = get_modrm_dr_operands ch RD WR in Mov(4,op2,op1)
  | 0x22 -> let (op1,op2) = get_modrm_cr_operands ch WR RD in Mov(4,op1,op2)
  | 0x23 -> let (op1,op2) = get_modrm_dr_operands ch WR RD in Mov(4,op1,op2)

  (* 0F 28/r --- MOVAPS xmm1,xmm2/m128 --- Move packed single precision floating-point values
                                           from xmm2/m128 to xmm1
     0F 29/r --- MOVAPS xmm2/m128,xmm1 --- Move packed single precision floating-point values
                                           from xmm1 to xmm2/m128                              *)

  | 0x28 -> let (op1,op2) = get_modrm_xmm_operands ch 16 WR RW in 
	    FXmmMove ("a",false,true,op2,op1)

  | 0x29 -> let (op1,op2) = get_modrm_xmm_operands ch 16 WR RD in 
	    FXmmMove ("a",false,true,op1,op2)

  (* 0F 2A/r --- CVTPI2PS xmm,mm/m64  --- Convert two signed doubleword integers from mm/m64
                                          to two sinle-prec floating-point values in xmm       *)

  | 0x2a -> let (op1,op2) = get_modrm_sized_operands ch 8 RD 16 WR in
	    FConvert (false,"pi","ps",op2,op1)

  (* 0F 2B/r --- MOVNTPS m128,xmm      --- Move packed single-prec floating-point values from
                                           xmm to m128 using non-temporal hint                *)

  | 0x2b -> let (op1,op2) = get_modrm_xmm_operands ch 16 WR RD in 
	    FXmmMove ("nt",false,true,op1,op2)

  (* 0F 2C/r --- CVTTPS2PI mm,xmm/m64  --- Convert two single-prec floating-point values from
                                           xmm/m64 to two signed doubleword integers in mm
                                           using truncation                   
     0F 2D/r --- CVTPS2PI mm,xmm/m64   --- Convert two packed single-prec floating-point values
                                           from xmm/m64 to two packed signed doublewords in
                                           mm   *)

  | 0x2c -> let (op1,op2) = get_modrm_xmm_mm_operands ch 8 RD WR in 
	    FConvert (true,"ps","pi",op2,op1)
	      
  | 0x2d -> let (op1,op2) = get_modrm_xmm_mm_operands ch 8 RD WR in 
	    FConvert (false,"ps","pi",op2,op1)

  (* 0F 2E/r --- UCOMISS xmm1,xmm2/m32 --- Compare lower single-precision floating-point
                                           value in xmm1 register with lower single-precision
                                           floating-point value in xmm2/m32 and set the
                                           status flags                 *)

  | 0x2e -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RD in 
	    FXmmOp ("ucomi",true,true,op2,op1)

  (* 0F 2F/r --- COMISS xmm1,xmm2/m32 --- Compare low single-precision floating-point values 
                                          in xmm1 and xmm2/mem32 and set the EFLAGS flags 
                                          accordingly.                  *)

  | 0x2f -> let (op1,op2) = get_modrm_xmm_operands ch 4 RD RD in
	    FXmmOp ("comi",true,true,op2,op1)

  (* 0F 31 --- RDTSC --- Read Time Stamp Counter into EDX:EAX                         *)

  | 0x31 -> ReadTimeStampCounter

  (* 0F 34 --- SYSENTER --- Fast call to privilege level 0 system procedures.         
     0F 35 --- SYSEXIT  --- Fast return from fast system call                         *)

  | 0x34 -> SysEnter
  | 0x35 -> SysExit

  | 0x38 -> px0f38 ch
    
  | 0x3a -> px0f3a ch

  | 0x3f -> px0f3f ch

  (* 0F 40/r --- CMOVO r32,r/m32   --- Move if overflow (OF=1)
     0F 41/r --- CMOVNO r32,r/m32  --- Move if not overflow (OF=0)
     0F 42/r --- CMOVB r32,r/m32   --- Move if below (CF=1)
     0F 42/r --- CMOVC r32,r/m32   --- Move if carry (CF=1)
     0F 42/r --- CMOVNAE r32,r/m32 --- Move if not above or equal (CF=1)
     0F 43/r --- CMOVAE r32,r/m32  --- Move if above or equal (CF=0)
     0F 43/r --- CMOVNB r32,r/m32  --- Move if not below (CF=0)
     0F 43/r --- CMOVNC r32,r/m32  --- Move if not carry (CF=0)
     0F 44/r --- CMOVE r32,r/m32   --- Move if equal (ZF=1)
     0F 44/r --- CMOVZ r32,r/m32   --- Move if zero (ZF=1)
     0F 45/r --- CMOVNE r32,r/m32  --- Move if not equal (ZF=0)
     0F 45/r --- CMOVNZ r32,r/m32  --- Move if not zero (ZF=0)
     0F 46/r --- CMOVBE r32,r/m32  --- Move if below or equal (CF=1 or ZF=1)  
     0F 46/r --- CMOVNA r32,r/m32  --- Move if not above (CF=1 or ZF=1)         
     0F 47/r --- CMOVA r32,r/m32   --- Move if above (CF=0 and ZF=0)
     0F 47/r --- CMOVNBE r32,r/m32 --- Move if not below or equal (CF=0 and ZF=0)
     0F 48/r --- CMOVS r32,r/m32   --- Move if sign (SF=1)
     0F 49/r --- CMOVNS r32,r/m32  --- Move if not sign (SF=0)
     0F 4A/r --- CMOVP r32,r/m32   --- Move if parity (PF=1)
     0F 4A/r --- CMOVPE r32,r/m32  --- Move if parity even (PF=1)
     0F 4B/r --- CMOVNP r32,r/m32  --- Move if not parity (PF=0)
     0F 4B/r --- CMOVPO r32,r/m32  --- Move if parity odd (PF=0)
     0F 4C/r --- CMOVL r32,r/m32   --- Move if less (SF != OF)
     0F 4C/r --- CMOVNGE r32,r/m32 --- Move if not greater or equal (SF != OF)
     0F 4D/r --- CMOVGE r32,r/m32  --- Move if greater or equal (SF=OF)
     0F 4D/r --- CMOVNL r32,r/m32  --- Move if not less (SF=OF)
     0F 4E/r --- CMOVLE r32,r/m32  --- Move if less or equal (ZF=1 or SF!=OF)
     0F 4E/r --- CMOVNG r32,r/m32  --- Move if not greater (ZF=1 or SF!OF)
     0F 4F/r --- CMOVG r32,r/m32   --- Move if greater (ZF=0 and SF=OF)
     0F 4F/r --- CMOVNLE r32,r/m32 --- Move if not less or equal (ZF=0 and SF=OF)
*)

  | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x47
  | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f ->
    let cc = index_to_condition_code (b2 - 0x40) in
    let (op1,op2) = get_modrm_operands ch RD WR in CMovcc (cc, 4, op2, op1) 
  
  (* 0F 52/r --- RSQRTPS xmm1,xmm2/m128 -- Computes the reciprocals of the square roots of
                                           the packed single-prec floating point values in
                                           xmm2/m128
     0F 53/r --- RCPPS xmm1,xmm2/m128  --- Computes the reciprocals of the packed single-prec
                                           floating-point values in xmm2/m128
     0F 54/r --- ANDPS xmm1,xmm2/m128  --- Bitwise logical AND of xmm2/m128 and xmm1 
     0F 55/r --- ANDNPS xmm1,xmm2/m128 --- Bitwise logical AND NOT of xmm2/m128 and xmm1
     0F 56/r --- ORPS xmm1,xmm2/m128   --- Bitwise or of xmm2/m128 and xmm1
     0F 57/r --- XORPS xmm1,xmm2/m128  --- Bitwise exclusive-or of xmm2/m128 and xmm1 
     0F 58/r --- ADDPS xmm1,xmm2/m128  --- Add packed single-precision floating point
                                           values from xmm2/m128 to xmm1
     0F 59/r --- MULPS xmm1,xmm2/m128  --- Multiply packed single-prec floating-point
                                           values in xmm2/m128 by xmm1
    all operations perform single precision operations, that is they store the result in
     lowest 32 bits of the xmm1 register only
  *)

  | 0x52 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("rsqrt",false,true,op2,op1)

  | 0x53 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("rcp",false,true,op2,op1)

  | 0x54 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("and",false,true,op2,op1)

  | 0x55 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("andn",false,true,op2,op1)

  | 0x56 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in	
	    FXmmOp ("or",false,true,op2,op1)

  | 0x57 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in	
	    FXmmOp ("xor",false,true,op2,op1)

  | 0x58 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("add",false,true,op2,op1)

  | 0x59 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("mul",false,true,op2,op1)

  (* 0F 5A/r --- CVTPS2PD xmm1,xmm2/m64 -- Convert two packed single-prec floating-point values
                                           in xmm2/m64 to two packed double-prec floating-point
                                           values in xmm1                                       
     0F 5B/r --- CVTDQ2PS xmm1,xmm2/m128 - Convert four packed signed doubleword integers from
                                           xmm2/m128 to four packed single-prec floating-point
                                           values in xmm1                               *)

  | 0x5a -> let (op1,op2) = get_modrm_xmm_operands ch 8  RD WR in 
	    FConvert (false,"ps","pd",op2,op1)

  | 0x5b -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FConvert (false,"dq","ps",op2,op1)

  (* 0F 5C/r --- SUBPS xmm1,xmm2/m128  --- Subtract packed single-prec floating-point
                                           values in xmm2/m128 from xmm1
     0F 5D/r --- MINPS xmm1,xmm2/m128  --- Return the minimum single-prec floating-point
                                           values in xmm2/m128
     0F 5E/r --- DIVPS xmm1,xmm2/m128  --- Divide packed single-prec floating-point values
                                           in xmm1 by packed single-prec floating-point
                                           values in xmm2/m128
     0F 5F/r --- MAXPS xmm1,xmm2/m128  --- Return the maximum single-prec floating-point
                                           values between xmm2/m128 and xmm1
     all operations perform single precision operations, that is they store the result in
     lowest 32 bits of the xmm1 register only                                                 *)

  | 0x5c -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("sub",false,true,op2,op1)
	      
  | 0x5d -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("min",false,true,op2,op1)

  | 0x5e -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("div",false,true,op2,op1)

  | 0x5f -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("max",false,true,op2,op1)

  (* 0F 60/r --- PUNPCKLBW mm,mm/m32 --- Interleave low-order bytes from mm and mm/m32
                                         into mm                                    
     0F 61/r --- PUNPCKLWD mm,mm/m32 --- Interleave low-order words from mm and mm/m32
                                         into mm                                    
     0F 62/r --- PUNPCKLDQ mm,mm/m32 --- Interleave low-order doublewords from mm and mm/m32
                                         into mm                                            *)

  | 0x60 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in Unpack ("l",1, op2, op1)
  | 0x61 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in Unpack ("l",2, op2, op1)
  | 0x62 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in Unpack ("l",4, op2, op1)

  (* 0F 63/r --- PACKSSWB mm1,mm2/m64 -- Converts 4 packed signed word integers from 
                                         mm1 and from mm2/m64 into 8 packed signed byte 
                                         integers in mm1 using signed saturation.        *)

  | 0x63 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedConvert ("sswb",op2,op1)

  (* 0F 64/r --- PCMPGTB mm1,mm2/m64 --- Compare packed signed byte integers in mm1 and mm2/m64
                                         for greater than and store result in mm1
     0F 65/r --- PCMPGTW mm1,mm2/m64 --- Compare packed signed word integers in mm1 and mm2/m64
                                         for greater than and store result in mm1
     0F 66/r --- PCMPGTD mm1,mm2/m64 --- Compare packed signed doubleword integers in mm1 and
                                         mm2/m64 and store result in mm1                   *)

  | 0x64 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedCompare ("gt",1,op2,op1)
  | 0x65 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedCompare ("gt",2,op2,op1)
  | 0x66 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedCompare ("gt",4,op2,op1)

  (* 0F 67/r --- PACKUSWB mm,mm/m64  --- Converts 4 signed word integers from mm and 4 signed
                                         word integers from mm/m64 into 8 unsigned byte 
                                         integers in mm using unsigned saturation.          *)

  | 0x67 -> let (op1,op2) = get_modrm_mm_operands ch 8 RW RD in PackedConvert("uswb",op2,op1)

  (* 0F 68/r --- PUNPCKHBW mm,mm/m64 --- Unpack and interleave high-order bytes from mm and
                                         mm/m64 into mm                                     
     0F 69/r --- PUNCHKHWD mm,mm/m64 --- Unpack and interleave high-order words from mm and
                                         mm/m64 into mm
     0F 6A/r --- PUNCHKHDQ mm,mm/m64 --- Unpack and interleave high-order doublewords from
                                         mm and mm/m64 into mm
 *)

  | 0x68 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in Unpack ("h",1, op2, op1)
  | 0x69 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in Unpack ("h",2, op2, op1)
  | 0x6a -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in Unpack ("h",4, op2, op1)

  (* 0F 6B/r --- PACKSSDW mm1,mm2/m64 -- Converts 2 packed signed doubleword integers 
                                         from mm1 and from mm2/m64 into 4 packed signed 
                                         word integers in mm1 using signed saturation. *)

  | 0x6b -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedConvert ("ssdw",op2,op1)

  (* 0F 6E/r --- MOVD mm,r/m32 --- Move doubleword from r/m32 to mm     *)

  | 0x6e -> let (op1,op2) = get_modrm_sized_operands ch 4 RD 8 WR in Movdw (4, op2, op1)

  (* 0F 6F/r --- MOVQ mm,mm/m64 -- Move quadword from mm/m64 to mm      *)

  | 0x6f -> let (op1,op2) = get_modrm_quadword_operands ch RD WR in Movdw (8, op2, op1)

  (* 0F 70/r ib --- PSHUFW mm1,mm2/m64,imm8 --- Shuffle the words in mm2/m64 based on the 
                                                encoding in imm8 and store the result in mm1        *)

  | 0x70 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedShuffle ("w", op2,op1,Some op3)

  | 0x71 -> px0f71 ch

  | 0x72 -> px0f72 ch

  | 0x73 -> px0f73 ch

  (* 0F 74/r --- PCMPEQB mm,mm/m64 --- Compare packed bytes in mm/m64 and mm for equality
     0F 75/r --- PCMPEQW mm,mm/m64 --- Compare packed words in mm/m64 and mm for equality
     0F 76/r --- PCMPEQD mm,mm/m64 --- Compare packed doublewords in mm/m64 and mm for
                                       equality                                          *)

  | 0x74 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedCompare ("eq",1,op2,op1)
	      
  | 0x75 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedCompare ("eq",2,op2,op1)
	      
  | 0x76 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedCompare ("eq",4,op2,op1)

  (* 0F 77 --- EMMS --- set the x87 FPU tag word to empty *)

  | 0x77 -> EmptyMmx

  (* 0F 7E/r --- MOVD r/m32,mm --- Move doubleword from mm to r/m32     *)

  | 0x7e -> let (op1,op2) = get_modrm_sized_operands ch 8 WR 4 RD in Mov (4, op1, op2)

  (* 0F 7F/r --- MOVQ mm/m64,mm -- Move quadword from mm to mm/m64      *)

  | 0x7f -> let (op1,op2) = get_modrm_quadword_operands ch WR RD in Mov (8, op1, op2)

  (* 0F 80 cd --- JO  rel32 --- Jump near if overflow (OF=1)
     0F 81 cd --- JNO rel32 --- Jump near if not overflow (OF=0)
     0F 82 cd --- JB  rel32 --- Jump near if below (CF=1)
     0F 82 cd --- JC  rel32 --- Jump near if carry (CF=1)
     0F 82 cd --- JNAE rel32 -- Jump near if not above or equal (CF=1)
     0F 83 cd --- JAE rel32 --- Jump near if above or equal (CF=0)
     0F 83 cd --- JNB rel32 --- Jump near if not below (CF=0)
     0F 83 cd --- JNC rel32 --- Jump near if not carry (CF=0)
     0F 84 cd --- JE  rel32 --- Jump near if equal (ZF=1)
     0F 84 cd --- JZ  rel32 --- Jump near if zero (ZF=1)
     0F 85 cd --- JNE rel32 --- Jump near if not equal (ZF=0)
     0F 85 cd --- JNZ rel32 --- Jump near if not zero (ZF=0)
     0F 86 cd --- JBE rel32 --- Jump near if below or equal (CF=1 or ZF=1) 
     0F 86 cd --- JNA rel32 --- Jump near if not above (CF=1 or ZF=1)
     0F 87 cd --- JA  rel32 --- Jump near if above (CF=0, ZF=0)
     0F 87 cd --- JNBE rel32 -- Jump near if not below or equal (CF=0, ZF=0)
     0F 88 cd --- JS  rel32 --- Jump near if sign (SF=1)
     0F 89 cd --- JNS rel32 --- Jump near if not sign (SF=0)
     0F 8A cd --- JP  rel32 --- Jump near if parity (PF=1)
     0F 8A cd --- JPE rel32 --- Jump near if parity even (PF=1)
     0F 8B cd --- JNP rel32 --- Jump near if not parity (PF=0)
     0F 8B cd --- JPO rel32 --- Jump near if parity odd (PF=0)
     0F 8C cd --- JL  rel32 --- Jump near if less (SF!=OF)
     0F 8C cd --- JNGE rel32 -- Jump near if not greater or equal (SF!=OF)
     0F 8D cd --- JGE rel32 --- Jump near if greater or equal (SF=OF)
     0F 8D cd --- JNL rel32 --- Jump near if not less (SF=OF)
     0F 8E cd --- JLE rel32 --- Jump near if less or equal (ZF=1 or SF!=OF)
     0F 8E cd --- JNG rel32 --- Jump near if not greater (Zf=1 or SF!=OF)
     0F 8F cd --- JG  rel32 --- Jump near if greater (ZF=0, SF=OF)
     0F 8F cd --- JNLE rel32 -- Jump near if not less or equal (ZF=0,SF=OF) *)

  | 0x80 | 0x81 | 0x82 | 0x83 | 0x84 | 0x85 | 0x86 | 0x87
  | 0x88 | 0x89 | 0x8a | 0x8b | 0x8c | 0x8d | 0x8e | 0x8f ->
    let cc = index_to_condition_code (b2 - 0x80) in
    begin
      try
	let op = read_target32_operand base ch in Jcc(cc,op)
      with
	Invalid_argument s -> 
	  InconsistentInstr ("Conditional jump with address problem: " ^ s)
		end
  
  (* 0F 90 --- SETO r/m8  ---- Set byte if overflow (OF=1)
     0F 91 --- SETNO r/m8 ---- Set byte if not overflow (OF=0)
     0F 92 --- SETB r/m8  ---- Set byte if below (CF=1)
     0F 92 --- SETC r/m8  ---- Set byte if carry (CF=1)
     0F 92 --- SETNAE r/m8 --- Set byte if not above or equal (CF=1)
     0F 93 --- SETEA r/m8 ---- Set byte if above or equal (CF=0)
     0F 93 --- SETNB r/m8 ---- Set byte if not below (CF=0)
     0F 93 --- SETNC r/m8 ---- Set byte if not carry (CF=0)
     0F 94 --- SETE r/m8  ---- Set byte if equal (ZF=1) 
     0F 94 --- SETZ r/m8  ---- Set byte if zero (ZF=1) 
     0F 95 --- SETNE r/m8 ---- Set byte if not equal (ZF=0)
     0F 95 --- SETNZ r/m8 ---- Set byte if not zero (ZF=0)
     0F 96 --- SETBE r/m8 ---- Set byte if below or equal (CF=1 or ZF=1) 
     0F 96 --- SETNA r/m8 ---- Set byte if not above (CF=1 or ZF=1)
     0F 97 --- SETA r/m8  ---- Set byte if above (CF=0 and ZF=0)
     0F 97 --- SETNBE r/m8 --- Set byte if not below or equal (CF=0 and ZF=0)
     0F 98 --- SETS r/m8  ---- Set byte if sign (SF=1)
     0F 99 --- SETNS r/m8 ---- Set byte if not sign (SF=0)
     0F 9A --- SETP r/m8  ---- Set byte if parity (PF=1)
     0F 9A --- SETPE r/m8 ---- Set byte if parity even (PF=1)
     0F 9B --- SETNP r/m8 ---- Set byte if not parity (PF=0)
     0F 9B --- SETPO r/m8 ---- Set byte if parity odd (PF=0)
     0F 9C --- SETL r/m8  ---- Set byte if less (SF != OF) 
     0F 9C --- SETNGE r/m8 --- Set byte if not greater or equal (SF!=OF)
     0F 9D --- SETGE r/m8 ---- Set byte if greater or equal (SF=OF)
     0F 9D --- SETNL r/m8 ---- Set byte if not less (SF=OF)
     0F 9E --- SETLE r/m8 ---- Set byte if less or equal (ZF=1 or SF!=OF)
     0F 9E --- SETNG r/m8 ---- Set byte if not greater (ZF=1 or SF!=OF)
     0F 9F --- SETG r/m8  ---- Set byte if greater (ZF=0,SF=OF) 
     0f 9F --- SETNLE r/m8 --- Set byte if not less or equal (ZF=0 and SF=OF)
*)

  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97
  | 0x98 | 0x99 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f ->
    let cc = index_to_condition_code (b2 - 0x90) in
    let (op,_) = get_modrm_byte_operands ch WR RD in Setcc (cc, op)

  (* 0F A0   --- PUSH FS   --- Push FS
     0F A1   --- POP FS    --- Pop FS *)

  | 0xa0 -> Push(4, seg_register_op FSegment RD)
  | 0xa1 -> Pop(4, seg_register_op FSegment WR)

  (* 0F A2   --- CPUID  --- Returns processor identification and feature 
                            information to the EAX, EBX, ECX and EDX
                            registers, as determined by input entered in EAX
                            (in some cases, ECX, as well)                    *)

  | 0xa2 -> Cpuid

  (* 0F A3/r --- BT  r/m32,r32 ---- Store selected bit in CF flag   *)

  | 0xa3 -> let (op1,op2) = get_modrm_operands ch RD RD in BitTest (op1, op2)

  (* 0F A4/r --- SHLD r/m32,r32,imm8 --- Shift r/m32 to left imm8 places 
                                         while shifting bits from r32 in from
                                         the right                            
     0F A5/r --- SHLD r/m32,r32,CL ----- Shift r/m32 to left CL places
                                         while shifting bits from r32 in from
                                         the right                             *)

  | 0xa4 -> let (op1,op2) = get_modrm_operands ch RW RD in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    Shld (op1, op2, op3)

  | 0xa5 -> let (op1,op2) = get_modrm_operands ch RW RD in Shld(op1, op2, cl_r RD)

  (* 0F A8 --- PUSH GS  -- Push Gs 
     0F A9 --- POP GS   -- Pop Gs *)

  | 0xa8 -> Push (4, seg_register_op GSegment RD)
  | 0xa9 -> Pop(4, seg_register_op GSegment WR)

  (* 0F AB/r --- BTS r/m32,r32  --- Store selected bit in CF flag and set      *)

  | 0xab -> let (op1,op2) = get_modrm_operands ch RW RD in BitTestAndSet (op1, op2)   

  (* OF AC   --- SHRD r/m32,r32,imm8 --- Shift r/m32 to right imm8 places
                                         while shifting bits from r32 in
                                         from the left  

     OF AD   --- SHRD r/m32,r32,CL   --- Shift r/m32 to right CL places
                                         while shifting bits from r32 in
                                         from the left                        *)

  | 0xac -> let (op1,op2) = get_modrm_operands ch RW RD in
	    let op3 = read_immediate_signed_byte_operand ch in
	    Shrd (op1, op2, op3)

  | 0xad -> let (op1,op2) = get_modrm_operands ch RW RD in Shrd (op1, op2, cl_r RD)

  | 0xae -> px0fae ch

  (* 0F AF/r --- IMUL r32,r/m32 --- dw register <- dw register * r/m32        
     Two-operand form: With this form the destination operand (the first operand) 
     is multiplied by the source operand (second operand). The destination operand 
     is a general-purpose register and the source operand is an immediate value, a 
     general-purpose register, or a memory location. The product is then stored in 
     the destination operand location.                                              *)

  | 0xaf -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RW in 
	    IMul (opsize,op2,op2,op1)

  (* 0F B0/r --- CMPXCHG r/m8,r8 --- Compare AL with r/m8. If equal, ZF is
                                     set and r8 is loaded into r/m8. Else
                                     clear ZF and load r/m8 into AL 
     0F B1/r --- CMPXCHG r/m32,r32 --- Compare EAX with r/m32. If equal, SF is
                                       set and r32 is loaded into r/m32. Else
                                       clear ZF and load r/m32 into EAX       *)

  | 0xb0 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in 
	    CmpExchange (1,op1,op2)

  | 0xb1 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RW RD in 
	    CmpExchange (opsize,op1,op2)

  (* 0F B3 --- BTR r/m32,r32 --- Store selected bit in CF flag and clear      *)

  | 0xb3 -> let (op1,op2) = get_modrm_operands ch RW RD in BitTestReset (op1, op2)

  (* 0F B6 --- MOVZX r32,r/m8 --- Move byte to doubleword with zero extension 
     0F B7 --- MOVZX r32,r/m16 -- Move word to doubleword with zero extension 

     Copies the contents of the source (second) operand to the destination operand
     and zero extends the value.                                                    *)

  | 0xb6 -> let (op1,op2) = get_modrm_sized_operands ch 1 RD 4 WR in Movzx (4,op2,op1)
  
  | 0xb7 -> let (op1,op2) = get_modrm_sized_operands ch 2 RD 4 WR in Movzx (4,op2,op1)

  | 0xba -> px0fba ch

  (* 0F BB/r --- BTC r/m32,r32 --- Store selected bit in CF flag and complement *)

  | 0xbb -> let (op1,op2) = get_modrm_operands ch RW RD in BitTestComplement (op1,op2)

  (* 0F BC/r --- BSF r32,r/m32 --- Bit scan forward on r/m32 
     0F BD/r --- BSR r32,r/m32 --- Bit scan reverse on r/m32                 *)

  | 0xbc -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD WR in 
	    BitScanForward (op2,op1)

  | 0xbd -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD WR in 
	    BitScanReverse (op2,op1)

  (* 0F BE --- MOVSX r32,r/m8 --- Move byte to doubleword with sign extension 
     0F BF --- MOVSX r32,r/m16 -- Move word to doubleword with sign extension *)

  | 0xbe -> let (op1,op2) = get_modrm_sized_operands ch 1 RD 4 WR in Movsx (4,op2,op1)
  | 0xbf -> let (op1,op2) = get_modrm_sized_operands ch 2 RD 4 WR in Movsx (4,op2,op1)

  (* 0F C0/r --- XADD r/m8,r8   --- exchange r8 and r/m8; load sum into r/m8
		 0F C1/r --- XADD r/m32,r32 --- exchange r32 and r/m32; load sum into r/m32 *)

  | 0xc0 -> let (op1,op2) = get_modrm_byte_operands ch RW RW in XAdd (op1,op2)
  | 0xc1 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RW RW in XAdd (op1,op2)

  (* 0F C3/r   --- MOVNTI m32,r32 --- Move doubleword from r32 to m32 using 
                                      non-temporal hint                         *)

  | 0xc3 -> let (op1,op2) = get_modrm_operands ch WR RD in Movnt (false,4,op1,op2)

  (* 0F C4/r ib --- PINSRW mm,r32/m16,imm8 --- Insert the low word from r32 or
                    from m16 into mm at the word position specified by imm8    *)

  | 0xc4 -> let (op1,op2) = get_modrm_sized_operands ch 4 WR 8 RD in 
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedInsert (2, op2, op1, op3)

  (* 0F C5/r ib --- PEXTRW reg,mm,imm8 --- Extract the word specified by imm8 from mm and 
                                           move it to reg, bits 15-0                        *)

  | 0xc5 -> let (op1,op2) = get_modrm_sized_operands ch 4 WR 8 RD in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedExtract (2, op1,op2,op3)

  (* 0F C6/r ib --- SHUFPS xmm1,xmm2/m128,imm8 --- Shuffle packed single precision
                    floating-point values selected by imm8 from xmm1 and xmm2/m128 to
                    xmm1                                                              *)

  | 0xc6 -> let (op1,op2) = get_modrm_double_quadword_operands ch RD RW in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    FXmmOpEx ("shuf", false, true, op2, op1, op3)

  | 0xc7 -> px0fc7 ch

  (* 0F C8+rd --- BSWAP r32 --- Reverses the byte order of a 32 bit register   *)

  | 0xc8 -> BSwap (eax_r RW)
  | 0xc9 -> BSwap (ecx_r RW)
  | 0xca -> BSwap (edx_r RW)
  | 0xcb -> BSwap (ebx_r RW)
  | 0xcc -> BSwap (esp_r RW)
  | 0xcd -> BSwap (ebp_r RW)
  | 0xce -> BSwap (esi_r RW)
  | 0xcf -> BSwap (edi_r RW)

  (* 0F D1/r --- PSRLW mm,mm/m64 --- Shift words in mm right by mm/m64
		 0F D2/r --- PSRLD mm,mm/m64 --- Shift doublewords in mm right by mm/m64
		 0F D3/r --- PSRLQ mm,mm/m64 --- Shift mm right by mm/m64                   *)

  | 0xd1 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("rl",2,op2,op1)
  | 0xd2 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("rl",4,op2,op1)
  | 0xd3 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("rl",8,op2,op1)

  (* 0F D4/r --- PADDQ mm1,mm2/m64 --- Add quadword integer mm2/m64 to mm1 *)

  | 0xd4 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedAdd (false,false,8,op2,op1)

  (* 0F D5/r --- PMULLW mm,mm/m64 --- Multiply packed signed word integers in mm1 and mm2/m64,
                                      store the low 16 bits in mm1                              *)

  | 0xd5 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedMultiply ("lw",op2,op1)

  (* 0F D8/r --- PSUBUSB mm,mm/m64 --- Subtract unsigned packed bytes in mm/m64 from
                                       unsigned packed bytes in mm and saturate results
     0F D9/r --- PSUBUSW mm,mm/m64 --- Subtract unsigned packed bytes in mm/m64 from
                                       unsigned packed bytes in mm and saturate results   *)

  | 0xd8 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (false,true,1,op2,op1)
	      
  | 0xd9 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (false,true,2,op2,op1)

  (* 0F DB/r --- PAND mm1,mm2/m64 --- Bitwise and of mm2/m64 and mm1  
     0F DC/r --- PADDUSB mm1,mm2/m64 --- Add packed unsigned byte integers from mm/m64 
                                         and mm and saturate the results
     0F DD/r --- PADDUSW mm1,mm2/m64 --- Add packed unsigned word integers from mm/m64 
                                         and mm and saturate the results                *)

  | 0xdb -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedOp ("and",8,op2,op1)
	      
  | 0xdc -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedAdd (false,true,1,op2,op1)
	      
  | 0xdd -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in
	    PackedAdd (false,true,2,op2,op1)

  (* 0F DF/r --- PANDN mm1,mm2/m64 --- Bitwise and not of mm2/m64 and mm1  *)

  | 0xdf -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedOp ("andn",8,op2,op1)

  (* 0F E0/r --- PAVGB mm1,mm2/m64 --- Average packed unsigned byte integers from mm2/m64
                                       and mm1 with rounding  
     0F E1/r --- PSRAW mm1,mm2/m64 --- Shift words in mm right by mm/mm64
     0F E2/r --- PSRAD mm1,mm2/m64 --- Shift doublewords in mm right by mm/mm64
     0F E3/r --- PAVGW mm1,mm2/m64 --- Average packed unsigned word integers from mm2/m64
                                       and mm1 with rounding                             *)

  | 0xe0 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedOp ("avg",1,op2,op1)
  | 0xe1 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("ra",2,op2,op1)
  | 0xe2 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("ra",4,op2,op1)
  | 0xe3 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedOp ("avg",2,op2,op1)

  (* 0F E4/r --- PMULHUW mm1,mm2/m64 --- Multiply the packed unsigned word integers in
                                         mm1 and mm2/m64 and store high 16 bits in mm1   
     0F E5/r --- PMULHW mm1,mm2/m64  --- Multiply the packed signed word integers in
                                         mm1 and mm2/m64 and store high 16 bits in mm1   *)

  | 0xe4 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedMultiply ("huw",op2,op1)
  | 0xe5 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedMultiply ("hw",op2,op1)

  (* 0F E7/r --- MOVNTQ m64,mm --- Move quadword from mm to m64 using non-temporal hint *)

  | 0xe7 -> let (op1,op2) = get_modrm_mm_operands ch 8 RW RD in Movnt (false,8,op1, op2)

  (* 0F E8/r --- PSUBSB mm,mm/m64 --- Subtract signed packed bytes in mm/m64 from signed
                                      packed bytes in mm and saturate results
     0F E9/r --- PSUBSW mm,mm/m64 --- Subtract signed packed words in mm/m64 from signed
                                      packed bytes in mm and saturate results              *)

  | 0xe8 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (true,false,1,op2,op1)

  | 0xe9 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (true,false,2,op2,op1)

  (* OF EB/r --- POR mm,mm/m64    --- Bitwise OR of mm/m64 and mm         
     0F EC/r --- PADDSB mm,m64    --- Add packed signed byte integers from mm/m64
                                      and mm and saturate the result
     0F ED/r --- PADDSW mm,m64    --- Add packed signed word integers from mm/m64
                                      and mm and saturate the result              *)

  | 0xeb -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedOp ("or",8,op2,op1)

  | 0xec -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedAdd (true,false,1,op2,op1)
	      
  | 0xed -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedAdd (true,false,2,op2,op1)

  (* 0F EE/r --- PMAX mm1,mm2/m64 --- Compare signed word integers in mm2/m64 and 
                                      mm1 and return maximum values               *)

  | 0xee -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in
	    PackedOp ("max",8,op2,op1)

  (* 0F EF/r --- PXOR mm1,mm2/m64 --- Bitwise XOR of mm1 and mm2/m64              *)

  | 0xef -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedOp ("xor",8,op2,op1)

  (* 0F F1/r --- PSLLW mm,mm/m64 --- Shift words in mm left by mm/m64 
     0F F2/r --- PSLLD mm,mm/m64 --- Shift doublewords in mm left by mm/m64 
     0F F3/r --- PSLLQ mm,mm/m64 --- Shift qword in mm left by mm/m64             *)

  | 0xf1 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("ll",2,op2,op1)
  | 0xf2 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("ll",4,op2,op1)
  | 0xf3 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedShift ("ll",8,op2,op1)

  (* 0F F4/r --- PMULUDQ mm1,mm2/m64 --- Multiply unsigned doubleword integer in mm1 by
                 unsigned doubleword integer in mm2/m64, and store the quadword result
                 in mm1                                                                 *)

  | 0xf4 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedMultiply ("udq", op2, op1)
 
  (* 0F F5/r --- PMADDWD mm,mm/m64 -- Multiply the packed words in mm by the packed
                                      words in mm/m64, add adjacent doubleword results
                                      and store in mm                                    *)

  | 0xf5 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedOp ("pmaddwd",8,op2,op1)

  (* 0F F6/r --- PSADBW mm1,mm2/m64 - Computes the absolute differences of the packed
                                      unsigned byte integers from mm2/m64 and mm1; 
                                      differences are then summed to produce and 
                                      unsigned word integer result                       *)

  | 0xf6 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedOp ("psadbw",8,op2,op1)

  (* 0F F8/r --- PSUBB mm,mm/m64 --- Subtract packed byte integers in mm/m64 from
                                     packed byte integers in mm
     0F F9/r --- PSUBW mm,mm/m64 --- Subtract packed word integers in mm/m64 from
                                     packed word integers in mm
     0F FA/r --- PSUBD mm,mm/m64 --- Subtract packed doubleword integers in mm/m64 from
                                     packed doubleword integers in mm        
     0F FB/r --- PSUBQ mm,mm/m64 --- Subtract quadword integer in mm from mm2/m64            *)

  | 0xf8 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (false,false,1,op2,op1)
	      
  | 0xf9 -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (false,false,2,op2,op1)
	      
  | 0xfa -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (false,false,4,op2,op1)
	      
  | 0xfb -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in 
	    PackedSubtract (false,false,8,op2,op1)

  (* 0F FC/r --- PADDB mm,mm/m64 --- Add packed byte integers from mm/m64 and mm   
     0F FD/r --- PADDW mm,mm/m64 --- Add packed word integers from mm/m64 and mm
     0F FE/r --- PADDD mm,mm/m64 --- Add packed doubleword integers from mm/m64 and mm     *)

  | 0xfc -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedAdd (false,false,1,op2,op1)
  | 0xfd -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedAdd (false,false,2,op2,op1)
  | 0xfe -> let (op1,op2) = get_modrm_mm_operands ch 8 RD RW in PackedAdd (false,false,4,op2,op1)

  | _ -> Unknown

