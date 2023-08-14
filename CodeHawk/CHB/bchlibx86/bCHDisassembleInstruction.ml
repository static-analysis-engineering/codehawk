(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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
open CHPretty
open CHNumerical

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHImmediate
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibx86 *)
open BCHDisassembleX0
open BCHDisassembleX8
open BCHDisassembleX9
open BCHDisassembleXc
open BCHDisassembleXd
open BCHDisassembleXf
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHOperand
open BCHX86Opcodes

module TR = CHTraceResult


let rec px660f 
    ?(seg_override=None)
    ?(addrsize_override=false) (ch:pushback_stream_int) (base:doubleword_int)  =
  let default nBytes = 
    begin
      ch#pushback nBytes ;
      parse_opcode ~seg_override ~addrsize_override ~opsize_override:true 0x0f ch base 
    end in
  let opc2 = ch#read_byte in
  match opc2 with

    (* 66 0F 10/r --- MOVUPD xmm1,xmm2/m128 --- Move packed double-prec floating-point values
                                                from xmm2/m128 to xmm1
       66 0F 11/r --- MOVUPD xmm2/m128,xmm1 --- Move double-prec floating-point value values
                                                from xmm1 to xmm2/m128
       66 0F 12/r --- MOVLPD xmm,m64        --- Move double-prec floating-point value from
                                                m64 to low quadword of xmm
       66 0F 13/r --- MOVLPD m64,xmm        --- Move double-prec floating-point value from
                                                low quadword of xmm to m64                   *)

  | 0x10 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmMove ("u",false,false,op1,op2)
	      
  | 0x11 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RW RD in 
	    FXmmMove ("u",false,false,op2,op1)

  | 0x12 -> let (op1,op2) = get_modrm_xmm_operands ch  8 RD RW in 
	    FXmmMove ("l",false,false,op1,op2)

  | 0x13 -> let (op1,op2) = get_modrm_xmm_operands ch  8 RW RD in 
	    FXmmMove ("l",false,false,op2,op1)

  (* 66 0F 14/r --- UNPCKLPD xmm1,xmm2/m128 --- Unpacks and Interleaves double-precision 
                                                floating-point values from low quadwords 
                                                of xmm1 and xmm2/m128.                  

     66 0F 15/r --- UNPCKHPD xmm1,xmm2/m128 --- Unpacks and Interleaves double-precision 
                                                floating-point values from high quadwords 
                                                of xmm1 and xmm2/m128.                    *)

  | 0x14 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("unpacklpd",true,false,op2,op1)

  | 0x15 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in
	    FXmmOp ("unpackhpd",true,false,op2,op1)

    (* 66 0F 16/r --- MOVHPD xmm,m64        --- Move double-prec floating-point value from
                                                m64 to high quadword of xmm
       66 0F 17/r --- MOVHPD m64,xmm        --- Move double-prec floating-point value from
                                                high quadword of xmm to m64

       66 0F 1F 84 00 00 00 00 00           --- 10-byte no-op

       66 0F 28/r --- MOVAPD xmm1,xmm2/m128 --- Move packed double precision floating
                                                point values from xmm2/m128 to xmm1
       66 0F 29/r --- MOVAPD xmm2,xmm1/m128 --- Move packed double precision floating
                                                point values from xmm1 to xmm2/m128    
    *)


  | 0x16 -> let (op1,op2) = get_modrm_xmm_operands ch  8 RD RW in 
	    FXmmMove ("h",false,false,op1,op2)

  | 0x17 -> let (op1,op2) = get_modrm_xmm_operands ch  8 RW RD in
	    FXmmMove ("h",false,false,op2,op1)

  | 0x1F ->
     let opc3 = ch#read_byte in
     begin
       match opc3 with
       | 0x84 ->
          let opc4 = ch#read_byte in
          begin
            match opc4 with
            | 0x00 ->
               let opc5 = ch#read_byte in
               begin
                 match opc5 with
                 | 0x00 ->
                    let opc6 =  ch#read_byte in
                    begin
                      match opc6 with
                      | 0x00 ->
                         let opc7 =  ch#read_byte in
                         begin
                           match opc7 with
                           | 0x00 ->
                              let opc8 = ch#read_byte in
                              begin
                                match opc8 with
                                | 0x00 -> MultiByteNop 10
                                | _ -> default 7
                              end
                           | _ -> default 6
                         end
                      | _ -> default 5
                    end
                 | _ -> default 4
               end
            | _ -> default 3
          end
       | _ -> default 2
     end

  | 0x28 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmMove ("a",false,false,op1,op2)
	      
  | 0x29 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RW RD in 
	    FXmmMove ("a",false,false,op2,op1)

  (* 66 0F 2A/r --- CVTPI2PD xmm,mm/m64   --- Convert two packed signed doubleword integers from
                                              mm/m64 to two packed double-prec floating-point
                                              values in xmm                          *)

  | 0x2A -> let (op1,op2) = get_modrm_sized_operands ch 8 RD 16 WR in 
	    FConvert (false,"pi","pd",op2,op1)

  (* 66 0F 2B/r --- MOVNTPD m128,xmm      --- Move packed double-prec floating-point values
                                              from xmm to m128 using non-temporal hint      *)

  | 0x2b -> let (op1,op2) = get_modrm_xmm_operands ch 16 WR RD in 
	    FXmmMove ("nt",false,false,op1,op2)

  (* 66 0F 2C/r --- CVTTPD2PI mm,xmm/m128  --- Convert two packed double-prec floating-point
                                               values from xmm/m128 to two packed signed 
                                               doubleword integers in mm using truncation
     66 0F 2D/r --- CVTPD2PI mm,xmm/m128   --- Convert two packed double-prec floating-point
                                               values from xmm/m128 to two packed signed 
                                               doubleword integers in mm               *)

  | 0x2c -> let (op1,op2) = get_modrm_sized_operands ch 16 RD 8 WR in 
	    FConvert (true, "pd","pi",op2,op1)

  | 0x2d -> let (op1,op2) = get_modrm_sized_operands ch 16 RD 8 WR in 
	    FConvert (false,"pd","pi",op2,op1)

  (* 66 0F 2E/r --- UCOMISD xmm1,xmm2/m128 --- Compares (unordered) the low double-prec
                                               floating-point values in xmm1 and xmm2/m64
                                               and set EFLAGS                              
     66 0F 2F/r --- COMISD xmm1,xmm2/m128  --- Compares low double-prec floating-point
                                               values in xmm1 and xmm2/m64 and set EFLAGS *)

  | 0x2e -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD RD in 
	    FXmmOp ("ucomi",true,false,op2,op1)

  | 0x2f -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD RD in 
	    FXmmOp ("comi",true,false,op2,op1)

  | 0x38 ->
    let opc3 = ch#read_byte in
    begin
      match opc3 with

      (* 66 0F 38 00/r --- PSHUFB xmm1,xmm2/m128 --- Shuffle bytes in xmm1 according to contents
                                                     of xmm2/m128                        *)
	
      | 0x00 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
		PackedShuffle ("b",op2,op1,None)

      (* 66 0F 38 OB/r --- PMULHRSW xmm1,xmm2/m128 --- Multiply 16-signed words, scale and 
                                                       round signed doublewords, pack high 
                                                       16 bits in xmm1                   *)

      | 0x0b -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
		PackedMultiply ("hrsw",op2,op1)

      (* 66 0F 38 1C/r --- PABSB xmm1,xmm2/m128 --- Compute absolute value of bytes in xmm2/m128
                                                    and store unsigned result in xmm1            
	 66 0F 38 1D/r --- PABSW xmm1,xmm2/m128 --- Compute absolute value of 16-bit integers in
                                                    xmm2/m128 and store unsigned result in xmm1
	 66 0F 38 1E/r --- PABSD xmm1,xmm2/m128 --- Compute absolute value of 32-bit integers in
                                                    xmm2/m128 and store unsigned result in xmm1
       *)

      | 0x1c -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
		PackedOp ("abs",1,op2,op1)

      | 0x1d -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in
		PackedOp ("abs",2,op2,op1)
		  
      | 0x1e -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
		PackedOp ("abs",4,op2,op1)

      (* 66 0F 38 28/r --- PMULDQ xmm1,xmm2/m128 --- Multiply packed signed dword integers in
                                                     xmm1 and xmm2/m128                    *)

      | 0x28 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
		PackedMultiply ("eq",op2,op1)

      (* 66 0F 38 29/r --- PCMPEQQ xmm1,xmm2/m128 --- Compare packed qwords in xmm2/m128 and
                                                      xmm1 for equality                     *)

      | 0x29 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
		PackedCompare ("eq",8,op2,op1)

      (* 66 0F 38 2A/r --- MOVNTDQA xmm1,m128 --- Move double quadword from m128 to xmm
                                                  using non-temporal hint                  *)

      | 0x2A -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
		Movnt (true,16,op2,op1)

      (* 66 0F 38 31/r --- PMOVZXBD xmm1,xmm2/m32 --- Zero extend 4 packed 8-bit integers in
                                                      the low 4 bytes of xmm2/m32 to 4 packed
                                                      32-bit integers in xmm1 
         66 0F 38 33/r --- PMOVZXWD xmm1,xmm2/m64 --- Zero extend 4 packed 16-bit integers in
                                                      the low 8 bytes of xmm2/m64 to 4 packed
                                                      32-bit integers in xmm1

       *)
      | 0x31 -> let (op1,op2) = get_modrm_xmm_operands ch 16 WR RD in
                PackedOp ("movzxbd",1,op2,op1)

      | 0x33 -> let (op1,op2) =  get_modrm_xmm_operands ch 16 WR RD in
                PackedOp ("movzxwd",2,op2,op1)
                
      (* 66 0F 38 37/r --- PCMPGTQ xmm1,xmm2/m128 --- Compare packed qwords in xmm2/m128 and
                                                      xmm1 for greater than                *)

      | 0x37 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
		PackedCompare ("gt",8,op2,op1)

      (* 66 0F 38 40/r --- PMULLD xmm1,xmm2/m128 --- Multiply packed dword signed integers 
                                                     in xmm1 and xmm2/m128 and store the 
                                                     low 32 bits of each in xmm1          *)

      | 0x40 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
		PackedMultiply ("ld", op2,op1)

      (* 66 0F 38 82/r --- INVPCID r32, m128 --- Invalidate Process Context Identifier *)

      | 0x82 ->
         let (op1, op2) = get_modrm_sized_operands ch 16 RD 4 RD in
         InvalidatePCID (op2, op1)

      (* 66 0F 38 DB/r --- AESIMC xmm1,xmm2/m128 --- Perform the InvMixColumn transformation on a
	                   128-bit round key from xmm2/m128 and store the result in xmm1

         66 0F 38 DC/r --- AESENC xmm1,xmm2/m128 --- Perform one round of an AES encryption flow,
                           operating on a 128-bit data (state) from xmm1 with a 128-bit round key
                           from xmm2/m128

         66 0F 38 DD/r --- AESENCLAST xmm1,xmm2/m128 --- Perform the last round of an AES 
                           encryption
                           flow, operating on a 128-bit data (state) from xmm1 with a 128-bit 
                           round key from xmm2/m128

         66 0F 38 DE/r --- AESDEC xmm1,xmm2/m128 --- Perform one round of an AES decryption flow
                           using the Equivalent Inverse Cipher operating on a 128-bit data 
                           (state) from xmm1 with a 128-bit round key from xmm2/m128

         66 0F 38 DF/r --- AESDECLAST xmm1,xmm2/m128 --- Perform the last round of an AES 
                           decryption
                           flow using the Equivalent Inverse Cipher, operaing on a 128-bit data
                           (state) from xmm1 with a 128-bit round key from xmm2/m128              *)

      | 0xdb -> let (op1,op2) = get_modrm_double_quadword_operands ch RW RD in 
		AESInvMix (op2,op1)

      | 0xdc -> let (op1,op2) = get_modrm_double_quadword_operands ch RW RD in 
		AESEncrypt (op2,op1)

      | 0xdd -> let (op1,op2) = get_modrm_double_quadword_operands ch RW RD in 
		AESEncryptLast (op2,op1)

      | 0xde -> let (op1,op2) = get_modrm_double_quadword_operands ch RW RD in 
		AESDecrypt (op2,op1)

      | 0xdf -> let (op1,op2) = get_modrm_double_quadword_operands ch RW RD in 
		AESDecryptLast (op2,op1)
									    
      | _ -> default 2
    end

  | 0x3a ->
    let opc3 = ch#read_byte in
    begin
      match opc3 with

      (* 66 0F 3A 0B --- ROUNDSD xmm1, xmm2/m64, imm8 ---
                         Round the low packed double precision floating-point value in 
                         xmm2/m64 and place the result in xmm1. The rounding mode is 
                         determined by imm8.
      *)

      | 0x0b -> let (op1,op2) = get_modrm_xmm_operands ch 8 RD RW in
		let op3 = read_immediate_unsigned_byte_operand ch in
		PackedRoundScalarDouble(op2, op1, op3)

      (* 66 0F 3A 0F --- PALIGNR xmm1,xmm2/m128,imm8 --- 
                         Concatenate destination and source operands, extract byte-aligned
	                       result shifted to the right by constant value imm8 into xmm1               *)

      | 0x0f -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in
		let op3 = read_immediate_unsigned_byte_operand ch in
		PackedAlignRight (op2, op1, op3)
					
      (* 66 0F 3A 14/r --- PEXTRB reg/m8,xmm2,imm8 -- Extract a byte integer value from xmm2 at
                                                      the source byte offset specified by imm8
                                                      into reg or m8
	 66 0F 3A 16/r --- PEXTRD r/m32,xmm2,imm8 --- Extract a dword integer value from xmm2 at
                                                      the source dword offset specified by imm8 
                                                      into r/m32                          *)
					
      | 0x14 -> let (op1,op2) = get_modrm_sized_operands ch 4 WR 16 RD in
		let op3 = read_immediate_unsigned_byte_operand ch in
		PackedExtract (1, op1, op2, op3)

      | 0x16 -> let (op1,op2) = get_modrm_sized_operands ch 4 WR 16 RD in
		let op3 = read_immediate_signed_byte_operand ch in
		PackedExtract (4, op1, op2, op3)
					
      (* 66 0F 3A 20/r --- PINSRB xmm1,r/m32,imm8 --- Insert a byte integer value from r/m32
         into xmm1 at the destination element specified by imm 8            *)
					
      | 0x20 ->	let (op1,op2) = get_modrm_sized_operands ch 4 RD 16 WR in
		let op3 = read_immediate_unsigned_byte_operand ch in
		PackedInsert (1, op2, op1, op3)
					
      (* 66 0F 3A 22/r --- PINSRD xmm1,r/m32,imm8 --- Insert a dword integer value from r/m32 
         into xmm1 at the destination element specified by imm 8            *)
					
      | 0x22 ->	let (op1,op2) = get_modrm_sized_operands ch 4 RD 16 WR in
		let op3 = read_immediate_unsigned_byte_operand ch in
		PackedInsert (4, op2, op1, op3)
					
      (* 66 0F 3A 44/r --- PCLMULQDQ xmm1, xmm2/m128, imm8 --- Carry-less multiplication of one
         quadword of xmm1 by one quadword of xmm2/m128; stores the 128-bit
         result in xmm1. The immediate is used to determine which quadwords
         of xmm1 and xmm2/m128 should be used:
         0 : LQL ; 1 : HQL ; 16 : LQH ; 17 : HQH                            *)
					
      | 0x44 ->
	let (op1,op2) = get_modrm_double_quadword_operands ch RD RW in
	let imm = read_immediate_unsigned_byte_operand ch in
	let immValue = imm#get_immediate_value#to_numerical#toInt in
	let xsel = match immValue with
	  |  0 -> "lql"
	  |  1 -> "hql"
	  | 16 -> "lqh"
	  | 17 -> "hqh"
	  | _ ->
	    begin
	      ch_error_log#add "disassembly" 
		(LBLOCK [ STR "Unexpected value in immediate for pclmulqdq instructions: " ; 
			  INT immValue ]) ;
	      "???"
	    end in
	let name = "pclmul" ^ xsel ^ "qdq" in
	PackedMultiply (name, op1, op2)

      (* 66 0F 3A 60/r imm8 --- PCMPESTRM xmm1, xmm2/m128, imm8 (op1:reg, op2:rm)
                                Perform a packed comparison of string data with explicit 
	                        lengths, generating a mask, and storing the result in XMM0

         66 0F 3A 61/r imm8 --- PCMPESTRI xmm1, xmm2/m128, imm8 (op1:reg, op2:rm)
                                Perform a packed comparison of string data with explicit 
	                        lengths, generating an index, and storing the result in ECX.

         66 0F 3A 62/r imm8 --- PCMPISTRM xmm1, xmm2/m128, imm8 (op1:reg, op2:rm) 
                                Perform a packed comparison of string data with implicit 
	                        lengths, generating a mask, and storing the result in XMM0.

	 66 0F 3A 63/r imm8 --- PCMPISTRI xmm1, xmm2/m128, imm8 
	                        Perform a packed comparison of string data with implicit 
                                lengths, generating an index, and storing the result in ECX. 
       *)

      | 0x60 ->
	let (op2,op1) = get_modrm_double_quadword_operands ch RD RD in
	let imm = read_immediate_unsigned_byte_operand ch in
	PackedCompareString (true,false,op1,op2,imm)

      | 0x61 ->
	let (op2,op1) = get_modrm_double_quadword_operands ch RD RD in
	let imm = read_immediate_unsigned_byte_operand ch in
	PackedCompareString (true,true,op1,op2,imm)

      | 0x62 ->
	let (op2,op1) = get_modrm_double_quadword_operands ch RD RD in
	let imm = read_immediate_unsigned_byte_operand ch in
	PackedCompareString (false,false,op1,op2,imm)

      | 0x63 ->
	let (op2,op1) = get_modrm_double_quadword_operands ch RD RD in
	let imm = read_immediate_unsigned_byte_operand ch in
	PackedCompareString (false,true,op1,op2,imm)

					
      (* 66 0F 3A DF/r --- AESKEYGENASSIST xmm1, xmm2/m128,imm8 --- Assist in AES round 
                           key generation
                           using an 8-bit Round Constant (RCON) specified in the immediate byte,
         operating on 128 bits of data specified in xmm2/m128 and store the result
         in xmm1                                                                *)
					
      | 0xdf -> let (op1,op2) = get_modrm_double_quadword_operands ch RD RW in
		let op3 = read_immediate_signed_byte_operand ch in
		AESKeyGenAssist (op2,op1,op3)
		  
      | _ -> default 2
    end
  (* 66 0F 50/r --- MOVMSKPD reg,xmm --- Extract 2-bit sign mask from xmm and store in 
                                         reg. The upper bits of r32 are filled with 
                                         zeros.                                        *)

  | 0x50 -> let (op2,op1) = get_modrm_xmm_reg_operands ch 16 WR RD in
	    PackedOp ("movmskpd",16,op1,op2)
			
  (* 66 0F 54/r  --- ANDPD xmm1,xmm2/m128  --- Bitwise logical AND of xmm2/m128 and xmm1
     66 0F 55/r  --- ANDNPD xmm1,xmm2/m128 --- Bitwise logical AND NOT of xmm2/m128 and xmm1
     66 0F 56/r  --- ORPD xmm1,xmm2/m128   --- Bitwise OR of xmm2/m128 and xmm1
     66 0F 57/r  --- XORPD xmm1,xmm2/m128  --- Bitwise exclusive OR of xmm2/m128 and xmm1
     66 0F 58/r  --- ADDPD xmm1,xmm2/m128  --- Add packed double-precision floating point 
                                               values from xmm2/m128 to xmm1 
     66 0F 59/r  --- MULPD xmm1,xmm2/m128  --- Multiply packed double-prec floating-point 
                                               vaues in xmm2/m128 by xmm1                   *)

  | 0x54 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("and",false,false,op2,op1)

  | 0x55 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("or",false,false,op2,op1)

  | 0x56 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("andn",false,false,op2,op1)

  | 0x57 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("xor",false,false,op2,op1)

  | 0x58 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("add",false,false,op2,op1)

  | 0x59 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("mul",false,false,op2,op1)

  (* 66 0F 5A/r  --- CVTPD2PS xmm1,xmm2/m128 - Convert two packed double-prec floating-point
                                               values in xmm2/m128 to two packed single-prec
                                               floating-point values in xmm1   

     66 0F 5B/r  --- CVTPS2DQ xmm1,xmm2/m128 - Convert four packed single-prec floating-point
                                               values from xmm2/m128 to four packed signed
                                               doubleword integers in xmm1               *)

  | 0x5a -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FConvert (false,"pd","ps",op2,op1)

  | 0x5b -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FConvert (false,"ps","dq",op2,op1)

  (* 66 0F 5C/r  --- SUBPD xmm1,xmm2/m128  --- Subtract packed double-prec floating-point
                                               values in xmm2/m128 from xmm1
     66 0F 5D/r  --- MINPD xmm1,xmm2/m128  --- Return the minimum double-prec floating-point
                                               values between xmm2/m128 and xmm1
     66 0F 5E/r  --- DIVPD xmm1,xmm2/m128  --- Divide packed double-prec floating-point values
                                               in xmm1 by packed double-prec floating-point
                                               values in xmm2/m128
     66 0F 5F/r  --- MAXPD xmm1,xmm2/m128  --- Return the maximum double-prec floating-point
                                               values between xmm2/m128 and xmm1                  *)

  | 0x5c -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FXmmOp ("sub",false,false,op2,op1)
	      
  | 0x5d -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FXmmOp ("min",false,false,op2,op1)

  | 0x5e -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FXmmOp ("div",false,false,op2,op1)

  | 0x5f -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("max",false,false,op2,op1)

  (* 66 0F 60/r --- PUNPCKLBW xmm1,xmm2/m128 --- Interleave low-order bytes from xmm1 and 
                                                 xmm2/m128 into xmm1
     66 0F 60/r --- PUNPCKLWD xmm1,xmm2/m128 --- Interleave low-order words from xmm1 and 
                                                 xmm2/m128 into xmm1
     66 0F 60/r --- PUNPCKLDQ xmm1,xmm2/m128 --- Interleave low-order doublewords from xmm1 
                                                 and xmm2/m128 into xmm1                     *)

  | 0x60 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in Unpack ("l",1,op2,op1)
  | 0x61 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in Unpack ("l",2,op2,op1)
  | 0x62 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in Unpack ("l",4,op2,op1)

  (* 66 0F 63/r --- PACKSSWB xmm1,xmm2/m128 -- Converts 8 packed signed word integers 
                                               from xmm1 and from xxm2/m128 into 16 packed
                                               signed byte integers in xxm1 using signed 
                                               saturation.                                *)

  | 0x63 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in PackedConvert("sswb",op2,op1)

  (* 66 0F 64/r --- PCMPGTB xmm1,xmm2/m128 --- Compare packed signed byte integers in xmm1 and
                                               xmm2/m128 for greater than and store the result
                                               in xmm1                                        
     66 0F 65/r --- PCMPGTW xmm1,xmm2/m128 --- Compare packed signed word integers in xmm1 and
                                               xmm2/m128 for greater than and store the result
                                               in xmm1
     66 0F 66/r --- PCMPGTD xmm1,xmm2/m128 --- Compare packed signed doubleword integers in
                                               xmm1 and xmm2/m128 for greater than and store
                                               the result in xmm1                           *)

  | 0x64 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedCompare ("gt",1,op2,op1)
  | 0x65 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedCompare ("gt",2,op2,op1)
  | 0x66 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedCompare ("gt",4,op2,op1)

  (* 66 0F 67/r --- PACKUSWB xmm1,xmm2/m128 --- Converts 8 signed word integers from xmm1 
                    and 8 signed word integers from xmm2/m128 into 16 unsigned byte integers 
                    in xmm1 using unsigned saturation    *)

  | 0x67 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in
	    PackedConvert ("uswb",op2,op1)

  (* 66 0F 68/r --- PUNPCKHBW xmm1,xmm1/m128 --- Unpack and interleave high-order bytes
                                                 from xmm1 and xmm2/m128 into xmm1
     66 0F 69/r --- PUNPCKHWD xmm1,xmm1/m128 --- Unpack and interleave high-order words
                                                 from xmm1 and xmm2/m128 into xmm1
     66 0F 6A/r --- PUNPCKHDQ xmm1,xmm1/m128 --- Unpack and interleave high-order doublewords
                                                 from xmm1 and xmm2/m128 into xmm1     *) 

  | 0x68 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Unpack ("h",1,op2,op1)
  | 0x69 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Unpack ("h",2,op2,op1)
  | 0x6a -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Unpack ("h",4,op2,op1)

  (* 66 0F 6B/r --- PACKSSDW xmm1,xmm2/m128 --- Converts 4 packed signed doubleword integers
                                                from xmm1 and from xxm2/m128 into 8 packed
                                                signed word integers in xxm1 using signed 
                                                saturation                               *)

  | 0x6b -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedConvert("ssdw",op2,op1)

 
  (* 66 0F 6C/r --- PUNPCKLQDQ xmm1,xmm1/m128 --- Unpack and interleave low-order quadword
                                                  from xmm1 and xmm2/m128 into xmm1
     66 0F 6D/r --- PUNPCKHQDQ xmm1,xmm1/m128 --- Unpack and interleave high-order quadword
                                                  from xmm1 and xmm2/m128 into xmm1          *)

  | 0x6c -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Unpack ("l",8,op2,op1)
  | 0x6d -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Unpack ("h",8,op2,op1)

  (* 66 0F 6E/r --- MOVD xmm,r/m32 --- Move doubleword from r/m32 to xmm                *)

  | 0x6e -> let (op1,op2) = get_modrm_sized_operands ch 4 RD 16 WR in Movdw (4, op2, op1)
       
  (* 66 0F 6F/r --- MOVDQA xmm1,xmm2/m128 --- Move aligned double quadword from
                                                xmm2/m128 to xmm1                       *) 
       
  | 0x6f -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Movdq (true,op2,op1)

  (* 66 0F 70/r ib --- PSHUFD xmm1,xmm2/m128,imm8 --- Shuffle the doubleword in xmm2/m128 
                                                      based on the encoding in imm8 and 
                                                      store the result in xmm1         *)

  | 0x70 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedShuffle ("d", op2,op1,Some op3)

  | 0x71 -> 
    let modrm = ch#read_byte in
    let (md,reg,rm) = decompose_modrm modrm in
    begin
      match reg with

      (* 66 0F 71/2 ib --- PSRLW xmm1,imm8 --- Shift words in xmm1 right by imm8
	 66 0F 71/4 ib --- PSRAW xmm1,imm8 --- Shift words in xmm1 right by imm8
	 66 0F 71/6 ib --- PSLLW xmm1,imm8 --- Shift words in xmm1 left by imm8    *)

      | 2 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("rl",2,op1,op2)
	       
      | 4 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("ra",2,op1,op2)
	       
      | 6 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("ll",2,op1,op2)
	       
      | _ -> default 2
	
    end
      
  | 0x72 ->
    let modrm = ch#read_byte in
    let (md,reg,rm) = decompose_modrm modrm in
    begin
      match reg with

      (* 66 0F 72/2 ib --- PSRLD xmm1,imm8 --- Shift doublewords in xmm1 right by imm8 while
                                               shifting in 0s  
         66 0F 72/4 ib --- PSRAD xmm1,imm8 --- Shift doublewords in xmm1 right by imm8
         66 0F 72/6 ib --- PSLLD xmm1,imm8 --- Shift doublewords in xmm1 left by imm8 while
                                               shifting in 0s                              *)

      | 2 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("rl",4,op1,op2)

      | 4 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("ra",4,op1,op2)
					
      | 6 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("ll",4,op1,op2)
					
      | _ -> default 2
    end
			
  | 0x73 -> 
    let modrm = ch#read_byte in
    let (md,reg,rm) = decompose_modrm modrm in
    begin
      match reg with
				
      (* 66 0F 73/2 ib --- PSRLQ  xmm1,imm8 --- Shift quadwords in xmm1 right by imm8 while
                                                shifting in 0s
	 66 0F 73/3 ib --- PSRLDQ xmm1,imm8 --- Shift xmm1 right by imm8 while shifting in 0s 
	 66 0F 73/6 ib --- PSLLQ  xmm1,imm8 --- Shift quadwords in xmm left by imm8 while 
                                                shifting in 0s
         66 0F 73/7 ib --- PSLLDQ xmm1,imm8 --- Shift xmm1 left by imm8 while shifting in 0s  *)
	
      | 2 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("rl",8,op1,op2)

      | 3 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("rl",16,op1,op2)
					
      | 6 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("ll",8,op1,op2)
	       
      | 7 -> let op1 = get_rm_operand md rm ~size:16 ch RD in
	     let op2 = read_immediate_unsigned_byte_operand ch in
	     PackedShift ("ll",16,op1,op2)
	       
      | _ -> default 2
    end
      
    (* 66 0F 74/r --- PCMPEQB xmm1,xmm2/m128 --- Compare packed bytes in xmm2/m128 and xmm1
                                                 for equality
       66 0F 75/r --- PCMPEQW xmm1,xmm2/m128 --- Compare packed words in xmm2/m128 and xmm1
                                                 for equality
       66 0F 76/r --- PCMPEQD xmm1,xmm2/m128 --- Compare packed doublewords in xmm2/m128 and xmm1
                                                 for equality                            *)

  | 0x74 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in PackedCompare ("eq",1,op2,op1)
  | 0x75 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in PackedCompare ("eq",2,op2,op1)
  | 0x76 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in PackedCompare ("eq",4,op2,op1)
			
  (* 66 0F 7C/r --- HADDPD xmm1,xmm2/m128 --- Horizontal add packed double-prec 
                                              floating-point values from xmm2/m128 to xmm1
     66 0F 7D/r --- HSUBPD xmm1,xmm2/m128 --- Horizontal subtract packed double-prec
                                              floating-point values from xmm2/m128 to xmm1  *)

  | 0x7c -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("hadd",false,false,op2,op1)
	      
  | 0x7d -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("hsub",false,false,op2,op1)

  (* 66 0F 7E/r --- MOVD r/m32,xmm --- Move doubleword from from xmm to r/m32      *)

  | 0x7e -> let (op1,op2) = get_modrm_sized_operands ch 4 WR 16 RD in Mov (4, op1, op2)

  (* 66 0F 7F/r --- MOVDQA xmm2/m128,xmm1 --- Move aligned double quadword from
                                                xmm1 to xmm2/m128                  *)
								   
  | 0x7f -> let (op1,op2) = get_modrm_xmm_operands ch 16 RW RD in Movdq (true,op1,op2)

  (* 66 0F A0  --- PUSH FS --- Push FS (16 bits)
     66 0F A1  --- POP FS  --- Pop FS  (16 bits)
     66 0F A8  --- PUSH GS --- Push GS (16 bits)  
     66 0F A9  --- POP GS  --- Pop GS  (16 bits)     *)

  | 0xa0 -> Push(2, seg_register_op FSegment RD)
  | 0xa1 -> Pop(2, seg_register_op FSegment WR)
  | 0xa8 -> Push(2, seg_register_op GSegment RD)
  | 0xa9 -> Pop(2, seg_register_op GSegment WR)

  (* 66 0F AE/6 --- TPAUSE r32, <edx>, <eax> Timed Pause *)

  | 0xae ->
     let modrmbyte = ch#read_byte in
     let (md, reg, rm) = decompose_modrm modrmbyte in
     begin
       match reg with
       | 6 -> let op = get_rm_operand md rm ch RD in TimedPause op
       | _ -> Unknown
     end

  (* 66 0F C2/r ib --- CMPPD xmm1,xmm2/m128,imm8 - Compare packed double-precision 
                                                   floating-point values in xmm2/m128 
                                                   and xmm1 using imm8 as comparison 
                                                   predicate                           *)

  | 0xc2 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RD in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    FXmmCompare (false,false,op2,op1,op3)

  (* 66 0F C4/r ib --- PINSRW xmm,r32/m16,imm8 --- Insert the low word from r32 or from m16
                                                  into mm at the word position specified
                                                  by imm8                                  *)

  | 0xc4 -> let (op1,op2) = get_modrm_sized_operands ch 4 RD 16 RW in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedInsert (2,op2,op1,op3)

  (* 66 0F C5/r ib --- PEXTRW reg,xmm,imm8 --- Extract the word specified by imm8 from xmm and
                                               move it to reg bits 15-0                        *)

  | 0xc5 -> let (op1,op2) = get_modrm_sized_operands ch 4 RD 16 WR in 
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    PackedExtract (2, op1,op2,op3)
	      
  (* 66 0F C6/r ib --- SHUFPD xmm1,xmm2/m128,imm --- Shuffle packed double-prec floating-point
                                                     values selected by imm8 from xmm1 and
                                                     xmm2/m128 to xmm1                  *)

  | 0xc6 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in
	    let op3 = read_immediate_unsigned_byte_operand ch in
	    FXmmOpEx ("shuf",false,false,op2,op1,op3)

  (* 66 0F D0/r --- ADDSUBPD xmm1,xmm2/m128 --- add/subtract double-precision floating-point
                                                values from xmm2/m128 to xmm1              *)

  | 0xd0 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    FXmmOp ("addsub",false,false,op2,op1)

  (* 66 0F D1/r --- PSRLW xmm1,xmm2/m128 --- Shift words in xmm1 right by xmm2/m128
     66 0F D2/r --- PSRLD xmm1,xmm2/m128 --- Shift doublewords right by xmm2/m128
     66 0F D3/r --- PSRLQ xmm1,xmm2/m128 --- Shift quadwords right by xmm2/m128       *)

  | 0xd1 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in PackedOp ("rl",2,op2,op1)
  | 0xd2 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in PackedOp ("rl",4,op2,op1)
  | 0xd3 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in PackedOp ("rl",8,op2,op1)
							       
  (* 66 0F D4/r --- PADDQ xmm1,xmm2/m128 --- Add packed quadword integers xmm2/m128 to xmm1 *)

  | 0xd4 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedAdd (false,false,8,op2,op1)

  (* 66 0F D5/r --- PMULLW xmm1,xmm2/m128 --- Multiply packed signed word integers in xmm1 and
                                              xmm2/m128 and store low 16 bits in xmm1          *)

  | 0xd5 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedMultiply ("lw",op2,op1)

  (* 66 0F D6/r --- MOVQ xmm2/m64, xmm1 --- Move quadword from xmm1 to xmm2/mem64.            *)

  | 0xd6 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in Movdw (8,op1,op2)

  (* 66 0F D7/r --- PMOVMSKB reg/xmm --- Move a byte mask of xmm to reg. The upper bits of 
                                         r32 or r64 are zeroed                                *)

  | 0xd7 -> let (op1,op2) = get_modrm_xmm_reg_operands ch 16 RD RW in
	    PackedOp ("movmskb",8,op2,op1)


  (* 66 0F D8/r --- PSUBUSB xmm1,xmm2/m128 --- Subtract packed unsigned byte integers in
                                               xmm2/m128 from packed unsigned integers in
                                               xmm1 and saturate results
     66 0F D9/r --- PSUBUSW xmm1,xmm2/m128 --- Subtract packed unsigned word integers in
                                               xmm2/m128 from packed unsigned integers in
                                               xmm1 and saturate results                   *)

  | 0xd8 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (false,true,1,op2,op1)

  | 0xd9 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (false,true,2,op2,op1)

  (* 66 0F DB/r --- PAND xmm1,xmm2/m128    --- Bitwise AND of xmm2/m128 and xmm1          
     66 0F DC/r --- PADDUSB xmm1,xmm1/m128 --- Add packed unsigned byte integers from xmm2/m128
                                               and xmm1 and saturate the results
     66 0F DD/r --- PADDUSW xmm1,xmm1/m128 --- Add packed unsigned word integers from xmm2/m128
                                               and xmm1 and saturate the results                 *)

  | 0xdb -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedOp ("and",16,op2,op1)

  | 0xdc -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedAdd (false,true,1,op2,op1)

  | 0xdd -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedAdd (false,true,2,op2,op1)

  (* 66 0F DF/r --- PANDN xmm1,xmm2/m128 --- Bitwise AND NOT of xmm2/m128 and xmm1     *)

  | 0xdf -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedOp ("andn",16,op2,op1)

  (* 66 0F E0/r --- PAVGB xmm1,xmm2/m128 --- Average packed unsigned byte integers from
                                             xmm2/m128 and xmm1 with rounding
     66 0F E1/r --- PSRAW xmm1,xmm2/m128 --- Shift words in xmm1 right by xmm2/m128 
     66 0F E2/r --- PSRAD xmm1,xmm2/m128 --- Shift doublewords in xmm1 right by xmm2/m128 
     66 0F E3/r --- PAVGW xmm1,xmm2/m128 --- Average packed unsigned word integers from
                                             xmm2/m128 and xmm1 with rounding             *)

  | 0xe0 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedOp ("avg",1,op2,op1)

  | 0xe1 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    PackedShift ("ra",2,op2,op1)
	      
  | 0xe2 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    PackedShift ("ra",4,op2,op1)

  | 0xe3 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedOp ("avg",2,op2,op1)

  (* 66 0F E4/r --- PMULHUW xmm1,xmm2/m128 --- Multiply packed unsigned word integers in xmm1
                                               and xmm2/m128 and store the high 16 bits in xmm1 
     66 0F E5/r --- PMULHW xmm1,xmm2/m128  --- Multiply packed signed word integers in xmm1
                                               and xmm2/m128 and store the high 16 bits in
                                               xmm1 *)

  | 0xe4 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedMultiply ("huw",op2,op1)

  | 0xe5 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedMultiply ("hw",op2,op1)

  (* 66 0F E6/r --- CVTTPD2DQ xmm1,xmm2/m128 --- Convert two packed double-prec floating-point
                                                 values from xmm2/m128 to two packed signed
                                                 doubleword integers in xmm1 using truncation  *)

  | 0xe6 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    FConvert (true,"pd","dq",op2,op1)

  (* 66 0F E7/r --- MOVNTDQ m128,xmm --- Move double quadword from xmm to m128 using
                                         non-temporal hint                              *)

  | 0xe7 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in Movnt (false,16,op1,op2)

  (* 66 0F E8/r --- PSUBSB xmm1,xmm2/m128 --- Subtract packed signed byte integers in xmm2/m128
                                              from packed signed byte integers in xmm1 and
                                              saturate results
     66 0F E8/r --- PSUBSB xmm1,xmm2/m128 --- Subtract packed signed word integers in xmm2/m128
                                              from packed signed word integers in xmm1 and
                                              saturate results                                *)

  | 0xe8 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (true,false,1,op2,op1)

  | 0xe9 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (true,false,2,op2,op1)

  (* 66 0F EB/r --- POR xmm1,xmm2/m128  ----- Bitwise OR of xmm1/m128 and xmm1   
     66 0F EC/r --- PADDSB xmm1,xmm1/m128 --- Add packed signed byte integers from xmm2/m128
                                              and xmm1 and saturate the results
     66 0F ED/r --- PADDSW xmm1,xmm1/m128 --- Add packed signed word integers from xmm2/m128
                                              and xmm1 and saturate the results *)

  | 0xeb -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedOp ("or",16,op2,op1)

  | 0xec -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    PackedAdd (true,false,1,op2,op1)

  | 0xed -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD WR in 
	    PackedAdd (true,false,2,op2,op1)

  (* 66 0F EE/r --- PMAXSW xmm1,xmm2/m128  -- Compare signed word integers in 
                                              xmm2/m128 and xmm1 and return maximum values. *)

  | 0xee -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in
	    PackedOp ("max",16,op2,op1)

  (* 66 0F EF/r --- PXOR xmm1,xmm2/m128 ----- Bitwise XOR of xmm2/m128 and xmm1 *)


  | 0xef -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedOp ("xor",16,op2,op1)

  (* 66 0F F1/r --- PSLLW xmm1,xmm2/m128 --- Shift words in xmm1 left by xmm2/m128
     66 0F F2/r --- PSLLD xmm1,xmm2/m128 --- Shift doublewords in xmm1 left by xmm1/m128
     66 0F F3/r --- PSLLQ xmm1,xmm2/m128 --- Shift quadwords in xmm1 left by xmm1/m128     *)

  | 0xf1 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedShift ("ll",2,op1,op1)

  | 0xf2 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedShift ("ll",4,op1,op1)

  | 0xf3 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedShift ("ll",8,op1,op1)

  (* 66 0F F4/r --- PMULUDQ xmm1,xmm2/m128 -- Multiply packed unsigned doubleword integers in
                                              xmm1 by packed unsigned doubleword integers in
                                              xmm2/m128 and store quadword result in xmm1   *)

  | 0xf4 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedMultiply ("udq",op2,op1)

  (* 66 0F F8/r --- PSUBB xmm1, xmm2/m128 --- Subtract packed byte integers in xmm2/m128
                                              from packed byte integers in xmm1  
     66 0F F9/r --- PSUBW xmm1, xmm2/m128 --- Subtract packed word integers in xmm2/m128
                                              from packed word integers in xmm1  
     66 0F FA/r --- PSUBD xmm1, xmm2/m128 --- Subtract packed doubleword integers in xmm2/m128
                                              from packed doubleword integers in xmm1            
     66 0F FB/r --- PSUBQ xmm1,xmm2/m128  --- Subtract packed quadword integers in xmm2/m128
                                              from packed quadword integers in xmm1           *)

  | 0xf8 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (false,false,1,op2,op1)

  | 0xf9 -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (false,false,2,op2,op1)

  | 0xfa -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (false,false,4,op2,op1)   

  | 0xfb -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedSubtract (false,false,8,op2,op1)   

  (* 66 0F FC/r --- PADDB xmm1,xmm2/m128 --- Add packed byte integers from xmm2/m128 and xmm1
     66 0F FD/r --- PADDW xmm1,xmm2/m128 --- Add packed word integers from xmm2/m128 and xmm1
     66 0F FE/r --- PADDD xmm1,xmm2/m128 --- Add packed doubleword integers from xmm2/m128 and 
                                             xmm1                                           *)

  | 0xfc -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedAdd (false,false,1,op2,op1)

  | 0xfd -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedAdd (false,false,2,op2,op1)

  | 0xfe -> let (op1,op2) = get_modrm_xmm_operands ch 16 RD RW in 
	    PackedAdd (false,false,4,op2,op1)
									
  | _ -> default 1


and parse_opcode
    ?(seg_override=None) 
    ?(opsize_override=false) 
    ?(addrsize_override=false) opc (ch:pushback_stream_int) (base:doubleword_int):opcode_t =
  let opsize = if opsize_override then 2 else 4 in
  let dseg = match seg_override with Some s -> s | _ -> DataSegment in
  let eseg = match seg_override with Some s -> s | _ -> ExtraSegment in
  match opc with
  (* 00/r ---- ADD r/m8,r8   ---- Add r8 to r/m8
     01/r ---- ADD r/m32,r32 ---- Add r32 to r/m32
     02/r ---- ADD r8,r/m8   ---- Add r/m8 to r8
     03/r ---- ADD r32,r/m32 ---- Add r/m32 to r32  *)

  | 0x00 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in Add (op1, op2)
  | 0x01 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RW RD in Add (op1, op2)
  | 0x02 -> let (op1,op2) = get_modrm_byte_operands ch RD RW in Add (op2, op1)
  | 0x03 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RW in Add (op2, op1)

  (* 04 ib --- ADD AL,imm8   ---- Add imm8 to AL
     05 id --- ADD EAX,imm32 ---- Add imm32 to EAX *)

  | 0x04 -> let op = read_immediate_signed_byte_operand ch in Add(al_r RW, op)
  | 0x05 -> let op = read_immediate_signed_operand opsize ch in 
	    let r = if opsize_override then ax_r RW else eax_r RW in
	    Add(r, op)

  (* 06 --- PUSH ES --- Push Extra segment register 
     07 --- POP ES  --- Pop Extra segment register     *)

  | 0x06 -> Push (opsize,seg_register_op ExtraSegment RD)
  | 0x07 -> Pop (opsize,seg_register_op ExtraSegment WR)

  (* 08/r ---- OR r/m8,r8   ----- r/m8 OR r8
     09/r ---- OR r/m32,r32 ----- r/m32 OR r32 
     0A/r ---- OR r8,r/m8   ----- r8 OR r/m8
     0B/r ---- OR r32,r/m32 ----- r32 OR r/m32 

     0C ib --- OR AL,imm8   ----- AL or imm8
     0D id --- OR EAX,imm32 ----- EAX or imm32 

     Performs a bitwise inclusive OR operation between the destination (first)
     and source (second) operands and stores the result in the destination operand
     location. 
     The OF and CF are cleared; the SF, ZF, and PF flags are set according to the
     result.                                                                       *)

  | 0x08 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in LogicalOr(op1, op2)
  | 0x09 -> let (op1,op2) = get_modrm_operands ch RW RD in LogicalOr(op1, op2)
  | 0x0a -> let (op1,op2) = get_modrm_byte_operands ch RD RW in LogicalOr(op2, op1)
  | 0x0b -> let (op1,op2) = get_modrm_operands ch RD RW in LogicalOr(op2, op1)

  | 0x0c -> let op = read_immediate_signed_byte_operand ch in LogicalOr (al_r RW, op)
  | 0x0d -> 
      let op = read_immediate_signed_operand opsize ch in
      let r = if opsize_override then ax_r RW else eax_r RW in 
      LogicalOr (r, op)

  (* 0E --- PUSH CS --- Push Code segment register *)

  | 0x0e -> Push (opsize,seg_register_op CodeSegment RD)

  | 0x0f -> px0f base opsize_override ch

  (* 10/r ---- ADC r/m8,r8   ---- Add with carry byte register to r/m8
     11/r ---- ADC r/m32,r32 ---- Add with CF r32 to r/m32
     12/r ---- ADC r8,r/m8   ---- Add with carry r/m8 to byte register
     13/r ---- ADC r32,r/m32 ---- Add with CF r/m32 to r32 *)

  | 0x10 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in AddCarry (op1, op2)
  | 0x11 -> let (op1,op2) = get_modrm_operands ch RW RD in AddCarry (op1,op2)
  | 0x12 -> let (op1,op2) = get_modrm_byte_operands ch RD RW in AddCarry (op2, op1)
  | 0x13 -> let (op1,op2) = get_modrm_operands ch RD RW in AddCarry (op2,op1)

  (* 14 ib --- ADC AL,imm8   ---- Add with carry imm8 to AL
     15 iw --- ADC AX, imm16 ---- Add with carry imm16 to AX
     15 id --- ADC EAX,imm32 ---- Add with carry imm32 to EAX                  *)

  | 0x14 -> let op = read_immediate_signed_byte_operand ch in AddCarry (al_r RW,op)
  | 0x15 -> 
      let op = read_immediate_signed_operand opsize ch in 
      let r = if opsize_override then ax_r RW else eax_r RW in
      AddCarry (r,op)

  (* 16 --- PUSH SS --- Push stack segment register 
     17 --- POP SS  --- Pop stack segment regiter      *)

  | 0x16 -> Push (opsize,seg_register_op StackSegment RD)
  | 0x17 -> Pop (opsize,seg_register_op StackSegment WR)

  (* 18/r ---- SBB r/m8,r8   ---- Subtract with borrow r8 from r/m8
     19/r ---- SBB r/m32,r32 ---- Subtract with borrow r32 from r/m32 
     1A/r ---- SBB r8,r/m8   ---- Subtract with borrow r/m8 from r8 
     1B/r ---- SBB r32,r/m32 ---- Subtract with borrow r/m32 from r32 
     1C ib --- SBB AL, imm8  ---- Subtract with borrow imm8 from AL
     1D iw --- SBB AX, imm16  --- Subtract with borrow imm16 from EAX
     1D id --- SBB EAX, imm32 --- Subtract with borrow imm32 from EAX
   *)

  | 0x18 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in SubBorrow (op1,op2)
  | 0x19 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RW RD in 
	    SubBorrow (op1,op2)

  | 0x1a -> let (op1,op2) = get_modrm_byte_operands ch RD RW in SubBorrow (op2,op1)
  | 0x1b -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RW in 
	    SubBorrow (op2,op1)

  | 0x1c -> let op = read_immediate_signed_byte_operand ch in SubBorrow (al_r RW, op)

  | 0x1d -> let op = read_immediate_signed_operand opsize ch in
	    let r = if opsize_override then ax_r RW else eax_r RW in
	    SubBorrow (r, op)

  (* 1E --- PUSH DS --- Push data segment register 
     1F --- POP DS  --- Pop data segment register     *)

  | 0x1e -> Push (opsize,seg_register_op DataSegment RD)
  | 0x1f -> Pop (opsize,seg_register_op DataSegment WR)

  (* 20/r ---- AND r/m8,r8   ---- r/m8 AND r8
     21/r ---- AND r/m32,r32 ---- r/m32 AND r32
     22/r ---- AND r8,r/m8   ---- r8 AND r/m8
     23/r ---- AND r32,r/m32 ---- r32 AND r/m32 
     24 ib --- AND AL,imm8   ---- AL AND imm8 
     25 id --- AND EAX,imm32 ---- EAX AND imm32 

     Performs a bitwise AND operation on the destination (first) and source
     (second) operands and stores the result in the destination operand location.
     The OF and CF flags are cleared; the SF, ZF, and PF flags are set according
     to the result.
  *)

  | 0x20 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in LogicalAnd (op1,op2)
  | 0x21 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RW RD in 
	    LogicalAnd (op1,op2)

  | 0x22 -> let (op1,op2) = get_modrm_byte_operands ch RD RW in LogicalAnd (op2,op1) 
  | 0x23 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RW in 
	    LogicalAnd (op2,op1)

  | 0x24 -> let op = read_immediate_unsigned_byte_operand ch in LogicalAnd (al_r RW, op)

  | 0x25 -> let op = read_immediate_unsigned_operand opsize ch in 
	    let r = if opsize_override then ax_r RW else eax_r RW in
	    LogicalAnd (r,op)

  (* 0x26 --- segment override prefix: ExtraSegment *)

  | 0x26 -> let opc = ch#read_byte in
	    parse_opcode ~addrsize_override ~opsize_override ~seg_override:(Some ExtraSegment) 
	      opc ch base

  (* 27   ---- DAA ---- Decimal Adjust AL after addition *)

  | 0x27 -> DAA


  (* 28/r ---- SUB r/m8,r8   ---- Subtract r8 from r/m8
     29/r ---- SUB r/m32,r32 ---- Subtract r32 from r/m32
     2A/r ---- SUB r8,r/m8   ---- Subtract r/m8 from r8
     2B/r ---- SUB r32,r/m32 ---- Subtract r/m32 from r32   *)

  | 0x28 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in Sub (op1,op2)
  | 0x29 -> let (op1,op2) = get_modrm_operands ch RW RD in Sub (op1,op2)
  | 0x2a -> let (op1,op2) = get_modrm_byte_operands ch RD RW in Sub (op2,op1)
  | 0x2b -> let (op1,op2) = get_modrm_operands ch RD RW in Sub (op2,op1)

  (* 2C ib --- SUB AL,imm8   ---- Subtract imm8 from AL
     2D iw --- SUB AX, imm16 ---- Subtract imm16 from AX
     2D id --- SUB EAX,imm32 ---- Subtract imm32 from EAX *)

  | 0x2c -> let op = read_immediate_signed_byte_operand ch in Sub(al_r RW, op)

  | 0x2d -> let op1 = if opsize_override then ax_r RW else eax_r RW in
	    let op2 = read_immediate_signed_operand opsize ch in 
	    Sub(op1, op2)

  (* 0x2E --- segment override prefix: CodeSegment *)

  | 0x2e -> let opc = ch#read_byte in
	    parse_opcode ~addrsize_override ~opsize_override ~seg_override:(Some CodeSegment)
	      opc ch base

  (* 0x2F --- Decimal adjust AL after subtraction *)

  | 0x2f -> DAS

  (* 30/r ---- XOR r/m8,r8   ---- r/m8 xor r8
     31/r ---- XOR r/m32,r32 ---- r/m32 xor r32
     32/r ---- XOR r8,r/m8   ---- r8 xor r/m8
     33/r ---- XOR r32,r/m32 ---- r32 xor r/m32                              
     34 ib --- XOR AL,imm8   ---- AL XOR imm8
     35 iw --- XOR AX, imm16 ---- AX XOR imm16
     35 id --- XOR EAX,imm32 ---- EAX XOR imm32                              

     Performs a bitwise exclusive OR operation on the destination (first) and source
     (second) operands and stores the result in the destination operand location.
     The OF and CF flags are cleared; the SF, ZF and PF flags are set according to the
     result.
*)

  | 0x30 -> let (op1,op2) = get_modrm_byte_operands ch RW RD in Xor (op1, op2)
  | 0x31 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RW RD in Xor (op1, op2)
  | 0x32 -> let (op1,op2) = get_modrm_byte_operands ch RD RW in Xor (op2, op1)
  | 0x33 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RW in Xor (op2, op1)

  | 0x34 -> let op = read_immediate_signed_byte_operand ch in Xor(al_r RW, op)

  | 0x35 -> let op1 = if opsize_override then ax_r RW else eax_r RW in
	    let op2 = read_immediate_signed_operand opsize ch in
	    Xor (op1, op2)

  (* 0x36 ---- segment override prefix: StackSegment *)

  | 0x36 -> let opc = ch#read_byte in
	    parse_opcode ~addrsize_override ~opsize_override ~seg_override:(Some StackSegment) 
	      opc ch base

  (* 37   ---- AAA --- ASCII Adjust after addition  *)

  | 0x37 -> AAA

  (* 38/r ---- CMP r/m8,r8   ---- Compare r8 with r/m8
     39/r ---- CMP r/m32,r32 ---- Compare r32 with r/m32 
     3A/r ---- CMP r8,r/m8   ---- Compare r/m8 with r8
     3B/r ---- CMP r32,r/m32 ---- Compare r/m32 with r32 *)

  | 0x38 -> let (op1,op2) = get_modrm_byte_operands ch RD RD in Cmp (op1, op2)
  | 0x39 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RD in Cmp (op1, op2)
  | 0x3a -> let (op1,op2) = get_modrm_byte_operands ch RD RD in Cmp (op2, op1)
  | 0x3b -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RD in Cmp (op2, op1)

  (* 3C ib --- CMP AL,imm8   ---- Compare imm8 with AL 
     3D iw --- CMP AX, imm16 ---- Compare imm16 with AX
     3D id --- CMP EAX,imm32 ---- Compare imm32 with EAX *)

  | 0x3c -> let op = read_immediate_signed_byte_operand ch in Cmp (al_r RD, op)

  | 0x3d -> let op = read_immediate_signed_operand opsize ch in
	    let r = if opsize_override then ax_r RD else eax_r RD in
	    Cmp (r, op)

  (* 0x3E --- segment override prefix: DataSegment *)

  | 0x3e -> let opc = ch#read_byte in
	    parse_opcode ~addrsize_override ~opsize_override ~seg_override:(Some DataSegment) 
	      opc ch base

  (* 0x3F --- AAS --- ASCII Adjust AL after subtraction *)
	      
  | 0x3f -> AAS	

  (* 40+rd -----  INC r32 ------- Increment doubleword register by 1 *)

  | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x47 ->
    let op = register_op (select_word_or_dword_reg opsize_override (opc - 0x40)) opsize RW in 
    Increment op

  (* 48+rd ----- DEC r32 ------- Decrement r32 by 1 *)

  | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f ->
    let op = register_op (select_word_or_dword_reg opsize_override (opc - 0x48)) opsize RW in 
    Decrement op

  (* 50+rd -----  PUSH r32 ------ Push r32  *)

  | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57 ->
    Push (opsize,cpureg_r ~opsize_override (opc - 0x50) RD)

  (* 58+rd -----  POP r32 ------- Pop top of stack into r32; increment stack pointer *)

  | 0x058 | 0x59 | 0x5a | 0x5b | 0x5c | 0x5d | 0x5e | 0x5f ->
    Pop (opsize,cpureg_r ~opsize_override (opc - 0x58) WR)

  (* 60 --- PUSHA --- Push EAX, ECX, EDX, EBX, original ESP, EBP, ESI, and EDI. 
     61 --- POPA  --- Pop EDI, ESI, EBP, EBX, EDX, ECX, and EAX.                    *)

  | 0x60 -> PushRegisters
  | 0x61 -> PopRegisters

  (* 63 --- ARPL r/m16,r16 --- Adjust RPL of r/m16 to not less than RPL of r16 
                               Adjusted Requested Privilege Level of Selector  *)

  | 0x63 -> let (op1,op2) = get_modrm_word_operands ch RW RD in Arpl (op1, op2)
      
  (* 0x64 --- FS segment override prefix 
     0x65 --- GS segment override prefix  *)

  | 0x64 -> let opc = ch#read_byte in
	    parse_opcode ~addrsize_override ~opsize_override ~seg_override:(Some FSegment) 
	      opc ch base

  | 0x65 -> let opc = ch#read_byte in
	    parse_opcode ~addrsize_override ~opsize_override ~seg_override:(Some GSegment) 
	      opc ch base

  | 0x66 -> 
    let opc = ch#read_byte in
    begin
      match opc with 

      | 0x0f -> px660f ch base

      (* 90 --- 2 byte no-op *)
              
      | 0x90 -> MultiByteNop 2

     (* Default 
	66 ---- change the default operand size from 32 to 16 *)

      | _ -> parse_opcode ~addrsize_override ~seg_override ~opsize_override:true opc ch base
    end

  (* 67 ------ address size override  *)

  | 0x67 -> let opc = ch#read_byte in
	    parse_opcode ~addrsize_override:true ~seg_override ~opsize_override opc ch base

  (* 68 ------ PUSH imm32 --------- Push sign-extended imm32;
                                    Stackpointer is decremented
                                    by the size of the stack
                                    pointer                             *)

  | 0x68 -> let op = read_immediate_signed_doubleword_operand ch in Push (4,op)

  (* 69/r iw - IMUL r16,r/m16 - r16 <- r/m32 * imm word
     69/r id - IMUL r32,r/m32 - r32 <- r/m32 * imm doubleword     *)

  | 0x69 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD WR in
	    let op3 = read_immediate_signed_operand opsize ch in
	    IMul (opsize,op2, op1, op3)

  (* 6A ------ PUSH imm8 ------ Push sign-extended imm8; stack
                                pointer is decremented by the
                                size of the stack pointer *)

  | 0x6a -> let op = read_immediate_signed_byte_operand ch in Push (opsize,op)

  (* 6B/r ib --- IMUL r16,r/m16,imm8 ---- r16 <- r/m16 * sign-extended imm8
     6B/r ib --- IMUL r32,r/m32,imm8 ---- r32 <- r/m32 * sign-extended imm8 *)

  | 0x6b -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RW in
	    let op3 = read_immediate_signed_byte_operand ch in
	    IMul (opsize,op2, op1, op3)

  (* 6C --- INSB --- Input byte from I/O port specified in DX into memory location ES:(E)DI
     6D --- INSD --- Input doubleword from I/O port specified in DX into memory location
                     ES:(E)DI                                                           *)

  | 0x6c -> InputStringFromPort (1, es_edi ~size:1 ~seg:eseg WR)
  | 0x6d -> InputStringFromPort (opsize, es_edi ~size:opsize ~seg:eseg WR)

  (* 6E --- OUTSB --- Output byte from memory location specified in DS:(E)SI or RSI to I/O
                      port specified in DX
     6F --- OUTSD --- Output doubleword from memory location specified in DE:(E)SI or RSI
                      to I/O port specified in DX                                        *)     

  | 0x6e ->  OutputStringToPort (1, ds_esi ~size:1 ~seg:dseg RD)
  | 0x6f ->  OutputStringToPort (opsize, ds_esi ~size:opsize ~seg:dseg RD)

  (* 70 ----- JO  rel8 ------ Jump short if overflow       (OF=1)
     71 ----- JNO rel8 ------ Jump short if not overflow   (OF=0)
     72 ----- JB  rel8 ------ Jump short if below          (CF=1)
     72 ----- JNAE rel8 ----- Jump short if not above      (CF=1)
     73 ----- JAE rel8 ------ Jump short if above or equal (CF=0)
     73 ----- JNB rel8 ------ Jump short if not below      (CF=0)
     73 ----- JNC rel8 ------ Jump short if not carry      (CF=0)
     74 ----- JE  rel8 ------ Jump short if equal          (ZF=1)
     74 ----- JZ  rel8 ------ Jump short if zero           (ZF=1)
     75 ----- JNE rel8 ------ Jump short if not equal      (ZF=0)
     75 ----- JNZ rel8 ------ Jump short if not zero       (ZF=0)
     76 ----- JBE rel8 ------ Jump short if below or equal (CF=1 or ZF=1)
     76 ----- JNA rel8 ------ Jump short if not above      (CF=1 or ZF=1)
     77  ---- JA  rel8 ------ Jump short if above          (CF=0, ZF=0)
     77 ----- JNBE rel8 ----- Jump short if not below or equal (CF=0, ZF=0)
     78 ----- JS  rel8 ------ Jump short if sign           (SF=1)
     79 ----- JNS rel8 ------ Jump short if not sign       (SF=0)
     7A ----- JP  rel8 ------ Jump short if parity         (PF=1)
     7A ----- JPA rel8 ------ Jump short if parity even    (PF=1)
     7B ----- JNP rel8 ------ Jump short if not parity     (PF=0)
     7B ----- JPO rel8 ------ Jump short if parity odd     (PF=0)
     7C  ---- JL  rel8 ------ Jump short if less           (SF!=OF)
     7C ----- JNGE rel8 ----- Jump short if not greater or equal (SF!=OF)
     7D ----- JGE rel8 ------ Jump short if greater or equal (SF=OF)
     7D ----- JNL rel8 ------ Jump short if not less       (SF=OF)
     7E ----- JLE rel8 ------ Jump short if less or equal  (ZF=1 or SF!=OF)
     7E ----- JNG rel8 ------ Jump short if not greater    (ZF=1 or SF!=OF)
     7F ----- JG  rel8 ------ Jump short if greater        (ZF=0, SF=OF)
     7F ----- JNLE rel8 ----- Jump short if not less or equal (ZF=0, SF=OF)  *)

  | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77
  | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f ->
    let cc = index_to_condition_code (opc - 0x70) in
    begin
      try
	let op = read_target8_operand base ch in Jcc (cc,op)
      with
	Invalid_argument s -> InconsistentInstr s
    end
  | 0x80 -> px80 ch
  | 0x81 -> px81 opsize_override ch
  | 0x82 -> px80 ch               (* 0x82 seems to be an alias for 0x80 *)
  | 0x83 -> px83 opsize_override ch

  (* 84/r ---- TEST r/m8,r8   ----- AND r8 with r/m8, set SF,ZF,PF according to result
     85/r ---- TEST r/m32,r32 ----- AND  r32 with r/m32, set SF,ZF,PF according to result *)

  | 0x84 -> let (op1,op2) = get_modrm_byte_operands ch RD RD in Test (op1,op2)
  | 0x85 -> let (op1,op2) = get_modrm_def_operands opsize_override ch RD RD in Test (op1,op2)

  (* 86/r ---- XCHG r/m8,r8  ----- Exchange r8 with byte from r/m8
     87/r ---- XCHG r/m32,r32 ---- Exchange r32 with doubleword from r/m32     *)

  | 0x86 -> let (op1,op2) = get_modrm_byte_operands ch RW RW in Xchg (op1, op2)
  | 0x87 -> let (op1,op2) = get_modrm_def_operands opsize_override ~seg_override ch RW RW in 
						Xchg (op1, op2)

  (* 88/r ---- MOV r/m8,r8   ------ Move r8 to r/m8
     89/r ---- MOV r/m32,r32 ------ Move r32 to r/m32
     8A/r ---- MOV r8,r/m8   ------ Move r/m8 to r8
     8B/r ---- MOV r32,r/m32 ------ Move r/m32 to r32 *)

  | 0x88 -> let (op1,op2) = get_modrm_byte_operands ch WR RD in  Mov (1, op1, op2)

  | 0x89 -> 
    let (op1,op2) = get_modrm_def_operands opsize_override ~seg_override ~addrsize_override
      ch WR RD in 
    Mov (opsize, op1, op2)

  | 0x8a -> let (op1,op2) = get_modrm_byte_operands ch RD WR in  Mov (1, op2, op1)

  | 0x8b -> 
    let (op1,op2) = get_modrm_def_operands opsize_override ~seg_override ~addrsize_override 
      ch RD WR in 
    Mov (opsize, op2, op1)

  (* 8C/r ---- MOV r/m16,SREG ---- Move segment register to r/m16 *)

  | 0x8c -> let (op1,op2) = get_modrm_seg_operands ~opsize_override ch WR RD in Mov (2,op1, op2)

  (* 8D/r ---- LEA r32,m --------- Store effective address for m in r32 *)

  | 0x8d -> let (op1,op2) = get_modrm_def_operands opsize_override ch AD WR in Lea (op2,op1)

  (* 8E/r ---- MOV SREG,r/m16 ---- Move r/m16 to segment register *)

  | 0x8e -> let (op1,op2) = get_modrm_seg_operands ~opsize_override ch RD WR in Mov (2,op2, op1)

  | 0x8f -> px8f ch

  (* 90+rd --- XCHG r32, EAX --- Exchange EAX with r32 *)

  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 ->
    let index = opc - 0x90 in
    let op1 = if opsize_override then ax_r RW else eax_r RW in
    let reg = if opsize_override then 
	index_to_word_register index 
      else 
	index_to_register index in
    let op2 = register_op reg opsize RW in
    Xchg (op2, op1)

  (* 98 ------ CBW  (16 bits) -- AX      <- sign-extend of AL
     98 ------ CWDE (32 bits) -- EAX     <- sign-extend of AX   *)

  | 0x98 -> 
      if opsize_override then 
	ConvertWordToDoubleword  (ax_r WR, al_r RD)
      else
	ConvertWordToDoubleword (eax_r WR, ax_r RD)

  (*  99 ------ CWD ---           DX:AX <- sign-extend of AX
      99 ------ CDQ ---           EDX:EAX <- sign-extend of EAX *)

  | 0x99 -> 
    if opsize_override then
      ConvertLongToDouble (dx_ax_r WR, ax_r RD )
    else
      ConvertLongToDouble (edx_eax_r WR, eax_r RD )

  (* 9B ------ WAIT  --- Check pending unmasked floating point exceptions
     9C ------ PUSHF --- Push EFLAGS 
     9D ------ POPF  --- Pop top of stack into EFLAGS    
     9E ------ SAHF  --- Store AH into Flags            
     9F ------ LAHF ---- Load AH <- Eflags(SF:ZF:0:AF:0:PF:1:CF) *)

  | 0x9b -> Wait
  | 0x9c -> PushFlags
  | 0x9d -> PopFlags
  | 0x9e -> StoreFlags
  | 0x9f -> LoadFlags

  (* A0 ------ MOV AL,moffs8   ---- Move byte at (seg:offset) to AL
     A1 ------ MOV EAX,moffs32 ---- Move doubleword at (seg:offset) to EAX 
     A2 ------ MOV moffs8,AL   ---- Move AL to seg:offset
     A3 ------ MOV moffs32,EAX ---- Mov EAX to (seg:offset)      *)

  | 0xa0 -> let a = ch#read_doubleword  in
	    let op = match seg_override with
	      | None -> absolute_op a 1 RD
	      | Some seg -> seg_absolute_op seg a 1 RD in
	    Mov ( 1, al_r WR, op)
	      
  | 0xa1 -> let a  = ch#read_doubleword in
	    let op = match seg_override with 
	      | None -> absolute_op a 4 RD
	      | Some seg -> seg_absolute_op seg a 4 RD in
	    Mov (4, eax_r WR, op)

  | 0xa2 -> let a = ch#read_doubleword in
	    let op = match seg_override with
	      | None -> absolute_op a 1 WR
	      | Some seg -> seg_absolute_op seg a 1 WR in
	    Mov (1, op, al_r RD)
	      
  | 0xa3 -> 
    let a = if addrsize_override then
	TR.tget_ok (numerical_to_doubleword (ch#read_num_signed_word))
      else 
	ch#read_doubleword in 
    let op = match seg_override with
      | None -> absolute_op a 4 WR
      | Some seg -> seg_absolute_op seg a 4 WR in
    Mov (4, op, eax_r RD)

  (* A4 ------ MOVS m8,m8    ----- move byte from address DS:ESI to ES:EDI
     A5 ------ MOVS m32,m32  ----- move dword from address DS:ESI to ES:EDI  *)

  | 0xa4 ->
     Movs (1,es_edi ~size:1 ~seg:eseg WR ,
           ds_esi ~size:1 ~seg:dseg RD,esi_r RW, edi_r RW)
  | 0xa5 ->
     Movs (opsize,es_edi ~size:opsize ~seg:eseg WR,
           ds_esi ~size:opsize ~seg:dseg RD, esi_r RW, edi_r RW)

  (* A6 ---- CMPS m8,m8 ---- compare byte at address DS:ESI with byte at address ES:EDI
     A7 ---- CMPS m32,m32 -- compare dword at address DS:ESI with dword at address ES:EDI  *)

  | 0xa6 -> Cmps (1,ds_esi ~size:1 ~seg:dseg RD, es_edi ~size:1 ~seg:eseg RD)
  | 0xa7 -> Cmps (opsize, ds_esi ~size:opsize ~seg:dseg RD, es_edi ~size:opsize ~seg:eseg RD)

  (* A8 ib --- TEST AL,imm8  ----- AND imm8 with AL, set SF,ZF,PF according to result 
     A9 ib --- TEST EAX,imm32 ---- AND imm32 with EAX, set SF,ZF,PF according to result   *)

  | 0xa8 -> let op = read_immediate_signed_byte_operand ch in Test (al_r RD,op)

  | 0xa9 -> let op1  = if opsize_override then ax_r RD else eax_r RD in
	    let op2 = read_immediate_signed_operand opsize ch in
	    Test (op1,op2)

  (* AA --- STOS m8  --- Store AL  at address ES:EDI
     AB --- STOS m32 --- Store EAX at address ES:EDI 
     66 AB  STOS m16 --- Store AX  at address ES:EDI    *)

  | 0xaa ->  Stos (1, es_edi ~size:1 ~seg:eseg WR, al_r RD, edi_r WR, dflag_op RD)
  | 0xab ->
     let srcop = if opsize = 2 then ax_r RD else eax_r RD in
     Stos (opsize, es_edi ~size:opsize ~seg:eseg WR, srcop, edi_r WR, dflag_op RD)

  (* AC --- LODSB --- Load byte at address DS:ESI into AL 
     AD --- LODSW --- Load word at address DS:ESI into AX           
     AD --- LODSD --- Load dword at address DS:ESI into EAX         *)

  | 0xac -> Lods (1, ds_esi ~size:1 ~seg:dseg RD)
  | 0xad -> Lods (opsize, ds_esi ~size:opsize ~seg:dseg RD)

  (* AE --- SCASB --- Compare AL with byte at ES:[EDI] and set status flags
     AF --- SCASW --- Compare AX with word at ES:[EDI] and set status flags
     AF --- SCASD --- Compare EAX with doubleword at ES:[EDI] and set status flags *)

  | 0xae -> Scas (1, es_edi ~size:1 ~seg:eseg RD)
  | 0xaf -> Scas (opsize, es_edi ~size:opsize ~seg:eseg RD)

  (* B0+rb --- MOV r8,imm8   ----- Move imm8 to r8 *)
  | 0xb0 | 0xb1 | 0xb2 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7 ->
    let regOp = register_op (index_to_byte_register (opc - 0xb0)) 1 WR in
    let op = read_immediate_signed_byte_operand ch in Mov (1, regOp, op)

  (* B8+rd --- MOV r32,imm32 ----- Move imm32 to r32 *)
  | 0xb8 | 0xb9 | 0xba | 0xbb | 0xbc | 0xbd | 0xbe | 0xbf ->
    let index = opc - 0xb8 in
    let reg = if opsize_override then 
	index_to_word_register index 
      else	
	index_to_register index in
    let regOp = register_op reg opsize WR in
    let op = read_immediate_unsigned_operand opsize ch in 
    Mov (opsize, regOp, op)

  | 0xc0 -> pxc0 ch
  | 0xc1 -> pxc1 opsize_override ch

  (* C2 iw -- RET imm16 - Near return to calling procedure and pop imm16
                          bytes from the stack
     C3 ----- RET ------- Near return to calling procedure *)

  | 0xc2 -> let imm = ch#read_i16 in Ret (Some imm)
  | 0xc3 -> Ret None

  | 0xc4 -> pxc4 ch   (* 3-byte avx instruction *)
  | 0xc5 -> pxc5 ch   (* 2-byte avx instruction *)

  | 0xc6 -> pxc6 ch
  | 0xc7 -> pxc7 opsize_override ch

  (* C8 --- ENTER imm16, imm8 --- Push EBP, set EBP to ESP, allocate stack space *)
  | 0xc8 ->
     let size = read_immediate_unsigned_word_operand ch in
     let nesting = read_immediate_unsigned_byte_operand ch in
     Enter (size,nesting)

  (* C9 --- LEAVE --- Set ESP to EBP, then pop EBP 
     
     Releases the stack frame set up by an earlier ENTER instruction. The LEAVE instruction
     copies the fram pointer (EBP) into the stack pointer register (ESP), which releases the
     stack space allocated to the stack frame. The old frame pointer (the frame pointer for
     the calling procedure that was saved by the ENTER instruction) is then popped from the
     stack into the EBP register, restoring the calling procedure's stack frame.        
   *)

  | 0xc9 -> Leave

  (* CA iw -- RET imm16 -- Far return to calling procedure and pop imm16
                           bytes from the stack
     CB    -- RET       -- Far return to calling procedure *)

  | 0xca -> let imm = ch#read_i16 in Ret (Some imm)
  | 0xcb -> Ret None

  (* CC ----- INT 3 ------- Interrupt 3: trap to debugger *)

  | 0xcc -> BreakPoint

  (* CD 29 ---- apparently added in Windows 8 as a new security feature;
                HexRays interpretation: int 29h  Win8: RtlFailFast(ecx)                 *)

  | 0xcd -> 
    let i = ch#read_byte in
    if i = 41 then 
      MiscOp "int 29h(RtlFailFast)"
    else if i = 6 then
      MiscOp "int 6 (undefined opcode)"
    else if i = 0x80 then
      LinuxSystemCall (eax_r RD)
    else
      begin
	ch_error_log#add "disassembly" 
	  (LBLOCK [ STR "Encountered opcode byte CD with index other than 0x29: " ; INT i ]) ;
	Unknown
      end

  (* CF ---- IRET ---- Interrupt return *)

  | 0xcf -> InterruptReturn opsize_override

  | 0xd0 -> pxd0 ch
  | 0xd1 -> pxd1 opsize_override ch
  | 0xd2 -> pxd2 ch
  | 0xd3 -> pxd3 opsize_override ch

  (* D4 0A --- AAM         --- ASCII Adjust AX after multiply
     D4 ib --- AAM imm8    --- ASCII Adjust AX after multiply    *)

  | 0xd4 ->
    let i = ch#read_byte in
    begin
      match i with
      | 0x0a -> AAM (ax_r RW)
      | _ ->
         AAM (immediate_op (TR.tget_ok (signed_immediate_from_int i)) 1)
    end

  (* D5 0A --- AAD          --- ASCII Adjust AX before division
     D5 ib --- AAD imm8     --- ASCII Adjust AX before division  *)
  | 0xd5 ->
    let i = ch#read_byte in
    begin
      match i with
      | 0x0a -> AAD (ax_r RW)
      | _ ->
         AAD (immediate_op (TR.tget_ok (signed_immediate_from_int i)) 1)
    end

  (* D6 --- SETALC --- Set Al on Carry (undocumented)                  *)

  | 0xd6 -> SetALC

  (* D7 --- XLAT --- Table Lookup Translation
                     Set AL to memory byte DS:[(E)BX + unsigned AL].   *)

  | 0xd7 -> TableLookupTranslation

  | 0xd8 -> pxd8 opsize_override ch
  | 0xd9 -> pxd9 opsize_override ch
  | 0xda -> pxda opsize_override ch
  | 0xdb -> pxdb opsize_override ch
  | 0xdc -> pxdc opsize_override ch
  | 0xdd -> pxdd opsize_override ch
  | 0xde -> pxde opsize_override ch
  | 0xdf -> pxdf opsize_override ch

  (* E2 cb --- LOOP rel8 --- Decrement count; jump short if count is not equal to 0 *)

  | 0xe2 -> 
    begin
      try
	let op = read_target8_operand base ch in DirectLoop op
      with
	Invalid_argument s ->
	  InconsistentInstr ("DirectLoop with address problem: " ^ s)
    end

  (* E3 cb --- JECXZ rel8 --- Jump short if ECX register is 0    *)

  | 0xe3 -> 
    begin
      try
	let op = read_target8_operand base ch in Jecxz op
      with
	Invalid_argument s ->
	  InconsistentInstr ("Jecxz with address problem: " ^ s)
    end

  (* E4 ib --- IN AL,imm8 --- Input byte from imm8 I/O port address into AL
     E5 ib --- IN AX,imm8 --- Input word from imm8 I/O port address into AX
     E5 ib --- IN EAX,imm8 -- Input dword from imm8 I/O port address into EAX *)
      
  | 0xe4 -> 
    let port = read_immediate_unsigned_byte_operand ch in
    InputFromPort (1,al_r WR,port)

  | 0xe5 -> 
    let port = read_immediate_unsigned_byte_operand ch in
    let dest = if opsize_override then ax_r WR else eax_r WR in
    InputFromPort (opsize,dest,port) 

  (* E6 ib --- OUT imm8,AL --- Output byte in AL to I/O port address imm8
     E7 ib --- OUT imm8,AX --- Output word in AX to I/O port address imm8
     E7 ib --- OUT imm8,EAX -- Output doubleword in EAX to I/O port address imm8 *)

  | 0xe6 -> 
    let port = read_immediate_unsigned_byte_operand ch in
    OutputToPort (1,port,al_r RD)

  | 0xe7 ->
    let port = read_immediate_unsigned_byte_operand ch in
    let dest = if opsize_override then ax_r RD else eax_r RD in
    OutputToPort (opsize,port,dest)

  (* E8 cd --- CALL rel32 --- Call near, relative, displacement
                              relative to next instruction      *)

  | 0xe8 -> 
    begin
      try
	let op = read_target32_operand base ch in DirectCall op
      with
	Invalid_argument s ->
	  InconsistentInstr ("Direct call with address problem " ^ s)
    end

  (* E9 cd --- JMP rel32 --- Jump near relative, RIP = RIP + 32bit disp 
     EB cb --- JMP rel8  --- Jump near, RIP=RIP+8bit disp sign-extended *)

  | 0xe9 -> 
    begin
      try
	let op = read_target32_operand base ch in DirectJmp op
      with
	Invalid_argument s ->
	  InconsistentInstr ("Direct jmp with address problem " ^ s)
    end

  | 0xea ->
     let addr = ch#read_doubleword in
     let sd = ch#read_ui16 in
     let op = far_absolute_op sd addr 4 RD in
     DirectJmp op

  | 0xeb -> 
    begin
      try
	let op = read_target8_operand  base ch in DirectJmp op 
      with
	Invalid_argument s ->
	  InconsistentInstr ("Direct jmp with address problem " ^ s)
    end

  (* EC --- IN AL,DX   --- Input byte from I/O port in DX into AL
     ED --- IN AX,DX   --- Input word from I/O port in DX into AX
     ED --- IN EAX,DX  --- Input word from I/O port in DX into EAX    *)

  | 0xec -> InputFromPort (1,al_r WR,dx_r RD)
  | 0xed -> 
    let dest = if opsize_override then ax_r WR else eax_r WR in
    InputFromPort (opsize, dest, dx_r RD)

  (* EE --- OUT DX,AL  --- Output byte in AL to I/O port address in DX
     EF --- OUT DX,AX  --- Output word in AX to I/O port address in DX
     EF --- OUT DX,EAX --- Output doubleword in EAX to I/O port address in DX *)

  | 0xee -> OutputToPort (1,dx_r RD, al_r RD)
  | 0xef ->
    let src = if opsize_override then ax_r RD else eax_r RD in
    OutputToPort (opsize,dx_r RD,src)
	    
      
  (* F0 --- LOCK --- prefix that forces an operation that ensures exclusive use of
                     shared memory in a multiprocessor environment                   *)

  | 0xf0 -> 
    let address = base#add_int (ch#pos - 1) in
    (* let opc = ch#read_byte in *)
    begin
      system_info#add_locked_instruction address ; MiscOp "lock"
      (* parse_opcode ~seg_override ~opsize_override opc ch base *)
    end

  | 0xf2 -> pxf2 dseg eseg opsize_override ch base
  | 0xf3 -> pxf3 dseg eseg opsize_override ch

  (* F4 --- HLT --- Halt; Stops instruction execution and places the processor in a HALT
                    state.                                                           *)

  | 0xf4 -> Halt

  (* F5 --- CMC --- Complement CF flag *)

  | 0xf5 -> ComplementCF

  | 0xf6 -> pxf6 ch
  | 0xf7 -> pxf7 opsize_override ch

  (* F8 --- CLC --- Clear Carry flag
     F9 --- STC --- Set Carry flag
     FA --- CLI --- Clear Interrupt flag
     FB --- STI --- Set Interrupt flag
     FC --- CLD --- Clear DF flag
     FD --- STD --- Set DF flag          

     Clears/sets the Direction Flag in the EFLAGS register. When the DF flag is set to 1,
     string operations decrement the index registers (ESI and/or EDI)
   *)

  | 0xf8 -> ClearCF
  | 0xf9 -> SetCF
  | 0xfa -> ClearInterruptFlag
  | 0xfb -> SetInterruptFlag
  | 0xfc -> ClearDF
  | 0xfd -> SetDF

  | 0xfe -> pxfe ch
  | 0xff -> pxff seg_override opsize_override ch

  | _ -> Unknown


let count = ref 0
let rep = ref 0 


(* base is used to compute an absolute target address for a relative jump or call:
   absolute address = base + position, so base should be the base of the code section
   being disassembled (not necessarily the code base, if there are multiple code
   sections)
*)
let disassemble_instruction (ch:pushback_stream_int) (base:doubleword_int) first_byte  = 
  try
   parse_opcode first_byte ch base
  with
    InconsistentInstruction s -> InconsistentInstr s
  | Invalid_input s -> InconsistentInstr s
  | IO.No_more_input ->
    let address = base#add_int ch#pos in
    begin
      ch_error_log#add "no more input"
	(LBLOCK [ STR "No more input at position " ; address#toPretty ; STR " (" ;
		  INT ch#pos ; STR ")" ]) ;
      raise IO.No_more_input
    end
	
