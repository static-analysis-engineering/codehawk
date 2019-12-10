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


let px9b opsize_override (ch:pushback_stream_int) =
  let b2 = ch#read_byte in
  match b2 with

  (* HB: These push backs are a guess based on objdump disassembly *)

  | 0x03
  | 0x0f
  | 0x2b
  | 0x47
  | 0x4f
  | 0x68
  | 0x85
  | 0x9b
  | 0xc3
  | 0xc9
  | 0xd1
  | 0xeb
  | 0xf6 -> begin ch#pushback 1 ; Wait end    (* HB: there are likely to be others *)

  | 0xd9 ->
    let modrm = ch#read_byte in
    let (md,reg,rm) = decompose_modrm modrm in
    begin
      match reg with
	
      (* 9B D9/6 --- FSTENV m14/28byte --- Store FPU environment to m14byte or m28byte
         after checking for pending unmasked floating-point exceptions
	 9B D9/7 --- FSTCW m2byte --- Store FPU control word to m2byte after checking
                                      for pending unmasked floating point exceptions *)
       
      | 6 -> let size = if opsize_override then 14 else 28 in
	     let op = get_rm_operand md rm ~size ch WR in
	     FStoreState ("env",true,size,op)

      | 7 -> let op = get_rm_word_operand md rm ch WR in FStoreState ("cw",true,2,op)
						      
      | _ -> Unknown

	end

  | 0xdb ->
    let b3 = ch#read_byte in
    begin
      match b3 with
					
      (* 9B DB E2 --- FCLEX --- Clear floating point exception flags after checking for 
                                pending unmasked floating point exceptions 
	 9B DB E3 --- FINIT --- Initialize FPU after checking for pending unmasked floating
                                point exceptions                                            *)

      | 0xe2 -> Fclex true
      | 0xe3 -> Finit true
	
      | _ -> Unknown
	
    end


  | 0xdd ->
    let modrm = ch#read_byte in
    let (md,reg,rm) = decompose_modrm modrm in
    begin
      match reg with

      (* 9B DD/6 --- FSAVE m94/108byte --- Store FPU state to m94byte or m108byte 
                                           after checking for pending unmasked 
                                           floating-point exceptions. Then 
                                           re-initialize the FPU                    *)

      | 6 -> let op = get_rm_operand md rm ch ~size:16 WR in FSaveState (true,op)
	
      (* 9B DD/7 --- FSTSW m2 byte --- Store FPU status word to m2byte after checking 
	                               for pending unmasked floating point exceptions *)

      | 7 -> let op = get_rm_word_operand md rm ch WR in FStoreState ("sw",true,2,op)
						      
      | _ -> Unknown
	
    end

  | 0xdf ->
    let b3 = ch#read_byte in
    begin
      match b3 with
	
      (* 9B DF E0 --- FWTSW AX --- Store FPU status word in AX register after checking
                                   for pending unmasked floating point exceptions      *)

      | 0xe0 -> FStoreState ("sw",true,2, ax_r WR)

      | _ -> Unknown
  
    end

  | _ -> Unknown
    
