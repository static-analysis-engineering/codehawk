(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023-2024  Aarno Labs LLC

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

(* tchlib *)
module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

(* bchlib *)
module D = BCHDoubleword
module SI = BCHSystemInfo
module SW = BCHStreamWrapper
module U = BCHByteUtilities

(* bchlibx86 *)
module R = BCHX86OpcodeRecords
module TF = BCHDisassembleInstruction

module TR = CHTraceResult


let testname = "bCHDisassembleX0Test"
let lastupdated = "2023-08-12"

let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)
                
let base = make_dw "0x400000"
                
let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:true s


(* single-byte instructions *)
let x86_0f_single () =
  let tests = [
      ("WBINVD",            "0f09", "wbinvd");
      ("UD2",               "0f0b", "ud2");
      ("WRMSR",             "0f30", "wrmsr");
      ("RDMSR",             "0f32", "rdmsr");
      ("RDPMC",             "0f33", "rdpmc");
    ] in
  begin
    TS.new_testsuite (testname ^ "_x86_double") lastupdated;
    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let firstbyte = ch#read_byte in
            let opcode = TF.disassemble_instruction ch base firstbyte in
            let opcodetxt = R.opcode_to_string opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* two-byte non-relative instructions *)
let x86_0f_double () =
  let tests = [
      ("LLDT-AX",      "0f00d0", "lldt ax");
      ("INVLPG-[EAX]", "0f0138", "invlpg (eax)");
      ("SERIALIZE",    "0f01e8", "serialize");
      ("XSAVE-[EDI]",  "0fae27", "xsave (edi)");
      ("XRSTOR-[EDI]", "0fae2f", "xrstor (edi)");
      ("MFENCE",       "0faef0", "mfence");
      ("UD1-ECX-ESP",  "0fb9cc", "ud1 ecx, esp");
      ("XRSTORS-[EDI]","0fc71f", "xrstors (edi)");
      ("XSAVES-[EDI]", "0fc72f", "xsaves (edi)");
      ("RDRABD-EDX",   "0fc7f2", "rdrand edx");
      ("RDSEED-EAX",   "0fc7f8", "rdseed eax");
    ] in
  begin
    TS.new_testsuite (testname ^ "_x86_double") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let firstbyte = ch#read_byte in
            let opcode = TF.disassemble_instruction ch base firstbyte in
            let opcodetxt = R.opcode_to_string opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    x86_0f_single ();
    x86_0f_double ();
    TS.exit_file ()
  end
    
