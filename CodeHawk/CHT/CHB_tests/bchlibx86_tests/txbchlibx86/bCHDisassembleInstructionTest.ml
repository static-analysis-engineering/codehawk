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


let testname = "bCHDisassembleInstructionTest"
let lastupdated = "2023-08-11"

let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)
                
let base = make_dw "0x400000"
                
let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:true s

 
(* single-byte instructions *)
let x86_single () =
  let tests = [
      ("PUSH ES",          "06", "push %es");
      ("POP ES",           "07", "pop %es");
      ("PUSH CS",          "0e", "push %cs");
      ("PUSH SS",          "16", "push %ss");
      ("POP SS",           "17", "pop %ss");
      ("PUSH DS",          "1e", "push %ds");
      ("POP DS",           "1f", "pop %ds");
      ("DAA",              "27", "daa");
      ("DAS",              "2f", "das");
      ("AAA",              "37", "aaa");
      ("AAS",              "3f", "aas");
      ("INC EAX",          "40", "inc eax");
      ("INC ECX",          "41", "inc ecx");
      ("INC EDX",          "42", "inc edx");
      ("INC EBX",          "43", "inc ebx");
      ("INC ESP",          "44", "inc esp");
      ("INC EBP",          "45", "inc ebp");
      ("INC ESI",          "46", "inc esi");
      ("INC EDI",          "47", "inc edi");
      ("DEC EAX",          "48", "dec eax");
      ("DEC ECX",          "49", "dec ecx");
      ("DEC EDX",          "4a", "dec edx");
      ("DEC EBX",          "4b", "dec ebx");
      ("DEC ESP",          "4c", "dec esp");
      ("DEC EBP",          "4d", "dec ebp");
      ("DEC ESI",          "4e", "dec esi");
      ("DEC EDI",          "4f", "dec edi");
      ("PUSH EAX",         "50", "push eax");
      ("PUSH ECX",         "51", "push ecx");
      ("PUSH EDX",         "52", "push edx");
      ("PUSH EBX",         "53", "push ebx");
      ("PUSH ESP",         "54", "push esp");
      ("PUSH EBP",         "55", "push ebp");
      ("PUSH ESI",         "56", "push esi");
      ("PUSH EDI",         "57", "push edi");
      ("POP EAX",          "58", "pop eax");
      ("POP ECX",          "59", "pop ecx");
      ("POP EDX",          "5a", "pop edx");
      ("POP EBX",          "5b", "pop ebx");
      ("POP ESP",          "5c", "pop esp");
      ("POP EBP",          "5d", "pop ebp");
      ("POP ESI",          "5e", "pop esi");
      ("POP EDI",          "5f", "pop edi");
      ("PUSHA",            "60", "pusha");
      ("POPA",             "61", "popa");
      ("XCHG EAX",         "90", "xchg eax, eax");
      ("XCHG ECX",         "91", "xchg ecx, eax");
      ("XCHG EDX",         "92", "xchg edx, eax");
      ("XCHG EBX",         "93", "xchg ebx, eax");
      ("XCHG ESP",         "94", "xchg esp, eax");
      ("XCHG EBP",         "95", "xchg ebp, eax");
      ("XCHG ESI",         "96", "xchg esi, eax");
      ("XCHG EDI",         "97", "xchg edi, eax");
      ("CWDE",             "98", "cwde");
      ("CDQ",              "99", "cdq");
      ("WAIT",             "9b", "wait");
      ("PUSHF",            "9c", "pushf");
      ("POPF",             "9d", "popf");
      ("SAHF",             "9e", "sahf");
      ("LAHF",             "9f", "lahf");
      ("RET",              "c3", "ret");
      ("LEAVE",            "c9", "leave");
      ("INT 3",            "cc", "int 3");
      ("IRET",             "cf", "iretd");
      ("SETALC",           "d6", "setalc");
      ("XLAT",             "d7", "xlat");
      ("IN-AL",            "ec", "in al, dx");
      ("IN-EAX",           "ed", "in eax, dx");
      ("OUT-AL",           "ee", "out dx, al");
      ("OUT-EAX",          "ef", "out dx, eax");
      ("HALT",             "f4", "hlt");
      ("CMC",              "f5", "cmc");
      ("CLC",              "f8", "clc");
      ("STC",              "f9", "stc");
      ("CLI",              "fa", "cli");
      ("STI",              "fb", "sti");
      ("CLD",              "fc", "cld");
      ("STD",              "fd", "std");
    ] in
  begin
    TS.new_testsuite (testname ^ "_x86_single") lastupdated;

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
let x86_double_nr () =
  let tests = [
      ("ADD-ESI-ECX",       "01ce", "add esi, ecx");
      ("ADD-EAX-EDX",       "01d0", "add eax, edx");
      ("ADD-EBX-EDX",       "01d3", "add ebx, edx");
      ("ADD-EAX-ESI",       "01f0", "add eax, esi");
      ("XOR-ECX-ECX",       "31c9", "xor ecx, ecx");
      ("XOR-EDX-EDX",       "31d2", "xor edx, edx");
      ("TEST-EAX-EAX",      "85c0", "test eax, eax");
      ("TEST-EBX-EBX",      "85db", "test ebx, ebx");
      ("TEST-ESI-ESI",      "85f6", "test esi, esi");
      ("MOV-EBX-EAX",       "89c3", "mov ebx, eax");
      ("MOV-ESI-EAX",       "89c6", "mov esi, eax");      
      ("MOV-EAX-EBX",       "89d8", "mov eax, ebx");
      ("MOV-EBP-ESP",       "89e5", "mov ebp, esp");
      ("MOV-EAX-EDI",       "89f8", "mov eax, edi");
      ("MOV-EDX-EDI",       "89fa", "mov edx, edi");
      ("MOV-EAX-[EBX]",     "8b03", "mov eax, (ebx)");
      ("MOV-EDX-[EAX]",     "8b10", "mov edx, (eax)");
      ("SHR-ECX-1",         "d1e9", "shr ecx, 0x1");
      ("SHL-EAX-CL",        "d3e0", "shl eax, cl");
      ("SHL-EDX-CL",        "d3e2", "shl edx, cl");
      ("NOT-EAX",           "f7d0", "not eax");
      ("NOT-EDX",           "f7d2", "not edx");
      ("CALL-[ESI]",        "ff1e", "call* (esi)");
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
let x86_quartet_nr () =
  let tests = [
      ("TZCNT-EAX-EAX",      "f30fbcc0", "tzcnt eax, eax");
      ("TZCNT-EDX-EDX",      "f30fbcd2", "tzcnt edx, edx");
    ] in
  begin
    TS.new_testsuite (testname ^ "_x86_quartet") lastupdated;

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
    x86_single ();
    x86_double_nr ();
    x86_quartet_nr ();
    TS.exit_file ()
  end
