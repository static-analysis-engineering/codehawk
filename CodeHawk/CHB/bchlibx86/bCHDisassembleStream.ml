(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* chlog *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHStreamWrapper

(* bchlibx86 *)
open BCHAssemblyInstruction
open BCHAssemblyInstructions
open BCHDisassembleInstruction


let disassemble_stream (vastart:doubleword_int) (codestring:string) =
  let size = String.length codestring in
  let ch = make_pushback_stream ~little_endian:true codestring in
  let _ = initialize_instructions size in
  let _ = initialize_assembly_instructions 0 size size vastart [] [] in
  let add_instruction position opcode bytes =
    let va = vastart#add_int position in
    let instr = make_assembly_instruction va opcode bytes in
    !assembly_instructions#set position instr in
  try
    while ch#pos < size do
      let prevpos =  ch#pos in
      try
        let firstbyte = ch#read_byte in
        let opcode = disassemble_instruction ch vastart firstbyte in
        let curpos = ch#pos in
        let instrlen = curpos - prevpos in
        let instrbytes = String.sub codestring prevpos instrlen in
        add_instruction prevpos opcode instrbytes
      with
      | Invalid_argument s ->
         begin
           ch_error_log#add
             "stream disassembly"
             (LBLOCK [
                  STR "failure disassembling instruction at ";
                  (vastart#add_int prevpos)#toPretty ]);
           raise (Invalid_argument s)
         end
    done
  with
  | BCH_failure p ->
     ch_error_log#add
       "stream disassembly"
       (LBLOCK [STR "failure in disassembling codestring: ";  p])
  | IO.No_more_input -> ()
