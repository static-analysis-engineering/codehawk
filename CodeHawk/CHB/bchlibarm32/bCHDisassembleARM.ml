(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs, LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDataBlock
open BCHDoubleword
open BCHFloc
open BCHFunctionApi
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHJumpTable
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities

(* bchlibelf *)
open BCHELFHeader
open BCHELFTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMTypes
open BCHDisassembleARMInstruction

module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)

let x2p = xpr_formatter#pr_expr

let disassemble (base:doubleword_int) (displacement:int) (x:string) =
  let size = String.length x in  
  (* let opcode_monitor = new opcode_monitor_t base size in *)
  let add_instruction position opcode bytes =
    let index = position + displacement in 
    let addr = base#add_int position in
    let instr = make_arm_assembly_instruction addr opcode bytes in
    begin
      !arm_assembly_instructions#set index instr ;
      (* opcode_monitor#check_instruction instr *)
    end in
  let ch = system_info#get_string_stream x in
  let not_code_length nc =
    match nc with
    | JumpTable jt -> jt#get_length
    | DataBlock db -> db#get_length in
  let not_code_set_string nc s =
    match nc with
    | DataBlock db -> db#set_data_string s
    | _ -> () in
  let is_data_block (pos:int) =
    (!arm_assembly_instructions#at_index (displacement+pos))#is_non_code_block in
  (* let is_not_code (pos:int) =
    let instr = !arm_assembly_instructions#at_index pos in
    match instr#get_opcode with | NotCode None -> true | _ -> false in *)
  let skip_data_block (pos:int) ch =
    let nonCodeBlock =
      (!arm_assembly_instructions#at_index (displacement+pos))#get_non_code_block in
    let len = not_code_length nonCodeBlock in
    let sdata = Bytes.make len ' ' in
    let _ = Bytes.blit (Bytes.of_string x) pos sdata 0 len in
    begin
      chlog#add
        "skip data block"
        (LBLOCK [ STR "pos: " ; INT pos; STR "; length: " ; INT len ]);
      ch#skip_bytes len;
      not_code_set_string nonCodeBlock (Bytes.to_string sdata)
    end in
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [ STR "base: " ; base#toPretty ;
                STR "; displacement: " ; INT displacement ;
                STR "; size: " ; INT size  ]) in
  try
    begin
      while ch#pos < size do
        let prevPos = ch#pos in
        if is_data_block prevPos then
          skip_data_block prevPos ch
        else
          let instrbytes = ch#read_doubleword in
          let opcode =
            try
              disassemble_arm_instruction ch base instrbytes
            with
            | _ -> OpInvalid in
          let currentPos = ch#pos in
          let instrLen = currentPos - prevPos in
          let instrBytes = Bytes.make instrLen ' ' in
          let _ = Bytes.blit (Bytes.of_string x) prevPos instrBytes 0  instrLen in
          let _ = add_instruction prevPos opcode (Bytes.to_string  instrBytes) in
          ()
      done ;
      (* !arm_assembly_instructions#set_not_code opcode_monitor#get_data_blocks *)
    end
  with
  | BCH_failure p ->
     begin
       pr_debug [ STR "Error in disassembly: " ; p ] ;
       raise (BCH_failure p)
     end
  | IO.No_more_input ->
     begin
       pr_debug [ STR "Error in disassembly: No more input" ; NL ];
       raise IO.No_more_input
     end
  

let disassemble_arm_sections () =
  let xSections = elf_header#get_executable_sections in
  let (startOfCode,endOfCode) =
    if (List.length xSections) = 0 then
      raise (BCH_failure (STR "Executable does not have section headers"))
    else
      let headers =
        List.sort (fun (h1,_) (h2,_) -> h1#get_addr#compare h2#get_addr) xSections in
      let (lowest,_) = List.hd headers in
      let (highest,_) = List.hd (List.rev headers) in
      let _ =
        chlog#add
          "disassembly"
          (LBLOCK [ pretty_print_list
                      headers
                      (fun (s,_) ->
                        LBLOCK [ STR s#get_section_name ; STR ":" ; s#get_addr#toPretty ;
                                 STR " (" ; s#get_size#toPretty ; STR ")" ])
                      "[" " ; " "]" ]) in
      let startOfCode = lowest#get_addr in
      let endOfCode = highest#get_addr#add highest#get_size in
      (startOfCode,endOfCode) in
  let sizeOfCode = endOfCode#subtract startOfCode in
  let datablocks = system_info#get_data_blocks in
  let _ = initialize_arm_instructions sizeOfCode#to_int in 
  let _ = pverbose 
            [ STR "Create space for " ; sizeOfCode#toPretty ; STR " (" ;
	      INT sizeOfCode#to_int ; STR ") instructions" ; NL ; NL ] in
  let _ =
    initialize_arm_assembly_instructions
      sizeOfCode#to_int startOfCode datablocks in
  let _ =
    List.iter
      (fun (h,x) ->
        let displacement = (h#get_addr#subtract startOfCode)#to_int in
        disassemble h#get_addr displacement x) xSections in
  let _ =
    pr_debug [ STR ((!BCHARMAssemblyInstructions.arm_assembly_instructions)#toString ()) ] in
  sizeOfCode
