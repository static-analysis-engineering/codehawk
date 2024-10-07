(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2024  Aarno Labs LLC

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

(* bchlib *)
open BCHByteUtilities
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHStreamWrapper

(* bchlibarm32 *)
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMInstructionAggregate
open BCHARMOpcodeRecords
open BCHARMTestSupport
open BCHARMTypes
open BCHDisassembleARM
open BCHDisassembleARMInstruction
open BCHDisassembleThumbInstruction
open BCHConstructARMFunction
open BCHFnARMDictionary

module TR = CHTraceResult


let string_of_opcode (opcode: arm_opcode_t) = arm_opcode_to_string opcode


let make_stream (s: string) =
  let bytestring = write_hex_bytes_to_bytestring s in
  make_pushback_stream ~little_endian:true bytestring


let arm_instructions_setup (base: doubleword_int) (size: int) =
  let xsize = TR.tget_ok (int_to_doubleword size) in
  let xsec = ("test", base, xsize) in
  begin
    initialize_arm_instructions [xsec];
    initialize_arm_assembly_instructions [xsec] []
  end


let arm_function_setup
      (faddr: doubleword_int) (bytes: string): arm_assembly_function_int =
  let bytestring = write_hex_bytes_to_bytestring bytes in
  let ch = make_stream bytes in
  let size = String.length bytestring in
  (* let xsize = TR.tget_ok (int_to_doubleword size) in *)
  begin
    ignore (functions_data#add_function faddr);
    (* initialize_arm_assembly_instructions [("test", faddr, xsize)] []; *)
    while ch#pos + 4 < size do
      let prevpos = ch#pos in
      let iaddr = faddr#add_int ch#pos in
      let instrbytes = ch#read_doubleword in
      let opcode = disassemble_arm_instruction ch iaddr instrbytes in
      let currentpos = ch#pos in
      let instrlen = currentpos - prevpos in
      let instrbytes = String.sub bytestring prevpos instrlen in
      let instr = make_arm_assembly_instruction iaddr false opcode instrbytes in
      set_arm_assembly_instruction instr
    done;
    let _ = set_block_boundaries () in
    let (_, fn) = construct_arm_assembly_function faddr in
    begin
      arm_assembly_functions#add_function fn;
      associate_condition_code_users ();
      fn
    end
  end


let thumb_function_setup
      (faddr: doubleword_int) (bytes: string): arm_assembly_function_int =
  let bytestring = write_hex_bytes_to_bytestring bytes in
  let ch = make_stream bytes in
  let size = String.length bytestring in
  (* let xsize = TR.tget_ok (int_to_doubleword size) in *)
  begin
    ignore (functions_data#add_function faddr);
    (* initialize_arm_assembly_instructions [("test", faddr, xsize)] []; *)
    while ch#pos + 2 < size do
      let prevpos = ch#pos in
      let iaddr = faddr#add_int ch#pos in
      let instrbytes = ch#read_ui16 in
      let opcode = disassemble_thumb_instruction ch iaddr instrbytes in
      let currentpos= ch#pos in
      let instrlen = currentpos - prevpos in
      let instrbytes = String.sub bytestring prevpos instrlen in
      let instr = make_arm_assembly_instruction iaddr false opcode instrbytes in
      let _ = set_arm_assembly_instruction instr in
      let optagg = identify_arm_aggregate ch instr in
      match optagg with
      | Some agg -> set_aggregate iaddr agg
      | _ -> ()
    done;
    let _ = set_block_boundaries () in
    let _ = construct_functions_arm ~construct_all_functions:false () in
    get_arm_assembly_function faddr
  end


let get_instrxdata_xprs (faddr: doubleword_int) (iaddr: doubleword_int) =
  let _ = testsupport#request_instrx_data in
  let finfo = get_function_info faddr in
  let fn = get_arm_assembly_function faddr in
  let id = mk_arm_opcode_dictionary faddr finfo#env#varmgr#vard in
  let _ =
    fn#itera
      (fun _baddr block ->
        block#itera
          (fun ctxtiaddr instr ->
            let loc = ctxt_string_to_location faddr ctxtiaddr in
            let floc = get_floc loc in
            ignore (id#index_instr instr floc))) in
  let (_, xprs) =
    TR.tget_ok (testsupport#retrieve_instrx_data iaddr#to_hex_string) in
  xprs


let get_instrxdata_tags (faddr: doubleword_int) (iaddr: doubleword_int) =
  let _ = testsupport#request_instrx_tags in
  let finfo = get_function_info faddr in
  let fn = get_arm_assembly_function faddr in
  let id = mk_arm_opcode_dictionary faddr finfo#env#varmgr#vard in
  let _ =
    fn#itera
      (fun _baddr block ->
        block#itera
          (fun ctxtiaddr instr ->
            let loc = ctxt_string_to_location faddr ctxtiaddr in
            let floc = get_floc loc in
            ignore (id#index_instr instr floc))) in
  TR.tget_ok (testsupport#retrieve_instrx_tags iaddr#to_hex_string)
