(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023  Aarno Labs LLC

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


module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator
module BS = TCHBchlibSpecification
module BU = TCHBchlibUtils

module ARMA = TCHBchlibarm32Assertion
module ARMU = TCHBchlibarm32Utils


(* chlib *)
open CHPretty
open CHLanguage

(* chutil *)
module TR = CHTraceResult

(* bchlib *)
module D = BCHDoubleword
module L = BCHLocation
module SI = BCHSystemInfo
module SW = BCHStreamWrapper
module U = BCHByteUtilities

(* bchlibarm32 *)
module ARMIS = BCHARMAssemblyInstructions
module R = BCHARMOpcodeRecords
module DT = BCHDisassembleARMInstruction
module TF = BCHTranslateARMToCHIF

open BCHFunctionData
open BCHBasicTypes
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstruction
open BCHLibTypes
open BCHARMTypes
open BCHARMCodePC
open BCHAnalyzeApp
open BCHARMCHIFSystem
open BCHFunctionInfo


let testname = "bCHARMAssemblyFunction"
let lastupdated = "2023-01-03"


let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)


let codemax = make_dw "0x400000"


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:true s


let conditional_return () =
  let tests = [
      ("POPEQ", "0x15d5c",
       "70402de9000050e37080bd087040bde800",
       [("0x15d5c", "F@_0x15d64");
        ("0x15d5c", "T@_0x15d64");
        ("F@_0x15d64", "0x15d68")])
    ] in
  begin
    TS.new_testsuite (testname ^ "_conditional_return") lastupdated;

    SI.system_info#set_elf_is_code_address D.wordzero codemax;
    ARMIS.initialize_arm_instructions 1000;
    List.iter (fun (title, sfaddr, bytes, expectedresult) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let faddr = make_dw sfaddr in
            let fn = ARMU.arm_function_setup faddr bytes in
            begin
              ARMA.equal_cfg_edges fn#get_cfg_edges expectedresult
            end)
      ) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    conditional_return ();
    TS.exit_file ()
  end
