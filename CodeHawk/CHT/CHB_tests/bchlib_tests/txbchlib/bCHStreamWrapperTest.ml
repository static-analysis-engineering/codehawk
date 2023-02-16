(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs LLC

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
open CHNumerical

(* tchblib *)
open TCHSpecification

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator
module BS = TCHBchlibSpecification

(* bchlib *)
module TF = BCHStreamWrapper
module U = BCHByteUtilities

let testname = "bCHStreamWrapper"
let lastupdated = "2023-02-12"
         


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  TF.make_pushback_stream ~little_endian:true s


let leb128_tests () =
  let tests = [
      ("leb0", "0000", "0");
      ("leb1", "0100", "1");
      ("leb127", "7f", "127");
      ("leb128", "8001", "128");
      ("leb129", "8101", "129");
      ("leb130", "8201", "130");
      ("leb12857", "b964", "12857")
    ] in
  begin
    TS.new_testsuite (testname ^ "_leb128_tests") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let intval = ch#read_dwarf_leb128 in
            A.equal_string result (string_of_int intval))) tests;

    TS.launch_tests ()
  end


let sleb128_tests () =
  let tests = [
      ("sleb0", "0000", "0");
      ("sleb1", "0100", "1");
      ("sleb-2", "7e", "-2");
      ("sleb127", "ff00", "127");
      ("sleb-127", "817f", "-127");
      ("sleb128", "8001", "128");
      ("sleb-128", "807f", "-128");
      ("sleb129", "8101", "129");
      ("sleb-129", "ff7e", "-129")
    ] in
  begin
    TS.new_testsuite (testname ^ "_sleb128_tests") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let intval = ch#read_dwarf_sleb128 32 in
            A.equal_string result (string_of_int intval))) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    leb128_tests ();
    sleb128_tests ();
    TS.exit_file ()
  end

        
            

  
