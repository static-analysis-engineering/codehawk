(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
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

(* chlib *)
open CHPretty
open CHNumerical

(* tchblib *)
open TCHSpecification

module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator
module BS = TCHBchlibSpecification

module D = BCHDoubleword
module TR = CHTraceResult


let testname = "bCHDoublewordTest"
let lastupdated = "2023-03-18"


let constant_string_to_doubleword (s: string) =
  TR.tget_ok (D.string_to_doubleword s)


let constant_numerical_to_doubleword (num: numerical_t) =
  TR.tget_ok (D.numerical_to_doubleword num)


let equal_dw = BA.equal_doubleword
let equal_dwr = BA.equal_doubleword_result


let wordmaxm1 = constant_string_to_doubleword "0xfffffffe"
let word1000 = constant_string_to_doubleword "0x0000100"

let numzero = mkNumerical 0
let numnegone = mkNumerical (-1)


let doubleword_basic () =
  begin

    TS.new_testsuite (testname ^ "_basic") lastupdated;

    TS.add_simple_test
      ~title:"zero"
      (fun () ->
        A.equal_string
          "0x0" (constant_string_to_doubleword "0x0")#to_hex_string);

    TS.add_simple_test
      ~title:"num-zero"
      (fun () ->
        A.equal_string
          "0x0" (constant_numerical_to_doubleword numzero)#to_hex_string);

    TS.add_simple_test
      ~title:"num-neg-one"
      (fun () ->
        A.equal_string
          "0xffffffff"
          (constant_numerical_to_doubleword numnegone)#to_hex_string);

    TS.add_simple_test
      ~title:"neg-one-signed"
      (fun () ->
        A.equal_string
          "-0x1" (TR.tget_ok (D.numerical_to_signed_hex_string numnegone)));

    TS.add_random_test
      ~title:"random"
      (G.make_int 0 BA.e32)
      (fun i -> (TR.tget_ok (D.int_to_doubleword i))#to_hex_string)
      [S.always => BS.is_int_doublewordstring];

    TS.add_simple_test
      ~title:"add-zero"
      (fun () -> equal_dw D.wordzero (D.wordzero#add D.wordzero));

    TS.add_simple_test
      ~title:"add-max"
      (fun () -> equal_dw D.wordmax (D.wordzero#add D.wordmax));

    TS.add_simple_test
      ~title:"wrap-max"
      (fun () ->
        equal_dw
          ~msg:"addition wraps around" wordmaxm1 (D.wordmax#add D.wordmax));

    TS.add_simple_test
      ~title:"wrap-zero"
      (fun () ->
        let dw31 = TR.tget_ok (D.int_to_doubleword BA.e31) in
        equal_dw ~msg:"addition wraps around" D.wordzero (dw31#add dw31));

    TS.add_random_test
      ~title:"msb"
      ~classifier:BG.msb_pair_classifier
      BG.doubleword_pair
      (fun (dw1, dw2) -> dw1#add dw2)
      [S.always => BS.is_sum_doubleword];

    TS.add_simple_test
      ~title:"subtract-zero"
      (fun () -> equal_dwr D.wordzero (D.wordzero#subtract D.wordzero));

    TS.add_simple_test
      ~title:"subtract-max-zero"
      (fun () -> equal_dwr D.wordmax (D.wordmax#subtract D.wordzero));

    TS.add_simple_test
      ~title:"subtract-max-max"
      (fun () -> equal_dwr D.wordzero (D.wordmax#subtract D.wordmax));

    TS.add_simple_test
      ~title:"xor-max"
      (fun () -> equal_dw D.wordzero (D.wordmax#xor D.wordmax));

    TS.add_simple_test
      ~title:"xor-zero-max"
      (fun () -> equal_dw D.wordmax (D.wordzero#xor D.wordmax));

    TS.add_simple_test
      ~title:"char-string"
      (fun () ->
        let dw = constant_string_to_doubleword "0x64636261" in
        A.equal_string
          ~msg:"" "['a' 'b' 'c' 'd']" (Option.get dw#to_char_string));

    TS.add_simple_test
      ~title:"to_string"
      (fun () ->
        let dw = constant_string_to_doubleword "0x61626364" in
        A.equal_string ~msg:"" "abcd" dw#to_string);

    TS.add_simple_test
      ~title:"to_string_fragment"
      (fun () ->
        let dw = constant_string_to_doubleword "0x61626364" in
        A.equal_string ~msg:"" "dcba" dw#to_string_fragment);

    TS.add_simple_test
      ~title:"fixed_length_hex_string-0"
      (fun () ->
        A.equal_string "00000000" D.wordzero#to_fixed_length_hex_string);

    TS.add_simple_test
      ~title:"fixed_length_hex_string-ff"
      (fun () ->
        let dw = constant_string_to_doubleword "0xff" in
        A.equal_string "000000ff" dw#to_fixed_length_hex_string);

    TS.add_simple_test
      ~title:"signed-hex-string-f"
      (fun () ->
        let dw = constant_string_to_doubleword "0xffffffff" in
        A.equal_string "-0x1" dw#to_signed_hex_string);

    TS.add_simple_test
      ~title:"to_aligned_0"
      (fun () ->
        let dw = constant_string_to_doubleword "0x4040" in
        let recvd = dw#to_aligned 4 in
        BA.equal_doubleword_alignment ("0x4040", 0) recvd);

    TS.add_simple_test
      ~title:"to_aligned_2"
      (fun () ->
        let dw = constant_string_to_doubleword "0x4042" in
        let recvd = dw#to_aligned 4 in
        BA.equal_doubleword_alignment ("0x4040", 2) recvd);

    TS.add_simple_test
      ~title:"to_aligned_up_2"
      (fun () ->
        let dw = constant_string_to_doubleword "0x4042" in
        let recvd = dw#to_aligned ~up:true 4 in
        BA.equal_doubleword_alignment ("0x4044", 2) recvd);

    TS.add_simple_test
      ~title:"unset-highest-bit-i"
      (fun () ->
        let dw = constant_string_to_doubleword "0xfffffff" in
        A.equal_string "0xfffffff" dw#unset_highest_bit#to_hex_string);

    TS.add_simple_test
      ~title:"unset-highest-bit-u"
      (fun () ->
        let dw = constant_string_to_doubleword "0x8abcdef1" in
        A.equal_string "0xabcdef1" dw#unset_highest_bit#to_hex_string);

    TS.launch_tests ()
  end


let doubleword_errors () =
  begin
    TS.new_testsuite (testname ^ "_assertions") lastupdated;

    TS.add_simple_test
      ~title:"hex-too-large"
      (fun () ->
        BA.returns_error
          ~msg:"hex string is too large"
          (fun dw -> dw#to_hex_string)
          (fun () -> D.string_to_doubleword "0xfffffffff"));

    TS.add_simple_test
      ~title:"subtract-no-wrap"
      (fun () ->
        BA.returns_error
          ~msg:"subtraction does not wrap around"
          (fun dw -> dw#to_hex_string)
          (fun () -> D.wordzero#subtract D.wordmax));

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    doubleword_basic ();
    doubleword_errors ();
    TS.exit_file ()
  end
