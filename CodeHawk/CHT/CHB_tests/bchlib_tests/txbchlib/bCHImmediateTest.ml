(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
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
open CHNumerical

module A = TCHAssertion
module G = TCHGenerator
module TS = TCHTestSuite

module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator

module I = BCHImmediate

module TR = CHTraceResult


let testname = "bCHImmediateTest"
let lastupdated = "2024-05-25"


let signed_imm (width: int) (value: int) =
  TR.tget_ok (I.make_immediate true width (mkNumerical value))


let signed_imm_result (width: int) (value: int) =
  I.make_immediate true width (mkNumerical value)


let unsigned_imm_result (width: int) (value: int) =
  I.make_immediate false width (mkNumerical value)


let imm_basic () =
  begin
    TS.new_testsuite (testname ^ "_basic") lastupdated;

    TS.add_simple_test
      ~title:"zero"
      (fun () ->
        BA.equal_string_imm_result_string "0" (unsigned_imm_result 4 0));

    TS.add_simple_test
      ~title:"small-value"
      (fun () ->
        BA.equal_string_imm_result_string "4" (unsigned_imm_result 4 4));

    TS.add_simple_test
      ~title:"medium-value"
      (fun () ->
        BA.equal_string_imm_result_string "0xc" (unsigned_imm_result 4 12));

    TS.add_simple_test
      ~title:"small-neg-value"
      (fun () ->
        BA.equal_string_imm_result_string "-4" (signed_imm_result 4 (-4)));

    TS.add_simple_test
      ~title:"medium-neg-value"
      (fun () ->
        BA.equal_string_imm_result_string "-0xc" (signed_imm_result 4 (-12)));

    TS.add_simple_test
      ~title:"sign-extend-pos"
      (fun () ->
        BA.equal_string_imm_result_hexstring "0x1" (I.imm1#sign_extend 4));

    TS.add_simple_test
      ~title:"sign-extend-neg"
      (fun () ->
        BA.equal_string_imm_result_hexstring
          "-0x1" ((signed_imm 1 (-1))#sign_extend 4));

    TS.add_simple_test
      ~title:"to-unsigned-pos"
      (fun () -> A.equal_string "0x1" I.imm1#to_unsigned#to_hex_string);

    TS.add_simple_test
      ~title:"to-unsigned-b"
      (fun () ->
        A.equal_string "0xff" (signed_imm 1 (-1))#to_unsigned#to_hex_string);

    TS.add_simple_test
      ~title:"to-unsigned-w"
      (fun () ->
        A.equal_string "0xffff" (signed_imm 2 (-1))#to_unsigned#to_hex_string);

    TS.add_simple_test
      ~title:"to-unsigned-dw"
      (fun () ->
        A.equal_string
          "0xffffffff" (signed_imm 4 (-1))#to_unsigned#to_hex_string);

    TS.add_simple_test
      ~title:"sign-extend-to-unsigned"
      (fun () ->
        A.equal_string
          "0xffffffff"
          (TR.tget_ok
             ((signed_imm 1 (-1))#sign_extend 4))#to_unsigned#to_hex_string);

    TS.launch_tests ();
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    imm_basic ();
    TS.exit_file ()
  end
