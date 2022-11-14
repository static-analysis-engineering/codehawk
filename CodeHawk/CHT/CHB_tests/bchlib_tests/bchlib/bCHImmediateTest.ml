(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

module A = TCHAssertion
module TS = TCHTestSuite

module I = BCHImmediate


let signed_imm (width: int) (value: int) =
  I.make_immediate true width (Big_int_Z.big_int_of_int value)


let unsigned_imm (width: int) (value: int) =
  I.make_immediate false width (Big_int_Z.big_int_of_int value)


let () =
  begin
    TS.new_testsuite "bCHImmediateTest";

    TS.add_simple_test
      (fun () -> A.equal_string "0x1" (I.imm1#sign_extend 4)#to_hex_string);

    TS.add_simple_test
      (fun () ->
        A.equal_string "-0x1" ((signed_imm 1 (-1))#sign_extend 4)#to_hex_string);

    TS.add_simple_test
      (fun () -> A.equal_string "0x1" I.imm1#to_unsigned#to_hex_string);

    TS.add_simple_test
      (fun () ->
        A.equal_string "0xff" (signed_imm 1 (-1))#to_unsigned#to_hex_string);

    TS.add_simple_test
      (fun () ->
        A.equal_string "0xffff" (signed_imm 2 (-1))#to_unsigned#to_hex_string);

    TS.add_simple_test
      (fun () ->
        A.equal_string "0xffffffff" (signed_imm 4 (-1))#to_unsigned#to_hex_string);

    TS.add_simple_test
      (fun () ->
        A.equal_string
          "0xffffffff"
          ((signed_imm 1 (-1))#sign_extend 4)#to_unsigned#to_hex_string);

    TS.launch_tests ();
    exit 0
  end
