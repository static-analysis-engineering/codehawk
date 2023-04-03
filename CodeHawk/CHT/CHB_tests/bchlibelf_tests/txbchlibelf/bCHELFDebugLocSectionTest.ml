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

(* chutil *)
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchlibelf *)
open BCHDwarfUtils
open BCHELFDebugLocSection
open BCHELFTypes
open BCHELFSectionHeader

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

(* tbchlibelf *)
module EA = TCHBchlibelfAssertion


let testname = "bCHELFDebugLocSection"
let lastupdated = "2023-03-29"


let debug_location_list_test () =
  let tests = [
      ("reg-0", "f4a9000007aa0000010050", [("0xa9f4", "0xaa07", "(R DW_OP_reg0)")]);
      ("reg-4", "07aa000018aa0000010054", [("0xaa07", "0xaa18", "(R DW_OP_reg4)")]);
      ("gnu-entry-value" , "18aa000020aa00000400f301509f",
       [("0xaa18", "0xaa20",
         "(O DW_OP_GNU_entry_value: DW_OP_reg0; DW_OP_stack_value)")]);
      ("lit-0+", "9ca60000cca600000200309f",
       [("0xa69c", "0xa6cc", "(O DW_OP_lit0; DW_OP_stack_value)")]);
      ("breg-0", "84aa000090aa00000300707f9f",
       [("0xaa84", "0xaa90", "(O DW_OP_breg0: -1; DW_OP_stack_value)")]);
      ("breg-2", "ecaa000010ab000002007201",
       [("0xaaec", "0xab10", "(O DW_OP_breg2: 1)")]);
      ("breg-2-3", "18ab000030ab00000300727d9f",
       [("0xab18", "0xab30", "(O DW_OP_breg2: -3; DW_OP_stack_value)")]);
      ("fbreg", "b0d4000034d90000030091e47a",
       [("0xd4b0", "0xd934", "(O DW_OP_fbreg: -668)")]);
      ("fbreg-f", "b8fb00000cfc00000300919076",
       [("0xfbb8", "0xfc0c", "(O DW_OP_fbreg: -1264)")]);
      ("fbreg-sv", "74d4000084d4000009007300917c1c23b0049f",
       [("0xd474", "0xd484",
         "(O DW_OP_breg3: 0; DW_OP_fbreg: -4; DW_OP_minus; DW_OP_plus_uconst: 560; DW_OP_stack_value)")]);
      ("minus", "d4d30000dcd300000600750070001c9f",
       [("0xd3d4", "0xd3dc",
         "(O DW_OP_breg5: 0; DW_OP_breg0: 0; DW_OP_minus; DW_OP_stack_value)")]);
      ("expr", "08b700001cb700001600750112404b242208ff1614404b24222d28010016139f",
       [("0xb708", "0xb71c",
         "(O DW_OP_breg5: 1; DW_OP_dup; DW_OP_lit16; DW_OP_lit27; DW_OP_shl; "
         ^ "DW_OP_plus; DW_OP_const1u: 255; DW_OP_swap; DW_OP_over; "
         ^ "DW_OP_lit16; DW_OP_lit27; DW_OP_shl; DW_OP_plus; DW_OP_lt; "
         ^ "DW_OP_bra: 1; DW_OP_swap; DW_OP_drop; DW_OP_stack_value)")]);
      ("expr-2", "e4cc0000f0cc00001700760112404b24220a00011614404b24222d28010016139f",
       [("0xcce4", "0xccf0",
         "(O DW_OP_breg6: 1; DW_OP_dup; DW_OP_lit16; DW_OP_lit27; DW_OP_shl; "
         ^ "DW_OP_plus; DW_OP_const2u: 256; DW_OP_swap; DW_OP_over; "
         ^ "DW_OP_lit16; DW_OP_lit27; DW_OP_shl; DW_OP_plus; DW_OP_lt; "
         ^ "DW_OP_bra: 1; DW_OP_swap; DW_OP_drop; DW_OP_stack_value)")]);
    ] in
  begin
    TS.new_testsuite (testname ^ "_get_abbrev_entry_test") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bytes = bytes ^ "000000000000000000" in
            let bytestring = U.write_hex_bytes_to_bytestring bytes in            
            let sectionheader = mk_elf_section_header () in
            let section = mk_elf_debug_loc_section bytestring sectionheader in
            let loclist = section#get_location_list in
            EA.equal_debug_location_list result loclist)) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    debug_location_list_test ();
    TS.exit_file ()
  end
  
