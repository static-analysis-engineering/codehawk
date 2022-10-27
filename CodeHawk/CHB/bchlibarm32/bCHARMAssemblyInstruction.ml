(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs, LLC

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
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHFunctionData
open BCHLibTypes
open BCHSystemInfo
open BCHSystemSettings

(* bchlibarm32 *)
open BCHARMDictionary
open BCHARMOpcodeRecords
open BCHARMTypes

class arm_assembly_instruction_t
        (vaddr: doubleword_int)
        (is_arm: bool)
        (opcode: arm_opcode_t)
        (instruction_bytes: string): arm_assembly_instruction_int =
object (self)
     
  val mutable block_entry = false
  val mutable inlined_call = false
  val mutable aggregate_dst = None
  val mutable aggregate = []
  val mutable subsumedby = None  (* refers to IT instruction *)
  val mutable blockcondition = false
  val mutable conditioncoveredby = None  (* refers to IT instruction *)

  method set_block_entry = block_entry <- true

  method set_inlined_call =
    let _ =
      if system_settings#collect_diagnostics then
        ch_diagnostics_log#add
          "inlined call"
          (LBLOCK [vaddr#toPretty; STR ": "; self#toPretty]) in
    inlined_call <- true

  (* applies to IfThen instruction:
     aggregates the dependents into one assignment *)
  method set_aggregate (dstop: arm_operand_int) (dependents: doubleword_int list) =
    begin
      aggregate <- dependents;
      aggregate_dst <- Some dstop
    end

  method get_dependents = aggregate

  method is_aggregate =
    match aggregate with
    | [] -> false
    | _ -> true

  method get_aggregate_dst =
    match aggregate_dst with
    | Some op -> op
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Internal error in get_aggregate_dst"]))

  (* applies to dependents of aggregate instructions *)
  method set_subsumed_by (iaddr: doubleword_int) = subsumedby <- Some iaddr

  method is_subsumed = match subsumedby with Some _ -> true | _ -> false

  method subsumed_by =
    match subsumedby with
    | Some iaddr -> iaddr
    | _ ->
       raise
         (BCH_failure (LBLOCK [STR "Instruction is not subsumed"]))

  method set_block_condition = blockcondition <- true

  method is_block_condition = blockcondition

  method set_condition_covered_by (iaddr: doubleword_int) =
    conditioncoveredby <- Some iaddr

  method is_condition_covered =
    match conditioncoveredby with Some _ -> true | _ -> false

  method condition_covered_by =
    match conditioncoveredby with
    | Some iaddr -> iaddr
    | _ ->
       raise
         (BCH_failure (LBLOCK [STR "Instruction condition is not covered"]))

  method is_arm32 = is_arm

  method is_block_entry = block_entry

  method is_valid_instruction =
    match opcode with
    | OpInvalid -> false
    | NotCode _ -> false
    | _ -> true

  method is_non_code_block =
    match opcode with
    | NotCode (Some _) -> true
    | _ -> false

  method is_not_code = match opcode with NotCode _ -> true | _ -> false

  method get_address = vaddr

  method get_opcode = opcode

  method get_instruction_bytes = instruction_bytes

  method get_bytes_ashexstring =
    byte_string_to_printed_string instruction_bytes

  method get_non_code_block =
    match opcode with
    | NotCode (Some b) -> b
    | _ ->
       let msg = (LBLOCK [STR "No data block found at "; vaddr#toPretty]) in
       begin
         ch_error_log#add "assembly instructions" msg;
         raise (BCH_failure msg)
       end

  method private is_function_entry_point =
    functions_data#is_function_entry_point self#get_address

  method is_inlined_call = inlined_call

  method toString = arm_opcode_to_string opcode

  method toPretty = LBLOCK [STR self#toString]

  method write_xml (node:xml_element_int) =
    let opc = self#get_opcode in
    let set = node#setAttribute in
    let stat = ref "" in
    begin
      (if self#is_function_entry_point then stat := !stat ^ "F");
      (if self#is_block_entry then stat := !stat ^ "B");
      (if self#is_aggregate then stat := !stat ^ "A");
      (if self#is_subsumed then stat := !stat ^ "S");
      (if !stat = "" then () else set "stat" !stat);
      set "ia" self#get_address#to_hex_string;
      arm_dictionary#write_xml_arm_opcode node opc;
      arm_dictionary#write_xml_arm_bytestring
        node ((byte_string_to_printed_string self#get_instruction_bytes))
    end

end

let make_arm_assembly_instruction
      (va: doubleword_int)
      (is_arm: bool)
      (opcode: arm_opcode_t)
      (instruction_bytes: string): arm_assembly_instruction_int =
  new arm_assembly_instruction_t va is_arm opcode instruction_bytes
