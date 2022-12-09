(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionSummary
open BCHLibTypes
open BCHSystemInfo

(* bchlibpower32 *)
open BCHPowerAssemblyInstruction
open BCHPowerTypes

module TR = CHTraceResult


(* --------------------------------------------------------------------------------
 * Note:
 * It is assumed that all instructions are at 4-byte boundaries. Address indices
 * are obtained by dividing the actual address by 4. Unlike x86 there are no
 * instructions in the instruction array at unaligned addresses.
 * -------------------------------------------------------------------------------- *)


let numArrays = 1000
let arrayLength = 100000


let power_instructions =
  ref (Array.make 1 (make_power_assembly_instruction wordzero false OpInvalid ""))


let power_instructions = 
  Array.make
    numArrays
    (Array.make 1 (make_power_assembly_instruction wordzero false OpInvalid ""))


let initialize_power_instructions len =
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [STR "Initialize "; INT len; STR " bytes"]) in
  let remaining = ref len in
  let index = ref 0 in
  begin
    while !remaining > 0 && !index < numArrays do
      power_instructions.(!index) <-
        Array.make
          arrayLength (make_power_assembly_instruction wordzero false OpInvalid "");
      remaining := !remaining - arrayLength ;
      index := !index + 1 
    done ;
    if !remaining > 0 then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Not sufficient array space to store all instruction bytes"]))
  end


let get_indices (index:int) = (index/arrayLength, index mod arrayLength)


let set_instruction (index: int) (instruction: power_assembly_instruction_int) =
  try
    let (i,j) = get_indices index in
    power_instructions.(i).(j) <- instruction
  with
  | Invalid_argument s ->
     raise (Invalid_argument ("set_instruction: " ^ s))


let initialize_instruction_segment (endindex: int) =
  for index = 0 to (endindex - 1) do
    set_instruction index (make_power_assembly_instruction wordzero false OpInvalid "")
  done


let get_instruction (index: int) =
  let (i,j) = get_indices index in
  try
    power_instructions.(i).(j)
  with
  | Invalid_argument s ->
     raise (
         Invalid_argument
           ("get_instruction: "
            ^ s
            ^ " ("
            ^ (string_of_int i)
            ^ ", "
            ^ (string_of_int j)
            ^ ")"))


let fold_instructions (f: 'a -> power_assembly_instruction_int -> 'a) (init: 'a) =
  Array.fold_left (fun a arr ->
    Array.fold_left (fun a1 opc -> f a1 opc) a arr) init power_instructions


let iter_instructions (f: power_assembly_instruction_int -> unit) =
  Array.iter (fun arr -> Array.iter f arr) power_instructions


let iteri_instructions (f: int -> power_assembly_instruction_int -> unit) =
  Array.iteri (fun i arr -> 
    let k = i * arrayLength in
    Array.iteri (fun j instr -> f (k+j) instr) arr) power_instructions


class power_assembly_instructions_t
        (len: int)
        (codebase: doubleword_int): power_assembly_instructions_int =
object (self)

  val codeBase = codebase
  val codeEnd = codebase#add_int len
  val length = len

  method is_code_address (va: doubleword_int) =
    codeBase#le va && va#lt codeEnd

  method set (index: int) (instr: power_assembly_instruction_int) =
    try
      set_instruction index instr
    with
    | Invalid_argument _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "set: Instruction index out of range: ";
                 INT index;
                 STR " (length is ";
                 INT length;
                 STR ")"]))

  method set_not_code (datablocks: data_block_int list) =
    List.iter self#set_not_code_block datablocks

  method private set_not_code_block (db: data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    let startindex = (TR.tget_ok (startaddr#subtract_to_int codeBase)) / 4 in
    let startinstr =
      make_power_assembly_instruction
        startaddr false (NotCode (Some (DataBlock db))) "" in
    let endindex = (TR.tget_ok (endaddr#subtract_to_int codeBase)) / 4 in
    begin
      self#set startindex startinstr ;
      for i = startindex + 1  to endindex - 1 do
        let iaddr = codeBase#add_int i in
        self#set i (make_power_assembly_instruction iaddr false (NotCode None) "")
      done
    end
    
  method length = length

  method at_index (index: int) =
    try
      let instr = get_instruction index in
      if instr#get_address#equal wordzero then
	let newInstr =
          make_power_assembly_instruction
            (codeBase#add_int index) false NoOperation "" in
	begin
          set_instruction index newInstr;
          newInstr
        end
      else
	instr
    with
    | Invalid_argument s ->
       raise
         (BCH_failure
	    (LBLOCK [
                 STR "at_index: Instruction index out of range: ";
                 INT index ;
                 STR ": ";
                 STR s;
		 STR " (length is ";
                 INT length ; STR ")"]))

  (* assume all instructions are aligned on 4-byte boundaries *)
  method at_address (va: doubleword_int) =
    try
      let index = (TR.tget_ok (va#subtract_to_int codeBase)) / 4 in
      self#at_index index
    with
    | BCH_failure p ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in assembly-instructions:at-address: ";
                 va#toPretty;
                 STR " with codeBase: ";
                 codeBase#toPretty;
                 STR ": ";
                 p]))

  method write_xml (node: xml_element_int) = ()

  method toString ?(filter = fun _ -> true) () = "string"

  method toPretty = STR (self#toString ())

end


let power_assembly_instructions = ref (new power_assembly_instructions_t 1 wordzero)


let initialize_power_assembly_instructions
      (length: int)    (* in bytes *)
      (codebase: doubleword_int) =
  begin
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "Initialize ";
           INT length;
           STR " bytes; ";
           codebase#toPretty;
           STR " - ";
           (codebase#add_int length)#toPretty]);
    power_assembly_instructions := new power_assembly_instructions_t length codebase
  end
