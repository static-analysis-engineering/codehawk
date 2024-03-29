(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
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

(* chutil *)
open CHTraceResult

(* bchlib *)
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerTypes


val pwr_assembly_instructions: pwr_assembly_instructions_int ref


(** Create an array of the given size to hold the assembly instructions. *)
val initialize_pwr_instructions:
  (string * doubleword_int * doubleword_int) list -> unit


(** Initialize the instruction array with instructions *)
val initialize_pwr_assembly_instructions:
  (string * doubleword_int * doubleword_int) list
  -> data_block_int list
  -> unit


(** [set_pwr_assembly_instruction instr] enters [instr] at the address
    obtained from [instr#get_address] in pwr_assembly_instructions store.
    If the obtained address is out-of-range an error message is logged
    and the instruction is further ignored. *)
val set_pwr_assembly_instruction: pwr_assembly_instruction_int -> unit


(** [get_pwr_assembly_instruction a] returns the assembly instruction at
    virtual address [a]. If [a] is out-of-range or if there is no instruction
    at [a] Error is returned.*)
val get_pwr_assembly_instruction:
  doubleword_int -> pwr_assembly_instruction_result


(** [has_next_valid_instruction a] returns true if there is an instruction with
    address higher than a with a valid instruction, without intervening data blocks
    or jump tables.*)
val has_next_valid_instruction: doubleword_int -> bool


(** [get_next_valid_instruction_address a] returns the smallest address greater
    than [a] that is the address of a valid instruction, without intervening
    data blocks or jump tables. If [a] is out-of-range or no such address exists,
    None is returned. *)
val get_next_valid_instruction_address: doubleword_int -> doubleword_int traceresult
