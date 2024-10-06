(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2024  Aarno Labs, LLC

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

(** Sequence of consecutive assembly instructions that represents a semantic unit.
    
    Examples:
    - switch statement constructed by 
      - table branch instructions (TBB/TBH), or
      - load from table into pc
      - indirect jump from table
      
    - question expression constructed by Thumb-2 if-then instruction
    
    In translation to CHIF, semantics are obtained from the anchor, all other
    instructions belonging to the aggregate are ignored.
 *)

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


val make_arm_instruction_aggregate:
  kind:arm_aggregate_kind_t
  -> instrs:arm_assembly_instruction_int list
  -> entry:arm_assembly_instruction_int
  -> exitinstr:arm_assembly_instruction_int
  -> anchor:arm_assembly_instruction_int
  -> arm_instruction_aggregate_int


val make_arm_jumptable_aggregate:
  jt:arm_jumptable_int
  -> instrs:arm_assembly_instruction_int list
  -> entry:arm_assembly_instruction_int
  -> exitinstr:arm_assembly_instruction_int
  -> anchor:arm_assembly_instruction_int
  -> arm_instruction_aggregate_int


val identify_arm_aggregate:
  pushback_stream_int
  -> arm_assembly_instruction_int
  -> arm_instruction_aggregate_int option
