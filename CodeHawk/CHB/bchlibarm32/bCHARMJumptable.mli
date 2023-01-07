(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
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

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


(** Facility to identify and construct jump tables for TBB/TBH, LDR, and BX *)   


(** [create_arm_table_branch ch instr] creates a jump table targeted by a TBB or TBH 
    instruction [instr] by processing the associated jump table bytes/halfwords
    from stream [ch] (Thumb-2 pattern).*)
val create_arm_table_branch:
  pushback_stream_int
  -> arm_assembly_instruction_int
  -> (arm_assembly_instruction_int list * arm_jumptable_int) option


(** [create_arm_ldr_jumptable ch instr] creates a jump table targeted by an LDR 
    instruction [instr] by processing the associated list of addresses from
    stream [ch] (Thumb-2 pattern).*)
val create_arm_ldr_jumptable:
  pushback_stream_int
  -> arm_assembly_instruction_int
  -> (arm_assembly_instruction_int list * arm_jumptable_int) option


(** [create_arm_ldrls_jumptable ch instr] creates a jump table targeted by an
    LDRLS instruction [instr] by processing the associated list of addresses
    from stream [ch] (ARM pattern).*)
val create_arm_ldrls_jumptable:
  pushback_stream_int
  -> arm_assembly_instruction_int
  -> (arm_assembly_instruction_int list * arm_jumptable_int) option


(** [create_bx_jumptable ch instr] creates a jump table targeted by a BX 
    instruction [instr] by processing the associated list of addresses from
    stream [ch].*)
val create_arm_bx_jumptable:
  pushback_stream_int
  -> arm_assembly_instruction_int
  -> (arm_assembly_instruction_int list * arm_jumptable_int) option
