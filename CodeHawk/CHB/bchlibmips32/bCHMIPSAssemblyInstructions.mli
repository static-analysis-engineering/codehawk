(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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

(* bchlibmips32 *)
open BCHMIPSTypes
open BCHMIPSAssemblyInstruction


(** Holds an array of all of the assembly instructions, made available through
    a class instance reference.

    This is the backing store of all assembly instructions. There is one array
    element for each word address (i.e., elements are at 4-byte boundaries).
 *)

(** Return a reference to the class wrapper of the array of assembly
    instructions.*)
val mips_assembly_instructions: mips_assembly_instructions_int ref 


(** Create an array of the given size to hold the assembly instructions.*)
val initialize_mips_instructions: int -> unit


(** Initialize the instruction array with instructions *)
val initialize_mips_assembly_instructions: 
  int    (* length in bytes of the combined executable sections *)
  -> doubleword_int   (* address of code base *)
  -> unit


(** [set_mips_assembly_instruction instr] enters [instr] at the address obtained
    from [instr#get_address] in the mips_assembly_instructions store.
    If the obtained address is out-of-range and the instruction is further
    ignored.*)
val set_mips_assembly_instruction: mips_assembly_instruction_int -> unit


(** [get_mips_assembly_instruction va] returns the assembly instruction at
    virtual address [va]. If [va] is out-of-range or if there is no instruction
    at [va] an Error result is returned.*)
val get_mips_assembly_instruction: doubleword_int -> mips_assembly_instruction_result

