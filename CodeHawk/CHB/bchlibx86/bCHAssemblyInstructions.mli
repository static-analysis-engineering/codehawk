(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
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

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types


(** Holds an array of all of the assembly instructions, made available through
    a class instance reference.

    This is the backing store of all assembly instructions.
*)


(** Return a reference to the class wrapper of the array of assembly
    instructions.*)
val assembly_instructions: assembly_instructions_int ref


(** Create an array of the given size to hold the assembly instructions.

    raises BCH_failure if not sufficient array space is available to
    store all instructions.*)
val initialize_instructions: int -> unit


(** Initialize the instruction array with [OpInvalid] instructions

    [initialize_assembly_instructions displacement endindex length code_baseaddr
    jumptables data_blocks] initializes an array of size at least [length] and
    initializes each element with either a proxy [OpInvalid] instruction or marks
    it as a data block or jump table, according to the start and end addresses
    of the jumptables and data blocks given in [jumptables] and [data_blocks];
    it then creates an instance of the assembly_instructions class to populate
    the array and provide other access.
*)
val initialize_assembly_instructions:
  int
  -> int
  -> int
  -> doubleword_int
  -> jumptable_int list
  -> data_block_int list
  -> unit
