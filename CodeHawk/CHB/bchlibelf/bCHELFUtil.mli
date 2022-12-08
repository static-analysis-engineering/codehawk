(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(* bchlibelf *)
open BCHELFTypes


val makeOffsetString : ?hexSize:doubleword_int -> 
  doubleword_int -> string -> unit -> string   (* raises Invalid_argument *)

val makeOffsetInput : ?hexSize:doubleword_int -> 
  doubleword_int -> string -> unit -> IO.input (* raises Invalid_argument *)

val memoize: ('a -> 'b) -> ('a -> 'b)

val decodeUnsignedLEB128 : IO.input -> int

val decodeSignedLEB128 : IO.input -> int

val doubleword_to_elf_section_header_type:
  doubleword_int -> elf_section_header_type_t

val doubleword_to_elf_section_header_string: doubleword_int -> string

val doubleword_to_dynamic_tag: doubleword_int -> elf_dynamic_tag_t
val doubleword_to_dynamic_tag_name: doubleword_int -> string
val doubleword_to_dynamic_tag_value: doubleword_int -> elf_dynamic_tag_value_t

val doubleword_to_arm_relocation_tag: doubleword_int -> elf_arm_relocation_tag_t
val doubleword_to_arm_relocation_tag_name: doubleword_int -> string

val elf_program_header_type_to_string: elf_program_header_type_t -> string

val doubleword_to_elf_program_header_type:
  doubleword_int -> elf_program_header_type_t

val elf_segment_to_raw_segment : elf_segment_t -> elf_raw_segment_int
val elf_section_to_raw_section : elf_section_t -> elf_raw_section_int
val elf_section_to_string_table: elf_section_t -> elf_string_table_int
val elf_section_to_symbol_table: elf_section_t -> elf_symbol_table_int
val elf_section_to_relocation_table: elf_section_t -> elf_relocation_table_int
val elf_section_to_dynamic_table: elf_section_t -> elf_dynamic_table_int
val elf_segment_to_dynamic_segment: elf_segment_t -> elf_dynamic_segment_int
