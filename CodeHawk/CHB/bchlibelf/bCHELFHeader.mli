(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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

(* bchlibx86 *)
open BCHDoubleword
open BCHPESectionHeader

(* bchlibelf *)
open BCHELFTypes
open BCHELFUtil


type elf_symbol_type = 
  | NoSymbolType
  | ObjectSymbol 
  | FunctionSymbol 
  | SectionSymbol 
  | FileSymbol
  | UnknownSymbol of int

(* Based on the Intel-specific part of the ABI *)
type elf_relocation_type_i386 = 
  | R_386_NONE 
  | R_386_32 
  | R_386_PC32 
  | R_386_GOT32 
  | R_386_PLT32 
  | R_386_COPY 
  | R_386_GLOB_DAT
  | R_386_JMP_SLOT 
  | R_386_RELATIVE 
  | R_386_GOTOFF 
  | R_386_GOTPC

val elf_header    : elf_header_int
val save_elf_files: unit -> unit
val load_elf_files: unit -> unit

val read_elf_file: string -> int -> bool * pretty_t
