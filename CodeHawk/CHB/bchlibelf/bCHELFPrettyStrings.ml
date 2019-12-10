(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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


let file_type_string typ =
  match typ with
  | 0 -> "No file type"
  | 1 -> "Relocatable File"
  | 2 -> "Executable File"
  | 3 -> "Shared object file"
  | 4 -> "Core file"
  | _ ->
     if typ >= 0xfe00 && typ <= 0xfeff then
       "Operating system-specific file(" ^ (string_of_int typ) ^ ")"
     else if typ >= 0xff00 && typ <= 0xffff then
       "Processor-specific file(" ^ (string_of_int typ) ^ ")"
     else
	"Invalid/Unknown file type(" ^ (string_of_int typ) ^ ")"
	  
let machine_to_string machine =
  match machine with
  | 0 -> "No machine"
  | 1 -> "AT&T WE 32100"
  | 2 -> "SUN SPARC"
  | 3 -> "Intel 80386"
  | 4 -> "Motorola m68k family"
  | 5 -> "Motorola m88k family"
  | 7 -> "Intel 80860"
  | 8 -> "MIPS R3000 big-endian"
  | 9 -> "IBM System/370"
  | 10 -> "MIPS R3000 little-endian"

  | 15 -> "HPPA"
  | 17 -> "Fujitsu VPP500"
  | 18 -> "Sun's \"v8plus\""
  | 19 -> "Intel 80960"
  | 20 -> "PowerPC"
  | 21 -> "PowerPC 64-bit"
  | 22 -> "IBM S390"

  | 36 -> "NEC V800 series"
  | 37 -> "Fujitsu FR20"
  | 38 -> "TRW RH-32"
  | 39 -> "Motorola RCE"
  | 40 -> "ARM"
  | 41 -> "Digital Alpha"
  | 42 -> "Hitachi SH"
  | 43 -> "SPARC v9 64-bit"
  | 44 -> "Siemens Tricore"
  | 45 -> "Argonaut RISC Core"
  | 46 -> "Hitachi H8/300"
  | 47 -> "Hitachi H8/300H"
  | 48 -> "Hitachi H8S"
  | 49 -> "Hitachi H8/500"
  | 50 -> "Intel Merced"
  | 51 -> "Stanford MIPS-X"
  | 52 -> "Motorola Coldfire"
  | 53 -> "Motorola M68HC12"
  | 54 -> "Fujitsu MMA Multimedia Accelerator"
  | 55 -> "Siemens PCP"
  | 56 -> "Sony nCPU embeeded RISC"
  | 57 -> "Denso NDR1 microprocessor"
  | 58 -> "Motorola Start*Core processor"
  | 59 -> "Toyota ME16 processor"
  | 60 -> "STMicroelectronic ST100 processor"
  | 61 -> "Advanced Logic Corp. Tinyj emb.fam"
  | 62 -> "AMD x86-64 architecture"
  | 63 -> "Sony DSP Processor"

  | 66 -> "Siemens FX66 microcontroller"
  | 67 -> "STMicroelectronics ST9+ 8/16 mc"
  | 68 -> "STmicroelectronics ST7 8 bit mc"
  | 69 -> "Motorola MC68HC16 microcontroller"
  | 70 -> "Motorola MC68HC11 microcontroller"
  | 71 -> "Motorola MC68HC08 microcontroller"
  | 72 -> "Motorola MC68HC05 microcontroller"
  | 73 -> "Silicon Graphics SVx"
  | 74 -> "STMicroelectronics ST19 8 bit mc"
  | 75 -> "Digital VAX"
  | 76 -> "Axis Communications 32-bit embedded processor"
  | 77 -> "Infineon Technologies 32-bit embedded processor"
  | 78 -> "Element 14 64-bit DSP Processor"
  | 79 -> "LSI Logic 16-bit DSP Processor"
  | 80 -> "Donald Knuth's educational 64-bit processor"
  | 81 -> "Harvard University machine-independent object files"
  | 82 -> "SiTera Prism"
  | 83 -> "Atmel AVR 8-bit microcontroller"
  | 84 -> "Fujitsu FR30"
  | 85 -> "Mitsubishi D10V"
  | 86 -> "Mitsubishi D30V"
  | 87 -> "NEC v850"
  | 88 -> "Mitsubishi M32R"
  | 89 -> "Matsushita MN10300"
  | 90 -> "Matsushita MN10200"
  | 91 -> "picoJava"
  | 92 -> "OpenRISC 32-bit embedded processor"
  | 93 -> "ARC Cores Tangent-A5"
  | 94 -> "Tensilica Xtensa Architecture"
  | 183 -> "ARM AARCH64"
  | 188 -> "Tilera TILEPro"
  | 191 -> "Tilera TILE-Gx"
  | _ -> "Unknown machine."

let section_header_type_to_string typ =
  match typ with
  | 0 -> "Null Section"
  | 1 -> "Program Bits"
  | 2 -> "Symbol Table"
  | 3 -> "String Table"
  | 4 -> "Relocation A"
  | 5 -> "Hash"
  | 6 -> "Dynamic"
  | 7 -> "Note"
  | 8 -> "No bits"
  | 9 -> "Relocation"
  | 10 -> "ShLib"
  | 11 -> "Dynamic Symbol Table"
  | 14 -> "Initialization Function Array"
  | 15 -> "Finalization Function Array"
  | 16 -> "Pre-Initialization Function Array"
  | 17 -> "Section Group"
  | 18 -> "Symbol Table Shndx"
  | _ -> "Unknown Type (" ^ (string_of_int typ) ^ ")"

let relocation_type_to_string typ =
  match typ with
  | 0 -> "R_386_NONE"
  | 1 -> "R_386_32"
  | 2 -> "R_386_PC32"
  | 3 -> "R_386_GOT32"
  | 4 -> "R_386_PLT32"
  | 5 -> "R_386_COPY"
  | 6 -> "R_386_GLOB_DAT"
  | 7 -> "R_386_JMP_SLOT"
  | 8 -> "R_386_RELATIVE"
  | 9 -> "R_386_GOTOFF"
  | 10 -> "R_386_GOTPC"
  | _ -> raise (Failure ("unexpected relocation type: " ^ string_of_int typ))

let symbol_type_to_string num =
  match num with
  | 0 -> "No Type"
  | 1 -> "Object"
  | 2 -> "Function"
  | 3 -> "Section"
  | 4 -> "File"
  | _ -> "Unknown (" ^ (string_of_int num) ^ ")"
