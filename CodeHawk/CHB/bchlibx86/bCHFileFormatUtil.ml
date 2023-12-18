(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
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

(* API to hide differences between PE and ELF *)

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHSystemInfo
open BCHSystemSettings

(* chutil *)
module TR = CHTraceResult

(* bchlibpe *)
module PEXN = BCHPEExnHandler
module PEH = BCHPEHeader
module PES = BCHPESections

(* bchlibelf *)
module ELFH = BCHELFHeader


let is_elf () = system_settings#is_elf


let register_exn_handler (vaddr:doubleword_int) (bytes:string) =
  if is_elf () then
    ()
  else
    PEXN.register_exn_handler vaddr bytes


let get_data_values (vaddr:doubleword_int) (s:data_export_spec_t) =
  if is_elf () then
    []
  else
    PES.pe_sections#get_data_values vaddr s


let get_export_directory_table () =
  if is_elf () then
    raise (BCH_failure (LBLOCK [ STR "Elf does not have an export table" ]))
  else
    PES.pe_sections#get_export_directory_table


let get_exported_data_values () =
  if is_elf () then
    []
  else
    PES.pe_sections#get_exported_data_values


let get_exported_functions () =
  if is_elf () then
    []
  else
    PES.pe_sections#get_exported_functions


let get_import_directory_table () =
  if is_elf () then
    raise (BCH_failure (LBLOCK [ STR "Elf does nnot have an import table" ]))
  else
    PES.pe_sections#get_import_directory_table


let get_imported_function_by_index (vaddr:doubleword_int) =
  if is_elf () then
    None
  else
    PES.pe_sections#get_imported_function_by_index vaddr


let get_read_only_initialized_doubleword (vaddr:doubleword_int) =
  if is_elf () then
    None
  else
    PES.pe_sections#get_read_only_initialized_doubleword vaddr


let get_string_reference (vaddr:doubleword_int) =
  if is_elf () then
    ELFH.elf_header#get_string_at_address vaddr
  else
    PES.pe_sections#get_string_reference vaddr


let has_export_directory_table () =
  if is_elf () then
    false
  else
    PES.pe_sections#has_export_directory_table


let has_import_directory_table () =
  if is_elf () then
    false
  else
    PES.pe_sections#has_import_directory_table


let is_image_address (n:numerical_t) =
  if is_elf () then
    true    (* TBD *)
  else
    try
      match PEH.pe_header#get_containing_section_name
              (TR.tget_ok (numerical_to_doubleword n)) with
      | Some _ -> true
      | _ -> false
    with
    | BCH_failure p ->
       let msg =
         LBLOCK [
             STR "is_image_address: "; n#toPretty; STR " ("; p; STR ")"] in
       begin
         ch_error_log#add "doubleword conversion" msg;
         false
       end


let is_exported (vaddr:doubleword_int) =
  if is_elf () then
    false
  else
    PES.pe_sections#is_exported vaddr


let is_read_only_address (vaddr:doubleword_int) =
  if is_elf () then
    false     (* TBD *)
  else
    PES.pe_sections#is_read_only_address vaddr


let write_xml_exn_handlers (node:xml_element_int) =
  if is_elf () then
    ()
  else
    PEXN.write_xml_exnhandlers node
