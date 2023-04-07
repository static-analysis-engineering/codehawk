(* =============================================================================
   CodeHawk Binary Analyzer 
   Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes

(* bchlibelf *)
open BCHDwarf
open BCHDwarfTypes   
open BCHELFTypes


module H = Hashtbl


class debug_abbrev_table_t
        (offset: doubleword_int)
        (d_entries: debug_abbrev_table_entry_t list): debug_abbrev_table_int =
object (self)

  val entries =
    let table = H.create (List.length d_entries) in
    begin
      List.iter (fun e -> H.add table e.dabb_index e) d_entries;
      table
    end
  val offset = offset

  method abbrev_entry (index: int) =
    if H.mem entries index then
      H.find entries index
    else
      raise
        (Invalid_argument
           ("abbrev_table @ "
            ^ offset#to_hex_string
            ^ ": entry "
            ^ (string_of_int index)
            ^ " not found"))

  method entry_count = H.length entries

  method offset = offset

end


(* -----------------------------------------------------------------------------
   DWARF sections:
   .debug_abbrev: Abbreviations used in the .debug_info section
   .debug_aranges: Lookup table for mapping addresses to compilation units
   .debug_frame: Call frame information
   .debug_info: Core DWARF information section (organized by compilation unit)
   .debug_line: Line number information
   .debug_loc: Location lists
   .debug_macinfo: Macro information (optional)
   .debug_pubnames: Lookup table for global objects and functions (optional)
   .debug_pubtypes: Lookup table for global types (optional)
   .debug_ranges: Address ranges
   .debug_str: String table
   .debug_types: Type descriptions (organized by compilation unit) (optional)
 ---------------------------------------------------------------------------- *)
class dwarf_query_service_t:dwarf_query_service_int =
object (self)

  val sections = H.create 5
  val abbrevtables = H.create 5
  val compilation_unit_headers = H.create 5

  method initialize (debugsections: (int * string * elf_section_t) list) =
    begin
      List.iter (fun (index, name, section) ->
          H.add sections name section) debugsections;
      (if self#has_debug_info then
         let headers =
           self#get_debug_info#compilation_unit_headers
             self#compilation_unit_offsets in
         List.iter (fun cuh ->
             H.add compilation_unit_headers cuh.dwcu_offset#index cuh)
           headers)
    end

  method has_debug = H.mem sections ".debug_info"

  method private has_aranges = H.mem sections ".debug_aranges"

  method private get_aranges: elf_debug_aranges_section_int =
    match (H.find sections ".debug_aranges") with
    | ElfDebugARangesSection s -> s
    | _ -> raise (Invalid_argument "dwarf_query_service:get_aranges")

  method private has_abbrev = H.mem sections ".debug_abbrev"

  method private get_abbrev: elf_debug_abbrev_section_int =
    match (H.find sections ".debug_abbrev") with
    | ElfDebugAbbrevSection s -> s
    | _ -> raise (Invalid_argument "dwarf_query_service:get_abbrev")

  method private has_debug_info = H.mem sections ".debug_info"

  method private get_debug_info: elf_debug_info_section_int =
    match (H.find sections ".debug_info") with
    | ElfDebugInfoSection s -> s
    | _ -> raise (Invalid_argument "dwarf_query_service:get_debug_info")

  method private has_str = H.mem sections ".debug_str"

  method private get_debug_str: elf_debug_str_section_int =
    match (H.find sections ".debug_str") with
    | ElfDebugStringSection s -> s
    | _ -> raise (Invalid_argument "dwarf_query_service:get_str")

  method private has_lkoc = H.mem sections ".debug_loc"

  method private get_debug_loc: elf_debug_loc_section_int =
    match (H.find sections ".debug_loc") with
    | ElfDebugLocSection s -> s
    | _ -> raise (Invalid_argument "dwarf_query_service:get_loc")

  method compilation_unit_offsets =
    if self#has_aranges then
      let s = self#get_aranges in
      s#debug_info_compilation_unit_offsets
    else
      []

  method compilation_unit (offset: doubleword_int) =
    if H.mem compilation_unit_headers offset#index then
      let header = H.find compilation_unit_headers offset#index in
      let abbrevtable = self#abbrev_table header.dwcu_abbrev_offset in
      let ch = self#get_debug_info#compilation_unit_stream offset in
      decode_compilation_unit
        ~get_abbrev_entry:abbrevtable#abbrev_entry
        ~get_string:self#get_debug_str#get_string
        ~get_loclist:self#get_debug_loc#get_loclist
        ~base:offset
        ~header
        ch
    else
      raise (Invalid_argument "dwarf_query_service:compilation_unit")

  method compilation_units =
    List.map self#compilation_unit self#compilation_unit_offsets

  method compilation_unit_variables (offset: doubleword_int) =
    let cu = self#compilation_unit offset in
    let exprlocs = ref 0 in
    let loclists = H.create 3 in
    let dwies = flatten_compilation_unit cu in
    let _ = pr_debug [STR "Dwies: "; INT (List.length dwies); NL] in
    let vars =
      List.filter (fun dwie ->
          match dwie.dwie_tag with
          | DW_TAG_variable | DW_TAG_formal_parameter -> true
          | _ -> false) dwies in
    let locations =
      List.iter (fun vdwie ->
          let atvs = vdwie.dwie_values in
          if List.exists (fun (attr, _) -> attr = DW_AT_location) atvs then
            let (attr, atv) = List.find (fun (attr, atv) -> attr = DW_AT_location) atvs in
            match atv with
            | DW_ATV_FORM_exprloc _ -> exprlocs := !exprlocs + 1
            | DW_ATV_FORM_sec_offset (LoclistPtr, offset) ->
               let loclist = self#get_debug_loc#get_loclist offset#index in
               let loclistlen =
                 match loclist with
                 | SingleLocation _ -> 1
                 | LocationList l -> List.length l in
               let loclistentry =
                 if H.mem loclists loclistlen then
                   H.find loclists loclistlen
                 else
                   0 in
               H.replace loclists loclistlen (loclistentry + 1)
            | _ -> ()
          else
            ()) vars in
    (!exprlocs, List.sort Stdlib.compare (H.fold (fun k v a -> (k, v) :: a) loclists []))

  method compilation_units_variables =
    let exprlocs = ref 0 in
    let loclists = H.create 3 in
    let _ =
      List.iter (fun offset ->
          let (x, l) = self#compilation_unit_variables offset in
          begin
            exprlocs := !exprlocs + x;
            List.iter (fun (len, count) ->
                let entry =
                  if H.mem loclists len then
                    H.find loclists len
                  else
                    0 in
                H.replace loclists len (entry + count)) l
          end) self#compilation_unit_offsets in
    (!exprlocs, List.sort Stdlib.compare (H.fold (fun k v a -> (k, v) :: a) loclists []))

  method abbrev_table (offset: doubleword_int) =
    let index = offset#index in
    if H.mem abbrevtables index then
      H.find abbrevtables index
    else
      if self#has_abbrev then
        let s = self#get_abbrev in
        let entries = s#get_abbrev_table index in
        let t = new debug_abbrev_table_t offset entries in
        begin
          H.add abbrevtables index t;
          t
        end
      else
        raise (Invalid_argument "dwarf_query_service:get_abbrev")

end

    
let dwarf_query_service = new dwarf_query_service_t