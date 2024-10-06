(* =============================================================================
   CodeHawk Binary Analyzer 
   Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023-2024  Aarno Labs LLC

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

(* chutil *)
open CHPrettyUtil

(* bchlib *)
open BCHDoubleword
open BCHLibTypes

(* bchlibelf *)
open BCHDwarf
open BCHDwarfOperationRecords
open BCHDwarfTypes
open BCHDwarfUtils
open BCHELFTypes


module H = Hashtbl
module TR = CHTraceResult


class debug_abbrev_table_t
        (offset: doubleword_int)
        (d_entries: debug_abbrev_table_entry_t list): debug_abbrev_table_int =
object

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


class debug_info_function_t
        (faddr: doubleword_int) (d: debug_info_entry_t):debug_info_function_int =
object (self)

  val variables = H.create 3

  method has_name: bool =
    has_dw_name d.dwie_values

  method name: string =
    if self#has_name then
      get_dw_name d.dwie_values
    else
      "?name?"

  method variable_location_stats =
    let sresult = ref [] in
    let lresult = ref [] in
    let add_sld (sld: single_location_description_t) =
      match sld with
      | SimpleLocation x -> sresult := x :: !sresult
      | _ -> () in
    let add_lld (sld: single_location_description_t) =
      match sld with
      | SimpleLocation x -> lresult := x :: !lresult
      | _ -> () in
    let add_entry (dle: debug_location_list_entry_t) =
      match dle with
      | LocationListEntry lle -> add_lld lle.lle_location
      | _ -> () in
    let _ =
      List.iter (fun (_, ld) ->
          match ld with
          | SingleLocation sld -> add_sld sld
          | LocationList entries -> List.iter add_entry entries) self#variables in
    (!sresult, !lresult)

  method variables: (string * debug_loc_description_t) list =
    let result = ref [] in
    let dwies = flatten_debug_info_entry d in
    let _ =
      List.iter (fun dwie ->
          match dwie.dwie_tag with
          | DW_TAG_variable ->
             let atvs = dwie.dwie_values in
             if has_dw_name atvs && has_dw_location atvs then
               let name = get_dw_name atvs in
               let location = get_dw_location atvs in
               result := (name, location) :: !result
             else
               ()
          | _ -> ()) dwies in
    List.sort (fun (name1, _) (name2, _) -> Stdlib.compare name1 name2) !result

  method toPretty =
    LBLOCK [
        faddr#toPretty; STR ": "; STR self#name; NL;
        LBLOCK (List.map (fun (name, loc) ->
                    LBLOCK [
                        STR "  ";
                        STR name;
                        STR ": ";
                        STR (debug_loc_description_to_string loc);
                        NL]) self#variables);
        NL; NL]

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
  val functions = H.create 5

  method initialize (debugsections: (int * string * elf_section_t) list) =
    begin
      List.iter (fun (_index, name, section) ->
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

  method private flatten_all: debug_info_entry_t list =
    let units = self#compilation_units in
    List.concat (List.map (fun cu -> flatten_debug_info_entry cu.cu_unit) units)

  method private collect_debug_info_functions =
    let dwies = self#flatten_all in
    List.iter (fun dwie ->
        match dwie.dwie_tag with
        | DW_TAG_subprogram when has_function_extent dwie.dwie_values ->
           let (faddr, _) = get_function_extent dwie.dwie_values in
           H.add functions faddr#index dwie
        | _ -> ()) dwies

  method debug_info_function_addresses: doubleword_int list =
    let _ = if (H.length functions) = 0 then self#collect_debug_info_functions in
    H.fold (fun k _ a -> (TR.tget_ok (index_to_doubleword k)) :: a) functions []

  method debug_info_function (faddr: doubleword_int) =
    let _ = if (H.length functions) = 0 then self#collect_debug_info_functions in
    if H.mem functions faddr#index then
      Some (new debug_info_function_t faddr (H.find functions faddr#index))
    else
      None

  method debug_info_functions =
    List.fold_left (fun acc faddr ->
        let optf = self#debug_info_function faddr in
        match optf with Some f -> f::acc | _ -> acc)
      [] self#debug_info_function_addresses

  method variable_location_stats: (int * int * int * dwarf_expr_t list * dwarf_expr_t list) =
    let sresult = ref [] in
    let lresult = ref [] in
    let svars = ref 0 in
    let lvars = ref 0 in
    let lvarlocs = ref 0 in
    let _ =
      List.iter (fun f ->
          let (sl ,ll) = f#variable_location_stats in
          let vars = f#variables in
          begin
            sresult := sl @ !sresult;
            lresult := ll @ !lresult;
            List.iter (fun (_, d) ->
                match d with
                | SingleLocation _ -> svars := !svars + 1
                | LocationList lst ->
                   begin
                     lvars := !lvars + 1;
                     lvarlocs := !lvarlocs + List.length lst
                   end
              ) vars
          end) self#debug_info_functions in
    (!svars, !lvars, !lvarlocs, !sresult, !lresult)

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

  method toPretty =
    let (svars, lvars, lvarlocs, sstats, lstats) = self#variable_location_stats in
    let sstats = List.concat sstats in
    let lstats = List.concat lstats in
    let lops = ref 0 in
    let plist l =
      let table = H.create 3 in
      let _ =
        List.iter (fun op ->
            let _ = lops := !lops + 1 in
            let name = get_dw_op_name op in
            let opcnt = if H.mem table name then H.find table name else 0 in
            H.replace table name (opcnt + 1)) l in
      let opcounts = H.fold (fun k v a -> (k, v) :: a) table [] in
      let opcounts =
        List.sort (fun (k1, v1) (k2, v2) -> Stdlib.compare (v1, k1) (v2, k2)) opcounts in
      LBLOCK
        (List.map (fun (k, v) ->
             LBLOCK [
                 (fixed_length_pretty (STR k) 20);
                 (fixed_length_pretty ~alignment:StrRight (INT v) 8);
                 NL]) opcounts) in
    let psstats = plist sstats in
    let _ = lops := 0 in
    let plstats = plist lstats in
    LBLOCK [STR "Single location variables: "; INT svars ; NL;
            STR "Location list variables: "; INT lvars;
            STR " with "; INT lvarlocs; STR " locations"; NL; NL;
            psstats; NL; NL; plstats; NL; NL;
            STR "Total number of operations in exprs: "; INT !lops; NL]

end

    
let dwarf_query_service = new dwarf_query_service_t
