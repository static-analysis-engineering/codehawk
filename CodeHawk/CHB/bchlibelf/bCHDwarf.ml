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
open BCHDoubleword
open BCHLibTypes

(* bchlibelf *)
open BCHDwarfTypes
open BCHDwarfUtils
open BCHELFTypes


(*
let decode_compilation_unit_header (ch: pushback_stream_int) =

  let len = ch#read_doubleword in
  let version = ch#read_ui16 in
  let debug_abbrev_offset = ch#read_doubleword in
  let address_size = ch#read_byte in
  {
    dwcu_length = len;
    dwcu_version = version;
    dwcu_offset = debug_abbrev_offset;
    dwcu_address_size = address_size
  }
 *)

let decode_debug_attribute_value
      ?(get_string=(fun (_:int) -> "?"))
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (attrspec: (dwarf_attr_type_t * dwarf_form_type_t)):
      (dwarf_attr_type_t * dwarf_attr_value_t) =
  let (attr, form) = attrspec in
  let value =
    match form with
    | DW_FORM_addr -> DW_ATV_FORM_addr ch#read_doubleword#to_hex_string
    | DW_FORM_data1 -> DW_ATV_FORM_data1 ch#read_byte
    | DW_FORM_data2 -> DW_ATV_FORM_data2 ch#read_ui16
    | DW_FORM_data4 -> DW_ATV_FORM_data4 ch#read_doubleword
    | DW_FORM_exprloc ->
       let size = ch#read_dwarf_leb128 in
       let locexpr = read_dwarf_expression ch size in
       DW_ATV_FORM_exprloc (size, locexpr)
    | DW_FORM_flag_present -> DW_ATV_FORM_flag_present 1
    | DW_FORM_sdata -> DW_ATV_FORM_sdata (ch#read_dwarf_sleb128 32)
    | DW_FORM_ref4 -> DW_ATV_FORM_ref4 (ch#read_doubleword#add base)
    | DW_FORM_sec_offset -> DW_ATV_FORM_sec_offset (ch#read_doubleword)
    | DW_FORM_string -> DW_ATV_FORM_string ch#read_null_terminated_string
    | DW_FORM_strp ->
       let offset = ch#read_doubleword in
       let s = get_string offset#index in
       DW_ATV_FORM_strp (offset, s)
    | _ -> DW_ATV_FORM_unknown (dwarf_form_type_to_string form) in
  (attr, value)


let decode_debug_attribute_values
      ?(get_string=(fun (_:int) -> "?"))
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (attrspecs: (dwarf_attr_type_t * dwarf_form_type_t) list) =
  List.map (decode_debug_attribute_value ~get_string ch base) attrspecs


let decode_variable_die
      ?(get_string=(fun (_:int) -> "?"))
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (get_abbrev_entry: int -> debug_abbrev_table_entry_t) =
  let abbrevindex = ch#read_dwarf_leb128 in
  let abbrev = get_abbrev_entry abbrevindex in
  let tag = abbrev.dabb_tag in
  let values =
    decode_debug_attribute_values ~get_string ch base abbrev.dabb_attr_specs in
  {
    ie_abbrev = abbrevindex;
    ie_tag = tag;
    ie_values = values;
    ie_children = []
  }


let decode_compilation_unit
      (get_string: int -> string)
      (cuh: debug_compilation_unit_header_t)
      (ch: pushback_stream_int)
      (get_abbrev_entry: int -> debug_abbrev_table_entry_t) =

  let rec decode_debug_info_entry ?(first=false) (base: doubleword_int) =
    let abbrevindex = ch#read_dwarf_leb128 in
    if abbrevindex = 0 then
      let _ = pr_debug [STR "-------------------------------------"; NL] in
      {
        ie_abbrev = 0;
        ie_tag = DW_TAG_unknown "0";
        ie_values = [];
        ie_children = []
      }
    else
      let abbrev = get_abbrev_entry abbrevindex in
      let tag = abbrev.dabb_tag in
      let _ = pr_debug [STR "Abbrev entry: "; INT abbrev.dabb_index;
                        STR " (";
                        STR (dwarf_tag_type_to_string tag);
                        STR ")"; NL] in
      let values = decode_debug_attribute_values ~get_string ch base abbrev.dabb_attr_specs in
      let _ = pr_debug [pretty_print_list values
                          (fun (t, v) -> LBLOCK [
                                             STR "  ";
                                             STR (dwarf_attr_type_to_string t);
                                             STR ": ";
                                             STR (dwarf_attr_value_to_string v);
                                             NL]) "" "" ""; NL] in
    let base =
      if first && List.exists (fun (t, v) -> t = DW_AT_low_pc) values then
        let (_, v) = List.find (fun (t, v) -> t = DW_AT_low_pc) values in
        match v with
        | DW_ATV_FORM_data4 dw -> dw
        | _ -> base
      else
        base in
    let children =
      if abbrev.dabb_has_children then
        decode_debug_info_entry_list base
      else
        [] in
    {
      ie_abbrev = abbrevindex;
      ie_tag = tag;
      ie_values = values;
      ie_children = children
    }

  and decode_debug_info_entry_list (base: doubleword_int) =
    let cdie = ref (decode_debug_info_entry base) in
    let children = ref [] in
    begin
      while (!cdie.ie_abbrev > 0) do
        children := !cdie :: !children;
        cdie := decode_debug_info_entry base
      done;
      List.rev !children
    end in

  let compilation_unit = decode_debug_info_entry ~first:true wordzero in
  {cu_header = cuh; cu_unit = compilation_unit}

