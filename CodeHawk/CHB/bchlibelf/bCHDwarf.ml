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
      ?(get_loclist=(fun (_:int) -> LocationList []))
      ~(attrspec:(dwarf_attr_type_t * dwarf_form_type_t))
      ~(base: doubleword_int)
      (ch: pushback_stream_int):(dwarf_attr_type_t * dwarf_attr_value_t) =
  let (attr, form) = attrspec in
  let value =
    match form with
    | DW_FORM_addr -> DW_ATV_FORM_addr ch#read_doubleword#to_hex_string
    | DW_FORM_block1 ->
       let size = ch#read_byte in
       let bytes = List.init size (fun _ -> ch#read_byte) in
       DW_ATV_FORM_block1 (size, bytes)
    | DW_FORM_data1 -> DW_ATV_FORM_data1 ch#read_byte
    | DW_FORM_data2 -> DW_ATV_FORM_data2 ch#read_ui16
    | DW_FORM_data4 -> DW_ATV_FORM_data4 ch#read_doubleword
    | DW_FORM_exprloc ->
       let size = ch#read_dwarf_leb128 in
       let locexpr = read_dwarf_expression ch ~base size in
       DW_ATV_FORM_exprloc (size, locexpr)
    | DW_FORM_flag_present -> DW_ATV_FORM_flag_present 1
    | DW_FORM_sdata -> DW_ATV_FORM_sdata (ch#read_dwarf_sleb128 32)
    | DW_FORM_ref4 -> DW_ATV_FORM_ref4 (ch#read_doubleword#add base)
    | DW_FORM_sec_offset ->
       let kind = secoffset_kind attr in
       DW_ATV_FORM_sec_offset (kind, ch#read_doubleword)
    | DW_FORM_string -> DW_ATV_FORM_string ch#read_null_terminated_string
    | DW_FORM_strp ->
       let offset = ch#read_doubleword in
       let s = get_string offset#index in
       DW_ATV_FORM_strp (offset, s)
    | _ -> DW_ATV_FORM_unknown (dwarf_form_type_to_string form) in
  (attr, value)


let decode_debug_attribute_values
      ?(get_string=(fun (_:int) -> "?"))
      ?(get_loclist=(fun (_:int) -> LocationList []))
      ~(attrspecs: (dwarf_attr_type_t * dwarf_form_type_t) list)
      ~(base: doubleword_int)
      (ch: pushback_stream_int) =
  List.map (fun attrspec ->
      decode_debug_attribute_value
        ~get_string ~get_loclist ~attrspec ~base ch) attrspecs


let decode_variable_die
      ~(get_abbrev_entry: int -> debug_abbrev_table_entry_t)
      ?(get_string=(fun (_:int) -> "?"))
      ?(get_loclist=(fun (_:int) -> LocationList []))
      ~(base: doubleword_int)
      (ch: pushback_stream_int) =
  let abbrevindex = ch#read_dwarf_leb128 in
  let abbrev = get_abbrev_entry abbrevindex in
  let tag = abbrev.dabb_tag in
  let values =
    decode_debug_attribute_values
      ~get_string ~attrspecs:abbrev.dabb_attr_specs ~base ch in
  {
    dwie_abbrev = abbrevindex;
    dwie_tag = tag;
    dwie_values = values;
    dwie_children = []
  }


let flatten_compilation_unit (dcu: debug_compilation_unit_t) =
  let result = ref [] in

  let rec add_entry (e: debug_info_entry_t) =
    begin
      result := e :: !result;
      List.iter add_entry e.dwie_children
    end in

  begin
    add_entry dcu.cu_unit;
    List.rev !result
  end


let decode_compilation_unit
      ~(get_abbrev_entry: int -> debug_abbrev_table_entry_t)
      ~(get_string: int -> string)
      ~(get_loclist: int -> debug_loc_description_t)
      ~(base: doubleword_int)
      ~(header: debug_compilation_unit_header_t)
      (ch: pushback_stream_int) =


  let rec decode_debug_info_entry ?(first=false) (pcbase: doubleword_int) =
    let abbrevindex = ch#read_dwarf_leb128 in
    if abbrevindex = 0 then
      let _ = pr_debug [STR "-------------------------------------"; NL] in
      {
        dwie_abbrev = 0;
        dwie_tag = DW_TAG_unknown "0";
        dwie_values = [];
        dwie_children = []
      }
    else
      let abbrev = get_abbrev_entry abbrevindex in
      let tag = abbrev.dabb_tag in
      let _ = pr_debug [STR "<";
                        STR base#to_hex_string;
                        STR "> ";
                        STR "Abbrev entry: "; INT abbrev.dabb_index;
                        STR " (";
                        STR (dwarf_tag_type_to_string tag);
                        STR ")"; NL] in
      let values =
        decode_debug_attribute_values
          ~get_string
          ~get_loclist
          ~attrspecs:abbrev.dabb_attr_specs
          ~base
          ch in

      let _ = pr_debug [pretty_print_list values
                          (fun (t, v) -> LBLOCK [
                                             STR "  ";
                                             STR (dwarf_attr_type_to_string t);
                                             STR ": ";
                                             STR (dwarf_attr_value_to_string v);
                                             NL]) "" "" ""; NL] in
    let pcbase =
      if first && List.exists (fun (t, v) -> t = DW_AT_low_pc) values then
        let (_, v) = List.find (fun (t, v) -> t = DW_AT_low_pc) values in
        match v with
        | DW_ATV_FORM_data4 dw -> dw
        | _ -> base
      else
        base in
    let children =
      if abbrev.dabb_has_children then
        decode_debug_info_entry_list pcbase
      else
        [] in
    {
      dwie_abbrev = abbrevindex;
      dwie_tag = tag;
      dwie_values = values;
      dwie_children = children
    }

  and decode_debug_info_entry_list (base: doubleword_int) =
    let cdie = ref (decode_debug_info_entry base) in
    let children = ref [] in
    begin
      while (!cdie.dwie_abbrev > 0) do
        children := !cdie :: !children;
        cdie := decode_debug_info_entry base
      done;
      List.rev !children
    end in

  let _ = pr_debug [NL; STR "===========================================================";
                    NL; STR "Decompilation unit at ";
                    base#toPretty; NL;
                    STR "================================================================";
                    NL] in
  let compilation_unit = decode_debug_info_entry ~first:true base in
  {cu_header = header; cu_unit = compilation_unit}

