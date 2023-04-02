(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
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

(* bchlib *)
open BCHLibTypes

(* bchlibelf *)
open BCHDwarfTypes
open BCHDwarfUtils
open BCHELFTypes

module A = TCHAssertion   


let equal_abbrev_entry
      ?(msg="")
      ~(expected: (int * string * bool * (string * string) list))
      ~(received: debug_abbrev_table_entry_t)
      () =
  let (x_index, x_tag, x_hasc, x_attrspecs) = expected in
  if not (x_index = received.dabb_index) then
    let s_expect = "abbrev: " ^ (string_of_int x_index) in
    A.fail s_expect (string_of_int received.dabb_index) msg
  else
    let r_tag = dwarf_tag_type_to_string received.dabb_tag in
    if not (x_tag = r_tag) then
      A.fail ("tag: " ^ x_tag) r_tag msg
    else if x_hasc && (not received.dabb_has_children) then
      A.fail "children: true" "false" msg
    else if (not x_hasc) && received.dabb_has_children then
      A.fail "children: false" "true" msg
    else
      A.make_equal_list
        (fun (x_attr, x_form) (r_attr, r_form) ->
          (x_attr = r_attr) && (x_form = r_form))
        (fun (attr, form) -> "(" ^ attr ^ ", " ^ form ^ ")")
        ~msg
        x_attrspecs
        (List.map (fun (attr, form) ->
             (dwarf_attr_type_to_string attr,
              dwarf_form_type_to_string form)) received.dabb_attr_specs)


let equal_variable_debuginfo_entry
      ?(msg="")
      ~(expected: (dwarf_attr_type_t * string) list)
      ~(received: debug_info_entry_t) =
  let recvvalues = received.ie_values in
  A.make_equal_list
    (fun (xat, xv) (rat, rv) -> (xat = rat) && (xv = rv))
    (fun (att, v) -> ((dwarf_attr_type_to_string att) ^ ": " ^ v))
    ~msg
    expected
    (List.map (fun (att, v) -> (att, dwarf_attr_value_to_string v)) recvvalues)


let equal_debug_location_list
      ?(msg="")
      ~(expected: (string * string * string) list)
      ~(received: debug_location_list_entry_t list) =
  A.make_equal_list
    (fun (xsa, xea, xx) (rsa, rea, rx) ->
      (xsa = rsa) && (xea = rea) && (xx = rx))
    (fun (sa, ea, x) -> sa ^ " " ^ ea ^ " " ^ x)
    ~msg
    expected
    (List.map (fun dle ->
         match dle with
         | LocationListEntry l ->
            (l.lle_start_address#to_hex_string,
             l.lle_end_address#to_hex_string,
             single_location_description_to_string l.lle_location)
         | BaseAddressSelectionEntry dw -> (dw#to_hex_string, "", "")
         | EndOfListEntry -> ("", "", "")) received)


let equal_compilation_unit_header
      ?(msg="")
      ~(expected: (string * int * string * int))
      ~(received: debug_compilation_unit_header_t)
      () =
  let (clen, cversion, coffset, csize) = expected in
  if not (received.dwcu_length#to_hex_string = clen) then
    A.fail clen received.dwcu_length#to_hex_string msg
  else if not (received.dwcu_version = cversion) then
    A.fail
      (string_of_int cversion)
      (string_of_int received.dwcu_version)
      msg
  else if not (received.dwcu_offset#to_hex_string = coffset) then
    A. fail coffset received.dwcu_offset#to_hex_string msg
  else if not (received.dwcu_address_size = csize) then
    A. fail
         (string_of_int csize)
         (string_of_int received.dwcu_address_size)
         msg
  else
    ()


let equal_compilation_unit
      ?(msg="")
      ~(expected:
          (string
           * string
           * int
           * dwarf_tag_type_t
           * (dwarf_attr_type_t * string) list))
      ~(received: debug_compilation_unit_t)
      () =
  let (xlen, xoffset, xnr, xtag, attrs) = expected in
  let hdr = received.cu_header in
  let cu = received.cu_unit in
  if not (xlen = hdr.dwcu_length#to_hex_string) then
    A.fail xlen hdr.dwcu_length#to_hex_string msg
  else if not (xoffset = hdr.dwcu_offset#to_hex_string) then
    A.fail xoffset hdr.dwcu_offset#to_hex_string msg
  else if not (xnr = cu.ie_abbrev) then
    A.fail (string_of_int xnr) (string_of_int cu.ie_abbrev) msg
  else if not (xtag = cu.ie_tag) then
    A.fail
      (dwarf_tag_type_to_string xtag)
      (dwarf_tag_type_to_string cu.ie_tag)
      msg
  else
    A.make_equal_list
      (fun (x_attr, x_val) (r_attr, r_val) ->
        (x_attr = r_attr) && (x_val = r_val))
      (fun (attr, v) -> "(" ^ attr ^ ", " ^ v ^ ")")
      ~msg
      (List.map (fun (attr, attrv) ->
           (dwarf_attr_type_to_string attr, attrv)) attrs)
      (List.map (fun (attr, attrv) ->
           (dwarf_attr_type_to_string attr,
            dwarf_attr_value_to_string attrv)) cu.ie_values)
