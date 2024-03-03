(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2024  Aarno Labs LLC

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
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypePretty
open BCHBCFiles
open BCHLibTypes


module H = Hashtbl


let struct_table_value_to_string (v: struct_table_value_t) =
  match v with
  | STVStringAddress s -> "address:" ^ s
  | STVString s -> "string:" ^ s
  | STVNum n -> "num:" ^ n#toString


class struct_table_record_t
        (address: string)
        (values: (int * struct_table_value_t) list): struct_table_record_int =
object (self)

  val address = address
  val recordvalues =
    let t = H.create (List.length values) in
    begin
      List.iter (fun (k, v) -> H.add t k v) values;
      t
    end

  method address = address

  method values = H.fold (fun k v a -> (k, v) :: a) recordvalues []

  method stringvalue (offset: int) =
    if H.mem recordvalues offset then
      match H.find recordvalues offset with
      | STVStringAddress s -> s
      | STVString s -> s
      | v ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Value at offset: ";
                   INT offset;
                   STR " is not a string address or string value: ";
                   STR (struct_table_value_to_string v)]))
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No struct value found at offset "; INT offset]))

  method intvalue (offset: int) =
    if H.mem recordvalues offset then
      match H.find recordvalues offset with
      | STVNum n -> n
      | v ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Value at offset : ";
                   INT offset;
                   STR " is not an integer value: ";
                   STR (struct_table_value_to_string v)]))
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No sturct value found at offset "; INT offset]))

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map (fun (k, v) ->
           let vnode = xmlElement "v" in
           let set = vnode#setAttribute in
           begin
             vnode#setIntAttribute "offset" k;
             (match v with
              | STVStringAddress s ->
                 begin
                   set "tag" "sa";
                   set "value" s
                 end
              | STVString s ->
                 begin
                   set "tag" "s";
                   set "value" s
                 end
              | STVNum n ->
                 begin
                   set "tag" "n";
                   set "value" n#toString
                 end);
             vnode
           end) self#values)

  method toPretty =
    LBLOCK (List.map (fun (k, v) ->
                LBLOCK [
                    INT k;
                    STR ": ";
                    STR (struct_table_value_to_string v);
                    NL]) self#values)

end


class struct_table_t (addr: string) (ty: btype_t): struct_table_int =
object (self)

  val address = addr
  val recordtype = bcfiles#resolve_type ty
  val records = H.create 7
  val fieldnames =
    let table = H.create 3 in
    let recty = bcfiles#resolve_type ty in
    let _ =
      match recty with
      | TPtr (TComp (ckey, _), _) ->
         let compinfo = bcfiles#get_compinfo ckey in
         List.iter (fun fld ->
             match fld.bfieldlayout with
             | Some (offset, _) ->
                if H.mem table offset then
                  raise
                    (BCH_failure
                       (LBLOCK [
                            STR "Found multiple offsets of ";
                            INT offset;
                            STR " in struct type ";
                            STR (btype_to_string recty)]))
                else
                  H.add table offset fld.bfname
             | _ ->
                raise
                  (BCH_failure
                     (LBLOCK [
                          STR "Struct type without field layout: ";
                          STR (btype_to_string recty)]))) compinfo.bcfields
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Unexpected type in creating struct table record: ";
                   btype_to_pretty recty])) in
    table

  val offsettypes =
    let table = H.create 3 in
    let recty = bcfiles#resolve_type ty in
    let _ =
      match recty with
      | TPtr (TComp (ckey, _), _) ->
         let compinfo = bcfiles#get_compinfo ckey in
         List.iter (fun fld ->
             match fld.bfieldlayout with
             | Some (offset, _) ->
                H.add table offset fld.bftype
             | _ ->
                raise
                  (BCH_failure
                     (LBLOCK [
                          STR "Struct type without field layout: ";
                          STR (btype_to_string recty)]))) compinfo.bcfields
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Unexpected type in creating struct table record: ";
                   btype_to_pretty recty])) in
    table

  method add_record
           (recaddr: string)
           (values: (int * struct_table_value_t) list) =
    let r = new struct_table_record_t recaddr values in
    begin
      H.add records recaddr r;
      chlog#add
        ("struct-table " ^ address)
        (LBLOCK [
             pretty_print_list values (fun (i, v) ->
                 LBLOCK [
                     INT i; STR ":"; STR (struct_table_value_to_string v)])
               "[" ", " "]"])
    end

  method address = address

  method record_type = recordtype

  method length = H.length records

  method type_at_offset (offset: int) =
    if H.mem offsettypes offset then
      H.find offsettypes offset
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Offset ";
                INT offset;
                STR " not present in record type";
                btype_to_pretty self#record_type]))

  method fieldname_at_offset (offset: int) =
    if H.mem fieldnames offset then
      H.find fieldnames offset
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "offset ";
                INT offset;
                STR " not present in record type";
                btype_to_pretty self#record_type]))

  method record_length = H.length offsettypes

  method field_offset_types: (int * btype_t) list =
    H.fold (fun k v a -> (k, v) :: a) offsettypes []

  method write_xml (node: xml_element_int) =
    let rl = H.fold (fun k v a -> (k, v) :: a) records [] in
    node#appendChildren
      (List.map (fun (k, r) ->
           let rnode = xmlElement "sr" in
           begin
             rnode#setAttribute "address" k;
             r#write_xml rnode;
             rnode
           end) rl)

end


class struct_tables_t =
object (self)

  val tables = H.create 3           (* hex address -> struct_table *)
  val tableaddresses = H.create 3   (* hex address -> variable name *)

  method add_table_address (addr: string) (v: string) (size: int) =
    begin
      H.add tableaddresses addr (v, size);
      chlog#add
        "struct table address"
        (LBLOCK [STR addr; STR ": "; STR v])
    end

  method table_variables =
    H.fold (fun k v a -> (k, v) :: a) tableaddresses []

  method new_table (addr: string) (ty: btype_t) =
    let table = new struct_table_t addr ty in
    begin
      H.add tables addr table;
      table
    end

  method get_table (va: string) =
    if self#has_table va then
      H.find tables va
    else
      raise
        (BCH_failure
           (LBLOCK [STR "Struct table not found at address "; STR va]))

  method has_table (va: string) = H.mem tables va

  method write_xml (node: xml_element_int) =
    let stables = H.fold (fun k v a -> (k, v) :: a) tables [] in
    node#appendChildren
      (List.map (fun (k, t) ->
           let tnode = xmlElement "struct-table" in
           begin
             t#write_xml tnode;
             tnode#setAttribute "address" k;
             tnode
           end) stables)

end


let structtables: struct_tables_int = new struct_tables_t
