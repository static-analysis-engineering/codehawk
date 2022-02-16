(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchcil *)
open BCHBCFiles
open BCHCBasicTypes

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes
open BCHVariableType

module H = Hashtbl


let call_back_table_value_to_string (v: call_back_table_value_t) =
  match v with
  | CBAddress s -> "address:" ^ s
  | CBTag s -> "tag:" ^ s
  | CBValue n -> "num:" ^ n#toString


class call_back_table_record_t
        (address: string)
        (values: (int * call_back_table_value_t) list): call_back_table_record_int =
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
      | CBTag s -> s
      | v ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Value at offset: ";
                   INT offset;
                   STR " is not a string: ";
                   STR (call_back_table_value_to_string v)]))
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No callback value found at offset "; INT offset]))

  method intvalue (offset: int) =
    if H.mem recordvalues offset then
      match H.find recordvalues offset with
      | CBValue n -> n
      | v ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Value at offset: ";
                   INT offset;
                   STR " is not an integer value: ";
                   STR (call_back_table_value_to_string v)]))
    else
      raise
        (BCH_failure
           (LBLOCK[
                STR "No callback value found at offset "; INT offset]))

  method addrvalue (offset: int) =
    if H.mem recordvalues offset then
      match H.find recordvalues offset with
      | CBAddress s -> s
      | v ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Value at offset: ";
                   INT offset;
                   STR " is not an address: ";
                   STR (call_back_table_value_to_string v)]))
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "No callback value found at offset "; INT offset]))

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map (fun (k, v) ->
           let vnode = xmlElement "v" in
           let set = vnode#setAttribute in
           begin
             vnode#setIntAttribute "offset" k;
             (match v with
              | CBAddress s ->
                 begin
                   set "tag" "address";
                   set "value" s
                 end
              | CBTag s ->
                 begin
                   set "tag" "tag";
                   set "value" s
                 end
              | CBValue n ->
                 begin
                   set "tag" "value";
                   set "value" n#toString
                 end);
             vnode
           end) self#values)

  method toPretty =
    LBLOCK (List.map (fun (k, v) ->
                LBLOCK [
                    INT k;
                    STR ": ";
                    STR (call_back_table_value_to_string v);
                    NL]) self#values)

end
    


class call_back_table_t (cba: string) (ty: btype_t): call_back_table_int =
object (self)

  val address = cba
  val recordtype = resolve_type ty
  val records = H.create 7
  val fieldnames =
    let table = H.create 3 in
    let recty = resolve_type ty in
    let _ =
      match recty with
      | TFun _ | TPtr (TFun _, _) ->
         H.add table 0 ("cbp_" ^ cba)
      | TPtr (TComp (ckey, _), _) ->
         let compinfo = get_compinfo_by_key ckey in
         List.iteri (fun i fld ->
             H.add table (i * 4) fld.bfname) compinfo.bcfields
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Unexpected type in creating callback table: ";
                   btype_to_pretty recty])) in
    table

  val offsettypes =
    let table = H.create 3 in
    let recty = resolve_type ty in
    let _ =
      match recty with
      | TFun _ -> H.add table 0 ty
      | TPtr (TFun (rty, args, b, attr), _) ->
         H.add table 0 (TFun (rty, args, b, attr))
      | TPtr (TComp (ckey, _), _) ->
         let compinfo = get_compinfo_by_key ckey in
         List.iteri (fun i fld ->
             let offset = i * 4 in
             match fld.bftype with
             | TFun _ -> H.add table offset fld.bftype
             | TPtr (TFun (rty, args, b, attr), _) ->
                H.add table offset (TFun (rty, args, b, attr))
             | _ ->
                H.add table offset (resolve_type fld.bftype)) compinfo.bcfields
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Unexpected type in creating callback record: ";
                   btype_to_pretty recty])) in
    table

  method add_record
           (recaddr: string)
           (values: (int * call_back_table_value_t) list) =
    let r = new call_back_table_record_t recaddr values in
    begin
      H.add records recaddr r;
      chlog#add
        ("call-back table " ^ address)
        (LBLOCK [
             pretty_print_list values (fun (i, v) ->
                 LBLOCK [
                     INT i; STR ":"; STR (call_back_table_value_to_string v)])
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
                STR " not present in record type ";
                btype_to_pretty self#record_type]))

  method fieldname_at_offset (offset: int) =
    if H.mem fieldnames offset then
      H.find fieldnames offset
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Offset ";
                INT offset;
                STR " not present in record type ";
                btype_to_pretty self#record_type]))

  method record_length =
    H.length offsettypes

  method field_offset_types: (int * btype_t) list =
    H.fold (fun k v a -> (k, v) :: a) offsettypes []

  method function_pointer_values: (string * btype_t) list =
    let rl = H.fold (fun _ v a -> v :: a) records [] in
    List.concat
      (List.map (fun r ->
           List.fold_left (fun acc (o, v) ->
               match v with
               | CBAddress addr ->
                  let fty = self#type_at_offset o in
                  (addr, fty) :: acc
               | _ -> acc) [] r#values) rl)

  method write_xml (node: xml_element_int) =
    let rl = H.fold (fun k v a -> (k, v) :: a) records [] in
    node#appendChildren
      (List.map (fun (k, r) ->
           let rnode = xmlElement "cbr" in
           begin
             rnode#setAttribute "address" k;
             r#write_xml rnode;
             rnode
           end) rl)
       
end


class call_back_tables_t =
object (self)

  val tables = H.create 3
  val tableaddresses = H.create 3

  method add_table_address (addr: string) (v: string) =
    begin
      H.add tableaddresses addr v;
      chlog#add
        "call-back table address"
        (LBLOCK [STR addr; STR ": "; STR v])
    end

  method set_function_pointers =
    H.iter (fun _ cbtable ->
        let fpointervalues = cbtable#function_pointer_values in
        List.iter (fun (addr, fty) ->
            begin
              self#add_to_functions_data addr fty;
              self#add_function_prototype addr fty
            end) fpointervalues) tables

  method private add_to_functions_data (addr: string) (fty: btype_t) =
    let dw = string_to_doubleword addr in
    let functiondata =
      if functions_data#is_function_entry_point dw then
        functions_data#get_function dw
      else
        functions_data#add_function dw in
    functiondata#set_function_type fty

  method private add_function_prototype (addr: string) (fty: btype_t) =
    let dw = string_to_doubleword addr in
    let functiondata = functions_data#get_function dw in
    let fname =
      if functiondata#has_name then
        functiondata#get_function_name
      else
        "sub_" ^ (String.sub addr 2 ((String.length addr) - 2)) in
    bcfiles#add_fundef fname fty

  method table_variables =
    H.fold (fun k v a -> (k, v) :: a) tableaddresses []

  method new_table (addr: string) (ty: btype_t) =
    let table = new call_back_table_t addr ty in
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
           (LBLOCK [STR "Call-back table not found at address"; STR va]))

  method has_table (va: string) =
    H.mem tables va

  method write_xml (node: xml_element_int) =
    let cbtables = H.fold (fun k v a -> (k, v) :: a) tables [] in
    node#appendChildren
      (List.map (fun (k, t) ->
           let tnode = xmlElement "call-back-table" in
           begin
             t#write_xml tnode;
             tnode#setAttribute "address" k;
             tnode
           end) cbtables)

end


let callbacktables: call_back_tables_int = new call_back_tables_t
