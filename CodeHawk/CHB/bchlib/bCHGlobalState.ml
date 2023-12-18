(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt
open XprToPretty
open XprXml

(* bchlib*)
open BCHBasicTypes
open BCHBCDictionary
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHCallTarget
open BCHConstantDefinitions
open BCHDoubleword
open BCHFunctionInfo
open BCHFunctionSummary
open BCHInterfaceDictionary
open BCHLibTypes
open BCHLocation
open BCHMemoryReference
open BCHPreFileIO
open BCHSystemInfo
open BCHXmlUtil

module H = Hashtbl
module TR = CHTraceResult


let geta_fail
      (name: string) (node: xml_element_int) (tag: string): doubleword_int =
  let dw = string_to_doubleword (node#getAttribute tag) in
  if Result.is_ok dw then
    TR.tget_ok dw
  else
    fail_tvalue
      (trerror_record
         (LBLOCK [
              STR "geta:system_info#";
              STR name;
              STR " with tag:";
              STR tag;
              STR " and value:";
              STR (node#getAttribute tag)]))
      dw


let pr_expr x =	if is_random x then STR "??" else xpr_formatter#pr_expr x
let four = int_constant_expr 4

let bcd = BCHBCDictionary.bcdictionary
let id = BCHInterfaceDictionary.interface_dictionary


let btype_equal (t1: btype_t) (t2: btype_t) =
  let i1 = bcd#index_typ t1 in
  let i2 = bcd#index_typ t2 in
  i1 = i2


let offset_equal (o1: int list) (o2: int list): bool =
  if (List.length o1) = (List.length o2) then
    List.fold_left2 (fun acc i1 i2 -> acc && (i1 = i2)) true o1 o2
  else
    false


let compare_btype_x (t1: btype_t) (t2: btype_t): int =
  if btype_equal t1 t2 then
    0
  else
    match (t1, t2) with
    | (TUnknown _, _) -> -1
    | (_, TUnknown _) -> 1
    | _ -> 2


let compare_size_x (s1: int option) (s2: int option): int =
  match (s1, s2) with
  | (None, None) -> 0
  | (None, _) -> -1
  | (_, None) -> 1
  | (Some ss1, Some ss2) when ss1 = ss2 -> 0
  | _ -> 2


let compare_gterm_x (g1: gterm_t) (g2: gterm_t): int =
  match (g1, g2) with
  | (GUnknownValue, GUnknownValue) -> 0
  | (GUnknownValue, _) -> -1
  | (_, GUnknownValue) -> 1
  | _ ->
     let i1 = id#index_gterm g1 in
     let i2 = id#index_gterm g2 in
     if i1 = i2 then 0 else 2


module DoublewordCollections = CHCollections.Make
  (struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
   end)

let get_sorted_kv_list table =
  let lst = ref [] in
  let _ = H.iter (fun k v -> lst := (k,v) :: !lst) table in
  List.sort (fun (k1,_) (k2,_) -> Stdlib.compare k1 k2) !lst


let nsplit (separator:char) (s:string):string list =
  let result = ref [] in
  let len = String.length s in
  let start = ref 0 in
  begin
    while !start < len do
      let s_index = try String.index_from s !start separator with Not_found -> len in
      let substring = String.sub s !start (s_index - !start) in
      begin
	result := substring :: !result ;
	start := s_index + 1
      end
    done;
    List.rev !result
  end


let g_arithmetic_op_to_string op =
  match op with
  | GPlus -> "plus"
  | GMinus -> "minus"
  | GTimes -> "times"
  | GDivide -> "divide"


let string_to_g_arithmetic_op (s:string) =
  match s with
  | "plus" -> GPlus
  | "minus" -> GMinus
  | "times" -> GTimes
  | "divide" -> GDivide
  | _ ->
     raise
       (BCH_failure (LBLOCK [STR "arithmetic g-op not recognized: "; STR s]))


let list_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
  let length = List.length in
  if (length l1) < (length l2) then
    -1
  else if (length l1) > (length l2) then
    1
  else
    List.fold_right2 (fun e1 e2 a -> if a = 0 then (f e1 e2) else a) l1 l2 0


let rec gterm_compare t1 t2 =
  match (t1,t2) with
  | (GConstant n1, GConstant n2) -> n1#compare n2
  | (GConstant _, _) -> -1
  | (_, GConstant _) -> 1
  | (GReturnValue loc1, GReturnValue loc2) -> loc1#compare loc2
  | (GReturnValue _, _) -> -1
  | (_, GReturnValue _) -> 1
  | (GSideeffectValue (loc1,n1), GSideeffectValue (loc2,n2)) ->
    let l1 = loc1#compare loc2 in if l1 = 0 then Stdlib.compare n1 n2 else l1
  | (GSideeffectValue _,_) -> -1
  | (_,GSideeffectValue _) -> 1
  | (GArgValue (a1,i1,o1), GArgValue (a2,i2,o2)) ->
    let l1 = a1#compare a2 in
    if l1 = 0 then
      let l2 = Stdlib.compare i1 i2 in
      if l2 = 0 then
	list_compare o1 o2 Stdlib.compare
      else l2
    else l1
  | (GArgValue _, _) -> -1
  | (_, GArgValue _) -> 1
  | (GArithmeticExpr (op1,gx1,gy1), GArithmeticExpr (op2,gx2,gy2)) ->
    let l1 = Stdlib.compare op1 op2 in
    if l1 = 0 then
      let l2 = gterm_compare gx1 gx2 in
      if l2 = 0 then
	gterm_compare gy1 gy2
      else l2
    else l1
  | (GArithmeticExpr _, _) -> -1
  | (_, GArithmeticExpr _) -> 1
  | _ -> 0


let rec gterm_to_pretty (t:gterm_t) =
  match t with
  | GConstant n -> n#toPretty
  | GReturnValue loc -> LBLOCK [ STR "rv(" ; loc#toPretty ; STR ")" ]
  | GSideeffectValue (loc,n) ->
     LBLOCK  [STR "se("; loc#toPretty; STR ","; STR n; STR ")"]
  | GArgValue (faddr,index,offset) ->
     LBLOCK [
         STR "arg(";
         faddr#toPretty;
         STR ")";
         STR "arg-";
         INT index;
	 STR (String.concat
                "" (List.map (fun i -> "[" ^ (string_of_int i) ^ "]") offset))]
  | GUnknownValue -> STR "?"
  | GArithmeticExpr (op,g1,g2) ->
     LBLOCK [
         gterm_to_pretty g1;
         STR " ";
         STR (g_arithmetic_op_to_string op);
         STR " ";
	 gterm_to_pretty g2]


class gv_reader_t
        (ty:btype_t)
        (size:int option)
        (fp:bool)
        (offset:int list):gv_reader_int =
object (self)

  method get_type = ty
  method get_size = size
  method get_offset = offset
  method is_function_pointer = fp

  method write_xml (node:xml_element_int) =
    begin
      bcd#write_xml_typ node self#get_type;
      (match self#get_size with
       | Some s -> node#setIntAttribute "size" s | _ -> ());
      (if (List.length offset) > 0 then
         node#setAttribute
           "offset"
           (String.concat "," (List.map string_of_int self#get_offset)));
      (if self#is_function_pointer then
         node#setAttribute "fp" "yes")
    end

  method toPretty =
    let pOffset = match offset with
      | [] -> STR ""
      | _ -> STR (String.concat "" (List.map (fun i ->
	"[" ^ (string_of_int i) ^ "]") offset)) in
    let pType =
      if is_unknown_type ty then STR "?" else STR (btype_to_string ty) in
    let pSize = match size with Some s -> INT s  | _ -> STR "?" in
    LBLOCK [ STR "-> (" ; pType ; STR"," ; pSize ; pOffset ; STR ")" ;  NL ]

end


let read_xml_reader (node: xml_element_int): gv_reader_t =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  let ty = bcd#read_xml_typ node in
  let size =
    if has "size" then
      Some (node#getIntAttribute "size")
    else
      None in
  let offset =
    if has "offset" then
      let intlist = node#getAttribute "offset" in
      List.map int_of_string (nsplit ',' intlist)
    else
      [] in
  let isfp = if has "fp" then (get "fp") = "yes" else false in
  new gv_reader_t ty size isfp offset


class gv_writer_t
        (ty:btype_t)
        (size:int option)
        (offset:int list)
        (v:gterm_t):gv_writer_int =
object (self: 'a)

  method get_type = ty
  method get_size = size
  method get_offset = offset
  method get_value = v

  method compare_x (other: 'a): int =
    if not (offset_equal self#get_offset other#get_offset) then
      2
    else if (compare_size_x self#get_size other#get_size) = 2 then
      2
    else if (compare_gterm_x self#get_value other#get_value) = 2 then
      2
    else if (compare_btype_x self#get_type other#get_type) = 2 then
      2
    else
      match (compare_gterm_x self#get_value other#get_value) with
      | -1 -> -1
      | 1 -> 1
      | _ ->
         match (compare_btype_x self#get_type other#get_type) with
         | -1 -> -1
         | 1 -> 1
         | _ -> compare_size_x self#get_size other#get_size


  method write_xml (node:xml_element_int) =
    begin
      bcd#write_xml_typ node self#get_type;
      (match self#get_size with
       | Some s -> node#setIntAttribute "size" s | _ -> ());
      (if (List.length offset) > 0 then
         node#setAttribute
           "offset"
           (String.concat "," (List.map string_of_int self#get_offset)));
      id#write_xml_gterm node v
    end

  method to_report_pretty (pr:gterm_t -> pretty_t) =
    let pOffset = match offset with
      | [] -> STR ""
      | _ ->
         STR (String.concat
                ""
                (List.map (fun i -> "[" ^ (string_of_int i) ^ "]") offset)) in
    let pType =
      if is_unknown_type ty then STR "?" else STR (btype_to_string ty) in
    let pSize = match size with Some s -> INT s  | _ -> STR "?" in
    LBLOCK [STR "<- ("; pType; STR","; pSize; pOffset; STR "): "; pr v; NL]

  method toPretty = self#to_report_pretty gterm_to_pretty
end


let read_xml_writer (node: xml_element_int): gv_writer_t =
  let has = node#hasNamedAttribute in
  let ty = bcd#read_xml_typ node in
  let size =
    if has "size" then
      Some (node#getIntAttribute "size")
    else
      None in
  let offset =
    if has "offset" then
      let intlist = node#getAttribute "offset" in
      List.map int_of_string (nsplit ',' intlist)
    else
      [] in
  let gterm = id#read_xml_gterm node in
  new gv_writer_t ty size offset gterm


class global_variable_t (address:doubleword_int):global_variable_int =
object (self)

  val readers = H.create 5  (* (faddr, iaddr) -> List of readers *)
  val writers = H.create 5  (* (faddr, iaddr) -> List of writers *)
  val preconditions = H.create 5 (* (faddr, iaddr) -> List of preconditions *)

  method add_reader
           ?(ty=t_unknown)
           ?(size=None)
           ?(offset=[])
           ?(fp=false)
           (loc:location_int) =
    let key = (loc#f#to_hex_string, loc#i#to_hex_string) in
    let rec same_offset l1 l2 =
      match (l1,l2)  with
      | ([], []) -> true
      | (h::_, []) -> false
      | ([], h::_) -> false
      | (h1::tl1, h2::tl2) -> h1 = h2 && same_offset tl1 tl2 in
    let entry = if H.mem readers key then H.find readers key else [] in
    let entry =
      if List.exists (fun r -> same_offset r#get_offset offset) entry then
        entry
      else
        (new gv_reader_t ty size fp offset) :: entry in
    H.replace readers key entry

  method add_writer
           ?(ty=t_unknown)
           ?(size=None)
           ?(offset=[])
           (v:gterm_t)
           (loc:location_int) =
    let key = (loc#f#to_hex_string, loc#i#to_hex_string) in
    let entry = if H.mem writers key then H.find writers key else [] in
    let writer = new gv_writer_t ty size offset v in
    let newentry =
      if List.for_all (fun w -> (w#compare_x writer) = 2) entry then
        writer :: entry
      else
        let (_, newentry) =
          List.fold_left (fun (added, acc) w ->
              if (w#compare_x writer) = -1 then
                if added then
                  (true, acc)
                else
                  (true, writer :: acc)
              else
                (added, w :: acc)) (false, []) entry in
        newentry in
    H.replace writers key newentry

  method add_precondition (loc: location_int) (xxp: xxpredicate_t) =
    let key = (loc#f#to_hex_string, loc#i#to_hex_string) in
    let entry =
      if H.mem preconditions key then H.find preconditions key else [] in
    let newentry = xxp :: entry in
    H.replace preconditions key newentry

  method get_address = address

  method get_values =
    H.fold (fun _ ws acc ->
        List.fold_left (fun wacc w ->
            match w#get_value with
            | GUnknownValue -> wacc
            | x -> x :: wacc) acc ws) writers []

  method get_types =
    H.fold (fun _ ws acc ->
        List.fold_left (fun wacc w ->
            match w#get_type with
            | TUnknown _ -> wacc
            | ty when List.exists (fun t -> btype_equal ty t) wacc -> wacc
            | ty -> ty :: wacc) acc ws) writers []

  method is_function_pointer =
    H.fold (fun _ v acc -> acc || List.exists (fun r -> r#is_function_pointer) v)
      readers false

  method private write_xml_readers (node: xml_element_int) =
    let values = H.fold (fun loc rs a -> (loc, rs) :: a) readers [] in
    node#appendChildren
      (List.map (fun ((faddr, iaddr), rs) ->
           let rsnode = xmlElement "rs" in
           begin
             rsnode#setAttribute "f" faddr;
             rsnode#setAttribute "i" iaddr;
             rsnode#appendChildren
               (List.map (fun r ->
                    let rnode = xmlElement "r" in
                    begin
                      r#write_xml rnode;
                      rnode
                    end) rs);
             rsnode
           end) values)

  method private read_xml_readers (node: xml_element_int) =
    List.iter (fun xrs ->
        let faddr = xrs#getAttribute "f" in
        let iaddr = xrs#getAttribute "i" in
        let gvreaders = List.map read_xml_reader (xrs#getTaggedChildren "r") in
        H.add readers (faddr, iaddr) gvreaders) (node#getTaggedChildren "rs")

  method private write_xml_writers (node: xml_element_int) =
    let values = H.fold (fun loc ws a -> (loc, ws) :: a) writers [] in
    node#appendChildren
      (List.map (fun ((faddr, iaddr), ws) ->
           let wsnode = xmlElement "ws" in
           begin
             wsnode#setAttribute "f" faddr;
             wsnode#setAttribute "i" iaddr;
             wsnode#appendChildren
               (List.map (fun w ->
                    let wnode = xmlElement "w" in
                    begin
                      w#write_xml wnode;
                      wnode
                    end) ws);
             wsnode
           end) values)

  method private write_xml_preconditions (node: xml_element_int) =
    let values = H.fold (fun loc pre a -> (loc, pre) :: a) preconditions [] in
    node#appendChildren
      (List.map (fun ((faddr, iaddr), lpre) ->
           let prenode = xmlElement "pre" in
           begin
             prenode#setAttribute "f" faddr;
             prenode#setAttribute "i" iaddr;
             id#write_xml_xxpredicate_list prenode lpre;
             prenode
           end) values)

  method private read_xml_writers (node: xml_element_int) =
    List.iter (fun xws ->
        let faddr = xws#getAttribute "f" in
        let iaddr = xws#getAttribute "i" in
        let gvwriters = List.map read_xml_writer (xws#getTaggedChildren "w") in
        H.add writers (faddr, iaddr) gvwriters) (node#getTaggedChildren "ws")

  method write_xml (node:xml_element_int) =
    begin
      (if H.length readers > 0 then
         let rnode = xmlElement "readers" in
         begin
           self#write_xml_readers rnode;
           node#appendChildren [rnode]
         end);
      (if H.length writers > 0 then
         let wnode = xmlElement "writers" in
         begin
           self#write_xml_writers wnode;
           node#appendChildren [wnode]
         end);
      (if H.length preconditions > 0 then
         let pnode = xmlElement "preconditions" in
         begin
           self#write_xml_preconditions pnode;
           node#appendChildren [pnode]
         end)
    end

  method read_xml (node:xml_element_int) =
    begin
      (if node#hasOneTaggedChild "readers" then
         self#read_xml_readers (node#getTaggedChild "readers"));
      (if node#hasOneTaggedChild "writers" then
         self#read_xml_writers (node#getTaggedChild "writers"))
    end

  method to_report_pretty (pr:gterm_t -> pretty_t) =
    let rs = get_sorted_kv_list readers in
    let ws = get_sorted_kv_list writers in
    LBLOCK [
        STR (string_repeat "~" 80);
        NL;
	pr (GConstant address#to_numerical);
        NL;
	INDENT (3,
                LBLOCK
                  (List.map (fun (_, wl) ->
                       (LBLOCK
                          (List.map (fun w ->
                               LBLOCK [w#to_report_pretty pr; NL]) wl))) ws));
        NL;
	INDENT (3,
                LBLOCK
                  (List.map (fun (_, rl) ->
	               (LBLOCK
                          (List.map (fun r ->
                               LBLOCK [r#toPretty; NL]) rl))) rs));
        NL]

  method toPretty = self#to_report_pretty gterm_to_pretty

end


class global_system_state_t:global_system_state_int =
object (self)

  val global_variables = new DoublewordCollections.table_t

  method initialize =
    match load_global_state_file () with
    | Some node ->
      begin
	self#read_xml node ;
	chlog#add
          "global state"
	  (LBLOCK [
               STR "Loaded ";
               INT global_variables#size;
               STR " from file"])
      end
    | _ ->
      chlog#add "global state" (STR "No file found")

  method private get_gvar (address:doubleword_int) =
    match global_variables#get address with
    | Some gvar -> gvar
    | _ ->
      let gvar = new global_variable_t address in
      begin global_variables#set address gvar ; gvar end

  method add_reader
           ?(ty=t_unknown)
           ?(size=Some 4)
           ?(offset=[])
           ?(fp=false)
           (gaddr:doubleword_int)
           (loc:location_int) =
    (self#get_gvar gaddr)#add_reader ~ty ~size ~offset ~fp loc

  method add_writer
           ?(ty=t_unknown)
           ?(size=Some 4)
           ?(offset=[])
           (v:gterm_t)
           (gaddr:doubleword_int)
           (loc:location_int) =
    (self#get_gvar gaddr)#add_writer ~ty ~size ~offset v loc

  method add_precondition
           (gaddr: doubleword_int) (loc: location_int) (xxp: xxpredicate_t) =
    (self#get_gvar gaddr)#add_precondition loc xxp

  method get_values (address:doubleword_int) = (self#get_gvar address)#get_values

  method get_types (address: doubleword_int) = (self#get_gvar address)#get_types

  method get_destinations (gterm:gterm_t) =
    global_variables#fold (fun acc gvaddr gv ->
      if List.exists (fun v -> (gterm_compare v gterm) = 0) gv#get_values then
	gvaddr :: acc
      else
	acc) []

  method write_xml (node:xml_element_int) =
    node#appendChildren (List.map (fun (dw, v) ->
      let vNode = xmlElement "gvar" in
      begin
	vNode#setAttribute "a" dw#to_hex_string;
	(if has_symbolic_address_name dw then
	    vNode#setAttribute "name" (get_symbolic_address_name dw));
	v#write_xml vNode;
	vNode
      end) global_variables#listOfPairs)

  method read_xml (node:xml_element_int) =
   List.iter (fun n ->
      let a = geta_fail "global_system_state#read_xml" n "a" in
      let gv = new global_variable_t a in
      begin
	gv#read_xml n;
	global_variables#set a gv
      end) (node#getTaggedChildren "gvar")

  method to_report_pretty (pr:gterm_t -> pretty_t) =
    LBLOCK (List.map (fun v -> v#to_report_pretty pr)
	      (List.rev global_variables#listOfValues))

  method toPretty = self#to_report_pretty gterm_to_pretty

end


let global_system_state = new global_system_state_t
