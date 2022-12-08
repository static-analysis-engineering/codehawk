(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchcil *)
open BCHBCDictionary
open BCHBCUtil
open BCHCBasicTypes

(* bchlib*)
open BCHBasicTypes
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
open BCHVariableType
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


class gv_writer_t
        (ty:btype_t)
        (size:int option)
        (offset:int list)
        (v:gterm_t):gv_writer_int =
object (self)

  method get_type = ty
  method get_size = size
  method get_offset = offset
  method get_value = v

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


class global_variable_t (address:doubleword_int):global_variable_int =
object (self)
  
  val readers = H.create 5  (* (faddr, iaddr) -> List of readers *)
  val writers = H.create 5  (* (faddr, iaddr) -> List of writers *)
    
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
    H.replace writers key (new gv_writer_t ty size offset v)
      
  method get_address = address
    
  method get_values =
    H.fold (fun _ v acc ->
      match v#get_value with GUnknownValue -> acc | x -> x :: acc) writers []

  method get_types =
    H.fold (fun _ v acc ->
      match v#get_type with
      | TUnknown _ -> acc
      | ty when List.exists (fun t -> btype_equal ty t) acc -> acc
      | ty -> ty :: acc) writers []

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

  method private write_xml_writers (node: xml_element_int) =
    let values = H.fold (fun loc writer a -> (loc, writer) :: a) writers [] in
    node#appendChildren
      (List.map (fun ((faddr, iaddr), writer) ->
           let wnode = xmlElement "w" in
           begin
             wnode#setAttribute "f" faddr;
             wnode#setAttribute "i" iaddr;
             writer#write_xml wnode;
             wnode
           end) values)

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
         end)
    end

  method read_xml (node:xml_element_int) = ()

  method to_report_pretty (pr:gterm_t -> pretty_t) =
    let rs = get_sorted_kv_list readers in
    let ws = get_sorted_kv_list writers in
    LBLOCK [
        STR (string_repeat "~" 80);
        NL;
	pr (GConstant address#to_numerical);
        NL;
	INDENT (3, LBLOCK (List.map (fun (_,w) -> w#to_report_pretty pr) ws));
        NL;
	INDENT (3,
                LBLOCK
                  (List.map (fun (_,rl) ->
	               (LBLOCK
                          (List.map (fun r ->
                               LBLOCK [ r#toPretty ; NL ]) rl))) rs));
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
	vNode#setAttribute "a" dw#to_hex_string ; 
	(if has_symbolic_address_name dw then 
	    vNode#setAttribute "name" (get_symbolic_address_name dw)) ;
	v#write_xml vNode ; 
	vNode 
      end) global_variables#listOfPairs)

  method read_xml (node:xml_element_int) =
   List.iter (fun n ->
      let a = geta_fail "global_system_state#read_xml" n "a" in
      let gv = new global_variable_t a in
      begin
	gv#read_xml n ;
	global_variables#set a gv
      end) (node#getTaggedChildren "gvar")
     
  method to_report_pretty (pr:gterm_t -> pretty_t) =
    LBLOCK (List.map (fun v -> v#to_report_pretty pr) 
	      (List.rev global_variables#listOfValues))

  method toPretty = self#to_report_pretty gterm_to_pretty
      
end


let global_system_state = new global_system_state_t
  
