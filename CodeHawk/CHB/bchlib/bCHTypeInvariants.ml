(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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
open CHCommon
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHUtil
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprXml

(* bchcil *)
open BCHCBasicTypes

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHTypeInvDictionary
open BCHUtilities
open BCHVariableType
open BCHXmlUtil

module H = Hashtbl


let btype_compare = BCHBCUtil.typ_compare


let maxlen = 20
let pr_expr = xpr_formatter#pr_expr


let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

let list_compare = BCHUtilities.list_compare

let type_invariant_fact_compare f1 f2 =
  match (f1, f2) with
  | (VarTypeFact (v1, t1, lst1), VarTypeFact (v2, t2, lst2)) ->
    let l1 = v1#compare v2 in 
    if l1 = 0 then 
      let l2 = btype_compare t1 t2 in 
      if l2 = 0 then
	list_compare lst1 lst2 Stdlib.compare
      else l2
    else l1
  | (VarTypeFact _, _) -> -1
  | (_, VarTypeFact _) -> 1
  | (ConstTypeFact (c1, t1), ConstTypeFact (c2, t2)) ->
    let l1 = c1#compare c2 in if l1 = 0 then btype_compare t1 t2 else l1
  | (ConstTypeFact _, _) -> -1
  | (_, ConstTypeFact _) -> 1
  | (XprTypeFact (x1, t1), XprTypeFact (x2, t2)) ->
     let l1 = syntactic_comparison x1 x2 in
     if l1 = 0 then btype_compare t1 t2 else l1


let type_invariant_fact_to_pretty (f: type_invariant_fact_t) =
  match f with
  | VarTypeFact (v, t, lst) ->
     let sInfo =
       match lst with
       | [] -> STR ""
       | h::tl ->
          LBLOCK [
              STR " (";
              STR h;
              STR ":";
	      pretty_print_list tl (fun s -> STR s) "" "." "";
              STR ")"] in
    LBLOCK [STR v#getName#getBaseName; STR ":"; btype_to_pretty t; sInfo]
  | ConstTypeFact (n, t) ->
     LBLOCK [n#toPretty; STR ":"; btype_to_pretty t]
  | XprTypeFact (x,t) ->
     LBLOCK [pr_expr x; STR ":"; btype_to_pretty t]



class type_invariant_t
        ~(tinvd:tinvdictionary_int)
        ~(index:int)
        ~(fact:type_invariant_fact_t): type_invariant_int =
object (self:'a)

  val tinvd = tinvd

  method index = index

  method compare (other:'a) = Stdlib.compare self#index other#index

  method get_fact = fact

  method get_variables = 
    match self#get_fact with VarTypeFact (v,_,_) -> [ v ] | _ -> []

  method write_xml (node:xml_element_int) =
    begin
      tinvd#write_xml_type_invariant_fact node self#get_fact;
      node#setIntAttribute "id" index
    end

  method toPretty = type_invariant_fact_to_pretty self#get_fact

end


let read_xml_type_invariant
      (tinvd:tinvdictionary_int) (node:xml_element_int):type_invariant_int =
  let index = node#getIntAttribute "id" in
  let fact = tinvd#read_xml_type_invariant_fact node in
  new type_invariant_t ~tinvd ~index ~fact


module TypeInvariantFactCollections = CHCollections.Make
  (struct
    type t = type_invariant_fact_t
    let compare = type_invariant_fact_compare
    let toPretty = type_invariant_fact_to_pretty
   end)


module TypeInvariantCollections = CHCollections.Make
  (struct
    type t = type_invariant_int
    let compare f1 f2 = f1#compare f2
    let toPretty f = f#toPretty
   end)


class location_type_invariant_t
        (tinvd:tinvdictionary_int) (iaddr:string):location_type_invariant_int =
object (self)

  val tinvd = tinvd
  val table = H.create 3
  val facts = H.create 3

  method add_fact (fact:type_invariant_fact_t) =
    let index = tinvd#index_type_invariant_fact fact in
    if H.mem facts index then () else
      let inv = new type_invariant_t ~tinvd ~index ~fact in
      begin
        H.add facts index inv ;
      end

  method get_var_facts (v:variable_t) =
    List.filter (fun f -> List.exists (fun fv -> fv#equal v) f#get_variables)
    (H.fold (fun _ v a -> v::a) facts [])

  method get_facts = H.fold (fun _ v a -> v::a) facts []

  method get_count = H.length facts

  method has_facts = (H.length facts) > 0

  method toPretty = 
    pretty_print_list
      self#get_facts (fun f -> LBLOCK [f#toPretty; NL]) "" "" ""

end
  
  
let make_string l = String.concat "," (List.map string_of_int l)


let rec make_strings l result =
  let llen = List.length l in
  if llen <= maxlen then
    List.rev ((make_string l) :: result)
  else
    let (lpre,lsuf) = list_split maxlen l in
    (make_strings lsuf ((make_string lpre) :: result))
      
      
class type_invariant_io_t
        (optnode:xml_element_int option)
        (tinvd:tinvdictionary_int)
        (fname:string): type_invariant_io_int =
object (self)

  val tinvd = tinvd
  val finvariants =
    new TypeInvariantCollections.set_t   (* location independent types *)
  val invariants = new StringCollections.table_t

  initializer
    match optnode with
    | Some node -> self#read_xml node
    | _ -> ()

  method private add (iaddr:string) (fact:type_invariant_fact_t) =
    (self#get_location_type_invariant iaddr)#add_fact fact

  method private add_function_fact (fact:type_invariant_fact_t) = ()

  method add_var_fact
           (iaddr:string) (v:variable_t) ?(structinfo=[]) (ty:btype_t) =
    self#add iaddr (VarTypeFact (v, ty, structinfo))

  method add_function_var_fact (v:variable_t) ?(structinfo=[]) (ty:btype_t) =
    self#add_function_fact (VarTypeFact (v,ty,structinfo))

  method add_const_fact (iaddr:string) (c:numerical_t) (ty:btype_t) =
    self#add iaddr (ConstTypeFact (c, ty))

  method add_xpr_fact (iaddr:string) (x:xpr_t) (ty:btype_t) =
    self#add iaddr (XprTypeFact (x, ty))

  method get_location_type_invariant (iaddr:string) =
    match invariants#get iaddr with
    | Some locInv -> locInv
    | _ ->
      let locInv = new location_type_invariant_t tinvd iaddr in
      begin invariants#set iaddr locInv; locInv end

  method get_facts = [] (* table#values *)

  method get_function_facts = finvariants#toList

  method get_variable_facts (iaddr:string) (v:variable_t) = []

  method get_location_facts =
    List.map (fun (k,v) -> (k, v#get_facts)) invariants#listOfPairs

  method get_table_size = 0  (* List.length table#values *)

  method get_invariant_count =
    invariants#fold (fun acc _ inv -> acc + inv#get_count) 0

  method private write_xml_facts
                   (node:xml_element_int) 
                   (locinv:location_type_invariant_int) =
    let findices = List.map (fun f -> f#index) locinv#get_facts in
    let findices = List.sort Stdlib.compare findices in
    node#appendChildren
      (List.map (fun s ->
           let iNode = xmlElement "tinvs" in
           begin
             iNode#setAttribute "indices" s;
             iNode
           end) (make_strings findices []))

  method private write_xml_finvariants (node:xml_element_int) =
    let findices = List.map (fun f -> f#index) finvariants#toList in
    match findices with
    | [] -> ()
    | _ ->
      let findices = List.sort Stdlib.compare findices in
      node#appendChildren
        (List.map (fun s ->
	     let iNode = xmlElement "tinvs" in
	     begin
               iNode#setAttribute "indices" s;
               iNode
             end) (make_strings findices []))
	
  method write_xml (node:xml_element_int) = ()

  method private read_xml_facts (node:xml_element_int) (iaddr:string)  = ()

  method private read_xml_locations (node:xml_element_int) =
    List.iter (fun n ->
      let iaddr = n#getAttribute "a" in
      self#read_xml_facts n iaddr) (node#getTaggedChildren "loc")

  method read_xml (node:xml_element_int) = ()

  method toPretty =
    let ppf = ref [] in
    let ppl = ref [] in
    begin
      finvariants#iter
        (fun v ->  ppf := (LBLOCK [INDENT(3, v#toPretty); NL]) :: !ppf);
      invariants#iter
        (fun k v ->
	  match v#get_facts with
	  | [] -> ()
	  | _ ->
             ppl := LBLOCK [STR k; NL; INDENT (3, v#toPretty); NL] :: !ppl);
      LBLOCK [
          STR "Type invariants for ";
          STR fname;
	  STR " valid at all locations: ";
          NL;
	  LBLOCK !ppf;
          NL;
          NL;
	  STR "Type invariants per location: ";
          NL;
          LBLOCK (List.rev !ppl)]
    end

end

let mk_type_invariant_io
      (optnode:xml_element_int option) (vard:vardictionary_int) =
  let tinvd = mk_tinvdictionary vard in
  new type_invariant_io_t optnode tinvd
