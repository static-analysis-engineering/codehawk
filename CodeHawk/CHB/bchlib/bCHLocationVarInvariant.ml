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
open CHLanguage
open CHPretty

(* chutil *)
open CHUtils
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHVarInvDictionary


module H = Hashtbl


let vardefuse_to_pretty ((v, sl): vardefuse_t) =
  LBLOCK [v#toPretty; pretty_print_list sl (fun s -> s#toPretty) " [" ", " "]"]


let var_invariant_fact_to_pretty (f: var_invariant_fact_t) =
  match f with
  | ReachingDef vardefuse ->
     LBLOCK [STR "reaching-def: "; vardefuse_to_pretty vardefuse]
  | FlagReachingDef vardefuse ->
     LBLOCK [STR "flag-reaching-def: "; vardefuse_to_pretty vardefuse]
  | DefUse vardefuse ->
     LBLOCK [STR "def-use: "; vardefuse_to_pretty vardefuse]
  | DefUseHigh vardefuse ->
     LBLOCK [STR "def-use-high: "; vardefuse_to_pretty vardefuse]


class var_invariant_t
        ~(varinvd: varinvdictionary_int)
        ~(index: int)
        ~(fact: var_invariant_fact_t): var_invariant_int =
object (self: 'a)

  val varinvd = varinvd
  val index = index
  val fact = fact

  method index = index

  method compare (other: 'a) =
    Stdlib.compare self#index other#index

  method get_fact = fact

  method is_reaching_def: bool =
    match fact with
    | ReachingDef _ -> true
    | _ -> false

  method is_flag_reaching_def: bool =
    match fact with
    | FlagReachingDef _ -> true
    | _ -> false

  method is_def_use: bool =
    match fact with
    | DefUse _ -> true
    | _ -> false

  method is_def_use_high: bool =
    match fact with
    | DefUseHigh _ -> true
    | _ -> false

  method get_variable: variable_t =
    match fact with
    | ReachingDef (v, _)
      | FlagReachingDef (v, _)
      | DefUse (v, _)
      | DefUseHigh (v, _) -> v

  method write_xml (node: xml_element_int) =
    begin
      varinvd#write_xml_var_invariant_fact node self#get_fact;
      node#setIntAttribute "index" index
    end

  method toPretty = var_invariant_fact_to_pretty fact

end

                      
let read_xml_var_invariant
      (varinvd: varinvdictionary_int)
      (node: xml_element_int): var_invariant_int =
  let index = node#getIntAttribute "index" in
  let fact = varinvd#read_xml_var_invariant_fact node in
  new var_invariant_t ~varinvd ~index ~fact


class location_var_invariant_t
        (varinvd: varinvdictionary_int)
        (iaddr: string): location_var_invariant_int =
object (self)

  val varinvd = varinvd
  val table = H.create 5  (* facts indexed by variable seq number *)
  val facts = H.create 3  (* var_invariant_fact index -> var_invariant_int *)

  method reset =
    begin
      H.clear table;
      H.clear facts;
    end

  method add_fact (fact: var_invariant_fact_t) =
    let index = varinvd#index_var_invariant_fact fact in
    if H.mem facts index then
      ()
    else
      let inv = new var_invariant_t ~varinvd ~index ~fact in
      let varindex = inv#get_variable#getName#getSeqNumber in
      let entry = if H.mem table varindex then H.find table varindex else [] in
      begin
        H.add facts index inv;
        H.replace table varindex (fact :: entry)
      end

  method get_var_facts (var: variable_t): var_invariant_int list =
    List.filter (fun f -> f#get_variable#equal var) self#get_facts

  method get_var_reaching_defs (var: variable_t): var_invariant_int list =
    List.filter (fun f -> f#is_reaching_def) (self#get_var_facts var)

  method get_var_flag_reaching_defs (var: variable_t): var_invariant_int list =
    List.filter (fun f -> f#is_flag_reaching_def) (self#get_var_facts var)

  method get_var_def_uses (var: variable_t): var_invariant_int list =
    List.filter (fun f -> f#is_def_use) (self#get_var_facts var)

  method get_var_def_uses_high (var: variable_t): var_invariant_int list =
    List.filter (fun f -> f#is_def_use_high) (self#get_var_facts var)

  method get_facts: var_invariant_int list =
    H.fold (fun _ v a -> v::a) facts []

  method get_count: int =
    H.length facts

  method has_facts: bool = self#get_count > 0

  method write_xml (node: xml_element_int) =
    let invs = List.sort Stdlib.compare (H.fold (fun k _ a -> k::a) facts []) in
    let attr = String.concat "," (List.map string_of_int invs) in
    node#setAttribute "ivfacts" attr

  method read_xml (node: xml_element_int) =
    if node#hasNamedAttribute "ivfacts" then
      let attr =
        try
          List.map
            int_of_string
            (CHUtil.string_nsplit ',' (node#getAttribute "ivfacts"))
        with
        | Failure _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "location_var_invariant:read_xml: int_of_string on ";
                     STR (node#getAttribute "ivfacts")])) in
      let facts = List.map varinvd#get_var_invariant_fact attr in
      List.iter self#add_fact facts

  method toPretty =
    LBLOCK (List.map (fun inv -> LBLOCK [inv#toPretty; NL]) self#get_facts)

end
    

class var_invariant_io_t
        (optnode: xml_element_int option)
        (varinvd: varinvdictionary_int)
        (fname: string): var_invariant_io_int =
object (self)

  val varinvd = varinvd
  val invariants = new StringCollections.table_t

  initializer
    match optnode with
    | Some node -> self#read_xml node
    | _ -> ()

  method private add (iaddr: string) (fact: var_invariant_fact_t) =
    (self#get_location_var_invariant iaddr)#add_fact fact

  method add_reaching_def
           (iaddr: string) (var: variable_t) (locs: symbol_t list) =
    self#add iaddr (ReachingDef (var, locs))

  method add_flag_reaching_def
           (iaddr: string) (var: variable_t) (locs: symbol_t list) =
    self#add iaddr (FlagReachingDef (var, locs))

  method add_def_use
           (iaddr: string) (var: variable_t) (locs: symbol_t list) =
    self#add iaddr (DefUse (var, locs))

  method add_def_use_high
           (iaddr: string) (var: variable_t) (locs: symbol_t list) =
    self#add iaddr (DefUseHigh (var, locs))

  method get_location_var_invariant (iaddr: string) =
    match invariants#get iaddr with
    | Some locInv -> locInv
    | _ ->
       let locInv = new location_var_invariant_t varinvd iaddr in
       begin
         invariants#set iaddr locInv;
         locInv
       end

  method write_xml (node: xml_element_int) =
    let dNode = xmlElement "varinv-dictionary" in
    let lNode = xmlElement "locations" in
    begin
      lNode#appendChildren
        (List.map (fun (s, locinv) ->
             let locNode = xmlElement "loc" in
             begin
               locNode#setAttribute "a" s;
               locinv#write_xml locNode;
               locNode
             end) invariants#listOfPairs);
      varinvd#write_xml dNode;
      node#appendChildren [lNode; dNode]
    end

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      varinvd#read_xml (getc "varinv-dictionary");
      List.iter (fun n ->
          let iaddr = n#getAttribute "a" in
          let locinv = self#get_location_var_invariant iaddr in
          locinv#read_xml n) ((getc "locations")#getTaggedChildren "loc")
    end

  method toPretty =
    let pp = ref [] in
    begin
      invariants#iter (fun k v ->
          pp := LBLOCK [STR k; NL; INDENT (3, v#toPretty); NL] :: !pp);
      LBLOCK [STR fname; STR ": "; NL; LBLOCK (List.rev !pp)]
    end

end


let mk_var_invariant_io
      (optnode: xml_element_int option) (vard: vardictionary_int) =
  let varinvd = mk_varinvdictionary vard in
  new var_invariant_io_t optnode varinvd
