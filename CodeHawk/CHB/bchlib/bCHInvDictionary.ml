(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHIndexTable
open CHLogger
open CHXmlDocument

(* xprlib *)
open XprDictionary

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHSumTypeSerializer

let bd = BCHDictionary.bdictionary

let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [ STR "Type " ; STR name ; STR " tag: " ; STR tag ;
             STR " not recognized. Accepted tags: " ;
             pretty_print_list accepted (fun s -> STR s) "" ", " "" ] in
  begin
    ch_error_log#add "serialization tag" msg ;
    raise (BCH_failure msg)
  end

class invdictionary_t (vard:vardictionary_int):invdictionary_int =
object (self)

  val vard = vard
  val non_relational_value_table = mk_index_table "non-relational-value-table"
  val linear_equality_table = mk_index_table "linear-equality-table"
  val invariant_fact_table = mk_index_table "invariant-fact-table"
  val invlist_table = mk_index_table "invariant-list-table"
  val mutable tables = []

  initializer
    tables <- [
      non_relational_value_table;
      linear_equality_table;
      invariant_fact_table;
      invlist_table
    ]

  method xd = vard#xd

  method index_non_relational_value (v:non_relational_value_t) =
    let index_optnum n = match n with
      | Some i -> self#xd#index_numerical i
      | _ -> (-1) in
    let tags = [ non_relational_value_mcts#ts v ] in
    let key = match v with
      | FSymbolicExpr x -> (tags,[ self#xd#index_xpr x ])
      | FIntervalValue (n1,n2) -> (tags, [ index_optnum n1; index_optnum n2 ])
      | FBaseOffsetValue (x,n1,n2,b) ->
         let args = [ self#xd#index_symbol x; index_optnum n1; index_optnum n2 ;
                      if b then 1 else 0 ] in
         (tags,args) in
    non_relational_value_table#add key

  method get_non_relational_value (index:int) =
    let name = "non_relational_value" in
    let (tags,args) = non_relational_value_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let get_optnum i = if i = (-1) then None else Some (self#xd#get_numerical i) in
    match (t 0) with
    | "sx" -> FSymbolicExpr (vard#xd#get_xpr (a 0))
    | "iv" -> FIntervalValue (get_optnum (a 0), get_optnum (a 1))
    | "bv" -> FBaseOffsetValue
                (self#xd#get_symbol (a 0),
                 get_optnum (a 1), get_optnum (a 2), (a 3) = 1)
    | s -> raise_tag_error name s non_relational_value_mcts#tags

  method private index_linear_equality (e:linear_equality_t) =
    let tags = e.leq_constant#toString ::
                 (List.map (fun (n,_) -> n#toString) e.leq_factors) in
    let args = List.map (fun (_,v) -> self#xd#index_variable v) e.leq_factors in
    linear_equality_table#add (tags,args)

  method private get_linear_equality (index:int) =
    let (tags,args) = linear_equality_table#retrieve index in
    let t = t "linear_equality" tags in
    let coeffs = List.map mkNumericalFromString (List.tl tags) in
    let vars = List.map self#xd#get_variable args in
    { leq_factors = List.map2 (fun c v -> (c,v)) coeffs vars ;
      leq_constant = mkNumericalFromString (t 0) }
                  
  method index_invariant_fact (f:invariant_fact_t) =
    let tags = [ invariant_fact_mcts#ts f ] in
    let key =
      match f with
      | Unreachable d -> (tags @ [ d ],[])
      | NonRelationalFact (v,nrv) ->
         (tags, [ self#xd#index_variable v ; self#index_non_relational_value nrv ])
      | RelationalFact x -> (tags, [ self#index_linear_equality x ])
      | InitialVarEquality (v,iv) ->
         (tags, [ self#xd#index_variable v ; self#xd#index_variable iv ])
      | InitialVarDisEquality (v,iv) ->
         (tags, [ self#xd#index_variable v ; self#xd#index_variable iv ])
      | TestVarEquality (v,tv,iaddr1,iaddr2) -> 
         (tags @ [ iaddr1 ; iaddr2 ],
          [ self#xd#index_variable v ; self#xd#index_variable tv ]) in
    invariant_fact_table#add key

  method get_invariant_fact (index:int) =
    let name = "invariant_fact" in
    let (tags,args) = invariant_fact_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "u" -> Unreachable (t 1)
    | "n" -> NonRelationalFact
               (self#xd#get_variable (a 0), self#get_non_relational_value (a 1))
    | "r" -> RelationalFact (self#get_linear_equality (a 0))
    | "ie" -> InitialVarEquality
                (self#xd#get_variable (a 0), self#xd#get_variable (a 1))
    | "id" -> InitialVarDisEquality
                (self#xd#get_variable (a 0), self#xd#get_variable (a 1))
    | "te" -> TestVarEquality
                (self#xd#get_variable (a 0), self#xd#get_variable (a 1),
                 t 1, t 2)
    | s -> raise_tag_error name s invariant_fact_mcts#tags

  method write_xml_non_relational_value
           ?(tag="inrv") (node:xml_element_int) (nrv:non_relational_value_t) =
    node#setIntAttribute tag (self#index_non_relational_value nrv)

  method read_xml_non_relational_value
           ?(tag="inrv") (node:xml_element_int):non_relational_value_t =
    self#get_non_relational_value (node#getIntAttribute tag)

  method write_xml_invariant_fact
           ?(tag="iif") (node:xml_element_int) (f:invariant_fact_t) =
    node#setIntAttribute tag (self#index_invariant_fact f)

  method read_xml_invariant_fact
           ?(tag="iif") (node:xml_element_int):invariant_fact_t =
    self#get_invariant_fact (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map (fun t ->
           let tnode = xmlElement t#get_name in
           begin t#write_xml tnode ; tnode end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK (List.map (fun t ->
                LBLOCK [ STR t#get_name ; STR ": " ; INT t#size ; NL ]) tables)


end

let mk_invdictionary = new invdictionary_t
