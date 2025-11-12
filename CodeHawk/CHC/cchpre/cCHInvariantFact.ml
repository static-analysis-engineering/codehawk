(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHPEPRTypes
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes

(* cchlib *)
open CCHLibTypes
open CCHUtilities

(* cchpre *)
open CCHInvDictionary
open CCHPreSumTypeSerializer
open CCHPreTypes

module H = Hashtbl


module ProgramContextCollections =
  CHCollections.Make
    (struct
      type t = program_context_int
      let compare c1 c2 = c1#compare c2
      let toPretty c = c#toPretty
    end)


let ccontexts = CCHContext.ccontexts

let pr_expr = xpr_formatter#pr_expr
let xpr_compare = syntactic_comparison

let pepr_domain = "pepr"
let intervals_domain = "intervals"
let valueset_domain = "valuesets"
let linear_equalities_domain = "linear equalities"
let symbolic_sets_domain = "symbolic sets"
let sym_pointersets_domain = "sym_pointersets"
let sym_initialized_domain = "sym_initialized"


let get_regions (syms:symbol_t list) =
  List.filter (fun s -> not (s#getBaseName = "pres#")) syms


let list_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
  let length = List.length in
  if (length l1) < (length l2) then
    -1
  else if (length l1) > (length l2) then
    1
  else
    List.fold_right2 (fun e1 e2 a -> if a = 0 then (f e1 e2) else a) l1 l2 0


let domain_of_invariant (nrv:non_relational_value_t) =
  match nrv with
  | FSymbolicExpr _ -> "linear equalities"
  | FSymbolicBound _ -> "pepr"
  | FIntervalValue _ -> "intervals"
  | FBaseOffsetValue _ -> "value sets"
  | FInitializedSet _ -> "initialization sets"
  | FRegionSet _ -> "region sets"
  | FPolicyStateSet _ -> "state sets"


let slist_compare lst1 lst2 =
  list_compare lst1 lst2 (fun s1 s2 -> s1#compare s2)


let lst_compare x1 x2 f =
  if (List.length x1) < (List.length x2) then
    -1
  else if (List.length x1) > (List.length x2) then
    1
  else List.fold_left2 (fun acc x x' -> if acc = 0 then f x x' else acc) 0 x1 x2


let xpr_list_compare l1 l2 = lst_compare l1 l2 xpr_compare

let xpr_list_list_compare l1 l2 = lst_compare l1 l2 xpr_list_compare


let non_relational_value_compare v1 v2 =
  let opt_numerical_compare i1 i2
    = match (i1, i2) with
    | (None, None) -> 0
    | (Some _, None) -> -1
    | (None, Some _) -> 1
    | (Some j1, Some j2) -> j1#compare j2 in
  match (v1, v2)  with
  | (FSymbolicExpr x1, FSymbolicExpr x2) -> xpr_compare x1 x2
  | (FSymbolicExpr _, _) -> -1
  | (_, FSymbolicExpr _) -> 1
  | (FSymbolicBound (bt1, x1), FSymbolicBound (bt2, x2)) ->
     let l0 = Stdlib.compare bt1 bt2 in
     if l0 = 0 then xpr_list_list_compare x1 x2 else l0
  | (FSymbolicBound _, _) -> -1
  | (_, FSymbolicBound _) -> 1
  | (FIntervalValue (lb1, ub1),FIntervalValue (lb2, ub2)) ->
    let l0 = opt_numerical_compare lb1 lb2 in
    if l0 = 0 then opt_numerical_compare ub1 ub2 else l0
  | (FIntervalValue _, _) -> -1
  | (_, FIntervalValue _) -> 1
  | (FBaseOffsetValue (_, b1, lb1, ub1, _),
     FBaseOffsetValue (_, b2, lb2, ub2, _)) ->
    let l0 = xpr_compare b1 b2 in
    if l0 = 0 then
      let l1 = opt_numerical_compare lb1 lb2 in
      if l1 = 0 then opt_numerical_compare ub1 ub2 else l1
    else l0
  | (FBaseOffsetValue _, _) -> -1
  | (_, FBaseOffsetValue _) -> 1
  | (FInitializedSet lst1, FInitializedSet lst2) ->
     let lenc = Stdlib.compare (List.length lst1) (List.length lst2) in
     if lenc = 0 then slist_compare lst1 lst2 else lenc
  | (FInitializedSet _, _) -> -1
  | (_, FInitializedSet _) -> 1
  | (FRegionSet lst1, FRegionSet lst2) -> slist_compare lst1 lst2
  | (FRegionSet _, _) -> -1
  | (_, FRegionSet _) -> 1
  | (FPolicyStateSet lst1, FPolicyStateSet lst2) -> slist_compare lst1 lst2


let xll_to_pretty (xll:xpr_t list list) =
    let xl_to_pretty l = pretty_print_list l pr_expr "[" " && " "]" in
    pretty_print_list xll xl_to_pretty "[" " || " "]"


let non_relational_value_to_pretty v =
  match v with
  | FSymbolicExpr v -> LBLOCK [STR "("; pr_expr v; STR ")"]
  | FSymbolicBound (bt,xll) ->
     LBLOCK [
         STR (bound_type_mfts#ts bt); STR ":[";
         xll_to_pretty xll]
  | FIntervalValue (lb,ub) ->
     LBLOCK [
         STR "[";
	 (match lb with Some v -> v#toPretty | _ -> STR "-oo");
	 STR "; ";
	 (match ub with Some v -> v#toPretty | _ -> STR "oo"); STR "]"]
  | FBaseOffsetValue (a,b,lb,ub,canbenull) ->
     LBLOCK [
         STR "(";
         pr_expr b;
         STR ")#";
	 STR (match a with Heap -> "H" | Stack -> "S" | External -> "F");
	 (match (lb,ub) with
	  | (None,None) -> STR "[?]"
	  | (Some lb,None) -> LBLOCK [STR "["; lb#toPretty; STR "; oo]"]
	  | (None,Some ub) -> LBLOCK [STR "[-oo; "; ub#toPretty; STR "]"]
	  | (Some lb, Some ub) ->
             LBLOCK [
                 STR "[";
                 lb#toPretty;
                 STR ";";
		 ub#toPretty;
                 STR "]"]);
	     (if canbenull then STR "" else STR " (not-null)")]
  | FInitializedSet lst ->
     pretty_print_list lst (fun s -> s#toPretty) "{" "," "}"
  | FRegionSet lst ->
     pretty_print_list lst (fun s -> s#toPretty) "R#{" "," "}"
  | FPolicyStateSet lst ->
     pretty_print_list lst (fun s -> s#toPretty) "PS#{" "," "}"


let invariant_fact_compare f1 f2 =
  match (f1,f2) with
  | (Unreachable d1,Unreachable d2) -> Stdlib.compare d1 d2
  | (Unreachable _,_) -> -1
  | (_,Unreachable _) -> 1
  | (NonRelationalFact (p1,v1),NonRelationalFact (p2,v2)) ->
    let r0 = p1#compare p2 in
    if r0 = 0 then non_relational_value_compare v1 v2 else r0
  | (NonRelationalFact _, _) -> -1
  | (_, NonRelationalFact _) -> 1
  | (ParameterConstraint x1, ParameterConstraint x2) -> xpr_compare x1 x2


let invariant_fact_to_pretty f =
  match f with
  | Unreachable s -> LBLOCK [STR "unreachable("; STR s; STR ")"]
  | NonRelationalFact (v,nrv) ->
     LBLOCK [v#toPretty; STR " = "; non_relational_value_to_pretty nrv]
  | ParameterConstraint x -> LBLOCK [pr_expr x]


let non_relational_fact_to_pretty f =
  match f with
  | Unreachable s -> LBLOCK [STR "unreachable("; STR s; STR ")"]
  | NonRelationalFact (_,nrv) -> non_relational_value_to_pretty nrv
  | ParameterConstraint x -> pr_expr x


let is_smaller_nrv (f1:non_relational_value_t) (f2:non_relational_value_t) =
  let is_smaller_bound b1 b2 =
    match (b1,b2) with
    | (Some x1,Some x2) -> x1#lt x2
    | (Some _,_) -> true
    | _ -> false in
  let is_larger_bound b1 b2 =
    match (b1,b2) with
    | (Some x1,Some x2) -> x1#gt x2
    | (Some _,_) -> true
    | _ -> false in
  let is_subset s1 s2 =
    let set1 = new SymbolCollections.set_t in
    let set2 = new SymbolCollections.set_t in
    let _ = set1#addList s1 in
    let _ = set2#addList s2 in
    set1#subset set2 in
  match (f1,f2) with
  | (FIntervalValue (lb1,ub1), FIntervalValue (lb2,ub2)) ->
     is_larger_bound lb1 lb2 || is_smaller_bound ub1 ub2
  | (FRegionSet s1, FRegionSet s2) -> is_subset s1 s2
  | (FPolicyStateSet s1, FPolicyStateSet s2) -> is_subset s1 s2
  | _ ->
    begin
      ch_error_log#add
        "invariant comparison"
	(LBLOCK [
             STR "Invariant facts are not intervals: ";
	     non_relational_value_to_pretty f1;
             STR " and ";
	     non_relational_value_to_pretty f2]);
      raise
        (CCHFailure
	   (LBLOCK [
                STR "Invariant facts are not intervals: ";
		non_relational_value_to_pretty f1;
                STR " and ";
		non_relational_value_to_pretty f2]))
    end


class invariant_t
        ~(invd:invdictionary_int)
        ~(index:int)                             (* index of invariant fact *)
        ~(fact:invariant_fact_t):invariant_int =
object (self:'a)

  val invd = invd

  method index = index

  method compare (other:'a) = Stdlib.compare self#index other#index

  method compare_lb (other:'a) =
    match (self#lower_bound, other#lower_bound) with
    | (Some _, None) -> -1
    | (None, Some _) -> 1
    | _ ->
       match (self#lower_bound_xpr, other#lower_bound_xpr) with
       | (Some _, None) -> -1
       | (None, Some _) -> 1
       | _ -> 0

  method compare_ub (other:'a) =
    match (self#upper_bound, other#upper_bound) with
    | (Some _, None) -> -1
    | (None, Some _) -> 1
    | _ ->
       match (self#upper_bound_xpr, other#upper_bound_xpr) with
       | (Some _, None) -> -1
       | (None, Some _) -> 1
       | _ -> 0

  method get_fact = fact

  method in_domain s =
    match self#get_fact with
    | Unreachable _ -> true
    | NonRelationalFact (_, nrv) -> (domain_of_invariant nrv) = s
    | ParameterConstraint _ -> s = "pepr"

  method applies_to_var ?(var_equal=false) (var:variable_t) =
    match self#get_fact with
    | NonRelationalFact (v, _) when var_equal -> v#equal var
    | NonRelationalFact (v, _) -> v#getName#equal var#getName
    | _ -> false

  method is_unreachable =
    match self#get_fact with Unreachable s -> Some s | _ -> None

  method is_interval = match fact with
  | NonRelationalFact (_, FIntervalValue _) -> true
  | _ -> false

  method is_symbolic_bound = match fact with
    | NonRelationalFact (_, FSymbolicBound _) -> true
    | _ -> false

  method is_regions = match fact with
    | NonRelationalFact (_, FRegionSet _) -> true
    | _ -> false

  method get_regions = match fact with
    | NonRelationalFact (_, FRegionSet syms) ->
       List.filter (fun s -> not (s#getBaseName = "pres#"))  syms
    | _ ->
       begin
         ch_error_log#add "invariant:get-regions" self#toPretty;
         raise
           (CCHFailure
              (LBLOCK [STR "invariant:get-regions: "; self#toPretty]))
       end

  method get_preservation_ids = match fact with
    | NonRelationalFact (_,FRegionSet syms) ->
       List.fold_left (fun acc s ->
           if s#getBaseName = "pres#" then
             s#getSeqNumber :: acc
           else
             acc) [] syms
    | _ ->
       begin
         ch_error_log#add "invariant:get-regions" self#toPretty;
         raise (CCHFailure
                  (LBLOCK [STR "invariant:get-regions: "; self#toPretty]))
       end

  method is_smaller (other:'a) =
    match (fact, other#get_fact) with
    | (NonRelationalFact (_,i1), NonRelationalFact (_,i2)) -> is_smaller_nrv i1 i2
    | _ ->
      begin
	ch_error_log#add
          "invariant comparison"
	  (LBLOCK [
               STR "Invariants are not non-relational values: ";
	       self#toPretty;
               STR " and ";
               other#toPretty]);
	raise
          (CCHFailure
	     (LBLOCK [
                  STR "Invariants are not non-relational values: ";
		  self#toPretty;
                  STR " and ";
                  other#toPretty]))
      end

  method direct_call_return_value =
    let get_direct_rv s =
      match s#getAttributes with
      | ("rv:" :: x :: _) -> Some x
      | _ -> None in
    match fact with
    | NonRelationalFact (_,FInitializedSet l) ->
       List.fold_left (fun acc s ->
           match acc with
           | Some _ -> acc
           | _ -> get_direct_rv s) None l
    | _ -> None

  method indirect_call_return_value =
    let get_indirect_rv s =
        match s#getAttributes with
        | ("indirect-call-rv:" :: x :: _) -> Some x
        | _ -> None in
    match fact with
    | NonRelationalFact (_,FInitializedSet l) ->
       List.fold_left (fun acc s ->
           match acc with
           | Some _ -> acc
           | _ -> get_indirect_rv s) None l
    | _ -> None

  method const_value =
    match fact with
    | NonRelationalFact (_, FIntervalValue (Some n1,Some n2)) when n1#equal n2 ->
       Some n1
    | NonRelationalFact (_, FSymbolicExpr (XConst (IntConst n))) -> Some n
    | _  -> None

  method lower_bound =
    match fact with
    | NonRelationalFact (_, FIntervalValue (Some n, _)) -> Some n
    | NonRelationalFact (_, FSymbolicExpr (XConst (IntConst n))) -> Some n
    | NonRelationalFact (_, FSymbolicBound (LB, [[XConst (IntConst n)]])) ->
       Some n
    | _ -> None

  method upper_bound =
    match fact with
    | NonRelationalFact (_, FIntervalValue (_, Some n)) -> Some n
    | NonRelationalFact (_, FSymbolicExpr (XConst (IntConst n))) -> Some n
    | NonRelationalFact (_, FSymbolicBound (UB, [[XConst (IntConst n)]]))
      -> Some n
    | _ -> None

  method lower_bound_xpr =
    match fact with
    | NonRelationalFact (_, FIntervalValue (Some n, _)) ->
       Some (num_constant_expr n)
    | NonRelationalFact (_, FSymbolicExpr x) -> Some x
    | NonRelationalFact (_, FSymbolicBound (LB, [[x]])) -> Some x
    | _ -> None

  method upper_bound_xpr =
    match fact with
    | NonRelationalFact (_, FIntervalValue (_, Some n)) ->
       Some (num_constant_expr n)
    | NonRelationalFact (_, FSymbolicExpr x) -> Some x
    | NonRelationalFact (_, FSymbolicBound (UB, [[x]])) -> Some x
    | _ -> None

  method lower_bound_xpr_alternatives =
    match fact with
    | NonRelationalFact (_, FSymbolicBound (LB, l)) when
           List.for_all (fun s -> (List.length s) = 1) l ->
       Some (List.map List.hd l)
    | _ -> None

  method upper_bound_xpr_alternatives =
    match fact with
    | NonRelationalFact (_, FSymbolicBound (UB, l)) when
           List.for_all (fun s -> (List.length s) = 1) l ->
       Some (List.map List.hd l)
    | _ -> None

  method pepr_lower_bound =
    match fact with
    | NonRelationalFact (_, FSymbolicBound (LB, l)) -> Some l
    | _ -> None

  method pepr_upper_bound =
    match fact with
    | NonRelationalFact (_, FSymbolicBound (UB, l)) -> Some l
    | _ -> None

  method expr =
    match fact with
    | NonRelationalFact (_, FIntervalValue (Some lb,Some ub)) when lb#equal ub ->
       Some (num_constant_expr lb)
    | NonRelationalFact (_, FSymbolicExpr x) -> Some x
    | _ -> None

  method symbolic_expr =
    match fact with
    | NonRelationalFact (_, FSymbolicExpr x) -> Some x
    | _ -> None

  method base_offset_value =
    match fact with
    | NonRelationalFact
      (_, FBaseOffsetValue (aty, base, optlb, optub, canbenull)) ->
       Some (aty,base,optlb,optub,canbenull)
    | _ -> None

  method write_xml (node:xml_element_int) =
    begin
      invd#write_xml_invariant_fact node self#get_fact;
      node#setIntAttribute "index" index
    end

  method value_to_pretty =
    match fact with
    | NonRelationalFact (_,nrv) -> non_relational_value_to_pretty nrv
    | _ -> self#toPretty

  method toPretty = invariant_fact_to_pretty fact

end


let _read_xml_invariant
      (invd:invdictionary_int) (node:xml_element_int):invariant_int =
  let index = node#getIntAttribute "index" in
  let fact = invd#read_xml_invariant_fact node in
  new invariant_t ~invd ~index ~fact


module InvariantFactCollections = CHCollections.Make
  (struct
    type t = invariant_fact_t
    let compare = invariant_fact_compare
    let toPretty = invariant_fact_to_pretty
   end)


(* container for multiple invariants at one location *)
module InvariantCollections = CHCollections.Make
  (struct
    type t = invariant_int
    let compare f1 f2 = f1#compare f2
    let toPretty f = f#toPretty
   end)


class location_invariant_t (invd:invdictionary_int):location_invariant_int =
object (self)

  val invd = invd
  val table = H.create 3   (*  variable-index -> invariant-fact index list *)
  val facts = H.create 3   (*  invariant-fact index -> invariant_int *)

  method get_invariants:invariant_int list =
    H.fold (fun _ v a -> v::a) facts []

  method get_sorted_invariants
           (cmp:invariant_int -> invariant_int -> int):invariant_int list =
    List.sort cmp self#get_invariants

  method get_var_invariants (v:variable_t):invariant_int list =
    if H.mem table v#getName#getSeqNumber then
      H.find table v#getName#getSeqNumber
    else
      []

  method get_parameter_constraints:invariant_int list =
    List.filter (fun i ->
        match i#get_fact with
        | ParameterConstraint _ -> true | _ -> false) self#get_invariants

  method add_fact (fact:invariant_fact_t) =
    let index = invd#index_invariant_fact fact in
    if H.mem facts index then () else
      let inv = new invariant_t ~invd ~index ~fact in
      begin
        H.add facts index inv;
        self#integrate_fact inv
      end

  method private integrate_fact (inv:invariant_int) =
    match inv#get_fact with
    | NonRelationalFact (v, _) ->
       let _ = chlog#add "integrate fact" (LBLOCK [v#toPretty; STR "; "; inv#toPretty]) in
       let vindex = v#getName#getSeqNumber in
       let entry =
         if H.mem table vindex then
           H.find table vindex
         else [] in
       let newentry =
         match entry with
         | [] -> [inv]
         | _ ->
            if inv#is_interval then
              let intervalfacts = List.filter (fun i -> i#is_interval) entry in
              let intervalfacts = match intervalfacts with
                | [] -> [inv]
                | [p] when inv#is_smaller p -> [inv]
                | [p] -> [p]
                | _ ->
                   let msg =
                     LBLOCK [
                         STR "Multiple interval facts: ";
                         pretty_print_list
                           intervalfacts
                           (fun p -> p#toPretty) "{" ", " "}"] in
                   begin
                     ch_error_log#add "interval facts" msg;
                     raise (CCHFailure msg)
                   end in
              intervalfacts @ (List.filter (fun i -> not i#is_interval) entry)
            else if inv#is_regions then
              let regionfacts = List.filter (fun i -> i#is_regions) entry in
              let regionfacts = match regionfacts with
                | [] -> [inv]
                | [p] when inv#is_smaller p -> [inv]
                | [p] -> [p]
                | _ ->
                   let msg =
                     LBLOCK [
                         STR "Multiple regions facts: ";
                         pretty_print_list
                           regionfacts
                           (fun p -> p#toPretty) "{" ", " "}"] in
                   begin
                     ch_error_log#add "regions facts" msg;
                     raise (CCHFailure msg)
                   end in
              regionfacts @ (List.filter (fun i -> not i#is_regions) entry)
            else
              inv :: entry in
       H.replace table vindex newentry
    | _ -> ()

  method write_xml (node:xml_element_int) =
    let invs = List.sort Stdlib.compare (H.fold (fun k _ a -> k::a) facts []) in
    if (List.length invs) > 0 then
      let attr = String.concat "," (List.map string_of_int invs) in
      node#setAttribute "ifacts" attr

  method read_xml (node:xml_element_int) =
    if node#hasNamedAttribute "ifacts" then
      let attr =
        try
          List.map int_of_string (nsplit ',' (node#getAttribute "ifacts"))
        with
          Failure _ ->
          raise
            (CCHFailure
               (LBLOCK [
                    STR "location_invariant:read_xml: int_of_string on ";
                    STR (node#getAttribute "ifacts")])) in
      let facts = List.map invd#get_invariant_fact attr in
      let facts = List.sort invariant_fact_compare facts in
      List.iter self#add_fact facts

  method toPretty =
    let vfacts = H.fold (fun _ v a -> v :: a) table [] in
    let otherfacts =
      H.fold (fun _ v acc ->
          match v#get_fact with
          | NonRelationalFact _ -> acc
          | _ -> v::acc) facts [] in
    let pvfact vf =
      match vf with
      | h::_ ->
         begin
           match h#get_fact with
           | NonRelationalFact(v,_) ->
              LBLOCK [
                  v#toPretty;
                  NL;
                  INDENT(
                      3,
                      LBLOCK (List.map (fun f -> LBLOCK [f#toPretty; NL]) vf));
                  NL]
           | _ -> STR ""
         end
      | _ -> STR "" in
    LBLOCK [
        LBLOCK (List.map pvfact vfacts);
        NL;
        LBLOCK (List.map (fun f -> LBLOCK [f#toPretty; NL]) otherfacts);
        NL]

end


class invariant_io_t
        (optnode:xml_element_int option)
        (invd:invdictionary_int):invariant_io_int =
object (self)

  val invd = invd
  val invariants: (location_invariant_int) ProgramContextCollections.table_t =
    new ProgramContextCollections.table_t

  initializer
    match optnode with
    | Some node -> self#read_xml node
    | _ -> ()

  method private add (context:program_context_int) (fact:invariant_fact_t) =
    (self#get_location_invariant context)#add_fact fact

  method get_invariant (index:int) =
    let fact = invd#get_invariant_fact index in
    new invariant_t ~invd ~index ~fact

  method get_location_invariant (context:program_context_int) =
    match invariants#get context with
    | Some locInv -> locInv
    | _ -> let locInv = new location_invariant_t invd in
      begin invariants#set context locInv; locInv end

  method add_fact (context:program_context_int) (f:invariant_fact_t) =
    self#add context f

  method write_xml (node:xml_element_int) =
    let dnode = xmlElement "inv-dictionary" in
    let lnode = xmlElement "location-invariants" in
    begin
      lnode#appendChildren
        (List.map (fun (c,locinv) ->
             let cnode = xmlElement "loc" in
             begin
               ccontexts#write_xml_context cnode c;
               locinv#write_xml cnode;
               cnode
             end) invariants#listOfPairs);
      invd#write_xml dnode ;
      node#appendChildren [dnode; lnode]
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      invd#read_xml (getc "inv-dictionary");
      List.iter (fun n ->
          let c = ccontexts#read_xml_context n in
          let locinv =  self#get_location_invariant c in
          locinv#read_xml n )
        ((getc "location-invariants")#getTaggedChildren "loc")
    end

end


let mk_invariant_io
      (optnode:xml_element_int option) (vard:vardictionary_int) =
  let invd = mk_invdictionary vard in
  new invariant_io_t optnode invd


let get_invariant_messages
      (invio:invariant_io_int) (l:(int * int list) list) =
  List.fold_left (fun acc (k,ilist) ->
      List.fold_left (fun acci invindex ->
          let inv = invio#get_invariant invindex in
          let p = LBLOCK [STR "["; INT k; STR "] "; inv#value_to_pretty] in
          p::acci) acc ilist) [] l


let prioritize_invariants (f: invariant_int -> bool) (invs: invariant_int list) =
  List.stable_sort
    (fun inv1 inv2 ->
      if f inv1 && f inv2 then
        0
      else if f inv1 then
        -1
      else
        1) invs
