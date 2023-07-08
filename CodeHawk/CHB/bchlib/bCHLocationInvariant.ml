(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
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
open CHAtlas
open CHBounds
open CHCommon
open CHIntervals
open CHNumerical
open CHNumericalConstraints
open CHPretty
open CHLanguage
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* xpr *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify
open XprUtil
open XprXml

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHInvDictionary
open BCHLibTypes
open BCHSystemSettings
open BCHVariable
open BCHXmlUtil

module H = Hashtbl
module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)

let tracked_locations = []

let track_location loc p =
  if List.mem loc tracked_locations then
    chlog#add ("tracked:" ^ loc) p
  

let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

let hex_cutoff = mkNumerical 10000  (* above this number print as hex value *)


(* The original function did not reverse the list like the utility function;
   not sure if the reversal is significant here. *)
let nsplit (separator: char) (s: string): string list =
  List.rev (CHUtil.string_nsplit separator s)


let pr_expr = xpr_formatter#pr_expr
let expr_compare = syntactic_comparison


(* Use the list_compare version that compares the elements starting from the
   last element *)
let list_compare = CHUtil.list_compare_r


let non_relational_value_compare v1 v2 =
  let opt_num_compare i1 i2 = match (i1,i2) with
    | (None,None) -> 0
    | (Some _,None) -> -1
    | (None,Some _) -> 1
    | (Some j1,Some j2) -> j1#compare j2 in
  match (v1,v2) with
  | (FSymbolicExpr f1,FSymbolicExpr f2) -> expr_compare f1 f2
  | (FSymbolicExpr _,_) -> -1
  | (_,FSymbolicExpr _) -> 1
  | (FIntervalValue (lb1, ub1), FIntervalValue (lb2, ub2)) ->
     let l0 = opt_num_compare lb1 lb2 in
     if l0 = 0 then
       opt_num_compare ub1 ub2
     else
       l0
  | (FIntervalValue _,_) -> -1
  | (_, FIntervalValue _) -> 1
  | (FBaseOffsetValue (b1, lb1, ub1,_), FBaseOffsetValue (b2, lb2, ub2,_)) ->
    let l0 = b1#compare b2 in
    if l0 = 0 then
      let l1 = opt_num_compare lb1 lb2 in
      if l1 = 0 then opt_num_compare ub1 ub2 else l1
    else l0


let non_relational_value_to_pretty v =
  try
    let num_to_pretty num = 
      if num#lt (mkNumerical 10000) then 
        STR num#toString
      else
        TR.tfold_default
          (fun s -> STR s)
          num#toPretty
          (numerical_to_hex_string num) in
    match v with
    | FSymbolicExpr v -> LBLOCK [STR "("; pr_expr v; STR ")"]
    | FIntervalValue (Some lb, Some ub) when lb#equal ub -> num_to_pretty lb
    | FIntervalValue (lb,ub) ->
       LBLOCK [
           STR "[";
           (match lb with Some v -> num_to_pretty v | _ -> STR "-oo");
	   STR " ; ";
           (match ub with Some v -> num_to_pretty v | _ -> STR "oo");
	   STR "]"]
    | FBaseOffsetValue (base,lb,ub,canbenull) ->
       LBLOCK [
           STR "(";
           base#toPretty;
           STR ")";
	   (match (lb,ub) with
	    | (None, None) -> STR ""
	    | (Some lb, None) ->
               LBLOCK [STR "+[ "; num_to_pretty lb; STR "; oo ]"]
	    | (None,Some ub) ->
               LBLOCK [STR "+[ -oo ; "; num_to_pretty ub; STR " ]"]
	    | (Some lb, Some ub) when lb#equal ub  && lb#equal numerical_zero ->
               STR ""
	    | (Some lb, Some ub) when lb#equal ub ->
	       LBLOCK [ STR "+ "; num_to_pretty lb]
	    | (Some lb, Some ub) ->
               LBLOCK [
                   STR "+[";
                   num_to_pretty lb;
                   STR ";";
		   num_to_pretty ub;
                   STR "]"]);
	   (if canbenull then STR "" else STR " (not-null)")]
  with
  | BCH_failure p ->
     let msg = LBLOCK [STR "non-relational-value-to-pretty: "; p] in
     begin
       ch_error_log#add "non-relational-value-to-pretty" msg;
       raise (BCH_failure msg)
     end


let linear_equality_to_canonical_form lineq =
  let factors =
    List.sort (fun (_, v1) (_, v2) -> v1#compare v2) lineq.leq_factors in
  let (fc,_) = List.hd factors in
  if fc#gt numerical_zero then 
    {leq_factors = factors; leq_constant = lineq.leq_constant}
  else
    let factors = List.map (fun (c,f) -> (c#neg,f)) factors in
    {leq_factors = factors; leq_constant = lineq.leq_constant#neg}


let numerical_constraint_to_linear_equality (nc: numerical_constraint_t) =
  let lineq = 
    {leq_factors = List.map (fun (c,f) -> (c, f#getVariable)) nc#getFactorsList;
     leq_constant = nc#getConstant} in
  linear_equality_to_canonical_form lineq


let linear_equality_to_pretty e =
  let pp_coeff first c =
    if c#equal numerical_one then
      if first then
	STR ""
      else 
	STR " + "
    else if c#equal numerical_one#neg then
      STR "-"
    else if c#lt numerical_zero then
      c#toPretty
    else
      LBLOCK [(if first then STR "" else STR " + "); c#toPretty] in
  let (lhs, _) =
    List.fold_left (fun (a, first) (c, f) ->
        ((LBLOCK [pp_coeff first c; f#toPretty])::a, false))
      ([],true) e.leq_factors in
  LBLOCK [LBLOCK (List.rev lhs); STR " = "; e.leq_constant#toPretty]


let linear_equality_get_vars e = List.map (fun (_, v) -> v) e.leq_factors


let linear_equality_get_unity_vars e =
  List.fold_left (fun acc (c, v) ->
    if c#equal numerical_one || c#neg#equal numerical_one then
      v :: acc 
    else acc) [] e.leq_factors


let is_variable_equality (lineq: linear_equality_t) =
  if lineq.leq_constant#equal numerical_zero then
    match lineq.leq_factors with
    | [(c1, v1); (c2, v2)] ->
       c1#equal numerical_one && c2#equal (mkNumerical (-1))
    | _ -> false
  else
    false


let get_variable_equality_variables (lineq: linear_equality_t) =
  if is_variable_equality lineq then
    linear_equality_get_vars lineq
  else
    []


let linear_equality_get_expr e v =
  let make_factor c f =
    if c#equal numerical_one then
      XVar f 
    else 
      XOp (XMult, [num_constant_expr c; XVar f]) in
  try
    let (c,f) = List.find (fun (_,f) -> f#equal v) e.leq_factors in
    let xfactors = List.filter (fun (_, f) -> not (f#equal v)) e.leq_factors in
    let x =
      if c#equal numerical_one then
	List.fold_left (fun a (c,f) -> XOp (XPlus, [a; make_factor c#neg f]))
	  (num_constant_expr e.leq_constant) xfactors
      else if c#equal numerical_one#neg then
	List.fold_left (fun a (c,f) -> XOp (XPlus, [a; make_factor c f]))
	  (num_constant_expr e.leq_constant#neg) xfactors
      else
	raise
          (BCH_failure
	     (LBLOCK [
                  STR "Case with higher coefficients not yet handled: ";
		  linear_equality_to_pretty e])) in
    simplify_xpr x
  with
    Not_found ->
    raise
      (BCH_failure
	 (LBLOCK [
              STR "Variable ";
              v#toPretty;
	      STR " not found in linear equality ";
	      linear_equality_to_pretty e]))


let linear_equality_compare e1 e2 =
  let l0 = e1.leq_constant#compare e2.leq_constant in
  if l0 = 0 then
    list_compare
      e1.leq_factors
      e2.leq_factors
      (fun (c1,f1) (c2,f2) ->
        let l0 = c1#compare c2 in if l0 = 0 then f1#compare f2 else l0)
  else
    l0


let invariant_fact_compare f1 f2 =
  match (f1,f2) with
  | (Unreachable d1,Unreachable d2) -> Stdlib.compare d1 d2
  | (Unreachable _,_) -> -1
  | (_,Unreachable _) -> 1
  | (NonRelationalFact (x1,v1),NonRelationalFact (x2,v2)) ->
     let l0 = x1#compare x2 in
     if l0 = 0 then non_relational_value_compare v1 v2 else l0
  | (NonRelationalFact _,_) -> -1
  | (_,NonRelationalFact _) -> 1
  | (RelationalFact e1,RelationalFact e2) -> linear_equality_compare e1 e2
  | (RelationalFact _,_) -> -1
  | (_, RelationalFact _) -> 1
  | (InitialVarEquality (v1,_), InitialVarEquality (v2,_)) -> v1#compare v2
  | (InitialVarEquality _, _) -> -1
  | (_, InitialVarEquality _) -> 1
  | (InitialVarDisEquality (v1,_), InitialVarDisEquality (v2,_)) -> v1#compare v2
  | (InitialVarDisEquality _,_) -> -1
  | (_,InitialVarDisEquality _) -> 1
  | (TestVarEquality (v1,_,ta1,ja1), TestVarEquality (v2,_,ta2,ja2)) -> 
    let l0 = v1#compare v2 in 
    if l0 = 0 then 
      let l1 = Stdlib.compare ta1 ta2 in
      if l1 = 0 then Stdlib.compare ja1 ja2 else l1
    else l0
		   

let invariant_fact_to_pretty f =
  match f with
  | Unreachable d ->
     LBLOCK [STR "unreachable("; STR d; STR ")"]
  | NonRelationalFact (p,v) ->
     LBLOCK [
         STR p#getName#getBaseName; STR ": "; non_relational_value_to_pretty v]
  | RelationalFact e ->
     linear_equality_to_pretty e
  | InitialVarEquality (v,vi) ->
     LBLOCK [STR "initvar("; v#toPretty; STR ")"]
  | InitialVarDisEquality (v,vi) ->
     LBLOCK [STR "initmod("; v#toPretty; STR ")"]
  | TestVarEquality (v, _, taddr, jaddr) ->
     LBLOCK [
         STR "testvar(";
         v#toPretty;
         STR "@";
         STR taddr;
         STR "_to_";
	 STR jaddr;
         STR ")"]


let is_smaller_nrv (f1:non_relational_value_t) (f2:non_relational_value_t) =
  let is_smaller_interval lb1 ub1 lb2  ub2 =
    match (lb1,ub1,lb2,ub2) with
    | (Some lb1, Some ub1, Some lb2, Some ub2) -> lb1#geq lb2 && ub1#leq ub2
    | (Some lb1, Some ub1, Some lb2, _) -> lb1#geq lb2
    | (Some lb1, Some ub1, _, Some ub2) -> ub1#leq ub2
    | (Some lb1, Some ub1, _, _) -> true
    | _ -> false in
  match (f1,f2) with
  | (FIntervalValue (lb1, ub1), FIntervalValue (lb2, ub2)) ->
     is_smaller_interval lb1 ub1 lb2 ub2
  | (FBaseOffsetValue (s1, lb1, ub1, _), FBaseOffsetValue(s2, lb2, ub2, _)) ->
     (s1#equal s2) && (is_smaller_interval lb1 ub1 lb2 ub2)
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
        (BCH_failure
	   (LBLOCK [
                STR "Invariant facts are not intervals: ";
		non_relational_value_to_pretty f1;
                STR " and ";
		non_relational_value_to_pretty f2]))
    end
     

class invariant_t
        ~(invd:invdictionary_int)
        ~(index:int)
        ~(fact:invariant_fact_t):invariant_int =
object (self:'a)

  val invd = invd
  val index = index
  val fact = fact

  method index = index

  method compare (other:'a) =
    Stdlib.compare self#index other#index

  method transfer (v: variable_t) =
    match fact with
    | NonRelationalFact (oldv, nrv) ->
       let newindex = v#getName#getSeqNumber in
       let newfact = NonRelationalFact (v, nrv) in
       {< index = newindex; fact = newfact >}
    | _ -> {< >}

  method get_fact = fact

  method is_constant =
    match fact with
    | NonRelationalFact (_, FIntervalValue (Some lb, Some ub)) -> lb#equal ub
    | _ -> false

  method is_interval =
    match fact with
    | NonRelationalFact (_, FIntervalValue _) -> true
    | _ -> false

  method is_base_offset_value =
    match fact with
    | NonRelationalFact (_, FBaseOffsetValue _) -> true
    | _ -> false

  method is_symbolic_expr =
    match fact with
    | NonRelationalFact (_, FSymbolicExpr _) -> true
    | _ -> false

  method is_linear_equality =
    match fact with
    | RelationalFact _ -> true
    | _ -> false

  method is_variable_equality =
    match fact with
    | RelationalFact lineq ->
       is_variable_equality lineq
    | _ -> false

  method get_variable_equality_variables =
    match fact with
    | RelationalFact lineq when is_variable_equality lineq ->
       get_variable_equality_variables lineq
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Not a variable-equality: "; self#toPretty]))

  method is_smaller (other:'a) =
    match (fact, other#get_fact) with
    | (NonRelationalFact (_, i1), NonRelationalFact (_, i2)) -> is_smaller_nrv i1 i2
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
          (BCH_failure
	     (LBLOCK [
                  STR "Invariants are not non-relational values: ";
		  self#toPretty;
                  STR " and ";
                  other#toPretty]))
      end

  method get_variables =
    match fact with | NonRelationalFact (v,_) -> [v] | _ -> []

  method write_xml (node:xml_element_int) =
    begin
      invd#write_xml_invariant_fact node self#get_fact;
      node#setIntAttribute "index" index
    end

  method toPretty = invariant_fact_to_pretty fact
end


let read_xml_invariant
      (invd:invdictionary_int) (node:xml_element_int):invariant_int =
  let index = node#getIntAttribute "index" in
  let fact = invd#read_xml_invariant_fact node in
  new invariant_t ~invd ~index ~fact


class location_invariant_t
        (invd:invdictionary_int) (iaddr:string):location_invariant_int =
object (self)

  val invd = invd
  val table = H.create 5   (* non-relational facts indexed by variable seq number *)
  val facts = H.create 3   (* invariant-fact index -> invariant_int  *)

  method reset =
    begin
      H.clear table;
      H.clear facts
    end

  method add_fact (fact:invariant_fact_t) =
    let index = invd#index_invariant_fact fact in
    if H.mem facts index then ()  else
      let inv = new invariant_t ~invd ~index ~fact  in
      begin
        H.add facts index inv;
        self#integrate_fact inv;
        track_location
          iaddr
          (LBLOCK [
               STR iaddr;
               STR ": add fact ";
               inv#toPretty])
      end

  method remove_initial_value_fact (fvar: variable_t) (fval: variable_t) =
    let index = fvar#getName#getSeqNumber in
    if H.mem table index then
      let e = H.find table index in
      let newfacts =
        List.filter (fun f ->
            match f#get_fact with
            | InitialVarEquality _ -> false
            | _ -> true) e in
      if (List.length e) != (List.length newfacts) then
        begin
          chlog#add
            "remove initial-value fact"
            (LBLOCK [STR iaddr; STR ":  "; fvar#toPretty; STR " - "; fval#toPretty]);
          H.replace table index newfacts
        end
      else
        ()
    else
      ()

  method private integrate_fact  (inv:invariant_int) =
    let add v f =
      let index = v#getName#getSeqNumber in
      let entry = 
	if H.mem table index then
	  let e = H.find table index in
	  if List.exists (fun w -> (f#compare w) = 0) e then 
	    e
              (* remove base-offset value when a symbolic expression is found *)
          else if f#is_symbolic_expr then
            f :: (List.filter (fun p -> not p#is_base_offset_value) e)
              (* only allow one interval in the set of facts *)          
	  else if f#is_interval then
	    let pfacts = List.filter (fun p -> p#is_interval) e in
	    match pfacts with
	    | [] -> f :: e
	    | [p] when f#is_smaller p ->
	      f :: (List.filter (fun p -> not p#is_interval) e)
	    | [p] -> e
	    | _ ->
               let msg =
                 LBLOCK [
                     STR "Multiple interval facts: ";
		     pretty_print_list pfacts (fun p -> p#toPretty) "{" "," "}";
                     STR " at ";
                     STR iaddr] in
	      begin
		ch_error_log#add "interval facts" msg;
		raise (BCH_failure msg)
	      end
          else if f#is_base_offset_value then
            let pfacts = List.filter (fun p -> p#is_base_offset_value) e in
            match pfacts with
            | [] -> f :: e
            | [ p ] when f#is_smaller p ->
               f :: (List.filter (fun p -> not p#is_base_offset_value) e)
            | [ p ] -> e
            | _ ->
               let msg =
                 LBLOCK [
                     STR "Multiple base-offset-value  facts: ";
                     pretty_print_list pfacts
                       (fun p -> p#toPretty) "{" "," "}" ] in
               begin
                 ch_error_log#add "base-offset-value facts" msg;
                 raise (BCH_failure msg)
               end
	  else f :: e
	else
	  [f] in
      H.replace table index entry in
    let add_relational_equality f =
      if f#is_variable_equality then
        let eqvars = f#get_variable_equality_variables in
        match eqvars with
        | [v1; v2] ->
           let v1index = v1#getName#getSeqNumber in
           let v2index = v2#getName#getSeqNumber in
           if H.mem table v2index then
             let v2facts = H.find table v2index in
             let v1newfacts =
               List.fold_left (fun a f ->
                   match f#get_fact with
                   | NonRelationalFact (_, nrv) ->
                      (f#transfer v1) :: a
                   | _ -> a) [] v2facts in
             let _ =
               track_location
                 iaddr
                 (LBLOCK [
                      STR "new v1facts: ";
                      LBLOCK
                        (List.map (fun inv ->
                             LBLOCK [inv#toPretty; STR "; "]) v1newfacts)]) in
             if H.mem table v1index then
               let v1facts = H.find table v1index in
               List.iter (fun f -> add v1 f) (v1newfacts @ v1facts)
             else
               H.add table v1index v1newfacts
           else
             ()
        | _ -> ()
      else
        () in
    begin
      match inv#get_fact with
      | NonRelationalFact (v, _)
      | InitialVarEquality (v, _)
      | InitialVarDisEquality (v, _)
      | TestVarEquality (v, _, _, _) -> add v inv
      | RelationalFact lineq -> add_relational_equality inv
      | _ -> ()
    end

  method private get_var_facts (v:variable_t) =
    let index = v#getName#getSeqNumber in
    let facts = if H.mem table index then H.find table index else [] in
    let _ =
      track_location
        iaddr
        (LBLOCK [
             STR "get_var_facts: ";
             v#toPretty;
             pretty_print_list facts (fun f -> f#toPretty) "[" "," "]" ]) in
    List.map (fun f -> f#get_fact) facts

  method get_facts =
    let factslist = H.fold (fun _ v a -> v::a) facts [] in
    factslist @
      (let l = ref [] in
       let _ =
         H.iter (fun _ v ->
             l := (List.filter (fun i -> i#is_interval) v) @ !l) table in !l)
    
  method get_count = 
    let nrCount = H.fold (fun _ v a -> a + (List.length v)) table 0 in
    nrCount + H.length facts   

  method private get = List.map (fun f -> f#get_fact) self#get_facts

  method private get_affine v =
    List.fold_left (fun acc f -> 
      match acc with Some _ -> acc | _ ->
	match f with
	| NonRelationalFact (w,FSymbolicExpr x) when w#equal v -> Some x
	| _ -> None) None (self#get_var_facts v)

  method private get_local v comparator =
    List.fold_left (fun acc f ->
      match f#get_fact with
      | RelationalFact e ->
	let vars = linear_equality_get_unity_vars e in
	if List.exists (fun f -> v#equal f) vars then
	  let vars = List.sort comparator vars in
	  if (List.hd vars)#equal v then 
	    None   (* variable is highest priority and should not be replaced *)
	  else
	    Some (linear_equality_get_expr e v)
	else
	  None
      | _ -> None) None self#get_facts

  method rewrite_expr (x:xpr_t) (comparator:(variable_t -> variable_t -> int)) =
    let subst1 v = 
      if self#is_constant v then
        XConst (IntConst (self#get_constant v))
      else
        XVar v in
    let subst2 v = 
      match self#get_affine v with 
      | Some x -> x
      | _ -> XVar v in
    let subst3 v =
      if self#var_has_initial_value v then
        XVar (self#get_initial_value v)
      else
        XVar v in
    let subst4 v =
      match self#get_external_exprs v with
      | [] -> XVar v
      | x :: tl -> x in
    let x1 = simplify_xpr (substitute_expr subst1 x) in
    let x2 = simplify_xpr (substitute_expr subst2 x1) in
    let x3 = simplify_xpr (substitute_expr subst3 x2) in
    let x4 = simplify_xpr (substitute_expr subst4 x3) in
    let result = simplify_xpr (substitute_expr subst3 x4) in
    let _ =
      track_location
        iaddr
        (LBLOCK [
             STR "rewrite: " ; x2p x; STR " --> ";
             STR "; x1: " ; x2p x1;
             STR "; x2: " ; x2p x2;
             STR "; x3: " ; x2p x3;
             STR "; x4: " ; x2p x4;
             STR "; result: "; x2p result]) in
    result

  method get_constant (v:variable_t) =
    let rec aux l =
      match l with
      | [] ->
         raise
           (BCH_failure
	      (LBLOCK [STR "Variable "; v#toPretty; STR " is not a constant"]))
      | f::tl ->
	match f with
	| NonRelationalFact (w, FIntervalValue (Some lb, Some ub)) 
	    when w#equal v && lb#equal ub -> lb
	| _ -> aux tl in
    aux (self#get_var_facts v)

  method get_interval (v:variable_t) =
    let rec aux l =
      match l with
      | [] -> 
	 raise
           (BCH_failure
	      (LBLOCK [STR "Variable "; v#toPretty; STR " is not an interval"]))
      | f::tl ->
	match f with
	| NonRelationalFact (w, FIntervalValue (lb,ub)) when w#equal v -> 
	  self#make_interval lb ub
	| _ -> aux tl in
    aux (self#get_var_facts v)

  method get_affine_offset (base:variable_t) (off:variable_t) =
    List.fold_left (fun acc f ->
      match acc with Some _ -> acc | _ ->
	match f with
	| InitialVarEquality (v,w) when w#equal base -> Some numerical_zero
	| NonRelationalFact (v,FSymbolicExpr x) ->
	  begin
	    match x with
	    | XVar w when w#equal off -> Some numerical_zero
	    | XOp (XPlus, [ XVar w; XConst (IntConst n) ])
	      | XOp (XPlus, [ XConst (IntConst n); XVar w ]) when w#equal base ->
               Some n
	    | XOp (XMinus, [ XVar w ; XConst (IntConst n) ]) when w#equal base ->
               Some n#neg
	    | _ -> None
	  end
	| _ -> None) None (self#get_var_facts off)

  method get_interval_offset (base:variable_t) (off:variable_t) =
    match self#get_affine_offset base off with
    | Some n -> mkSingletonInterval n
    | _ ->
      if self#is_base_offset off then
	let (sym, intv) = self#get_base_offset off in
	if sym#equal base#getName then
          intv
        else
          topInterval
      else
	topInterval

  method get_external_exprs (v:variable_t) =
    if v#isTmp then
      []
    else
      let result =
        List.fold_left (fun acc f ->
            match f with
            | NonRelationalFact (w, FSymbolicExpr x) when w#equal v ->
               x :: acc | _ -> acc) [] (self#get_var_facts v) in
      let _ =
        track_location
          iaddr
          (LBLOCK [
               STR "get_external_exprs: ";
               v#toPretty;
               STR " --> ";
               pretty_print_list result x2p "[" "," "]"]) in
      result

  method get_known_variables =
    let nrFacts = ref [] in
    let add v = nrFacts := v :: !nrFacts in
    let _ = H.iter (fun _ facts ->
      List.iter (fun f ->
	match f#get_fact with
	| NonRelationalFact (v,FSymbolicExpr _) -> add v
	| NonRelationalFact (v,FIntervalValue (Some lb,Some ub))
             when lb#equal ub -> add v
	| InitialVarEquality (v,_) -> add v
	| _ -> ()) facts) table in
    !nrFacts

  method are_equal v1 v2 = 
    match self#get_affine_offset v1 v2 with Some n -> n#is_zero 
    | _ -> 
      H.fold (fun _ f acc ->
	if acc then acc else
	  match f#get_fact with
	  | RelationalFact le ->
	    let vars = List.map snd le.leq_factors in
	    let coeffs = List.map fst le.leq_factors in
	    (List.length vars) = 2
	    && le.leq_constant#equal numerical_zero
	    && List.exists (fun v -> v1#equal v) vars
	    && List.exists (fun v -> v2#equal v) vars
	    && (match coeffs with
		| [ c1 ; c2 ] -> 
		   (c1#equal numerical_one && c2#equal numerical_one#neg)
                   || (c1#equal numerical_one#neg && c2#equal numerical_one)
		| _ -> acc)
	  | _ -> acc) facts false   (* apply to relational facts only *)
		      
	      
  method test_var_is_equal
           (v:variable_t) (taddr:ctxt_iaddress_t) (jaddr:ctxt_iaddress_t) =
    List.fold_left (fun acc f ->
        if acc then
          acc
        else
          let _ =
            track_location jaddr
              (LBLOCK [STR "testvar: "; invariant_fact_to_pretty f]) in
	  match f with
	  | TestVarEquality (tv,_,ta,ja) -> ta = taddr && ja = jaddr
	  | _ -> acc) false (self#get_var_facts v)

  method var_has_initial_value (var:variable_t) =
    List.fold_left (fun acc f ->
      if acc then acc else
	match f with
	| InitialVarEquality (v,_) -> var#equal v
	| _ -> acc) false (self#get_var_facts var)

  method private get_initial_value (var:variable_t) =
    let result = List.fold_left (fun acc f ->
      match acc with Some _ -> acc | _ ->
	match f with 
	| InitialVarEquality (v,iv) when v#equal var -> Some iv
	| _ -> acc) None (self#get_var_facts var) in
    match result with
    | Some v -> v
    | _ ->
       raise
         (BCH_failure
	    (LBLOCK [
                 STR "Variable does not have an initial value: "; 
		 var#toPretty]))

  method get_init_disequalities =
    let result = ref [] in
    let add v = result := v :: !result in
    let _ = H.iter (fun _ facts ->
      List.iter (fun f ->
	match f#get_fact with InitialVarDisEquality (_, iv) -> add iv | _ -> ()) 
	facts) table in
    !result

  method get_init_equalities =
    let result = ref [] in
    let add v = result := v :: !result in
    let _ = H.iter (fun _ facts ->
      List.iter (fun f ->
	match f#get_fact with InitialVarEquality (_, iv) -> add iv | _ -> ())
	facts) table in
    !result

  method get_known_initial_values = 
    self#get_init_equalities @ self#get_init_disequalities

  method private make_interval (lb:numerical_t option) (ub:numerical_t option) =
    let make_number_bound i = bound_of_num i in
    let make_lower_bound b = 
      match b with None -> minus_inf_bound | Some i -> make_number_bound i in
    let make_upper_bound b = 
      match b with None -> plus_inf_bound | Some i -> make_number_bound i in
    match (lb,ub) with
    | (None,None) -> topInterval
    | (Some lb, Some ub) -> mkInterval lb ub
    | _ -> new interval_t (make_lower_bound lb) (make_upper_bound ub)
      
  method get_base_offset (v:variable_t) =
    let rec aux l =
      match l with
      | [] -> 
	 raise
           (BCH_failure
	      (LBLOCK [
                   STR "Variable "; v#toPretty; STR " is not a base-offset"]))
      | f::tl ->
	match f with 
	| NonRelationalFact (w, FBaseOffsetValue (base,lb,ub,_)) when w#equal v ->
	  (base, self#make_interval lb ub)
	| _ -> aux tl in
    aux (self#get_var_facts v)

  method get_base_offset_constant (v:variable_t) =
    let rec aux l =
      match l with
      | [] -> 
	 raise
           (BCH_failure
	      (LBLOCK [
                   STR "Variable "; v#toPretty; STR " is not a base-offset"]))
      | f::tl ->
	match f with 
	| NonRelationalFact (w, FBaseOffsetValue (base,Some lb,Some ub,_))
             when w#equal v && lb#equal ub ->
	  (base, lb)
	| _ -> aux tl in
    aux (self#get_var_facts v)
    
	  
  method is_constant v = 
    List.fold_left (fun acc f ->
      if acc then acc else
	match f with
	| NonRelationalFact (w, FIntervalValue (Some lb, Some ub)) 
	    when lb#equal ub && w#equal v -> true
	| _ -> false) false (self#get_var_facts v)

  method is_interval v = 
    List.fold_left (fun acc f ->
      if acc then acc else
	match f with
	| NonRelationalFact (w, FIntervalValue _) when w#equal v -> true
	| _ -> false) false (self#get_var_facts v)

  method is_base_offset v = 
    List.fold_left (fun acc f ->
      if acc then acc else
	match f with
	| NonRelationalFact (w, FBaseOffsetValue (_,_,_,_)) when w#equal v -> true
	| _ -> false) false (self#get_var_facts v)

  method is_base_offset_constant v =
    List.fold_left (fun acc f ->
        if acc then acc else
          match f with
          | NonRelationalFact (w,FBaseOffsetValue (_,Some lb, Some ub,_))
               when w#equal v && lb#equal ub -> true
          | _ -> false) false (self#get_var_facts v)

  method is_unreachable =
    List.fold_left (fun acc f ->
        if acc then
          acc
        else
          match f with
          | Unreachable _ -> true
          | _ -> acc) false self#get

  method var_has_symbolic_expr v =
    List.fold_left (fun acc f ->
      if acc then acc else
	match f with
	| NonRelationalFact (w, FSymbolicExpr _) when v#equal v -> true
	| _ -> false) false (self#get_var_facts v)

  method write_xml (node:xml_element_int) = 
    let invs = List.sort Stdlib.compare (H.fold (fun k _ a -> k::a) facts []) in
    if (List.length invs) > 0  then
      let attr = String.concat "," (List.map string_of_int invs) in
      node#setAttribute "ifacts" attr

  method read_xml (node:xml_element_int) =
    if node#hasNamedAttribute "ifacts" then
      let attr =
        try
          List.map int_of_string  (nsplit ',' (node#getAttribute "ifacts"))
        with
        | Failure _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "location_invariant:read_xml: int_of_strinngn on ";
                     STR (node#getAttribute "ifacts") ])) in
      let facts = List.map invd#get_invariant_fact attr in
      let facts = List.sort invariant_fact_compare facts  in
      List.iter self#add_fact facts
      
  method toPretty = self#toPrettyVar None

  method toPrettyVar (vnames:(variable_t -> string) option) =
    let xpr_formatter = match vnames with
      | Some vs -> make_xpr_formatter default_sym_to_pretty (fun v -> STR (vs v))
      | _ -> xpr_formatter in
    let facts = self#get in
    let unrDomains = List.fold_left (fun acc f ->
      match f with Unreachable s -> s :: acc | _ -> acc) [] facts in
    let pUnr = match unrDomains with
      | [] -> STR ""
      | _ ->
         LBLOCK [
             STR "Unreachability signalled by: ";
	     pretty_print_list unrDomains (fun s -> STR s) "" ", " "";
             NL] in
    let initFactVars = List.fold_left (fun acc f ->
      match f with InitialVarEquality (v,_) -> v :: acc | _ -> acc) [] facts in
    let initFactVars = List.sort (fun v1 v2 -> 
      Stdlib.compare v2#getName#getBaseName v1#getName#getBaseName) initFactVars in
    let pInit = List.map  (fun v -> 
      LBLOCK [STR "   "; STR v#getName#getBaseName; NL]) initFactVars in
    let pInit = match pInit with
      | [] -> STR ""
      | _ ->
         LBLOCK [
             STR "Variables that still have their initial value: ";
             NL;
	     LBLOCK pInit;
             NL] in
    let pTest = List.fold_left (fun acc f ->
      match f with
      | TestVarEquality (v,_,taddr,jaddr) ->
	 (LBLOCK [
              STR "Test var: ";
              v#toPretty;
              STR " (";
              STR taddr;
	      STR " -> ";
              STR jaddr;
              STR ")";
              NL]) :: acc
      | _ -> acc) [] facts in
    let nrFacts = List.fold_left (fun acc f ->
      match f with NonRelationalFact (v,x) -> (v,x) :: acc | _ -> acc) [] facts in
    let nrFacts = List.sort (fun (v1,_) (v2,_) -> 
      Stdlib.compare v2#getName#getBaseName v1#getName#getBaseName) nrFacts in
    let maxNameLen = List.fold_left (fun acc (v,_) ->
      let len = String.length v#getName#getBaseName in
      if len > acc then len else acc) 0 nrFacts in
    let p_null b = if b then STR "(can be null)" else STR "(not null)" in
    let isprintable num = num#geq (mkNumerical 32) && (mkNumerical 127)#geq num in
    let p_num n =
      if n#gt hex_cutoff then
        TR.tfold_default
          (fun s -> STR s)
          n#toPretty
	  (numerical_to_hex_string n)
      else if isprintable n then
	LBLOCK [
            n#toPretty;
            STR " ('";
            STR (String.make 1 (Char.chr n#toInt)); STR "')"]
      else 
	n#toPretty in
    let p_intv lb ub = match (lb,ub) with
      | (Some lb, Some ub) when lb#equal ub -> p_num lb
      | (Some lb, Some ub) -> 
	LBLOCK [STR "["; p_num lb; STR " ; "; p_num ub; STR "]"]
      | (Some lb, _) ->	LBLOCK [STR "["; p_num lb; STR " ; ->)"]
      | (_, Some ub) -> LBLOCK [STR "(<- ; "; p_num ub; STR "]"]
      | _ -> STR "" in
    let pNrv = List.fold_left (fun acc (v,x) ->
      let prefix = 
	LBLOCK [
            fixed_length_pretty (STR v#getName#getBaseName) maxNameLen;
	    STR ": "] in
      match x with
      | FSymbolicExpr x -> 
	(LBLOCK [prefix; xpr_formatter#pr_expr x; NL]) :: acc
      | FIntervalValue (lb,ub) -> (LBLOCK [prefix; p_intv lb ub; NL]) :: acc
      | FBaseOffsetValue (base,lb,ub,canbenull) ->
	 (LBLOCK [
              prefix;
              STR "(base) ";
              base#toPretty;
	      STR " + ";
              p_intv lb ub;
              STR " "; p_null canbenull;
              NL]) :: acc)
      [] nrFacts in
    let pRel = List.fold_left (fun acc f ->
      match f with
      | RelationalFact lineq ->
         (LBLOCK [linear_equality_to_pretty lineq; NL]) :: acc
      | _ -> acc) [] facts in
    LBLOCK [pUnr; pInit; LBLOCK pTest; LBLOCK pNrv; NL; LBLOCK pRel]
end


let make_location_invariant = new location_invariant_t

                            
let get_bound (b:bound_t) =
  match b#getBound with MINUS_INF | PLUS_INF -> None | NUMBER n -> Some n


class invariant_io_t
        (optnode:xml_element_int option)
        (invd:invdictionary_int)
        (fname:string):invariant_io_int =
object (self)

  val invd = invd
  val invariants = new StringCollections.table_t

  initializer
    match optnode with
    | Some node -> self#read_xml node
    | _ -> ()

  method reset = 
    begin
      invariants#removeList invariants#listOfKeys ;
      chlog#add "reset invariants" (STR fname)
    end

  method private add (iaddr:string) (fact:invariant_fact_t) =
    (self#get_location_invariant iaddr)#add_fact fact

  method add_symbolic_expr_fact (iaddr:string) (v:variable_t) (x:xpr_t) =
    self#add iaddr (NonRelationalFact (v,FSymbolicExpr x))

  method set_unreachable (iaddr:string) (domain:string) =
    self#add iaddr (Unreachable domain)

  method add_constant_fact (iaddr:string) (v:variable_t) (n:numerical_t) =
    self#add iaddr (NonRelationalFact (v,FIntervalValue (Some n,Some n)))

  method add_interval_fact (iaddr:string) (v:variable_t) (i:interval_t) =
    let fact =
      if i#isBottom then
	Unreachable "intervals"
      else
	NonRelationalFact
          (v,FIntervalValue (get_bound i#getMin, get_bound i#getMax)) in
    self#add iaddr fact

  method add_valueset_fact
           (iaddr:string)
           (v:variable_t)
           (base:symbol_t)
           (i:interval_t)
           (canbenull:bool) =
    let fact =
      if i#isBottom then
	Unreachable "valuesets"
      else
	let nrv =
          FBaseOffsetValue
            (base, get_bound i#getMin, get_bound i#getMax, canbenull) in
	NonRelationalFact (v,nrv) in
    self#add iaddr fact

  method add_initial_value_fact (iaddr:string) (v:variable_t) (ival:variable_t) =
    self#add iaddr (InitialVarEquality (v,ival))

  method remove_initial_value_fact
           (iaddr: string) (v: variable_t) (ival: variable_t) =
    (self#get_location_invariant iaddr)#remove_initial_value_fact v ival

  method add_initial_disequality_fact
           (iaddr:string) (v:variable_t) (ival:variable_t) =
    self#add iaddr (InitialVarDisEquality (v,ival))

  method add_test_value_fact (iaddr:string) (tvar:variable_t) (tval:variable_t) 
    (taddr:ctxt_iaddress_t) (jaddr:ctxt_iaddress_t) =
    self#add iaddr (TestVarEquality (tvar,tval,taddr,jaddr))

  method add_lineq (iaddr:string) (nc:numerical_constraint_t) =
    self#add iaddr (RelationalFact (numerical_constraint_to_linear_equality nc))

  method get_location_invariant (iaddr:string) =
    match invariants#get iaddr with
    | Some locInv -> locInv
    | _ -> 
      let locInv = new location_invariant_t invd iaddr in
      begin invariants#set iaddr locInv ; locInv end

  method get_constants k = 
    match invariants#get k with
    | Some locInv -> 
      List.fold_left (fun acc i -> 
	  if i#is_constant then
            i#get_variables @ acc
          else acc) [] locInv#get_facts
    | _ -> []

  method get_invariant_count =
    invariants#fold (fun acc _ inv -> acc + inv#get_count) 0

  method write_xml (node:xml_element_int) =
    let dNode = xmlElement "inv-dictionary" in
    let lNode = xmlElement "locations" in
    begin
      lNode#appendChildren (List.map (fun (s,locinv) ->
	let locNode = xmlElement "loc" in
	begin 
	  locNode#setAttribute "a" s ; 
	  locinv#write_xml locNode ; 
	  locNode 
	end)  invariants#listOfPairs) ;
      invd#write_xml dNode ;
      node#appendChildren [ lNode ; dNode ]
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      invd#read_xml (getc "inv-dictionary") ;
      List.iter (fun n ->
          let iaddr = n#getAttribute "a" in
          let locinv = self#get_location_invariant iaddr in
          locinv#read_xml n) ((getc "locations")#getTaggedChildren "loc")
    end

  method toPretty = 
    let pp = ref [] in
    begin
      invariants#iter (fun k v -> 
	pp := LBLOCK [ STR k ; NL ; INDENT (3, v#toPretty) ; NL ] :: !pp) ;
      LBLOCK [ STR fname ; STR ": " ; NL ; LBLOCK (List.rev !pp) ]
    end
end


let mk_invariant_io (optnode:xml_element_int option) (vard:vardictionary_int) =
  let invd = mk_invdictionary vard in
  new invariant_io_t optnode invd
