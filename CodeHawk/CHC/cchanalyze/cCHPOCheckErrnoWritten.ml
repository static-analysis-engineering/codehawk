(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* xprlib *)
open XprTypes

(* cchlib *)
(* open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty *)

(* cchpre *)
(* open CCHPOPredicate *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

module VarUF = CHUnionFind.Make
    (struct 
      type t = int
      let toPretty v = CHPretty.INT v
      let compare = compare
    end)

module ErrnoP = CCHErrnoWritePredicateSymbol


class errno_written_checker_t
  (poq: po_query_int)
  (locinv: location_invariant_int)
  (invs: invariant_int list) =
object (self)

  val equalities =
    begin
      let uf = new VarUF.union_find_t in
      locinv#get_invariants
      |> List.iter begin fun i -> 
          match i#get_fact with
          | NonRelationalFact (x, FSymbolicExpr (XVar y)) -> uf#union (x#getName#getSeqNumber) (y#getName#getSeqNumber)
          | _ -> ()
      end;
      uf
    end

  method private simplify = Xsimplify.simplify_xpr

  method private get_conditions (i: invariant_int): ErrnoP.t list option =
    match i#get_fact with
    | NonRelationalFact (_, FInitializedSet syms) -> 
      List.fold_left begin fun acc s ->
          match acc with
          | Some l ->
            Option.bind
             (ErrnoP.from_symbol s) 
             (fun (c : ErrnoP.t) -> Some (c :: l))
          | None -> None
      end (Some []) syms
    | _ -> None 

  method private meet_intervals vid =
    let take_opt take_second x y =
      match x, y with
      | Some x', Some y' ->  if take_second x' y' then (true, Some y') else (false, Some x')
      | Some x', None -> false, Some x'
      | None, Some y' -> false, Some y'
      | _ -> false, None
    in

    let exact_interval x (i : invariant_int) = 
      match i#get_fact with
      | NonRelationalFact (vv, FIntervalValue (Some lb, Some ub)) when 
        equalities#find (vv#getName#getSeqNumber) = (equalities#find x) && lb#equal ub -> Some lb
      | _ -> None
    in

    let interval_of_inv x (i: invariant_int) = match i#get_fact with
    | NonRelationalFact (vv, _) when equalities#find (vv#getName#getSeqNumber) = equalities#find x -> 
      i#lower_bound, i#upper_bound
    | ParameterConstraint e -> 
      begin match self#simplify e with
      | XOp (op, [XVar vv; XConst (IntConst c)]) when equalities#find(vv#getName#getSeqNumber) = equalities#find x ->
        begin match op with
        | XLe -> None, Some (c)
        | XLt -> None, Some (c#sub numerical_one)
        | XGt -> Some (c#add numerical_one), None
        | XGe -> Some c, None
        | _   -> None, None
        end
      | _ -> None, None
    end
    | _ -> None, None
    in

    let refine_interval x (deps, lb, ub) (i : invariant_int) =
      let lbi, ubi = interval_of_inv x i in
      let improved_l, lb' = take_opt (fun x y -> y#gt x) lb lbi in
      let improved_u, ub' = take_opt (fun x y -> y#lt x) ub ubi in
      let deps' = if improved_l || improved_u then i#index :: deps else deps in
      (deps', lb', ub')
    in

    let meet_invariants x (deps, lb, ub) i =
      match exact_interval x i with   
      | Some v -> ([i#index], Some v, Some v)
      | _ -> refine_interval x (deps, lb, ub) i
    in

    List.fold_left (meet_invariants (equalities#find vid)) ([], None, None) locinv#get_invariants
  
  method private find_constant_proof x =
    match self#meet_intervals x with
      | deps, Some lb, Some ub when lb#equal ub -> Some (deps, lb)
      | _ -> None

  method private check_condition_safe (wc: ErrnoP.t): dependencies_t option =
    let prove_eq_this_const x c =
      Option.bind (self#find_constant_proof x) begin fun (deps, k) ->
        if k#equal c then Some (DLocal deps) else None
      end
    in

    match wc with
    | True -> 
      Some (DLocal [])

    | VarInt (v, l, u) -> 
      let deps, l', u' = self#meet_intervals v in

      (* Check computed interval is within bound of requested (l, u)*)
      let lt_ok = match l, l' with
      | None, _ -> true
      | Some l_spec, Some l_found -> (mkNumerical l_spec)#leq l_found
      | _ -> false
      in let ub_ok = match u, u' with
      | None, _ -> true
      | Some u_spec, Some u_found -> u_found#leq (mkNumerical u_spec)
       | _ -> false
      in if lt_ok && ub_ok then Some (DLocal deps) else None

    | VarNull v -> 
      prove_eq_this_const v numerical_zero

  method check_safe : bool = 
    let disjuncts = List.filter_map self#get_conditions invs in
    let check_all = 
        List.fold_left begin fun acc c -> 
          match acc with
          | Some (_) -> 
            Option.bind (self#check_condition_safe c) (fun _ -> Some (DLocal []))
          | _ -> None
          end (Some (DLocal []))
    in
    let check_alternatives = List.find_map check_all in
    let pf = check_alternatives disjuncts in
    match pf with
    | Some deps -> 
      poq#record_safe_result deps ":)"; true
    | _ -> false

end
let check_errno_written poq locinv = 
  let invs = poq#get_errno_write_invariants in
  let checker = new errno_written_checker_t poq locinv invs in
  checker#check_safe