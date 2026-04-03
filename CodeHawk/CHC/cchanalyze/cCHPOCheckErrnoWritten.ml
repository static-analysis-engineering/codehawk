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
open CHBounds
open CHIntervals
open CHNumerical

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open XprTypes

(* cchpre *)
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

let (let*) = Option.bind

let interval_of_bounds lb ub = 
  let l = Option.fold ~none:minus_inf_bound ~some:bound_of_num lb in
  let u = Option.fold ~none:plus_inf_bound ~some:bound_of_num ub in
  new interval_t l u

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

  method private message_of_cond (c: ErrnoP.t): string =
    let str_of_vid x = 
      let v = poq#env#get_variable_manager#get_variable x in
      pretty_to_string (v#toPretty) 
    in
    match c with
    | Unknown ->
        "(unknown)" (* This is not actually provable unless it is unreachable*)

    | True -> 
        "(unconditional)"

    | VarInt (x, lb, ub) -> 
      let name = str_of_vid x in
      let int = interval_of_bounds (Option.map mkNumerical lb) (Option.map mkNumerical ub) in
      let int_str = pretty_to_string int#toPretty in
      name ^ " in range " ^ int_str

    | VarNull x -> 
      let name = str_of_vid x in
      name ^ " is NULL"

  method private get_conditions (i: invariant_int): ErrnoP.t list option =
    match i#get_fact with
    | NonRelationalFact (_, FInitializedSet syms) -> 
      List.fold_left begin fun acc s ->
          match acc with
          | Some l -> 
            let* c = ErrnoP.from_symbol s
            in Some(c :: l)
          | None -> None
      end (Some []) syms
    | _ -> None 

  method private meet_intervals vid =
    let interval_of_inv x (i: invariant_int) = match i#get_fact with
    | NonRelationalFact (vv, _) when equalities#find (vv#getName#getSeqNumber) = equalities#find x -> 
      interval_of_bounds i#lower_bound i#upper_bound

    | ParameterConstraint e -> 
      begin match self#simplify e with
      | XOp (op, [XVar vv; XConst (IntConst c)]) when equalities#find(vv#getName#getSeqNumber) = equalities#find x ->
        begin match op with
        | XLe -> interval_of_bounds None (Some c)
        | XLt -> interval_of_bounds None (Some (c#sub numerical_one))
        | XGt -> interval_of_bounds (Some (c#add numerical_one)) None
        | XGe -> interval_of_bounds (Some c) None
        | _   -> topInterval
        end
      | _ -> topInterval
    end
    | _ -> topInterval
    in

    let refine_interval x (deps, int) (i : invariant_int) =
      let int' = int#meet (interval_of_inv x i) in
      if int'#equal int then
        (deps, int')
      else
        (i#index :: deps, int')
    in

    List.fold_left (refine_interval (equalities#find vid)) ([], interval_of_bounds None None) locinv#get_invariants
  
  method private find_constant_proof x =
    let deps, int = self#meet_intervals x in
    let* v = int#singleton in
    Some (deps, v)

  method private check_condition_safe (wc: ErrnoP.t): int list option =
    let prove_eq_this_const x c =
      let* (deps, k) = self#find_constant_proof x in
      if k#equal c then Some deps else None
    in

    match wc with
    | Unknown ->
      None

    | True -> 
      Some []

    | VarInt (v, l, u) -> 
      let spec = interval_of_bounds (Option.map mkNumerical l) (Option.map mkNumerical u) in
      let deps, v_int = self#meet_intervals v in
      CHPretty.(pr_debug [STR "VarInt: "; v_int#toPretty; STR " <= "; spec#toPretty; STR (string_of_bool (v_int#leq spec)) ; NL ]);
      if v_int#leq spec then 
        (* Computed interval is contained in spec*)
        Some deps
      else 
        None

    | VarNull v -> 
      prove_eq_this_const v numerical_zero

  method check_safe : bool = 
    let disjuncts = List.filter_map self#get_conditions invs in
    CHPretty.(pr_debug [ INT (List.length disjuncts); STR " alternative." ; NL ]);
    let check_all = 
        List.fold_left begin fun acc c -> 
          match acc with
          | Some (results) -> 
            let* deps = self#check_condition_safe c
            in Some ((deps, c) :: results)
          | _ -> None
          end (Some [])
    in
    let check_alternatives = List.find_map check_all in
    let pf = check_alternatives disjuncts in
    match pf with
    | Some results -> 
      let deps, conds = List.split results in
      let pre_msg = 
        begin match conds with
        | [] -> "(empty)" (*I think, conds is a conjunction so empty is trivially true but this shouldn't be possible*)
        | [c] -> self#message_of_cond c
        | c::cs -> List.fold_left (fun msgs c -> msgs ^", " ^ self#message_of_cond c) (self#message_of_cond c) cs
        end in
      let msg = "errno is set written if: " ^ pre_msg in
      poq#record_safe_result (DLocal (List.concat deps)) msg; true
    | _ -> false
end
let check_errno_written poq locinv = 
  let invs = poq#get_errno_write_invariants in
  let checker = new errno_written_checker_t poq locinv invs in
  checker#check_safe