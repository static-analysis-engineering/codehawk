(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026 Aarno Labs LLC

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
open CHNumerical

(* xprlib *)
open Xprt
open XprTypes
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHLibTypes
open CCHTypesUtil

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes
open CCHCommand

module TR = CHTraceResult


type correction_t =
  | RangeCorrection of numerical_t * numerical_t * numerical_t * numerical_t
  | BoolCorrection of numerical_t


(* Primary proof obligations of a function indexed by cfg context. *)
let po_table_cache:
      (string * proof_obligation_int list * (int, proof_obligation_int list) Hashtbl.t)
        option ref = ref None


let get_context_ppos
      (fname: string) (context: program_context_int): proof_obligation_int list =
  let pos = CCHProofScaffolding.proof_scaffolding#get_proof_obligations fname in
  let table =
    match !po_table_cache with
    | Some (f, l, t) when f = fname && l == pos -> t
    | _ ->
       let t = Hashtbl.create 53 in
       begin
         List.iter (fun (po: proof_obligation_int) ->
             if po#is_ppo then
               let ix = ccontexts#index_context po#get_context#project_on_cfg in
               let entry = Option.value ~default:[] (Hashtbl.find_opt t ix) in
               Hashtbl.replace t ix (po :: entry)) pos;
         po_table_cache := Some (fname, pos, t);
         t
       end in
  Option.value ~default:[] (Hashtbl.find_opt table (ccontexts#index_context context))


(* True if there is at least one primary proof obligation in [context] that
   satisfies [f], and all of them have been proven safe. *)
let is_proven_safe_in_context
      (env: c_environment_int)
      (context: program_context_int)
      (f: po_predicate_t -> bool): bool =
  match List.filter (fun po -> f po#get_predicate)
          (get_context_ppos env#get_functionname context) with
  | [] -> false
  | pos -> List.for_all (fun po -> po#is_safe) pos


let integer_kind_of_exp (env: c_environment_int) (e: exp): ikind option =
  match type_of_exp env#get_fdecls e with
  | Ok t ->
     (match CCHFileEnvironment.file_environment#get_type_unrolled t with
      | TInt (ik, _) -> Some ik
      | _ -> None)
  | Error _ -> None


let unsigned_ikind (ty: typ): ikind option =
  match CCHFileEnvironment.file_environment#get_type_unrolled ty with
  | TInt (ik, _) when (not (is_signed_type ik)) && ik <> IBool -> Some ik
  | _ -> None


(* Value of an integer constant expression (possibly cast). *)
let rec integer_constant_value (e: exp): numerical_t option =
  match e with
  | Const (CInt (i64, ik, _)) ->
     Some (mkNumerical_big (CCHBasicUtil.cint_to_big i64 ik))
  | CastE (TInt _, e1) -> integer_constant_value e1
  | _ -> None


let unsigned_shift_factor (e2: exp) (ty: typ): numerical_t option =
  match unsigned_ikind ty with
  | Some ik ->
     let m = (get_safe_upperbound ik)#add numerical_one in   (* 2^N *)
     (match integer_constant_value e2 with
      | Some k when k#geq numerical_zero && k#lt (mkNumerical 128) ->
         let p = power_of_two k#toInt in
         if p#lt m then Some p else None
      | _ -> None)
  | None -> None


(* Drops the corrections that are excluded by a proven proof obligation
   (no_lb, no_ub) and returns None if no correction is left. *)
let mk_range_correction
      (lo: numerical_t)
      (hi: numerical_t)
      (slo: numerical_t)
      (shi: numerical_t)
      (no_lb: bool)
      (no_ub: bool): correction_t option =
  let slo = if no_lb || slo#geq lo then lo else slo in
  let shi = if no_ub || shi#leq hi then hi else shi in
  if slo#equal lo && shi#equal hi then
    None
  else
    Some (RangeCorrection (lo, hi, slo, shi))


let get_correction
      (env: c_environment_int)
      (context: program_context_int)
      (e: exp): correction_t option =
  let same e e' = CCHTypesCompare.exp_compare e e' = 0 in
  let proven = is_proven_safe_in_context env context in
  match e with
  | BinOp ((PlusA | MinusA | Mult) as op, e1, e2, ty) ->
     (match unsigned_ikind ty with
      | Some ik ->
         (* both operands are in [0, max] (usual arithmetic conversions) *)
         let max = get_safe_upperbound ik in
         let (slo, shi) =
           match op with
           | PlusA -> (numerical_zero, max#add max)
           | MinusA -> (max#neg, max)
           | _ -> (numerical_zero, max#mult max) in
         let no_lb =
           proven (fun p ->
               match p with
               | PUIntUnderflow (op', e1', e2', _) ->
                  op' = op && same e1 e1' && same e2 e2'
               | _ -> false) in
         let no_ub =
           proven (fun p ->
               match p with
               | PUIntOverflow (op', e1', e2', _) ->
                  op' = op && same e1 e1' && same e2 e2'
               | _ -> false) in
         mk_range_correction numerical_zero max slo shi no_lb no_ub
      | None -> None)
  | BinOp (Shiftlt, _, e2, ty) ->
     (* C11 6.5.7p4: for unsigned E1, E1 << E2 is E1 * 2^E2 reduced modulo
        2^N. E2 is in [0, N-1] (otherwise UB, covered by the non-negative
        and width-overflow proof obligations), so the mathematical value is
        in [0, max * 2^k] for a constant shift k, and in [0, max * 2^(N-1)]
        otherwise. There is no proof obligation for this wrap around, so the
        correction is never dropped. *)
     (match unsigned_ikind ty with
      | Some ik ->
         let max = get_safe_upperbound ik in
         let factor =
           match unsigned_shift_factor e2 ty with
           | Some p -> p
           | None -> (max#add numerical_one)#div (mkNumerical 2) in
         mk_range_correction
           numerical_zero max numerical_zero (max#mult factor) false false
      | None -> None)
  | UnOp (Neg, _, ty) ->
     (match unsigned_ikind ty with
      | Some ik ->
         let max = get_safe_upperbound ik in
         mk_range_correction numerical_zero max max#neg numerical_zero false false
      | None -> None)
  | CastE (ty, e1) ->
     (match (CCHFileEnvironment.file_environment#get_type_unrolled ty,
             integer_kind_of_exp env e1) with
      | (TInt (ikto, _), Some ikfrom) ->
         let slo = get_safe_lowerbound ikfrom in
         let shi = get_safe_upperbound ikfrom in
         if ikto = IBool then
           if ikfrom = IBool then None else Some (BoolCorrection slo)
         else
           let lo = get_safe_lowerbound ikto in
           let hi = get_safe_upperbound ikto in
           let no_lb =
             proven (fun p ->
                 match p with
                 | PSignedToUnsignedCastLB (_, ik', e')
                   | PSignedToSignedCastLB (_, ik', e') ->
                    ik' = ikto && same e1 e'
                 | _ -> false) in
           let no_ub =
             proven (fun p ->
                 match p with
                 | PSignedToUnsignedCastUB (_, ik', e')
                   | PSignedToSignedCastUB (_, ik', e')
                   | PUnsignedToSignedCast (_, ik', e')
                   | PUnsignedToUnsignedCast (_, ik', e') ->
                    ik' = ikto && same e1 e'
                 | _ -> false) in
           mk_range_correction lo hi slo shi no_lb no_ub
      | _ -> None)
  | _ -> None


let fold_constant (c: correction_t) (n: numerical_t): numerical_t =
  match c with
  | RangeCorrection (lo, hi, _, _) ->
     if n#geq lo && n#leq hi then
       n
     else
       let m = (hi#sub lo)#add numerical_one in
       let r = (n#sub lo)#modulo m in
       let r = if r#lt numerical_zero then r#add m else r in
       lo#add r
  | BoolCorrection _ ->
     if n#equal numerical_zero then numerical_zero else numerical_one


let correction_code
      (env: c_environment_int) (v: variable_t) (c: correction_t): c_cmd_t list =
  let tmpProvider = fun () -> env#mk_num_temp in
  let cstProvider = fun (n:numerical_t) -> env#mk_num_constant n in
  let x = XVar v in
  let cst (n: numerical_t) = num_constant_expr n in
  let guard (b: xpr_t) =
    let (code, bExp) = xpr2boolexpr tmpProvider cstProvider b in
    [code; make_c_cmd (make_assert bExp)] in
  let assign (rhs: xpr_t) =
    let (code, numExp) = xpr2numexpr tmpProvider cstProvider rhs in
    [code; make_c_cmd (ASSIGN_NUM (v, numExp))] in
  match c with
  | BoolCorrection slo ->
     let zero = zero_constant_expr in
     let branches =
       [(guard (XOp (XGe, [x; zero]))) @ (guard (XOp (XLe, [x; zero])));
        (guard (XOp (XGt, [x; zero]))) @ (assign (cst numerical_one))]
       @ (if slo#lt numerical_zero then
            [(guard (XOp (XLt, [x; zero]))) @ (assign (cst numerical_one))]
          else []) in
     [make_c_branch branches]
  | RangeCorrection (lo, hi, slo, shi) ->
     let m = (hi#sub lo)#add numerical_one in
     let havoc () =
       (make_c_cmd (ABSTRACT_VARS [v]))
       :: ((guard (XOp (XGe, [x; cst lo]))) @ (guard (XOp (XLe, [x; cst hi])))) in
     let low_one = slo#lt lo in
     let low_many = slo#lt (lo#sub m) in
     let high_one = shi#gt hi in
     let high_many = shi#gt (hi#add m) in
     let inrange =
       (if low_one then guard (XOp (XGe, [x; cst lo])) else [])
       @ (if high_one then guard (XOp (XLe, [x; cst hi])) else []) in
     let low1 =
       if low_one then
         [(guard (XOp (XLt, [x; cst lo])))
          @ (if low_many then guard (XOp (XGe, [x; cst (lo#sub m)])) else [])
          @ (assign (XOp (XPlus, [x; cst m])))]
       else [] in
     let lown =
       if low_many then
         [(guard (XOp (XLt, [x; cst (lo#sub m)]))) @ (havoc ())]
       else [] in
     let high1 =
       if high_one then
         [(guard (XOp (XGt, [x; cst hi])))
          @ (if high_many then guard (XOp (XLe, [x; cst (hi#add m)])) else [])
          @ (assign (XOp (XMinus, [x; cst m])))]
       else [] in
     let highn =
       if high_many then
         [(guard (XOp (XGt, [x; cst (hi#add m)]))) @ (havoc ())]
       else [] in
     if low_one || high_one then
       [make_c_branch ((inrange :: low1) @ lown @ high1 @ highn)]
     else
       []
