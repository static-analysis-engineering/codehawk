(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
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
open CHPretty

(* chutil *)
open CHLogger

(* cchlib *)
open CCHBasicTypes
open CCHSettings
open CCHTypesCompare
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHCheckValid
open CCHPOPredicate
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes
open CCHPOCheckBuffer
open CCHPOCheckCast
open CCHPOCheckControlledResource
open CCHPOCheckFormatCast
open CCHPOCheckCommonBase
open CCHPOCheckCommonBaseType
open CCHPOCheckAllocationBase
open CCHPOCheckInScope
open CCHPOCheckStackAddressEscape
open CCHPOCheckIndexLowerBound
open CCHPOCheckIndexUpperBound
open CCHPOCheckInitialized
open CCHPOCheckLocallyInitialized
open CCHPOCheckInitializedRange
open CCHPOCheckIntOverflow
open CCHPOCheckIntUnderflow
open CCHPOCheckUIntUnderflow
open CCHPOCheckLowerBound
open CCHPOCheckUpperBound
open CCHPOCheckNoOverlap
open CCHPOCheckNotNull
open CCHPOCheckNotZero
open CCHPOCheckNonNegative
open CCHPOCheckWidthOverflow
open CCHPOCheckNullTerminated
open CCHPOCheckOutputParameterInitialized
open CCHPOCheckOutputParameterUnaltered
open CCHPOCheckPointerCast
open CCHPOCheckPreservedAllMemory
open CCHPOCheckPtrLowerBound
open CCHPOCheckPtrUpperBound
open CCHPOCheckSignedToSignedCastLB
open CCHPOCheckSignedToSignedCastUB
open CCHPOCheckSignedToUnsignedCastLB
open CCHPOCheckSignedToUnsignedCastUB
open CCHPOCheckUnsignedToSignedCast
open CCHPOCheckUnsignedToUnsignedCast
open CCHPOCheckValidMem
open CCHPOCheckValueConstraint
open CCHPOCheckValuePreserved
open CCHPOQuery


module H = Hashtbl

module ExpCollections = CHCollections.Make
  (struct
    type t = exp
    let compare  = exp_compare
    let toPretty = exp_to_pretty
  end)

let make_record
      (p: proof_obligation_int)
      (m: dependencies_t)
      (evtxt: string)
      (status: po_status_t) =
  begin
    p#set_status status;
    p#set_explanation ~site:None evtxt;
    p#set_dependencies m;
    true
  end


let make_unreachable (p: proof_obligation_int) (domain: string) =
  let _ = chlog#add "unreachable" (STR domain) in
  make_record p (DUnreachable domain) "unreachable" Grey


class type po_checker_int =
object

  method get_result: bool
end


class po_checker_t
        (env:c_environment_int)
        (fApi:function_api_int)
        (invIO:invariant_io_int)
        (p:proof_obligation_int):po_checker_int =
object

  val fdecls = env#get_fdecls
  val context = p#get_context

  method private has_post_allocation_base _ = false

  method private has_post_global_mem _ = false

  method private check_pointer_cast (_tfrom:typ) (_tto:typ) (_e:exp) = false

  method get_result:bool =
    let poq = mk_poq env fApi invIO p in
    match p#get_predicate with
    | PAllocationBase e -> check_allocation_base poq e
    | PBuffer (e1,e2) -> check_buffer poq e1 e2
    | PCast (t1,t2,e) -> check_cast poq t1 t2 e
    | PCommonBase (e1,e2) -> check_common_base poq e1 e2
    | PCommonBaseType (e1,e2) -> check_common_base_type poq e1 e2
    | PControlledResource (r,e) -> check_controlled_resource poq r e
    | PFormatCast (t1,t2,e) -> check_format_cast poq t1  t2 e
    | PInScope e -> check_in_scope poq e
    | PStackAddressEscape (v,e) -> check_stack_address_escape poq v e
    | PIndexLowerBound e -> check_index_lower_bound poq e
    | PIndexUpperBound (e1,e2) -> check_index_upper_bound poq e1 e2
    | PInitialized lval -> check_initialized poq lval
    | PLocallyInitialized (vinfo, lval) -> check_locally_initialized poq vinfo lval
    | PInitializedRange (e1,e2) -> check_initialized_range poq e1 e2
    | PIntOverflow (op,e1,e2,k) -> check_signed_int_overflow poq op e1 e2 k
    | PUIntOverflow (op,e1,e2,k) -> check_unsigned_int_overflow poq op e1 e2 k
    | PIntUnderflow (op,e1,e2,k) -> check_int_underflow poq op e1 e2 k
    | PUIntUnderflow (op,e1,e2,k) -> check_unsigned_int_underflow poq op e1 e2 k
    | PLowerBound (t,e) -> check_lower_bound poq t e
    | PNoOverlap (e1,e2) -> check_no_overlap poq e1 e2
    | PNotNull e -> check_not_null poq e
    | PNotZero e -> check_not_zero poq e
    | PNonNegative e -> check_non_negative poq e
    | PWidthOverflow (e,k) -> check_width_overflow poq e k
    | PNullTerminated e -> check_null_terminated poq e
    | PPtrLowerBound (t,op,e1,e2) -> check_ptr_lower_bound poq t op e1 e2
    | PPtrUpperBound (t,op,e1,e2) -> check_ptr_upper_bound poq t op e1 e2
    | PPtrUpperBoundDeref (t,op,e1,e2) ->
       check_ptr_upper_bound ~strict:true poq t op e1 e2
    | PSignedToSignedCastLB (kfrom,kto,e) ->
       check_signed_to_signed_cast_lb poq kfrom kto e
    | PSignedToSignedCastUB (kfrom,kto,e) ->
       check_signed_to_signed_cast_ub poq kfrom kto e
    | PSignedToUnsignedCastLB (kfrom,kto,e) ->
       check_signed_to_unsigned_cast_lb poq kfrom kto e
    | PSignedToUnsignedCastUB (kfrom,kto,e) ->
       check_signed_to_unsigned_cast_ub poq kfrom kto e
    | PUnsignedToSignedCast (kfrom,kto,e) ->
       check_unsigned_to_signed_cast poq kfrom kto e
    | PUnsignedToUnsignedCast (kfrom,kto,e) ->
       check_unsigned_to_unsigned_cast poq kfrom kto e
    | PPointerCast (tfrom,tto,e) -> check_pointer_cast poq tfrom tto e
    | PUpperBound (t,e) -> check_upper_bound poq t e
    | PValidMem e -> check_valid_mem poq e
    | PValueConstraint e -> check_value_constraint poq e
    | PValuePreserved e -> check_value_preserved poq e
    | PPreservedAllMemory -> check_preserved_all_memory poq
    | POutputParameterInitialized (v, offset) ->
       check_outputparameter_initialized poq v offset
    | POutputParameterUnaltered (v, offset) ->
       check_outputparameter_unaltered poq v offset
    | _ -> false

end


let is_unreachable facts =
  List.fold_left (fun acc f ->
      match acc with Some _ -> acc | _ -> f#is_unreachable)
    None facts

let _check_file_assumptions _fenv _file_assumptions _p = false

let _lift_global_predicate _fenv _fnApi _id _exps _p =  false

let _lift_gac_ds_predicate _fenv _fnApi _id _p = false


(* Check if the proof obligation is
   - statement-valid (valid with information local to the statement only)
   - function-valid (valid relative to function invariants)
   - api-valid (valid relative to one or more api-assumptions )
*)
let check_proof_obligations
      (env:c_environment_int)
      (fApi:function_api_int)
      (invIO:invariant_io_int)
      (proofObligations:proof_obligation_int list) =
  List.iter (fun p ->
      let msg s =
        LBLOCK [
            STR "Failure ";
            s;
            STR " for ";
            STR (if p#is_ppo then "ppo " else "spo ");
            INT p#index;
            STR ": ";
            po_predicate_to_pretty p#get_predicate] in
      let default () =
        (* check for statement validity *)
        try
          begin
            check_ppo_validity env#get_functionname env#get_fdecls p;
            if p#is_closed then
              ()
            else if (new po_checker_t env fApi invIO p)#get_result then
              ()
          end
        with
        | CCHFailure s -> raise (CCHFailure (msg s))
        | Failure s -> raise (CCHFailure (msg (STR s))) in

      match is_unreachable
              (invIO#get_location_invariant
                 p#get_context#project_on_cfg)#get_invariants with
      | Some domain ->
         if system_settings#use_unreachability then
           ignore ((make_unreachable p domain))
         else
           begin
	     chlog#add
               "unreachable"
	       (LBLOCK [
                    location_to_pretty p#get_location;
                    STR " (domain: ";
                    STR domain;
                    STR ")"]);
             default ()
           end
      | _ ->
         default ()) proofObligations
