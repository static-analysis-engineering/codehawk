(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs LLC

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

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes

(* bchlib *)
open BCHBCTypePretty
open BCHBTerm
open BCHCStructConstant
open BCHLibTypes
open BCHExternalPredicate


let x2p = xpr_formatter#pr_expr


let rec xxp_to_xpo_predicate
      (termev: bterm_evaluator_int)
      (loc: location_int)
      (xxp: xxpredicate_t): xpo_predicate_t =
  let btx t =
    match termev#bterm_xpr t with
    | Some x -> x
    | _ ->
       let _ =
         chlog#add
           "unable to convert bterm"
           (LBLOCK [loc#toPretty; STR " "; (bterm_to_pretty t)]) in
       random_constant_expr in

  match xxp with
  | XXAllocationBase t -> XPOAllocationBase (btx t)
  | XXBlockWrite (ty, t1, t2) -> XPOBlockWrite (ty, btx t1, btx t2)
  | XXBuffer (ty, t1, t2) -> XPOBuffer (ty, btx t1, btx t2)
  | XXEnum (t, s, b) -> XPOEnum (btx t, s, b)
  | XXFalse -> XPOFalse
  | XXFreed t -> XPOFreed (btx t)
  | XXFunctional -> XPOFunctional
  | XXFunctionPointer (ty, t) -> XPOFunctionPointer (ty, btx t)
  | XXIncludes (t, c) -> XPOIncludes (btx t, c)
  | XXInitialized t -> XPOInitialized (btx t)
  | XXInitializedRange (ty, t1, t2) -> XPOInitializedRange (ty, btx t1, btx t2)
  | XXInputFormatString t -> XPOInputFormatString (btx t)
  | XXInvalidated t -> XPOInvalidated (btx t)
  | XXModified t -> XPOModified (btx t)
  | XXNewMemory (t1, t2) -> XPONewMemory (btx t1, btx t2)
  | XXStackAddress t -> XPOStackAddress (btx t)
  | XXHeapAddress t -> XPOHeapAddress (btx t)
  | XXGlobalAddress t -> XPOGlobalAddress (btx t)
  | XXNoOverlap (t1, t2) -> XPONoOverlap (btx t1, btx t2)
  | XXNotNull t -> XPONotNull (btx t)
  | XXNull t -> XPONull (btx t)
  | XXNotZero t -> XPONotZero (btx t)
  | XXNonNegative t -> XPONonNegative (btx t)
  | XXPositive t -> XPOPositive (btx t)
  | XXNullTerminated t -> XPONullTerminated (btx t)
  | XXOutputFormatString t -> XPOOutputFormatString (btx t)
  | XXRelationalExpr (op, t1, t2) -> XPORelationalExpr (op, btx t1, btx t2)
  | XXSetsErrno -> XPOSetsErrno
  | XXStartsThread (t1, t2) -> XPOStartsThread (btx t1, List.map btx t2)
  | XXTainted t -> XPOTainted (btx t)
  | XXValidMem t -> XPOValidMem (btx t)
  | XXDisjunction xl ->
     XPODisjunction (List.map (xxp_to_xpo_predicate termev loc) xl)
  | XXConditional (x1, x2) ->
     XPOConditional (
         xxp_to_xpo_predicate termev loc x1,
         xxp_to_xpo_predicate termev loc x2)


let rec xpo_predicate_to_pretty (p: xpo_predicate_t) =
  let default (name: string) (xprs: xpr_t list) =
    LBLOCK [STR name; pretty_print_list xprs x2p "(" ", " ")"] in
  match p with
  | XPOAllocationBase t -> default "allocation-base" [t]
  | XPOBlockWrite (ty, t1, t2) ->
     LBLOCK [
         STR "block-write(";
         STR (btype_to_string ty);
         STR ", ";
         x2p t1;
         STR ", ";
         x2p t2;
         STR ")"]
  | XPOBuffer (ty, t1, t2) ->
     LBLOCK [
         STR "buffer(";
         STR (btype_to_string ty);
         STR ", ";
         x2p t1;
         STR ", ";
         x2p t2;
         STR ")"]
  | XPOEnum (t, s, b) ->
     LBLOCK [
         x2p t; STR ": member of "; STR s; (if b then STR " (flags)" else STR "")]
  | XPOFalse -> STR "false"
  | XPOFreed t -> default "freed" [t]
  | XPOFunctional -> STR "functional"
  | XPOFunctionPointer (ty, t) ->
     LBLOCK [
         STR "function-pointer(";
         STR (btype_to_string ty);
         STR ", ";
         x2p t;
         STR ")"]
  | XPOIncludes (t, c) ->
     LBLOCK [x2p t; STR " includes "; cstructconstant_to_pretty c]
  | XPOInitialized t -> default "initialized" [t]
  | XPOInitializedRange (ty, t1, t2) ->
     LBLOCK [
         STR "initialize-range(";
         STR (btype_to_string ty);
         STR ", ";
         x2p t1;
         STR ", ";
         x2p t2;
         STR ")"]
  | XPOInputFormatString t -> default "input-format-string" [t]
  | XPOInvalidated t -> default "invalidated" [t]
  | XPOModified t -> default "modified" [t]
  | XPONewMemory (t1, t2) -> default "new-memory" [t1; t2]
  | XPOStackAddress t -> default "stack-address" [t]
  | XPOHeapAddress t -> default "heap-address" [t]
  | XPOGlobalAddress t -> default "global-address" [t]
  | XPONoOverlap (t1, t2) -> default "no-overlap" [t1; t2]
  | XPONotNull t -> default "not-null" [t]
  | XPONull t -> default "null" [t]
  | XPONotZero t -> default "not-zero" [t]
  | XPONonNegative t -> default "non-negative" [t]
  | XPONullTerminated t -> default "null-terminated" [t]
  | XPOOutputFormatString t -> default "output-format-string" [t]
  | XPOPositive t -> default "positive" [t]
  | XPORelationalExpr (op, t1, t2) ->
     LBLOCK [x2p t1; STR (relational_op_to_string op); x2p t2]
  | XPOSetsErrno -> STR "sets errno"
  | XPOStartsThread (t, tt) -> default "starts-thread" (t :: tt)
  | XPOTainted t -> default "tainted" [t]
  | XPOValidMem t -> default "valid-mem" [t]
  | XPODisjunction pl ->
     pretty_print_list pl xpo_predicate_to_pretty "[" " || " "]"
  | XPOConditional (p1, p2) ->
     LBLOCK [
         xpo_predicate_to_pretty p1; STR " implies "; xpo_predicate_to_pretty p2]
