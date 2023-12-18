(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023  Aarno Labs LLC

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
open CHLogger
open CHXmlDocument
open CHXmlReader

(* xprlib *)
open XprTypes
open XprToPretty

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeTransformer
open BCHBCTypeXml
open BCHBTerm
open BCHCStructConstant
open BCHLibTypes
open BCHTypeDefinitions
open BCHUtilities
open BCHXmlUtil


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end
       

let rec xxpredicate_compare (p1: xxpredicate_t) (p2: xxpredicate_t): int =
  let btc = bterm_compare in
  match (p1, p2) with
  | (XXAllocationBase t1, XXAllocationBase t2) -> btc t1 t2
  | (XXAllocationBase _, _) -> -1
  | (_, XXAllocationBase _) -> 1
  | (XXBlockWrite (_, t1, _), XXBlockWrite (_, t2, _)) -> btc t1 t2
  | (XXBlockWrite _, _) -> -1
  | (_, XXBlockWrite _) -> 1
  | (XXBuffer (_, t1, _), XXBuffer (_, t2, _)) -> btc t1 t2
  | (XXBuffer _, _) -> -1
  | (_, XXBuffer _) -> 1
  | (XXEnum (t1, s1, _), XXEnum (t2, s2, _)) ->
     let l0 = btc t1 t2 in if l0 = 0 then Stdlib.compare s1 s2 else l0
  | (XXEnum _, _) -> -1
  | (_, XXEnum _) -> 1
  | (XXFalse, XXFalse) -> 0
  | (XXFalse, _) -> -1
  | (_, XXFalse) -> 1
  | (XXFreed t1, XXFreed t2) -> btc t1 t2
  | (XXFreed _, _) -> -1
  | (_, XXFreed _) -> 1
  | (XXFunctional, XXFunctional) -> 0
  | (XXFunctional, _) -> -1
  | (_, XXFunctional) -> 1
  | (XXFunctionPointer (_, t1), XXFunctionPointer (_, t2)) -> btc t1 t2
  | (XXFunctionPointer _, _) -> -1
  | (_, XXFunctionPointer _) -> 1
  | (XXIncludes (t1, _), XXIncludes (t2, _)) -> btc t1 t2
  | (XXIncludes _, _) -> -1
  | (_, XXIncludes _) -> 1
  | (XXInitialized t1, XXInitialized t2) -> btc t1 t2
  | (XXInitialized _, _) -> -1
  | (_, XXInitialized _) -> 1
  | (XXInitializedRange (_, t1, _), XXInitializedRange (_, t2, _)) -> btc t1 t2
  | (XXInitializedRange _, _) -> -1
  | (_, XXInitializedRange _) -> 1
  | (XXInputFormatString t1, XXInputFormatString t2) -> btc t1 t2
  | (XXInputFormatString _, _) -> -1
  | (_, XXInputFormatString _) -> 1
  | (XXInvalidated t1, XXInvalidated t2) -> btc t1 t2
  | (XXInvalidated _, _) -> -1
  | (_, XXInvalidated _) -> 1
  | (XXModified t1, XXModified t2) -> btc t1 t2
  | (XXModified _, _) -> -1
  | (_, XXModified _) -> 1
  | (XXNewMemory (t1, _), XXNewMemory (t2, _)) -> btc t1 t2
  | (XXNewMemory _, _) -> -1
  | (_, XXNewMemory _) -> 1
  | (XXStackAddress t1, XXStackAddress t2) -> btc t1 t2
  | (XXStackAddress _, _) -> -1
  | (_, XXStackAddress _) -> 1
  | (XXHeapAddress t1, XXHeapAddress t2) -> btc t1 t2
  | (XXHeapAddress _, _) -> -1
  | (_, XXHeapAddress _) -> 1
  | (XXGlobalAddress t1, XXGlobalAddress t2) -> btc t1 t2
  | (XXGlobalAddress _, _) -> -1
  | (_, XXGlobalAddress _) -> 1
  | (XXNoOverlap (t11, t12), XXNoOverlap (t21, t22)) ->
     let l0 = btc t11 t21 in if l0 = 0 then btc t12 t22 else l0
  | (XXNoOverlap _, _) -> -1
  | (_, XXNoOverlap _) -> 1
  | (XXNotNull t1, XXNotNull t2) -> btc t1 t2
  | (XXNotNull _, _) -> -1
  | (_, XXNotNull _) -> 1
  | (XXNull t1, XXNull t2) -> btc t1 t2
  | (XXNull _, _) -> -1
  | (_, XXNull _) -> 1
  | (XXNotZero t1, XXNotZero t2) -> btc t1 t2
  | (XXNotZero _, _) -> -1
  | (_, XXNotZero _) -> 1
  | (XXNonNegative t1, XXNonNegative t2) -> btc t1 t2
  | (XXNonNegative _, _) -> -1
  | (_, XXNonNegative _) -> 1
  | (XXNullTerminated t1, XXNullTerminated t2) -> btc t1 t2
  | (XXNullTerminated _, _) -> -1
  | (_, XXNullTerminated _) -> 1
  | (XXOutputFormatString t1, XXOutputFormatString t2) -> btc t1 t2
  | (XXOutputFormatString _, _) -> -1
  | (_, XXOutputFormatString _) -> 1
  | (XXPositive t1, XXPositive t2) -> btc t1 t2
  | (XXPositive _, _) -> -1
  | (_, XXPositive _) -> 1
  | (XXRelationalExpr (op1, t11, t12), XXRelationalExpr (op2, t21, t22)) ->
     let l0 = Stdlib.compare op1 op2 in
     if l0 = 0 then
       let l1 = btc t11 t21 in
       if l1 = 0 then
         btc t12 t22
       else
         l1
     else
       l0
  | (XXRelationalExpr _, _) -> -1
  | (_, XXRelationalExpr _) -> 1
  | (XXSetsErrno, XXSetsErrno) -> 0
  | (XXSetsErrno, _) -> -1
  | (_, XXSetsErrno) -> 1
  | (XXStartsThread (t1, tl1), XXStartsThread (t2, tl2)) ->
     let l0 = btc t1 t2 in if l0 = 0 then list_compare tl1 tl2 btc else l0
  | (XXStartsThread _, _) -> -1
  | (_, XXStartsThread _) -> 1
  | (XXTainted t1, XXTainted t2) -> btc t1 t2
  | (XXTainted _, _) -> -1
  | (_, XXTainted _) -> 1
  | (XXValidMem t1, XXValidMem t2) -> btc t1 t2
  | (XXValidMem _, _) -> -1
  | (_, XXValidMem _) -> 1
  | (XXDisjunction pl1, XXDisjunction pl2) ->
     list_compare pl1 pl2 xxpredicate_compare
  | (XXDisjunction _, _) -> -1
  | (_, XXDisjunction _) -> 1
  | (XXConditional (p11, p12), XXConditional (p21, p22)) ->
     let l0 = xxpredicate_compare p11 p21 in
     if l0 = 0 then
       xxpredicate_compare p12 p22
     else
       l0


let rec xxpredicate_terms (p: xxpredicate_t): bterm_t list =
  match p with
  | XXAllocationBase t -> [t]
  | XXBlockWrite (_, t1, t2) -> [t1; t2]
  | XXBuffer (_, t1, t2) -> [t1; t2]
  | XXEnum (t, _, _) -> [t]
  | XXFalse -> []
  | XXFreed t -> [t]
  | XXFunctional -> []
  | XXFunctionPointer (_, t) -> [t]
  | XXIncludes (t, _) -> [t]
  | XXInitialized t -> [t]
  | XXInitializedRange (_, t1, t2) -> [t1; t2]
  | XXInputFormatString t -> [t]
  | XXInvalidated t -> [t]
  | XXModified t -> [t]
  | XXNewMemory (t1, t2) -> [t1; t2]
  | XXStackAddress t -> [t]
  | XXHeapAddress t -> [t]
  | XXGlobalAddress t -> [t]
  | XXNoOverlap (t1, t2) -> [t1; t2]
  | XXNotNull t -> [t]
  | XXNull t -> [t]
  | XXNotZero t -> [t]
  | XXNonNegative t -> [t]
  | XXNullTerminated t -> [t]
  | XXOutputFormatString t -> [t]
  | XXPositive t -> [t]
  | XXRelationalExpr (_, t1, t2) -> [t1; t2]
  | XXSetsErrno -> []
  | XXStartsThread (t, tt) -> t :: tt
  | XXTainted t -> [t]
  | XXValidMem t -> [t]
  | XXDisjunction pl -> List.concat (List.map xxpredicate_terms pl)
  | XXConditional (p1, p2) ->
     (xxpredicate_terms p1) @ (xxpredicate_terms p2)


(* ----------------------------------------------------------------- printing *)

let relational_op_to_string = function
  | PEquals -> " = "
  | PLessThan -> " < "
  | PLessEqual -> " <= "
  | PGreaterThan -> " > "
  | PGreaterEqual -> " >= "
  | PNotEqual -> " != "

               
let relational_op_to_xml_string = function
  | PEquals -> "eq"
  | PLessThan -> "lt"
  | PLessEqual -> "leq"
  | PGreaterThan -> "gt"
  | PGreaterEqual -> "geq"
  | PNotEqual -> "neq"
                                

(* ---------------------------------------------------------------- operators *)

let relational_op_to_xop = function
  | PEquals -> XEq
  | PLessThan -> XLt
  | PLessEqual -> XLe
  | PGreaterThan -> XGt
  | PGreaterEqual -> XGe
  | PNotEqual -> XNe


let xop_to_relational_op op =
  match op with
  | XEq -> PEquals
  | XLt -> PLessThan
  | XLe -> PLessEqual
  | XGt -> PGreaterThan
  | XGe -> PGreaterEqual
  | XNe -> PNotEqual
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "expr operator ";
               STR (xop_to_string op);
	       STR " cannot be represented by a relational operator"]))
               
let is_relational_xop = function
  | XEq | XLt | XLe | XGt | XGe | XNe -> true
  | _ -> false
                   

let is_relational_operator (op:string) =
  match op with
  | "eq" | "neq" | "gt" | "lt" | "geq" | "leq" -> true
  | _ -> false


let get_relational_operator (op:string)  =
  match op with
  | "eq"  -> PEquals
  | "neq" -> PNotEqual
  | "gt"  -> PGreaterThan
  | "lt"  -> PLessThan
  | "geq" -> PGreaterEqual
  | "leq" -> PLessEqual
  | _ ->
    begin
      ch_error_log#add "internal error"
	(LBLOCK [ STR "get_relational_expression: " ; STR op ]) ;
      raise (Internal_error "get_relational_expression")
    end
           

let rec xxpredicate_to_pretty (p: xxpredicate_t) =
  let btp = bterm_to_pretty in
  let default (name: string) (terms: bterm_t list) =
    LBLOCK [STR name; pretty_print_list terms btp "(" ", " ")"] in
  match p with
  | XXAllocationBase t -> default "allocation-base" [t]
  | XXBlockWrite (ty, t1, t2) ->
     LBLOCK [
         STR "block-write(";
         STR (btype_to_string ty);
         STR ", ";
         btp t1;
         STR ", ";
         btp t2;
         STR ")"]
  | XXBuffer (ty, t1, t2) ->
     LBLOCK [
         STR "buffer(";
         STR (btype_to_string ty);
         STR ", ";
         btp t1;
         STR ", ";
         btp t2;
         STR ")"]
  | XXEnum (t, s, b) ->
     LBLOCK [
         btp t; STR ": member of "; STR s; (if b then STR " (flags)" else STR "")]
  | XXFalse -> STR "false"
  | XXFreed t -> default "freed" [t]
  | XXFunctional -> STR "functional"
  | XXFunctionPointer (ty, t) ->
     LBLOCK [
         STR "function-pointer(";
         STR (btype_to_string ty);
         STR ", ";
         btp t;
         STR ")"]
  | XXIncludes (t, c) ->
     LBLOCK [btp t; STR " includes "; cstructconstant_to_pretty c]
  | XXInitialized t -> default "initialized" [t]
  | XXInitializedRange (ty, t1, t2) ->
     LBLOCK [
         STR "initialize-range(";
         STR (btype_to_string ty);
         STR ", ";
         btp t1;
         STR ", ";
         btp t2;
         STR ")"]
  | XXInputFormatString t -> default "input-format-string" [t]
  | XXInvalidated t -> default "invalidated" [t]
  | XXModified t -> default "modified" [t]
  | XXNewMemory (t1, t2) -> default "new-memory" [t1; t2]
  | XXStackAddress t -> default "stack-address" [t]
  | XXHeapAddress t -> default "heap-address" [t]
  | XXGlobalAddress t -> default "global-address" [t]
  | XXNoOverlap (t1, t2) -> default "no-overlap" [t1; t2]
  | XXNotNull t -> default "not-null" [t]
  | XXNull t -> default "null" [t]
  | XXNotZero t -> default "not-zero" [t]
  | XXNonNegative t -> default "non-negative" [t]
  | XXNullTerminated t -> default "null-terminated" [t]
  | XXOutputFormatString t -> default "output-format-string" [t]
  | XXPositive t -> default "positive" [t]
  | XXRelationalExpr (op, t1, t2) ->
     LBLOCK [btp t1; STR (relational_op_to_string op); btp t2]
  | XXSetsErrno -> STR "sets errno"
  | XXStartsThread (t, tt) -> default "starts-thread" (t :: tt)
  | XXTainted t -> default "tainted" [t]
  | XXValidMem t -> default "valid-mem" [t]
  | XXDisjunction pl ->
     pretty_print_list pl xxpredicate_to_pretty "[" " || " "]"
  | XXConditional (p1, p2) ->
     LBLOCK [
         xxpredicate_to_pretty p1; STR " implies "; xxpredicate_to_pretty p2]


let rec modify_types_xxp
          (f: type_transformer_t) (p: xxpredicate_t): xxpredicate_t =
  let mt = modify_type f in
  let mbt = modify_types_bterm f in
  let mxp = modify_types_xxp f in
  match p with
  | XXAllocationBase t -> XXAllocationBase (mbt t)
  | XXBlockWrite (ty, t1, t2) -> XXBlockWrite (mt ty, mbt t1, mbt t2)
  | XXBuffer (ty, t1, t2) -> XXBuffer (mt ty, mbt t1, mbt t2)
  | XXEnum (t, s, b) -> XXEnum (mbt t, s, b)
  | XXFalse -> XXFalse
  | XXFreed t -> XXFreed (mbt t)
  | XXFunctional -> XXFunctional
  | XXFunctionPointer (ty, t) -> XXFunctionPointer (mt ty, mbt t)
  | XXIncludes (t, c) -> XXIncludes (mbt t, c)
  | XXInitialized t -> XXInitialized (mbt t)
  | XXInitializedRange (ty, t1, t2) -> XXInitializedRange (mt ty, mbt t1, mbt t2)
  | XXInputFormatString t -> XXInputFormatString (mbt t)
  | XXInvalidated t -> XXInvalidated (mbt t)
  | XXModified t -> XXModified (mbt t)
  | XXNewMemory (t1, t2) -> XXNewMemory (mbt t1, mbt t2)
  | XXStackAddress t -> XXStackAddress (mbt t)
  | XXHeapAddress t -> XXHeapAddress (mbt t)
  | XXGlobalAddress t -> XXGlobalAddress (mbt t)
  | XXNoOverlap (t1, t2) -> XXNoOverlap (mbt t1, mbt t2)
  | XXNotNull t -> XXNotNull (mbt t)
  | XXNull t -> XXNull (mbt t)
  | XXNotZero t -> XXNotZero (mbt t)
  | XXNonNegative t -> XXNonNegative (mbt t)
  | XXPositive t -> XXPositive (mbt t)
  | XXNullTerminated t -> XXNullTerminated (mbt t)
  | XXOutputFormatString t -> XXOutputFormatString (mbt t)
  | XXRelationalExpr (op, t1, t2) -> XXRelationalExpr (op, mbt t1, mbt t2)
  | XXSetsErrno -> XXSetsErrno
  | XXStartsThread (t, tt) -> XXStartsThread (mbt t, List.map mbt tt)
  | XXTainted t -> XXTainted (mbt t)
  | XXValidMem t -> XXValidMem (mbt t)
  | XXDisjunction xl -> XXDisjunction (List.map mxp xl)
  | XXConditional (x1, x2) -> XXConditional (mxp x1, mxp x2)
