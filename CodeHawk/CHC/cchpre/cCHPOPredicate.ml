(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024-2025 Aarno Labs LLC

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

(* cchlib *)
open CCHBasicTypes
open CCHExternalPredicate
open CCHFileEnvironment
open CCHLibTypes
open CCHSumTypeSerializer
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesTransformer
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHPreSumTypeSerializer
open CCHPreTypes


let po_predicate_tag p =
  match p with
  | PAllocationBase _ -> "allocation-base"
  | PCast _ -> "cast"
  | PCommonBase _ -> "common-base"
  | PCommonBaseType _ -> "common-base-type"
  | PControlledResource _ -> "controlled-resource"
  | PFormatCast _ -> "format-cast"
  | PFormatString _ -> "format-string"
  | PIndexLowerBound _ -> "index-lower-bound"
  | PIndexUpperBound _ -> "index-upper-bound"
  | PInitialized _ -> "initialized"
  | PLocallyInitialized _ -> "locally-initialized"
  | PInitializedRange _ -> "initialized-range"
  | PInScope _ -> "in-scope"
  | PIntOverflow _ -> "int-overflow"
  | PIntUnderflow _ ->  "int-underflow"
  | PLowerBound _ -> "lower-bound"
  | PNonNegative _ -> "non-negative"
  | PNoOverlap _ -> "no-overlap"
  | PNotNull _ -> "not-null"
  | PNotZero _ -> "not-zero"
  | PNull _ -> "null"
  | PNullTerminated _ -> "null-terminated"
  | PPointerCast _ -> "pointer-cast"
  | PPtrLowerBound _ -> "pointer-lower-bound"
  | PPtrUpperBound _ -> "pointer-upper-bound"
  | PPtrUpperBoundDeref _ ->  "pointer-upper-bound-deref"
  | PStackAddressEscape _ -> "stack-address-escape"
  | PSignedToSignedCastLB _ -> "signed-to-signed-cast-lb"
  | PSignedToSignedCastUB _ -> "signed-to-signed-cast-ub"
  | PSignedToUnsignedCastLB _ -> "signed-to-unsigned-cast-lb"
  | PSignedToUnsignedCastUB _ -> "signed-to-unsigned-cast-ub"
  | PTypeAtOffset _ -> "type-at-offset"
  | PUIntOverflow _ -> "uint-overflow"
  | PUIntUnderflow _ -> "uint-underflow"
  | PUnsignedToSignedCast _ -> "unsigned-to-signed-cast"
  | PUnsignedToUnsignedCast _ -> "unsigned-to-signed-cast"
  | PUpperBound _ -> "upper-bound"
  | PValueConstraint _ -> "value-constraint"
  | PVarArgs _ -> "var-args"
  | PWidthOverflow _ -> "width-overflow"
  | PValidMem _ -> "valid-mem"
  | PPreservedAllMemory -> "preserved-all-memory"
  | PPreservedAllMemoryX _ -> "preserved-all-memory-x"
  | POutputParameterInitialized _ -> "outputparameter-initialized"
  | POutputParameterUnaltered _ -> "outputparameter-unaltered"
  | _ -> "misc"


class po_predicate_walker_t =
object (self)

  method walk_varinfo (_index: int) (_v: varinfo) = ()

  method walk_exp (_index:int) (_e:exp) = ()

  method walk_type (_index:int) (_t:typ) = ()

  method walk_lval (index:int) ((lhost,offset):lval) =
    begin
      (match lhost with Var _ -> () | Mem e -> self#walk_exp index e);
      self#walk_offset index offset
    end

  method walk_offset (index:int) (o:offset) =
    match o with
    | Index (e,offset) ->
      begin self#walk_exp index e; self#walk_offset index offset end
    | Field (_,offset) -> self#walk_offset index offset
    | _ -> ()

  method walk_predicate (p:po_predicate_t) =
    let we = self#walk_exp in
    let wt = self#walk_type in
    let wl = self#walk_lval in
    let wv = self#walk_varinfo in
    let wo = self#walk_offset in
    match p with
    | PNotNull e | PNull e | PValidMem e | PInScope e
      | PControlledResource (_, e)
      | PAllocationBase e
      | PGlobalAddress e | PHeapAddress e
      | PDistinctRegion (e, _)
      | PNewMemory  e -> we 1 e
    | PTypeAtOffset (t, e) | PLowerBound (t, e) | PUpperBound (t, e) ->
       begin
         wt 1 t;
         we 2 e
       end
    | PIndexLowerBound e -> we 1 e
    | PIndexUpperBound (e1,e2) ->
       begin
         we 1 e1;
         we 2 e2
       end
    | PInitialized l -> wl 1 l
    | PLocallyInitialized (v, l) ->
       begin
         wv 1 v;
         wl 2 l;
       end
    | PStackAddressEscape (None,e) -> we 2 e
    | PStackAddressEscape (Some l,e) ->
       begin
         wl 1 l;
         we 2 e
       end
    | PInitializedRange (base,e) ->
       begin
         we 1 base;
         we 2 e
       end
    | PCast (t1,t2,e) ->
       begin
         wt 1 t1;
         wt 2 t2;
         we 3 e
       end
    | PFormatCast (t1,t2,e) ->
       begin
         wt 1 t1;
         wt 2 t2;
         we 3 e
       end
    | PPointerCast (t1,t2,e) ->
       begin
         wt 1 t1;
         wt 2 t2;
         we 3 e
       end
    | PSignedToUnsignedCastLB (_, _, e)
      | PSignedToUnsignedCastUB (_, _, e)
      | PUnsignedToSignedCast (_, _, e)
      | PUnsignedToUnsignedCast (_, _, e)
      | PSignedToSignedCastLB (_, _, e)
      | PSignedToSignedCastUB (_, _, e) -> we 3 e
    | PNotZero e
    | PNonNegative e
    | PWidthOverflow (e, _)
    | PNullTerminated e -> we 1 e
    | PIntUnderflow (_, e1, e2, _)
      | PIntOverflow (_, e1, e2, _)
      | PUIntUnderflow (_, e1, e2, _)
      | PUIntOverflow (_, e1, e2, _) ->
       begin
         we 2 e1;
         we 3 e2
       end
    | PBuffer (e1, e2) ->
       begin
         we 1 e1;
         we 2 e2
       end
    | PRevBuffer (e1, e2) ->
       begin
         we 1 e1;
         we 2 e2
       end
    | PPtrLowerBound (t, _, e1, e2)
      | PPtrUpperBound (t, _, e1, e2) ->
       begin
         wt 1 t;
         we 3 e1;
         we 4 e2
       end
    | PPtrUpperBoundDeref (t, _, e1, e2) ->
       begin
         wt 1 t;
         we 3 e1;
         we 4 e2
       end
    | PCommonBase (e1,e2)
      | PCommonBaseType (e1,e2) ->
       begin
         we 1 e1;
         we 2 e2
       end
    | PFormatString e -> we 1 e
    | PVarArgs (e, _n, el) ->
       begin
         we 1 e;
         List.iteri (fun i e -> we (i+3) e) el
       end
    | PNoOverlap (e1,e2) ->
       begin
         we 1 e1;
         we 2 e2
       end
    | PValueConstraint e -> we 1 e
    | PDSCondition (_, e) -> we 1 e
    | PMemoryPreserved e -> we 1 e
    | PValuePreserved e -> we 1 e
    | PConfined e -> we 1 e
    | PUniquePointer e -> we 1 e
    | PContract (_, _, e) -> we 1 e
    | PPreservedAllMemory -> ()
    | PPreservedAllMemoryX l -> List.iteri (fun i e -> we (i+1) e) l
    | PContractObligation _ -> ()
    | POutputParameterInitialized (v, o) ->
       begin
         wv 1 v;
         wo 2 o
       end
    | POutputParameterUnaltered (v, o) ->
       begin
         wv 1 v;
         wo 2 o
       end

end


class find_exp_walker_t (pred:(exp -> bool))=
object

  inherit exp_walker_t as super

  val mutable result = []

  method! walk_exp (exp:exp) =
    if pred exp then result <- exp :: result else super#walk_exp exp

  method get_result = result

end


class _find_var_walker_t =
object

  inherit exp_walker_t as super

  val mutable result = []

  method! walk_lhost (lhost:lhost) =
    match lhost with
    | Var (_,vid) -> result <- vid :: result
    | Mem e -> super#walk_exp e

  method get_result = result

end


class collect_predicate_expressions_t =
object

  inherit po_predicate_walker_t

  val mutable exps = []

  method! walk_exp index e = exps <- (index, e) :: exps

  method! walk_lval index l = exps <- (index, Lval l) :: exps

  method get_indexed_expressions = exps

end


let collect_indexed_predicate_expressions (p:po_predicate_t) =
  let walker = new collect_predicate_expressions_t in
  let _ = walker#walk_predicate p in
  walker#get_indexed_expressions


class _predicate_get_exp_walker_t (walker:find_exp_walker_t) =
object

  inherit po_predicate_walker_t

  method! walk_exp _index e = walker#walk_exp e

  method get_result = walker#get_result

end


let po_predicate_to_full_pretty p =
  match p with
  | PNotNull e -> LBLOCK [STR "not-null("; exp_to_pretty e; STR ")"]
  | PGlobalAddress e ->
     LBLOCK [STR "global-address("; exp_to_pretty e; STR ")"]
  | PHeapAddress e -> LBLOCK [STR "heap-address("; exp_to_pretty e; STR ")"]
  | PControlledResource (r, e) ->
     LBLOCK [
         STR "controlled-resource:";
         STR r;
         STR "(";
         exp_to_pretty e;
         STR ")"]
  | PNull e -> LBLOCK [STR "null("; exp_to_pretty e; STR ")"]
  | PValidMem e -> LBLOCK [STR "valid-mem("; exp_to_pretty e; STR ")"]
  | PInScope e -> LBLOCK [STR "in-scope("; exp_to_pretty e; STR ")"]
  | PStackAddressEscape (None, e) ->
     LBLOCK [STR "stack-address-escape("; exp_to_pretty e; STR  ")"]
  | PStackAddressEscape (Some v, e) ->
     LBLOCK [
         STR "stack-address-escape(";
         lval_to_pretty v;
         STR ",";
         exp_to_pretty e;
         STR ")"]
  | PAllocationBase e ->
    LBLOCK [STR "allocation-base("; exp_to_pretty e; STR ")"]
  | PTypeAtOffset (t, e) ->
     LBLOCK [
         STR "type-compatible(";
         typ_to_pretty t;
         STR ", region-type(";
	 exp_to_pretty e;
	 STR "), ";
         STR "offset(";
         exp_to_pretty e;
         STR "))"]
  | PLowerBound (t, e) ->
     LBLOCK [
         STR "index(";
         typ_to_pretty t;
         STR ", offset(";
         exp_to_pretty e;
	 STR ")) >= 0"]
  | PUpperBound (t, e) ->
     LBLOCK [
         STR "index(";
         typ_to_pretty t;
         STR ", offset(";
         exp_to_pretty e;
	 STR ")) < range(";
         typ_to_pretty t;
         STR ", offset(";
	 exp_to_pretty e;
         STR "))"]
  | PIndexLowerBound e -> LBLOCK [exp_to_pretty e; STR " >= 0 "]
  | PIndexUpperBound (e1, e2) ->
    LBLOCK [exp_to_pretty e1; STR " < "; exp_to_pretty e2]
  | PInitialized lval ->
     LBLOCK [STR "initialized("; lval_to_pretty lval; STR ")"]
  | PLocallyInitialized (vinfo, lval) ->
     LBLOCK [
         STR "locally-initialized(";
         STR vinfo.vname;
         STR ",";
         lval_to_pretty lval;
         STR ")"]
  | PInitializedRange (base, len) ->
     LBLOCK [
         STR "initialized-range(";
         exp_to_pretty base;
         STR ",";
	 exp_to_pretty len;
         STR ")"]
  | PCast (fromt, tot, e) ->
     LBLOCK [
         STR "cast((";
         typ_to_pretty fromt;
         STR ") ";
         exp_to_pretty e;
	 STR ": ";
         typ_to_pretty tot;
         STR ")"]
  | PFormatCast (fromt, tot, e) ->
     LBLOCK [
         STR "format-cast((";
         typ_to_pretty fromt;
         STR ")";
         exp_to_pretty e;
         STR  ": " ;
         typ_to_pretty tot;
         STR  ")"]
  | PPointerCast (fromt, tot, e) ->
     LBLOCK [
         STR "pointer-cast((";
         typ_to_pretty fromt;
         STR ") ";
	 exp_to_pretty e;
         STR ": ";
         typ_to_pretty tot;
         STR ")"]
  | PSignedToUnsignedCastLB (fromt, tot, e) ->
     LBLOCK [
         STR "signed-to-unsigned-cast-lb((";
	 STR (int_type_to_string fromt);
         STR ") ";
	 exp_to_pretty e;
         STR ": ";
	 STR (int_type_to_string tot);
         STR ")"]
  | PSignedToUnsignedCastUB (fromt, tot, e) ->
     LBLOCK [
         STR "signed-to-unsigned-cast-ub((";
	 STR (int_type_to_string fromt);
         STR ") ";
	 exp_to_pretty e;
         STR ": ";
	 STR (int_type_to_string tot);
         STR ")"]
  | PUnsignedToSignedCast (fromt, tot, e) ->
     LBLOCK [
         STR "unsigned-to-signed-cast((";
	 STR (int_type_to_string fromt);
         STR ") ";
	 exp_to_pretty e;
         STR ": ";
	 STR (int_type_to_string tot);
         STR ")"]
  | PUnsignedToUnsignedCast (fromt,tot,e) ->
     LBLOCK [
         STR "unsigned-to-unsigned-cast((";
	 STR (int_type_to_string fromt);
         STR ") ";
	 exp_to_pretty e;
         STR ": ";
	 STR (int_type_to_string tot);
         STR ")"]
  | PSignedToSignedCastLB (fromt, tot, e) ->
     LBLOCK [
         STR "signed-to-signed-cast-lb((";
	 STR (int_type_to_string fromt);
         STR ") ";
	 exp_to_pretty e;
         STR ": ";
	 STR (int_type_to_string tot);
         STR ")"]
  | PSignedToSignedCastUB (fromt, tot, e) ->
     LBLOCK [
         STR "signed-to-signed-cast-ub((";
	 STR (int_type_to_string fromt);
         STR ") ";
	 exp_to_pretty e;
         STR ": ";
	 STR (int_type_to_string tot);
         STR ")"]
  | PNotZero e -> LBLOCK [exp_to_pretty e; STR " != 0 "]
  | PNonNegative e -> LBLOCK [exp_to_pretty e; STR " >= 0 "]
  | PNullTerminated e ->
    LBLOCK [STR "null-terminated("; exp_to_pretty e; STR ")"]
  | PIntUnderflow (op, e1, e2, ik) ->
     LBLOCK [
         exp_to_pretty e1;
         STR (binop_mfts#ts op);
         exp_to_pretty e2;
	 STR " >= MIN(";
         STR (int_type_to_string ik);
         STR ")"]
  | PIntOverflow (op, e1, e2, ik) ->
     LBLOCK [
         exp_to_pretty e1;
         STR (binop_mfts#ts op);
         exp_to_pretty e2;
	 STR " <= MAX(";
         STR (int_type_to_string ik);
         STR ")"]
  | PUIntUnderflow (op, e1, e2, _ik) ->
     LBLOCK [
         exp_to_pretty e1;
         STR (binop_mfts#ts op);
         exp_to_pretty e2;
	 STR " >= 0 "]
  | PUIntOverflow (op, e1, e2, ik) ->
     LBLOCK [
         exp_to_pretty e1;
         STR (binop_mfts#ts op);
         exp_to_pretty e2;
	 STR " <= MAX(";
         STR (int_type_to_string ik);
         STR ")"]
  | PWidthOverflow (e, ik) ->
     LBLOCK [
         exp_to_pretty e;
         STR " < max-width(";
         STR (int_type_to_string ik);
         STR ")"]
  | PPtrLowerBound (t, op, e1, e2) ->
     LBLOCK [
         STR "index(";
         typ_to_pretty t;
         STR ", ";
	 STR "offset(";
         exp_to_pretty e1;
	 STR (binop_mfts#ts op);
         exp_to_pretty e2;
         STR " >= 0"]
  | PPtrUpperBound (t, op, e1, e2) ->
     LBLOCK [
         STR "index(";
         typ_to_pretty t;
         STR ", ";
	 STR "offset(";
         exp_to_pretty e1;
         STR ") ";
	 STR (binop_mfts#ts op);
         exp_to_pretty e2;
	 STR " < range(";
         typ_to_pretty t;
         STR ", ";
	 STR "offset(";
         exp_to_pretty e1;
	 STR "))"]
  | PPtrUpperBoundDeref (t, op, e1, e2) ->
     LBLOCK [
         STR "index(";
         typ_to_pretty t;
         STR ", ";
         STR "offset(";
	 exp_to_pretty e1;
         STR ") ";
	 STR (binop_mfts#ts op);
         exp_to_pretty e2;
	 STR " < range(";
         typ_to_pretty t;
         STR ", ";
	 STR "offset(";
         exp_to_pretty e1;
	 STR "))"]
  | PCommonBase (e1, e2) ->
     LBLOCK [
         STR "common-base(";
         exp_to_pretty e1;
         STR ", ";
         exp_to_pretty e2;
         STR ")"]
  | PBuffer (e1, e2) ->
     LBLOCK [
         STR "buffer(";
         exp_to_pretty e1;
         STR ", ";
         exp_to_pretty e2;
         STR ")"]
  | PRevBuffer (e1, e2) ->
     LBLOCK [
         STR "rev-buffer(";
         exp_to_pretty e1;
         STR ", ";
         exp_to_pretty e2;
         STR ")"]
  | PCommonBaseType (e1, e2) ->
     LBLOCK [
         STR "common-basetype(";
         exp_to_pretty e1;
         STR ", ";
	 exp_to_pretty e2;
         STR ")"]
  | PFormatString e ->
     LBLOCK [STR "format-string("; exp_to_pretty e; STR ")"]
  | PVarArgs (e, n, el) ->
     LBLOCK [
         STR "var-args(fmt:";
         exp_to_pretty e;
         STR "; req-argcount: ";
         INT n;
         STR "; args: ";
         pretty_print_list el exp_to_pretty "[" "," "]"]
  | PNoOverlap (e1, e2) ->
     LBLOCK [
         STR "no-overlap(";
         exp_to_pretty e1;
         STR ",";
	 exp_to_pretty e2;
         STR ")"]
  | PNewMemory e -> LBLOCK [STR "new-memory("; exp_to_pretty e; STR ")"]
  | PDistinctRegion (e, i) ->
     LBLOCK [STR "distinct-region("; exp_to_pretty e; STR ","; INT i; STR ")"]
  | PValueConstraint e ->
     LBLOCK [STR "value-constraint("; exp_to_pretty e; STR ")"]
  | PDSCondition (c, e) ->
     LBLOCK [
         STR "data-structure-condition(";
         STR c.dsc_name;
         STR ", ";
         exp_to_pretty e;
         STR ")"]
  | PMemoryPreserved e ->
     LBLOCK [STR "preserves-memory("; exp_to_pretty e; STR ")"]
  | PValuePreserved e ->
     LBLOCK [STR "preserves-value("; exp_to_pretty e; STR ")"]
  | PContract (fid,name,e) ->
     LBLOCK [
         STR "contract(";
         INT fid;
         STR ",";
         STR name;
         STR ",";
         exp_to_pretty e;
         STR ")"]
  | PConfined e ->
     LBLOCK [STR "confined("; exp_to_pretty e; STR ")"]
  | PUniquePointer e ->
     LBLOCK [STR "unique-pointer("; exp_to_pretty e; STR ")"]
  | PPreservedAllMemory -> STR "preserved-all-memory"
  | PPreservedAllMemoryX l ->
     LBLOCK [
         STR "preserved-all-memory-x";
         pretty_print_list l exp_to_pretty "(" "," ")"]
  | PContractObligation s -> LBLOCK [STR  "contract-obligation:"; STR s]
  | POutputParameterInitialized (vinfo, offset) ->
     LBLOCK [
         STR "outputparameter-initialized(";
         STR vinfo.vname;
         STR ", ";
         offset_to_pretty offset;
         STR ")"]
  | POutputParameterUnaltered (vinfo, offset) ->
     LBLOCK [
         STR "outputparameter-unaltered(";
         STR vinfo.vname;
         STR ", ";
         offset_to_pretty offset;
         STR ")"]


let pr_expr op e1 e2 t = exp_to_pretty (BinOp (op, e1, e2,t ))


let po_predicate_to_pretty ?(full=false) (p:po_predicate_t) =
  let pe = exp_to_pretty in
  let pl = lval_to_pretty in
  if full then po_predicate_to_full_pretty p else
    match p with
    | PControlledResource (r, e) ->
       LBLOCK [STR "controlled-resource:"; STR r; STR "("; pe e;  STR ")"]
    | PGlobalAddress e ->
       LBLOCK [STR "global-address("; exp_to_pretty e; STR ")"]
    | PHeapAddress e -> LBLOCK [STR "heap-address("; exp_to_pretty e; STR ")"]
    | PNotNull e -> LBLOCK [STR "not-null("; pe e; STR ")"]
    | PNull e -> LBLOCK [STR "null("; pe e; STR ")"]
    | PValidMem e -> LBLOCK [STR "valid-mem("; pe e; STR ")"]
    | PInScope e -> LBLOCK [STR "in-scope("; pe e; STR ")"]
    | PStackAddressEscape (None, e) ->
       LBLOCK [STR "stack-address-escape("; exp_to_pretty e; STR  ")"]
    | PStackAddressEscape (Some v, e) ->
       LBLOCK [STR "stack-address-escape("; pl v; STR ", "; pe e; STR ")"]
    | PAllocationBase e -> LBLOCK [STR "allocation-base("; pe e; STR ")"]
    | PNewMemory e -> LBLOCK [STR "new-memory("; pe e; STR ")"]
    | PDistinctRegion (e, i) ->
       LBLOCK [STR "distinct-region("; exp_to_pretty e; STR ","; INT i; STR ")"]
    | PTypeAtOffset (t, e) ->
       LBLOCK [
           STR "type-compatible(";
           typ_to_pretty t;
           STR ", region-type(";
	   pe e;
           STR "), offset(";
           pe e;
           STR "))"]
    | PLowerBound (t, e) ->
       LBLOCK [STR "lower-bound("; typ_to_pretty t; STR ", "; pe e; STR ")"]
    | PUpperBound (t, e) ->
       LBLOCK [STR "upper-bound("; typ_to_pretty t; STR ", "; pe e; STR ")"]
    | PIndexLowerBound e -> LBLOCK [STR "index-lowerbound("; pe e; STR ")"]
    | PIndexUpperBound (e1, e2) ->
       LBLOCK [STR "index-upperbound("; pe e1; STR ","; pe e2; STR ")"]
    | PInitialized lval -> LBLOCK [STR "initialized("; pl lval; STR ")"]
  | PLocallyInitialized (vinfo, lval) ->
     LBLOCK [
         STR "locally-initialized("; STR vinfo.vname; STR ","; pl lval; STR ")"]
    | PInitializedRange (base, len) ->
      LBLOCK [STR "initialized-range("; pe base; STR ", "; pe len; STR ")"]
    | PCast (fromt, tot, e) ->
       LBLOCK [
           STR "cast((";
           typ_to_pretty fromt;
           STR ") ";
           pe e;
           STR ": ";
	   typ_to_pretty tot;
           STR ")"]
    | PFormatCast (fromt, tot, e) ->
       LBLOCK [
           STR "format-cast((";
           typ_to_pretty fromt;
           STR ")";
           exp_to_pretty e;
           STR  ": " ;
           typ_to_pretty tot;
           STR  ")"]
    | PPointerCast (fromt, tot, e) ->
       LBLOCK [
           STR "pointer-cast((";
           typ_to_pretty fromt;
           STR ") ";
           pe e;
	   STR ": ";
           typ_to_pretty tot;
           STR ")"]
    | PSignedToUnsignedCastLB (fromt, tot, e) ->
       LBLOCK [
           STR "signed-to-unsigned-cast-lb((";
           STR (int_type_to_string fromt);
	   STR ") ";
           pe e;
           STR ": ";
           STR (int_type_to_string tot);
           STR ")"]
    | PSignedToUnsignedCastUB (fromt, tot, e) ->
       LBLOCK [
           STR "signed-to-unsigned-cast-ub((";
           STR (int_type_to_string fromt);
	   STR ") ";
           pe e;
           STR ": ";
           STR (int_type_to_string tot);
           STR ")"]
    | PUnsignedToSignedCast (fromt, tot, e) ->
       LBLOCK [
           STR "unsigned-to-signed-cast((";
           STR (int_type_to_string fromt);
	   STR ") ";
           pe e;
           STR ": ";
           STR (int_type_to_string tot);
           STR ")"]
    | PUnsignedToUnsignedCast (fromt, tot, e) ->
       LBLOCK [
           STR "unsigned-to-unsigned-cast((";
           STR (int_type_to_string fromt);
	   STR ") ";
           pe e;
           STR ": ";
           STR (int_type_to_string tot);
           STR ")"]
    | PSignedToSignedCastLB (fromt, tot, e) ->
       LBLOCK [
           STR "signed-to-signed-cast-lb((";
           STR (int_type_to_string fromt);
	   STR ") ";
           pe e;
           STR ": ";
           STR (int_type_to_string tot);
           STR ")"]
    | PSignedToSignedCastUB (fromt, tot, e) ->
       LBLOCK [
           STR "signed-to-signed-cast-ub((";
           STR (int_type_to_string fromt);
	   STR ") ";
           pe e;
           STR ": ";
           STR (int_type_to_string tot);
           STR ")"]
    | PNotZero e -> LBLOCK [pe e; STR " != 0"]
    | PNonNegative e -> LBLOCK [pe e; STR " >= 0"]
    | PNullTerminated e -> LBLOCK [STR "null-terminated("; pe e; STR ")"]
    | PIntUnderflow (op, e1, e2, ik) ->
       LBLOCK [
           STR "int-underflow(";
           pr_expr op e1 e2 (TInt (ik,[]));
	   STR ", ";
           STR (int_type_to_string ik);
           STR ")"]
    | PIntOverflow (op, e1, e2, ik) ->
       LBLOCK [
           STR "uint-overflow(";
           pr_expr op e1 e2 (TInt (ik, []));
	   STR ", ";
           STR (int_type_to_string ik);
           STR ")"]
    | PUIntUnderflow (op, e1, e2, ik) ->
       LBLOCK [
           STR "uint-underflow(";
           pr_expr op e1 e2 (TInt (ik, []));
	   STR ", ";
           STR (int_type_to_string ik);
           STR ")"]
    | PUIntOverflow (op, e1, e2, ik) ->
       LBLOCK [
           STR "uint-overflow(";
           pr_expr op e1 e2 (TInt (ik, []));
	   STR ", ";
           STR (int_type_to_string ik);
           STR ")"]
    | PWidthOverflow (e, ik) ->
       LBLOCK [
           STR "width-overflow(";
           pe e;
	   STR ", ";
           STR (int_type_to_string ik);
           STR ")"]
    | PPtrLowerBound (t, op, e1, e2) ->
      LBLOCK [STR "ptr-lowerbound("; pr_expr op e1 e2 t; STR ")"]
    | PPtrUpperBound (t, op, e1, e2) ->
      LBLOCK [STR "ptr-upperbound("; pr_expr op e1 e2 t; STR ")"]
    | PPtrUpperBoundDeref (t, op, e1, e2) ->
      LBLOCK [STR "ptr-upperbound-deref("; pr_expr op e1 e2 t; STR ")"]
    | PCommonBase (e1, e2) ->
      LBLOCK [STR "common-base("; pe e1; STR ", "; pe e2; STR ")"]
    | PCommonBaseType (e1, e2) ->
      LBLOCK [STR "common-base("; pe e1; STR ", "; pe e2; STR ")"]
    | PFormatString e ->
      LBLOCK [STR "format-string("; pe e; STR ")"]
    | PVarArgs (e, n, el) ->
       LBLOCK [
           STR "var-args(fmt:";
           exp_to_pretty e;
           STR "; req-argcount: ";
           INT n;
           STR "; args: ";
           pretty_print_list el exp_to_pretty "[" "," "]"]
    | PNoOverlap (e1, e2) ->
       LBLOCK [STR "no-overlap("; pe e1; STR ", "; pe e2; STR ")"]
    | PBuffer (e1, e2) ->
       LBLOCK [STR "buffer("; pe e1; STR  ", "; pe e2; STR ")"]
    | PRevBuffer (e1, e2) ->
       LBLOCK [STR "rev-buffer("; pe e1; STR  ", "; pe e2; STR ")"]
    | PValueConstraint e ->
       LBLOCK [STR "value_constraint("; pe e; STR ")"]
    | PDSCondition (c, e) ->
       LBLOCK [
           STR "data-structure-condition(";
           STR c.dsc_name;
           STR ", ";
           pe e;
           STR ")"]
    | PMemoryPreserved e ->
       LBLOCK [STR "preserves-memory("; exp_to_pretty e; STR ")"]
    | PValuePreserved e ->
       LBLOCK [STR "preserves-value("; exp_to_pretty e; STR ")"]
    | PContract (fid, name, e) ->
       LBLOCK [
           STR "contract(";
           INT fid;
           STR ",";
           STR name; STR ",";
           exp_to_pretty e;
           STR ")"]
    | PConfined e ->
       LBLOCK [STR "confined("; exp_to_pretty e; STR ")"]
    | PUniquePointer e ->
       LBLOCK [STR "unique-pointer("; exp_to_pretty e; STR ")"]
    | PPreservedAllMemory -> STR "preserved-all-memory"
    | PPreservedAllMemoryX l ->
       LBLOCK [
           STR "preserved-all-memory-x";
           pretty_print_list l exp_to_pretty "(" "," ")"]
    | PContractObligation s -> LBLOCK [STR "contract-obligation:"; STR s]
  | POutputParameterInitialized (vinfo, offset) ->
     LBLOCK [
         STR "outputparameter-initialized(";
         STR vinfo.vname;
         STR ", ";
         offset_to_pretty offset;
         STR ")"]
  | POutputParameterUnaltered (vinfo, offset) ->
     LBLOCK [
         STR "outputparameter-unaltered(";
         STR vinfo.vname;
         STR ", ";
         offset_to_pretty offset;
         STR ")"]


let get_global_vars_in_exp (env:cfundeclarations_int) (e:exp) =
  let is_global_var e =
    match e with
    | Lval (Var (_,vid),_) when vid > 0 -> (env#get_varinfo_by_vid vid).vglob
    | _ -> false in
  let ewalker = new find_exp_walker_t is_global_var in
  let _ = ewalker#walk_exp e in
  ewalker#get_result


let has_global_vars_in_exp (env:cfundeclarations_int) (e:exp) =
  match get_global_vars_in_exp env e with [] -> false | _ -> true


let is_opaque (p:po_predicate_t) =
  let is_opaque_var e =
      match e with
      | Lval (Var (_,vid),_) -> vid < 0
      | _ -> false in
  let exps = collect_indexed_predicate_expressions p in
  let result = ref [] in
  let _ =
    List.iter (fun (_,e) ->
        let ewalker = new find_exp_walker_t is_opaque_var in
        let _ = ewalker#walk_exp e in
        result := ewalker#get_result @ !result) exps in
  (List.length !result) > 0


(* avoid an unbounded sequence of assumptions *)
let check_assumption_predicates
      (existingpredicates:po_predicate_t list) (p:po_predicate_t) =
  try
    List.fold_left (fun acc pred ->
        match acc with
        | None -> None
        | Some p' ->
           let sp' = po_predicate_mcts#ts p' in
           let sp = po_predicate_mcts#ts pred in
           if sp' = sp then
             match (p', pred) with
             | (PIntUnderflow (op', x1', x2', ik'),
                PIntUnderflow (op, x1, x2, ik)) ->
                (if (op' = op) && ((exp_compare x1' x1) = 0) && (ik' = ik) then
                   match (op,x2',x2) with
                   | (MinusA,Const (CInt (i64', _, _)),Const (CInt (i64, _, _))) ->
                      if Int64.compare i64' i64 < 0 then
                        Some pred
                      else
                        None
                   | _ -> acc
                 else
                   acc)
             | _ -> acc
           else acc) (Some p) existingpredicates
  with
    _ -> Some p


let rec offset_to_s_offset (o:offset) =
  match o with
  | NoOffset ->  ArgNoOffset
  | Field ((fname,_),t) -> ArgFieldOffset (fname,offset_to_s_offset t)
  | Index (Const (CInt (i64,_,_)),t) ->
     ArgIndexOffset (mkNumericalFromInt64 i64,offset_to_s_offset t)
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "offset cannot be converted to s_offset:";
               offset_to_pretty o]))


let rec exp_to_sterm (fdecls:cfundeclarations_int) (e:exp) =
  let es = exp_to_sterm fdecls in
  match e with
  | Const (CInt (i64,_,_)) ->
     NumConstant (mkNumericalFromString (Int64.to_string i64))
  | Lval (Var (vname,vid),offset) when vid = (-1) ->
     ArgValue (ParGlobal vname, offset_to_s_offset offset)
  | Lval (Var (vname,vid),offset) ->
     if fdecls#is_formal vid then
       let vinfo = fdecls#get_varinfo_by_vid vid in
       ArgValue (ParFormal vinfo.vparam, offset_to_s_offset offset)
     else if fdecls#is_local vid then
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Local variable cannot be converted to s_term: ";
                 STR vname]))
     else
       ArgValue (ParGlobal vname, offset_to_s_offset offset)
  | Lval (Mem (Lval (Var (vname,vid),voffset)),moffset) when vid = (-1) ->
     let arg = ArgValue (ParGlobal vname, offset_to_s_offset voffset) in
     ArgAddressedValue (arg,offset_to_s_offset moffset)
  | Lval (Mem (Lval (Var (vname,vid),voffset)),moffset) ->
     let arg =
       if fdecls#is_formal vid then
       let vinfo = fdecls#get_varinfo_by_vid vid in
       ArgValue (ParFormal vinfo.vparam, offset_to_s_offset voffset)
     else if fdecls#is_local vid then
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Local variable cannot be converted to s_term: ";
                   STR vname]))
     else
       ArgValue (ParGlobal vname, offset_to_s_offset voffset) in
     ArgAddressedValue (arg,offset_to_s_offset moffset)
  | BinOp (op, e1, e2, _) -> ArithmeticExpr (op, es e1, es e2)
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "exp cannot be converted to s_term: "; exp_to_pretty e]))


let po_predicate_to_xpredicate (fdecls:cfundeclarations_int) (p:po_predicate_t) =
  let es = exp_to_sterm fdecls in
  let numzero = NumConstant numerical_zero in
  match p with
  | PHeapAddress e -> XHeapAddress (es e)
  | PGlobalAddress e -> XGlobalAddress (es e)
  | PNotNull e -> XNotNull (es e)
  | PNull e -> XNull (es e)
  | PControlledResource (r,e) ->  XControlledResource (r, es e)
  | PAllocationBase e -> XAllocationBase (es e)
  | PIndexLowerBound e -> XRelationalExpr (Ge, (es e), numzero)
  | PIndexUpperBound (e1,e2) -> XRelationalExpr (Lt, (es e1), (es e2))
  | PInitialized lval -> XInitialized (es (Lval lval))
  | PInitializedRange (e1,e2) -> XInitializedRange (es e1, es e2)
  | PNotZero e -> XRelationalExpr (Ne, es e, numzero)
  | PNonNegative e -> XRelationalExpr (Gt, es e, numzero)
  | PNullTerminated e -> XNullTerminated (es e)
  | PNoOverlap (e1,e2) -> XNoOverlap (es e1, es e2)
  | PValueConstraint e ->
     (match e with
      | BinOp (op, e1, e2, _) when is_relational_operator op ->
         XRelationalExpr (op, es e1, es e2)
      | _ ->
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Value constraint cannot be converted to xpredicate: ";
                   po_predicate_to_pretty p])))
  | PConfined e -> XConfined (es e)
  | PMemoryPreserved e -> XPreservesMemory (es e)
  | PUniquePointer e -> XUniquePointer (es e)
  | PValidMem  e -> XValidMem (es e)
  | PPreservedAllMemory -> XPreservesAllMemory
  | PPreservedAllMemoryX l -> XPreservesAllMemoryX (List.map es l)
  | PBuffer (e1, e2) -> XBuffer (es e1, es e2)
  | PRevBuffer (e1,e2) -> XRevBuffer (es e1, es e2)
  | PNewMemory e -> XNewMemory (es e)
  | PIntOverflow (op, e1, e2, k)
    | PUIntOverflow (op, e1, e2, k) ->
     let safeub = get_safe_upperbound k in
     let exp = BinOp (op, e1, e2, TInt (k,[])) in
     XRelationalExpr (Le, es exp, NumConstant safeub)
  | PIntUnderflow (op, e1, e2, k) ->
     let safelb = get_safe_lowerbound k in
     let exp = BinOp (op, e1, e2, TInt (k,[])) in
     XRelationalExpr (Ge, es exp, NumConstant safelb)
  | PUIntUnderflow (op, e1, e2, k) ->
     let exp = BinOp (op, e1, e2, TInt (k,[])) in
     XRelationalExpr (Ge, es exp, NumConstant numerical_zero)
  | PSignedToSignedCastLB (_, ikto, e) ->
     let safelb = get_safe_lowerbound ikto in
     XRelationalExpr (Ge, es e, NumConstant safelb)
  | PSignedToSignedCastUB (_, ikto, e) ->
     let safeub = get_safe_upperbound ikto in
     XRelationalExpr (Le, es e, NumConstant safeub)
  | PSignedToUnsignedCastLB (_, _, e) ->
     XRelationalExpr (Ge, es e, NumConstant numerical_zero)
  | PSignedToUnsignedCastUB (_, ikto, e) ->
     let safeub = get_safe_upperbound ikto in
     XRelationalExpr (Le, es e, NumConstant safeub)
  | PUnsignedToSignedCast (_, ikto, e)
    | PUnsignedToUnsignedCast (_, ikto, e) ->
     let safeub = get_safe_upperbound ikto in
     XRelationalExpr (Le, es e, NumConstant safeub)
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Predicate cannot be converted to xpredicate: ";
               po_predicate_to_pretty p]))


let rec s_offset_to_offset (tgttype:typ) (s:s_offset_t) =
  match s with
  | ArgNoOffset -> NoOffset
  | ArgFieldOffset (fname,ss) ->
     begin
       match file_environment#get_type_unrolled tgttype with
       | TComp (ckey,_) ->
          let cinfo = file_environment#get_comp ckey in
          let finfo =
            try
              List.find (fun finfo -> finfo.fname = fname) cinfo.cfields
            with
            | Not_found ->
               raise
                 (CCHFailure
                    (LBLOCK [
                         STR "Field ";
                         STR fname;
                         STR " not found in struct ";
                         STR cinfo.cname; STR " (";
                         INT ckey;
                         STR ")"])) in
          Field ((fname, ckey), s_offset_to_offset finfo. ftype ss)
       | _ ->
          raise
            (CCHFailure
               (LBLOCK [
                    STR "Unexpected target type for field: ";
                    STR fname;
                    STR "; offset: ";
                    typ_to_pretty tgttype]))
     end
  | ArgIndexOffset (n,ArgNoOffset) when n#equal numerical_zero -> NoOffset
  | ArgIndexOffset (n,ss) ->
     match tgttype with
     | TArray (tt,_,_) | TPtr (tt,_) ->
        Index (make_constant_exp n, s_offset_to_offset tt ss)
     | _ ->
        raise
          (CCHFailure
             (LBLOCK [
                  STR "Unexpected target type for index offset: ";
                  typ_to_pretty tgttype]))


let rec sterm_to_exp
          ?(returnexp=None) (fdecls:cfundeclarations_int) (t:s_term_t) =
  let te = sterm_to_exp ~returnexp fdecls in
  match t with
  | ReturnValue ->
     (match returnexp with
      | Some e -> e
      | _ ->
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Unable to convert return value (no expression provided): ";
                   s_term_to_pretty t])))
  | ArgValue (ParFormal n, soff) ->
     let vinfo = fdecls#get_formal n in
     let offset = s_offset_to_offset vinfo.vtype soff in
     Lval (Var (vinfo.vname, vinfo.vid), offset)
  | ArgValue (ParGlobal name, soff) ->
     let vinfo = file_environment#get_globalvar_by_name name in
     let offset = s_offset_to_offset vinfo.vtype soff in
     Lval (Var (vinfo.vname, vinfo.vid), offset)
  | NumConstant i -> Const (CInt (Int64.of_string i#toString, IInt, None))
  | ArithmeticExpr (op, t1, t2) -> BinOp (op, te t1, te t2, TInt (IInt,[]))
  | ArgAddressedValue (t, soff) ->
     let base = te t in
     let tgttype = type_of_tgt_exp fdecls base in
     let offset = s_offset_to_offset tgttype soff in
     Lval (Mem base, offset)
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Conversion of s_term: "; s_term_to_pretty t;
               STR " currently not supported"]))


let xpredicate_to_po_predicate
      ?(returnexp=None) (fdecls:cfundeclarations_int) (p:xpredicate_t) =
  let te = sterm_to_exp ~returnexp fdecls in
  match p with
  | XAllocationBase t -> PAllocationBase (te t)
  | XControlledResource (r, t) -> PControlledResource (r, te t)
  | XNewMemory t -> PNewMemory (te t)
  | XConfined t -> PConfined (te t)
  | XInitialized t ->
     (match te t with
      | Lval lval -> PInitialized lval
      | e ->
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Dereferenced initialized values not yet implemented ";
                   exp_to_pretty e])))
  | XInitializedRange (t1,t2) -> PInitializedRange (te t1, te t2)
  | XBuffer (t1, t2) -> PBuffer (te t1, te t2)
  | XRevBuffer (t1, t2) -> PRevBuffer (te t1, te t2)
  | XGlobalAddress t -> PGlobalAddress (te t)
  | XHeapAddress t -> PHeapAddress (te t)
  | XNoOverlap (t1,t2) -> PNoOverlap (te t1, te t2)
  | XNotNull t -> PNotNull (te t)
  | XNotZero t -> PNotZero (te t)
  | XNonNegative t -> PNonNegative (te t)
  | XNull t -> PNull (te t)
  | XValidMem t -> PValidMem (te t)
  | XNullTerminated t -> PNullTerminated (te t)
  | XOutputFormatString t -> PFormatString (te t)
  | XPreservesAllMemory -> PPreservedAllMemory
  | XPreservesAllMemoryX l -> PPreservedAllMemoryX (List.map te l)
  | XPreservesMemory t -> PMemoryPreserved (te t)
  | XRelationalExpr (op,t1,t2) ->
     PValueConstraint (BinOp (op, te t1,te t2, TInt (IBool,[])))
  | XUniquePointer t -> PUniquePointer (te t)
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Conversion of xpredicate ";
               xpredicate_to_pretty p;
               STR " currently not supported"]))
