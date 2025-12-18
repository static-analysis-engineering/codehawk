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

(* ============================================================================== *
 * Adapted from CIL                                                               *
 * ============================================================================== *)

(* chlib *)
open CHCommon
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xsimplify
open Xprt
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHDictionary
open CCHLibTypes
open CCHMachineSizes
open CCHSettings
open CCHSumTypeSerializer
open CCHTypesSize
open CCHTypesCompare
open CCHTypesToPretty
open CCHUtilities

module B = Big_int_Z
module H = Hashtbl


let fenv = CCHFileEnvironment.file_environment


let binop_to_xop (op:binop):xop_t =
  match op with
  | PlusA | PlusPI | IndexPI -> XPlus
  | MinusA | MinusPI | MinusPP -> XMinus
  | Mult -> XMult
  | Div -> XDiv
  | Mod -> XMod
  | Shiftlt -> XShiftlt
  | Shiftrt -> XShiftrt
  | Lt -> XLt
  | Gt -> XGt
  | Le -> XLe
  | Ge -> XGe
  | Eq -> XEq
  | Ne -> XNe
  | BAnd -> XBAnd
  | BXor -> XBXor
  | BOr -> XBOr
  | LAnd -> XLAnd
  | LOr -> XLOr

let rec exp_to_xpr (exp:exp):xpr_t option =
  try
    match exp with
    | Const (CInt (i64, _, _)) ->
       Some (num_constant_expr (mkNumerical_big (B.big_int_of_int64 i64)))
    | BinOp (op, e1, e2, _)  ->
       begin
         match (exp_to_xpr e1, exp_to_xpr e2) with
         | (Some x1, Some x2) -> Some (XOp (binop_to_xop op, [x1; x2]))
         | _ -> None
       end
    | _ -> None
  with _ -> None

let is_relational_operator (op:binop) =
  match op with
  | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr -> true
  | _ -> false

let reverse_relational_operator (op:binop) =
  match op with
  | Lt -> Ge
  | Le -> Gt
  | Ge -> Lt
  | Gt -> Le
  | Eq -> Ne
  | Ne -> Eq
  | _ ->
     raise (CCHFailure (LBLOCK [STR "unable to reverse operator ";
                                 STR (binop_to_print_string op)]))

let zero = Const (CInt (Int64.of_int 0,IInt,None))
let one  = Const (CInt (Int64.of_int 1,IInt,None))

let make_constant_exp (n:numerical_t) =
  Const (CInt (Int64.of_string n#toString,IInt,None))

let void_type   = TVoid([])
let int_type    = TInt(IInt, [])
let uint_type   = TInt(IUInt, [])
let _long_type   = TInt(ILong, [])
let ulong_type  = TInt(IULong, [])
let char_type   = TInt(IChar, [])
let _bool_type   = TInt(IBool, [])

let char_ptr_type = TPtr(char_type, [])
let _char_const_ptr_type = TPtr(TInt(IChar, [Attr("const", [])]), [])
let string_literal_type = char_ptr_type

let void_ptr_type = TPtr(void_type, [])
let _int_ptr_type  = TPtr(int_type, [])
let _uint_ptr_type = TPtr(uint_type, [])

let wchar_type    = int_type            (* ***check: machine dependent *** *)
let sizeof_type  = ulong_type           (* ***check: machine dependent *** *)

let _double_type  = TFloat(FDouble, [])


let get_typ_attributes (t:typ) =
  match t with
  | TVoid a -> a
  | TInt (_,a) -> a
  | TFloat (_,a) -> a
  | TPtr (_,a) -> a
  | TArray (_,_,a) -> a
  | TFun (_,_,_,a) -> a
  | TNamed (_,a) -> a
  | TComp (_,a) -> a
  | TEnum (_,a) -> a
  | TBuiltin_va_list a -> a


let is_enum_constant (ename:string) (exp:exp) =
  let einfo = fenv#get_enum ename in
  let eexps = List.map (fun (_, _, e, _) -> e) einfo.eitems in
  List.exists (fun e -> (exp_compare e exp) = 0) eexps


let maxval w signed =
  let x = if signed then w-1 else w in
  let v = B.power_int_positive_int 2 x in
  (mkNumerical_big v)#sub numerical_one


let minval w =
  let v = B.power_int_positive_int 2 (w-1) in
  (mkNumerical_big v)#neg


let rec is_field_offset offset =
  match offset with
  | NoOffset -> false
  | Index (_, offset) -> is_field_offset offset
  | Field (_, NoOffset) -> true
  | Field (_, offset) -> is_field_offset offset


let rec add_offset base_offset offset =
  match base_offset with
  | NoOffset -> offset
  | Index (e, ioffset) -> Index (e, add_offset ioffset offset)
  | Field (f, foffset) -> Field (f, add_offset foffset offset)


let rec is_constant_offset offset =
  match offset with
  | NoOffset -> true
  | Field (_, o) -> is_constant_offset o
  | Index (e, o) -> is_constant_index_exp e && is_constant_offset o


and is_constant_index_exp e =
  match e with
  | Const (CInt _) -> true
  | Const (CChr _) -> true
  | Const (CEnum _) -> true
  | SizeOf _ | SizeOfE _ -> true
  | _ -> false


let rec is_constant_string (e:exp) =
  match e with
  | Const (CStr _) -> true
  | CastE (_,x) -> is_constant_string x
  | _ -> false


let rec type_of_exp (fdecls:cfundeclarations_int) (x:exp) : typ =
  try
    let ty =
      match x with
      | Const (CInt (_, ik, _)) -> TInt (ik,[])
      | Const (CChr _) -> int_type
      | Const (CStr _) -> string_literal_type
      | Const (CWStr _) -> TPtr (wchar_type,[])
      | Const (CReal (_,fk,_)) -> TFloat (fk, [])
      | Const (CEnum (tag,_,_)) -> type_of_exp fdecls tag
      | Lval lv -> type_of_lval fdecls lv
      | SizeOf _ | SizeOfE _ | SizeOfStr _ -> sizeof_type
      | AlignOf _ | AlignOfE _ -> sizeof_type
      | UnOp (_,_,t)
        | BinOp (_,_,_,t)
        | Question (_,_,_,t)
        | CastE (t,_) -> t
      | AddrOf lv -> TPtr (type_of_lval fdecls lv, [])
      | AddrOfLabel _ -> void_ptr_type
      | StartOf lv ->
         begin
	   match fenv#get_type_unrolled (type_of_lval fdecls lv) with
	   | TArray (t, _, a) -> TPtr (t, a)
	   | otherTyp ->
	      raise
                (CCHFailure
                   (LBLOCK [
                        STR "type_of_exp: StartOf on a non-array: ";
			typ_to_pretty otherTyp]))
         end
      | FnApp (_, exp, _) ->
         begin
           match type_of_exp fdecls exp with
           | TFun (t, _, _, _) -> t
           | _ -> TVoid [] end
      | CnApp (_, _, t) -> t in
    fenv#get_type_unrolled ty
  with
  | CHFailure p ->
     begin
       ch_error_log#add
         "type of exp"
         (LBLOCK [
              STR "Error in type_of_exp with: "; exp_to_pretty x; STR ": "; p]);
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Error in type_of_exp with: ";
                 exp_to_pretty x;
                 STR ": ";
                 p]))
     end

and returntype_of_exp (fdecls:cfundeclarations_int) (x:exp): typ =
  match type_of_exp fdecls x with
  | TFun (t,_,_,_) -> t
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "returntype-of-exp encountered non-function type: ";
               exp_to_pretty x]))


and type_of_tgt_exp (fdecls:cfundeclarations_int) e =
  let t = type_of_exp fdecls e in
  match t with
  | TPtr (tt,_) -> tt
  | _ ->
     raise
       (CCHFailure
	  (LBLOCK [
               STR "type-of-tgt-exp: type of expression ";
	       exp_to_pretty e;
               STR " is not a pointer type: ";
	       typ_to_pretty t]))


and type_of_lval (fdecls:cfundeclarations_int) (lv:lval) =
  try
    (match lv with
     | (Var (vname,vid), offset) ->
        let vinfo =
          if vid > 0 then
            fdecls#get_varinfo_by_vid vid
          else
            fdecls#get_varinfo_by_name vname in
        type_of_offset fdecls vinfo.vtype offset
     | (Mem x, offset) ->
        match fenv#get_type_unrolled (type_of_exp fdecls x) with
        | TPtr (t, _) -> type_of_offset fdecls t offset
        | TFun _ as t -> t
        | TBuiltin_va_list _ as t -> t
        | otherTyp ->
           raise
             (CCHFailure
                (LBLOCK [
                     STR "type_of_lval: Mem on a non-pointer: ";
		     lval_to_pretty lv;
                     STR ": ";
                     typ_to_pretty otherTyp])))
  with
  | CCHFailure p ->
     begin
       ch_error_log#add
         "type-of-lval"
         (LBLOCK [lval_to_pretty lv; STR ": "; p]);
       raise (CCHFailure p)
     end


and is_field_lval_exp (e:exp) =
  match e with Lval (_,offset) -> is_field_offset offset | _ -> false


(* ignoring attributes for now *)
and type_of_offset (fdecls:cfundeclarations_int) (t:typ) (offset:offset) : typ =
  try
    (match offset with
     | NoOffset -> t
     | Index (_, o) ->
        begin
          match fenv#get_type_unrolled t with
	  | TArray (t, _, _) -> type_of_offset fdecls t o
          | otherTyp ->
	     raise
               (CCHFailure
                  (LBLOCK [
                       STR "type_of_offset: Index on a non-array: ";
		       typ_to_pretty otherTyp]))
        end
     | Field ((fname, ckey), o) ->
        let ftype = fenv#get_type_unrolled (fenv#get_field_type ckey fname) in
        type_of_offset fdecls ftype o)
  with
  | CCHFailure p ->
     begin
       ch_error_log#add
         "type-of-offset"
         (LBLOCK [
              typ_to_pretty t;
              STR ", ";
              offset_to_pretty offset;
              STR ": ";
              p]);
       raise (CCHFailure p)
     end


let is_signed_type (ik:ikind) =
  match ik with
  | IChar | ISChar | IInt | IShort | ILong | ILongLong -> true
  | _ -> false


let is_unsigned_type (ik:ikind) =
  match ik with
  | IUChar | IUInt | IUShort | IULong | IULongLong -> true
  | _ -> false


let is_character_type (ik:ikind) =
  match ik with
  | IUChar | ISChar | IChar -> true
  | _ -> false


let is_bool_type (ik:ikind) =
  match ik with IBool -> true | _ -> false


let has_const_attribute (t:typ) =
  List.exists
    (fun a ->
      match a with
      | Attr ("const", _) -> true
      | Attr ("pconst", _) -> true
      | _ -> false)
    (get_typ_attributes t)


let has_deref_const_attribute (t: typ) =
  match t with
  | TPtr (tgt, _) -> has_const_attribute tgt
  | _ -> false


let is_char ik =
  match ik with IChar | ISChar | IUChar -> true | _ -> false


let is_int ik =
  match ik with IInt | IUInt -> true | _ -> false


let is_short ik =
  match ik with IShort | IUShort -> true | _ -> false


let is_long ik =
  match ik with ILong | IULong -> true | _ -> false


let is_longlong ik =
  match ik with ILongLong | IULongLong -> true | _ -> false


(** {1 Integer promotion: C Standard 6.3.1.8}

   First, both types are promoted to either signed or unsigned int.

   If both operands have the same type, then no further conversion is needed.

   Otherwise, if both operands have signed integer types or both have unsigned
   integer types, the operand with the type of lesser integer conversion rank
   is converted to the type of the operand with greater rank.

   Otherwise, if the operand that has unsigned integer type has rank greater
   or equal to the rank of the type of the other operand, then the operand
   with signed integer type is converted to the type of the operand with
   unsigned integer type.

   Otherwise, if the type of the operand with signed integer type can represent
   all of the values of the type of the operand with unsigned integer type, then
   the operand with unsigned integer type is converted to the type of the operand
   with signed integer type.

   Otherwise, both operands are converted to the unsigned integer type
   corresponding  to the type of the operand with signed integer type.
 *)

let get_integer_promotion (ty1:typ) (ty2:typ) =
  let promote ik =
    match ik with
    | IChar | ISChar | IShort -> IInt
    | IUChar | IUShort -> IUInt
    | _ -> ik in
  let ik = match (ty1,ty2) with
    | (TInt (ik1,_), TInt (ik2,_)) ->
       let ik1 = promote ik1 in
       let ik2 = promote ik2 in
       if ik1 = ik2 then
         ik1
       else
         begin
           match (ik1,ik2) with
           | (IInt, ILong) | (ILong, IInt) -> ILong
           | (IInt, ILongLong) | (ILongLong, IInt) -> ILongLong
           | (ILong, ILongLong) | (ILongLong, ILong) -> ILongLong
           | (IUInt, IULong) | (IULong, IUInt) -> IULong
           | (_, IULongLong) | (IULongLong, _) -> IULongLong
           | (IInt, IUInt) | (IUInt, IInt) -> IUInt
           | (ILong, IULong) | (IULong, ILong) -> IULong
           | (IInt, IULong) | (IULong, IInt) -> IULong
           | (ILong, IUInt) | (IUInt, ILong) -> ILong
           | (ILongLong, IUInt) | (IUInt, ILongLong) -> ILongLong
           | (IUInt128, _) | (_, IUInt128) -> IUInt128
           | (IInt128, _) | (_, IInt128) -> IInt128
           | _ ->
              raise
                (CCHFailure
                   (LBLOCK [
                        STR "Missing case in integer promotion: ";
                        STR (int_type_to_string ik1);
                        STR " and ";
                        STR (int_type_to_string ik2)]))
         end
    | _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Unexpected types for integer promotion: ";
                 typ_to_pretty ty1;
                 STR " and ";
                 typ_to_pretty ty2])) in
  TInt  (ik, [])


let rec get_field_offset offset =
  match offset with
  | NoOffset ->
     raise
       (CCHFailure
          (LBLOCK [offset_to_pretty offset; STR " is not a field offset"]))
  | Field ((fname,ckey),NoOffset) -> (fname,ckey)
  | Field (_,offset)
  | Index (_,offset) -> get_field_offset offset


let get_field_lval_exp (e:exp) =
  match e with
  | Lval (_, offset) -> get_field_offset offset
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [STR "Expression is not a field lval: "; exp_to_pretty e]))


let ikind_size_leq (ik1:ikind) (ik2:ikind) : bool =
  (ik1 = ik2) ||
    (is_char ik1
     && (is_char ik2
         || is_short ik2
         || is_int ik2
         || is_long ik2
         || is_longlong ik2))
    || (is_short ik1
        && (is_short ik2
            || is_int ik2
            || is_long ik2
            || is_longlong ik2))
    || (is_int ik1
        && (is_int ik2
            || is_long ik2
            || is_longlong ik2))
    || (is_long ik1
        && (is_long ik2 || is_longlong ik2))
    || (is_longlong ik1 && is_longlong ik2)


(** returns true if c is known to be less than the value ik can represent;
    returns false if not known *)
let const_fits_kind (c:constant) (target_ik:ikind) =
  try
    match c with
    | CInt (i64, cik, _) ->
       ikind_size_leq cik target_ik ||
         (match target_ik with
          | ISChar -> ((Int64.to_int i64) < 128) && (Int64.to_int i64 >= (-128))
          | _ -> ((Int64.to_int i64) < 256  && (Int64.to_int i64 >= 0)))
    | CChr __-> true
    | _ -> false
  with
  | _ -> false


let enum_fits_kind (ename: string) (target_ik:ikind) =
  let einfo = fenv#get_enum ename in
  List.for_all (fun (_, _, e, _) ->
      match e with
      | Const c -> const_fits_kind c target_ik
      | _ -> false) einfo.eitems


let exp_has_repeated_field (e:exp) =
  let rec aux e l =
    let check fname fkey =
      List.exists (fun (fn,fk) -> fname = fn && fkey = fk) l in
    match e with
    | CastE (_, Lval (Var _, Field ((fname, fkey), _)))
    | Lval (Var _, Field ((fname, fkey), _)) -> check fname fkey
    | CastE (_, Lval (Mem e, Field ((fname, fkey),_)))
      | Lval (Mem e, Field ((fname, fkey),_)) ->
       check fname fkey || aux e ((fname,fkey)::l)
    | _ -> false in
  aux e []


(** returns true if x is known to be not zero; returns false if unknown or zero *)
let rec is_not_zero (x:exp) =
  match x with
  | Const (CInt (i64, _,_ )) -> not ((Int64.compare i64 Int64.zero) = 0)
  | SizeOf (TInt _)
    | SizeOf (TPtr _)
    | SizeOf (TFloat _) -> true
  | SizeOf ((TNamed _) as tt) ->
     is_not_zero (SizeOf (fenv#get_type_unrolled tt))
  | _ -> false


let get_safe_upperbound (kind:ikind) =
  try
    let md k =
      let ms =
        if system_settings#has_wordsize then
          match system_settings#get_wordsize with
          | 32 -> linux_32_machine_sizes
          | 64 -> linux_64_machine_sizes
          | _ -> linux_16_machine_sizes
        else
          linux_16_machine_sizes in
      let mn v = match get_const v with
        | Some num -> num#toInt * 8          (* machine sizes are in bytes *)
        | _ ->
           raise
             (CCHFailure
                (STR "Unexpected condition in get_safe_upperbound")) in
      match k with
      | IInt -> maxval (mn ms.sizeof_int) true
      | IShort -> maxval (mn ms.sizeof_short) true
      | IUInt -> maxval (mn ms.sizeof_int) false
      | IUShort -> maxval (mn ms.sizeof_short) false
      | ILong -> maxval (mn ms.sizeof_long) true
      | ILongLong -> maxval (mn ms.sizeof_longlong) true
      | IULong -> maxval (mn ms.sizeof_long) false
      | IULongLong -> maxval (mn ms.sizeof_longlong) false
      | IUInt128 -> maxval (mn ms.sizeof_int128) false
      | IInt128 -> maxval (mn ms.sizeof_int128) true
      | _ ->
         raise
           (CCHFailure (STR "Unexpected condition in get_safe_upperbound")) in
    match kind with
    | IBool -> numerical_one
    | IChar | ISChar -> maxval 8 true
    | IUChar -> maxval 8 false
    | _ -> md kind
  with
    _ ->
    begin
      ch_error_log#add "safe-upperbound" (STR (ikind_mfts#ts kind));
      raise
        (CCHFailure
           (LBLOCK [
                STR "Error in get_safe_upperbound: "; STR (ikind_mfts#ts kind)]))
    end


let get_safe_lowerbound (kind:ikind) =
  try
    let md k =
      let ms =
        if system_settings#has_wordsize then
          match system_settings#get_wordsize with
          | 32 -> linux_32_machine_sizes
          | 64 -> linux_64_machine_sizes
          | _ -> linux_16_machine_sizes
        else
          linux_16_machine_sizes in
      let mn v = match get_const v with
        | Some num -> num#toInt * 8        (* machine sizes are in bytes *)
        | _ ->
           raise
             (CCHFailure (STR "Unexpected condition in get_safe_lowerbound")) in
      match k with
      | IInt -> minval (mn ms.sizeof_int)
      | IShort -> minval (mn ms.sizeof_short)
      | ILong -> minval (mn ms.sizeof_long)
      | ILongLong -> minval (mn ms.sizeof_longlong)
      | IInt128 -> minval (mn ms.sizeof_int128)
      | _ ->
         raise
           (CCHFailure (STR "Unexpcted condition in get_safe_lowerbound")) in
    match kind with
    | IBool -> numerical_zero
    | IChar | ISChar -> minval 8
    | IUChar -> numerical_zero
    | IInt | IShort -> md kind
    | IUInt | IUShort -> numerical_zero
    | ILong | ILongLong | IInt128 -> md kind
    | IULong | IULongLong | IUInt128 -> numerical_zero
  with
  | CHFailure p ->
     begin
       ch_error_log#add "safe-lowerbound" (STR (ikind_mfts#ts kind));
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Error in get_safe_upperbound: ";
                 STR (ikind_mfts#ts kind);
                 STR ": ";
                 p]))
     end


(** returns true if i is known to be less than the value target_ik can
    represent, according to minimum prescribed widths; returns false otherwise *)
let int_fits_kind (num:numerical_t) (target_ik:ikind) =
  num#leq (get_safe_upperbound target_ik) && num#geq (get_safe_lowerbound target_ik)


(* TODO: determine min/max values for the floating number kinds *)
let float_fits_kind (f:float) (_target_f:fkind) =
  f < float_of_string "3.402823E38"


let get_safe_bit_width (kind:ikind) =
  let ms =
    if system_settings#has_wordsize then
      match system_settings#get_wordsize with
      | 32 -> linux_32_machine_sizes
      | 64 -> linux_64_machine_sizes
      | _ -> linux_16_machine_sizes
    else
      linux_16_machine_sizes in
  let mn v = match get_const v with
    | Some num -> num#toInt * 8          (* machine sizes are in bytes *)
    | _ ->
       raise
         (CCHFailure (STR "Unexpected condition in get_safe_bit_width")) in
  match kind with
  | IBool -> 1
  | IChar | ISChar | IUChar -> 8
  | IShort| IUShort -> mn ms.sizeof_short
  | IInt | IUInt -> mn ms.sizeof_int
  | ILong | IULong -> mn ms.sizeof_long
  | ILongLong | IULongLong -> mn ms.sizeof_longlong
  | IInt128 | IUInt128 -> mn ms.sizeof_int128


let get_required_minimum_bit_width (n:int) =
  if n < 8 then 8
  else if n < 16 then 16
  else if n < 32 then 32
  else if n < 64 then 64
  else if n < 128 then 128
  else if n < 256 then 256
  else
    raise
      (CCHFailure
         (LBLOCK [
              STR "Unexpected value in get-required-minimum-bit-width: ";
              INT n]))


let is_safe_int_cast (fromi:ikind) (toi:ikind)	=
  match (fromi,toi) with
  | (IBool, IInt)
  | (IChar, IInt)        (* both signed and unsigned interpretations fit *)
  | (IChar, ILong)
  | (IChar, ILongLong)
  | (ISChar, IInt)
  | (ISChar, IShort)
  | (ISChar, ILong)
  | (IUChar, IUShort)
  | (IUChar, IUInt)
  | (IUChar, IULong)
  | (IUChar, IULongLong)
  | (IUChar, IShort)
  | (IUChar, IInt)
  | (IUChar, ILong)
  | (IUChar, ILongLong)
  | (IInt, ILong)
  | (IInt, ILongLong)
  | (IShort, IInt)
  | (IShort, ILong)
  | (IShort, ILongLong)
  | (ILong, ILongLong)
  | (IUInt, IULong)
  | (IUInt, IULongLong)
  | (IUShort, IUInt)
  | (IUShort, IULong)
  | (IUShort, IULongLong)
  | (IULong, IULongLong) -> true
  | (IUInt128, IUInt128) -> true
  | (IUInt128, _) -> false
  | (IInt128, IUInt128) -> false
  | (IUChar, IUInt128)
    | (IUShort, IUInt128)
    | (IUInt, IUInt128)
    | (IULong, IUInt128)
    | (IULongLong, IUInt128) -> true
  | (IChar, IInt128)
    | (ISChar, IInt128)
    | (IShort, IInt128)
    | (IInt, IInt128)
    | (ILong, IInt128)
    | (ILongLong, IInt128)
    | (IInt128, IInt128) -> true
  | _ -> false


let is_system_struct_name (s: string): bool =
  List.mem s ["FILE"; "__IO_FILE"]


let is_system_struct (t: typ): bool =
    match t with
    | TNamed (s, _) -> is_system_struct_name s
    | tt ->
       match fenv#get_type_unrolled tt with
       | TComp (ckey, _) ->
          let cinfo = fenv#get_comp ckey in
          is_system_struct_name cinfo.cname
       | _ -> false


let is_integral_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TInt _ -> true
  | _ -> false


let is_unsigned_integral_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TInt (ik,_) -> is_unsigned_type ik
  | _ -> false


let is_char_star_type (t: typ): bool =
  match fenv#get_type_unrolled t with
  | TPtr (TInt (ik, _), _) ->
     (match ik with IChar | IUChar | ISChar -> true | _ -> false)
  | _ -> false


let is_pointer_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TPtr _ -> true
  | _ -> false


let is_string_type (t:typ) =
  let is_char ik =
    match ik with
    | IChar | ISChar | IUChar -> true
    | _ -> false in
  match fenv#get_type_unrolled t with
  | TPtr (TInt (ik, _), _) -> is_char ik
  | _ -> false


let is_void_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TVoid _ -> true
  | _ -> false


let is_array_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TArray _ -> true
  | _ -> false


let is_void_ptr_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TPtr (TVoid _, _) -> true
  | _ -> false


let is_function_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TFun _ -> true
  | _ -> false


let is_struct_type (t:typ) =
  match fenv#get_type_unrolled t with
  | TComp _ -> true
  | _ -> false


let is_float_type  (t:typ) =
  match fenv#get_type_unrolled t with
  | TFloat _ -> true
  | _ -> false


let is_volatile_type (t:typ) =
  List.exists
    (fun a -> match a with Attr ("volatile",_) -> true | _ -> false)
    (get_typ_attributes t)


let rec is_scalar_struct_type (t: typ): bool =
  match fenv#get_type_unrolled t with
  | TComp (ckey, _) ->
     let cinfo = fenv#get_comp ckey in
     List.for_all (fun finfo ->
         match fenv#get_type_unrolled finfo.ftype with
         | TInt _
           | TFloat _
           | TPtr _
           | TVoid _ -> true
         | TComp _ -> is_scalar_struct_type finfo.ftype
         | _ -> false) cinfo.cfields
  | _ -> false


let rec get_scalar_struct_offsets (t: typ): offset list =
  if is_scalar_struct_type t then
    match fenv#get_type_unrolled t with
    | TComp (ckey, _) ->
       let cinfo = fenv#get_comp ckey in
       List.fold_left (fun acc finfo ->
           match finfo.ftype with
           | TInt _
             | TFloat _
             | TPtr _ -> (Field ((finfo.fname, finfo.fckey), NoOffset)) :: acc
           | TComp _ ->
              let suboffsets = get_scalar_struct_offsets finfo.ftype in
              let suboffsets =
                List.map (fun suboffset ->
                    Field ((finfo.fname, finfo.fckey), suboffset))
                  (List.rev suboffsets) in
              suboffsets @ acc
           | _ -> acc) [] cinfo.cfields
    | _ -> []
  else
    raise
      (CCHFailure
         (LBLOCK [
              STR "Type is not a scalar struct: "; typ_to_pretty t]))


let constant_value (c:constant) =
  match c with
  | CInt (i64, _, _) ->
     num_constant_expr (mkNumerical_big (B.big_int_of_int64 i64))
  | _ -> random_constant_expr


let rec size_of_align (fdecls:cfundeclarations_int) (t:typ) =
  match fenv#get_type_unrolled t with
  | TInt (IChar, _)
  | TInt (ISChar, _)
  | TInt (IUChar, _) -> int_constant_expr 1
  | TInt (IBool, _) -> symbolic_sizes.alignof_bool
  | TInt (IUInt,_)
  | TInt (IInt, _) -> symbolic_sizes.alignof_int
  | TInt (IShort, _)
  | TInt (IUShort, _) -> symbolic_sizes.alignof_short
  | TInt (ILong, _)
  | TInt (IULong, _) -> symbolic_sizes.alignof_long
  | TInt (ILongLong, _)
    | TInt (IULongLong, _) -> symbolic_sizes.alignof_longlong
  | TInt (IInt128, _)
    | TInt (IUInt128, _) -> symbolic_sizes.alignof_int128
  | TFloat (FFloat, _) -> symbolic_sizes.alignof_float
  | TFloat (FDouble, _) -> symbolic_sizes.alignof_double
  | TFloat (FLongDouble, _) -> symbolic_sizes.alignof_longdouble
  | TFloat (FComplexFloat, _) -> symbolic_sizes.alignof_complex_float
  | TFloat (FComplexDouble, _) -> symbolic_sizes.alignof_complex_double
  | TFloat (FComplexLongDouble, _) -> symbolic_sizes.alignof_complex_longdouble
  | TVoid _ -> random_constant_expr
  | TPtr _ -> symbolic_sizes.alignof_ptr
  | TArray (et, Some _len, _) -> size_of_align fdecls et
  | TArray _ -> random_constant_expr
  | TFun _ -> symbolic_sizes.alignof_fun
  | TNamed _ -> random_constant_expr
  | TComp _ -> random_constant_expr
  | TEnum _ -> symbolic_sizes.alignof_enum
  | TBuiltin_va_list _ -> random_constant_expr


let rec exp_value (fdecls:cfundeclarations_int) (x:exp) =
  match x with
  | Const c -> constant_value c
  | Lval _ -> random_constant_expr
  | SizeOf t -> size_of_type fdecls t
  | SizeOfE exp -> size_of_type fdecls (type_of_exp fdecls exp)
  | SizeOfStr s ->
     let (_,_,len) = mk_constantstring s in int_constant_expr len
  | AlignOf t -> size_of_align fdecls t
  | AlignOfE exp -> size_of_align fdecls (type_of_exp fdecls exp)
  | UnOp _ -> random_constant_expr
  | BinOp (op, x1, x2,_) -> binop_value fdecls op x1 x2
  | Question _ -> random_constant_expr
  | CastE (_, x1) -> exp_value fdecls x1
  | AddrOf _ -> random_constant_expr
  | AddrOfLabel _ -> random_constant_expr
  | StartOf _ -> random_constant_expr
  | FnApp _ -> random_constant_expr
  | CnApp _ -> random_constant_expr


and binop_value (fdecls:cfundeclarations_int) op x1 x2 =
  match op with
  | PlusA -> XOp (XPlus, [exp_value fdecls x1; exp_value fdecls x2])
  | Mult -> XOp (XMult, [exp_value fdecls x1; exp_value fdecls x2])
  | Div -> XOp (XDiv, [exp_value fdecls x1; exp_value fdecls x2])
  | _ -> random_constant_expr


and size_of_type (fdecls:cfundeclarations_int) (t:typ) =
  let machine_sizes = fenv#get_machine_sizes in
  let t = fenv#get_type_unrolled t in
  let size = match t with
  | TInt (IChar, _)
  | TInt (ISChar, _)
  | TInt (IUChar, _) -> int_constant_expr 1
  | TInt (IBool, _) -> machine_sizes.sizeof_bool
  | TInt (IUInt,_)
  | TInt (IInt, _) -> machine_sizes.sizeof_int
  | TInt (IShort, _)
  | TInt (IUShort, _) -> machine_sizes.sizeof_short
  | TInt (ILong, _)
  | TInt (IULong, _) -> machine_sizes.sizeof_long
  | TInt (ILongLong, _)
    | TInt (IULongLong, _) -> machine_sizes.sizeof_longlong
  | TInt (IInt128, _)
    | TInt (IUInt128, _) -> machine_sizes.sizeof_int128
  | TFloat (FFloat, _) -> machine_sizes.sizeof_float
  | TFloat (FDouble, _) -> machine_sizes.sizeof_double
  | TFloat (FLongDouble, _) -> machine_sizes.sizeof_longdouble
  | TFloat (FComplexFloat, _) -> machine_sizes.sizeof_complex_float
  | TFloat (FComplexDouble, _) -> machine_sizes.sizeof_complex_double
  | TFloat (FComplexLongDouble, _) -> machine_sizes.sizeof_complex_longdouble
  | TVoid _ -> machine_sizes.sizeof_void
  | TPtr _ -> machine_sizes.sizeof_ptr
  | TArray (et,Some len,_) ->
     XOp (XMult, [exp_value fdecls len; size_of_type fdecls et])
  | TArray _ -> random_constant_expr
  | TFun _ -> machine_sizes.sizeof_fun
  | TNamed _ -> byte_size_of_typ fenv t
  | TComp _ -> byte_size_of_typ  fenv t
  | TEnum _ -> machine_sizes.sizeof_enum
  | TBuiltin_va_list _ -> random_constant_expr in
  simplify_xpr size


and range_of_type (fdecls:cfundeclarations_int) (t:typ) =
  try
    let max_bits = 64 in
    match fenv#get_type_unrolled t with
    | TInt (ik, _) ->
       let bytes = size_of_type fdecls t in
       let signed = is_signed_type ik in
       begin
         match bytes with
         | XConst (IntConst n) -> get_type_range (8 * n#toInt) signed
         | _ -> get_type_range max_bits signed
       end
    | TEnum _ -> range_of_type fdecls (TInt (IInt,[]))
    | TPtr _
      | TFun _
      | TArray _ -> get_type_range system_settings#get_wordsize false
    | t ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Unexpected query for type range for "; typ_to_pretty t]))
  with
    _ ->
    begin
      ch_error_log#add "range-of-type"  (typ_to_pretty t);
      raise
        (CCHFailure
           (LBLOCK [STR "Error in range_of_type with "; typ_to_pretty t]))
    end


let size_of_exp_type (fdecls:cfundeclarations_int) (x:exp) =
  size_of_type fdecls (type_of_exp fdecls x)


let max_size_of_align (_t:typ) = 64


let rec max_exp_value (fdecls:cfundeclarations_int) (x:exp) =
  match x with
  | Const c -> constant_value c
  | Lval _ -> random_constant_expr
  | SizeOf t -> max_size_of_type fdecls t
  | SizeOfE exp -> max_size_of_type fdecls (type_of_exp fdecls exp)
  | SizeOfStr s ->
     let (_, _, len) = mk_constantstring s in int_constant_expr len
  | AlignOf t -> int_constant_expr (max_size_of_align  t)
  | AlignOfE exp ->
     int_constant_expr (max_size_of_align (type_of_exp fdecls exp))
  | UnOp _ -> random_constant_expr
  | BinOp (op, x1, x2,_ ) -> max_binop_value fdecls op x1 x2
  | Question _ -> random_constant_expr
  | CastE (_, x1) -> max_exp_value fdecls x1
  | AddrOf _ -> random_constant_expr
  | AddrOfLabel _ -> random_constant_expr
  | StartOf _ -> random_constant_expr
  | FnApp _ -> random_constant_expr
  | CnApp _ -> random_constant_expr


and max_binop_value (fdecls:cfundeclarations_int) op x1 x2 =
  match op with
  | PlusA -> XOp (XPlus, [max_exp_value fdecls x1; max_exp_value fdecls x2])
  | Mult -> XOp (XMult, [max_exp_value fdecls x1; max_exp_value fdecls x2])
  | Div -> XOp (XDiv, [max_exp_value fdecls x1; max_exp_value fdecls x2])
  | _ -> random_constant_expr


and max_size_of_type (fdecls:cfundeclarations_int) (t:typ) =
  match fenv#get_type_unrolled t with
  | TInt (IChar, _)
  | TInt (ISChar, _)
  | TInt (IUChar, _) -> int_constant_expr 1
  | TInt _ -> int_constant_expr max_sizes.sizeof_int
  | TFloat _ -> int_constant_expr max_sizes.sizeof_float
  | TVoid _ -> int_constant_expr max_sizes.sizeof_void
  | TPtr _ -> int_constant_expr max_sizes.sizeof_ptr
  | TArray (et,Some len,_) ->
     XOp (XMult, [max_exp_value fdecls len; max_size_of_type fdecls et])
  | TArray _ -> random_constant_expr
  | TFun _ -> int_constant_expr max_sizes.sizeof_fun
  | TNamed _ -> random_constant_expr
  | TComp _ -> random_constant_expr
  | TEnum _ -> int_constant_expr max_sizes.sizeof_enum
  | TBuiltin_va_list _ -> random_constant_expr


let max_size_of_exp_type (fdecls:cfundeclarations_int) (x:exp) =
  max_size_of_type fdecls (type_of_exp fdecls x)


let byte_offset_of_field (_fdecls:cfundeclarations_int) (_f:fieldinfo) =
  random_constant_expr


let update_type
      (enum_lgmap:(string,string) H.t) (comp_lgmap:(int,int) H.t) (t:typ) =
  let rec update_typ t =
    let update_arg (name,ty,attr) = (name,update_typ ty,attr) in
    let update_opt_args optArgs =
      match optArgs with
      | Some args -> Some (List.map update_arg args)
      | None -> None in
    match t with
    | TEnum (ename,attr) ->
      begin
	try TEnum (H.find enum_lgmap ename,attr) with
	  Not_found ->
	  ch_error_log#add
            "enum not found" (LBLOCK [STR "update_type "; STR ename]);
	  t
      end
    | TComp (ckey, attr) ->
      begin
	try
	  TComp (H.find comp_lgmap ckey, attr)
	with
	  Not_found ->
	  ch_error_log#add
            "comp not found" (LBLOCK [STR "update_type: "; INT ckey]);
	  t
      end
    | TPtr (tt, attr) -> TPtr (update_typ tt, attr)
    | TArray (tt, x, attr) -> TArray (update_typ tt, x, attr)
    | TFun (tt, args, vararg, attr) ->
       TFun (update_typ tt,update_opt_args args, vararg, attr)
    | _ -> t in
  update_typ t


let get_pointer_expr_target_type (fdecls:cfundeclarations_int) (e:exp) =
  let ty = type_of_exp fdecls e in
  match ty with
  | TPtr (t,_) -> t
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [STR "not a pointer type: "; typ_to_pretty ty]))
