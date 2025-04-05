(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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
open CHTimingLog

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHLibTypes


let bd = BCHDictionary.bdictionary


let type_cap_label_compare (c1: type_cap_label_t) (c2: type_cap_label_t) =
  match (c1, c2) with
  | (FRegParameter r1, FRegParameter r2) -> register_compare r1 r2
  | (FRegParameter _, _) -> -1
  | (_, FRegParameter _) -> 1
  | (FStackParameter (n1, m1), FStackParameter (n2, m2)) ->
     Stdlib.compare (n1, m1) (n2, m2)
  | (FStackParameter _, _) -> -1
  | (_, FStackParameter _) -> 1
  | (FLocStackAddress n1, FLocStackAddress n2) -> Stdlib.compare n1 n2
  | (FLocStackAddress _, _) -> -1
  | (_, FLocStackAddress _) -> 1
  | (FReturn, FReturn) -> 0
  | (FReturn, _) -> -1
  | (_, FReturn) -> 1
  | (Load, Load) -> 0
  | (Load, _) -> -1
  | (_, Load) -> 1
  | (Store, Store) -> 0
  | (Store, _) -> -1
  | (_, Store) -> 1
  | (Deref, Deref) -> 0
  | (Deref, _) -> -1
  | (_, Deref) -> 1
  | (LeastSignificantByte, LeastSignificantByte) -> 0
  | (LeastSignificantByte, _) -> -1
  | (_, LeastSignificantByte) -> 1
  | (LeastSignificantHalfword, LeastSignificantHalfword) -> 0
  | (LeastSignificantHalfword, _) -> -1
  | (_, LeastSignificantHalfword) -> 1
  | (OffsetAccess (n1, m1), OffsetAccess (n2, m2)) ->
     Stdlib.compare (n1, m1) (n2, m2)
  | (OffsetAccess _, _) -> -1
  | (_, OffsetAccess _) -> 1
  | (OffsetAccessA (n1, m1), OffsetAccessA (n2, m2)) ->
     Stdlib.compare (n1, m1) (n2, m2)


let type_cap_label_to_string (c: type_cap_label_t) =
  match c with
  | FRegParameter r -> "param_" ^ (register_to_string r)
  | FStackParameter (size, offset) ->
     "param_" ^ (string_of_int size) ^ "_off_" ^ (string_of_int offset)
  | FLocStackAddress offset -> "stackaddr_" ^ (string_of_int offset)
  | FReturn -> "rtn"
  | Load -> "load"
  | Store -> "store"
  | Deref -> "deref"
  | LeastSignificantByte -> "lsb"
  | LeastSignificantHalfword -> "lsh"
  | OffsetAccess (size, offset) ->
     if size = 4 then
       "acc_" ^ (string_of_int offset)
     else
       "s_" ^ (string_of_int size) ^ "_acc_" ^ (string_of_int offset)
  | OffsetAccessA (size, offset) ->
     "se_" ^ (string_of_int size) ^ "_acca_" ^ (string_of_int offset)


let type_base_variable_to_string (v: type_base_variable_t) =
  match v with
  | FunctionType faddr -> "t_sub_" ^ faddr
  | DataAddressType gaddr -> "t_" ^ gaddr
  | GlobalVariableType gaddr -> "t_gv_" ^ gaddr
  | RegisterLhsType (reg, faddr, iaddr) ->
     "t_rlhs_" ^ (register_to_string reg) ^ "_" ^ faddr ^ "_" ^ iaddr
  | LocalStackLhsType (off, faddr, iaddr) ->
     "t_lslhs_" ^ (string_of_int off) ^ "_" ^ faddr ^ "_" ^ iaddr


let type_variable_to_string (v: type_variable_t) =
  type_base_variable_to_string v.tv_basevar
  ^ (match v.tv_capabilities with
     | [] -> ""
     | l -> "." ^ (String.concat "." (List.map type_cap_label_to_string l)))


let type_constant_to_string (c: type_constant_t) =
  match c with
  | TyAsciiDigit -> "t_digit"
  | TyAsciiCapsLetter -> "t_caps"
  | TyAsciiSmallLetter -> "t_letter"
  | TyAsciiControl -> "t_ctrl"
  | TyAsciiPrintable -> "t_ascii_p"
  | TyAscii -> "t_ascii"
  | TyExtendedAscii -> "t_ascii_x"
  | TyZero -> "t_nil"
  | TyTInt (sg, si) ->
     (match sg with
      | Signed -> "t_signed"
      | Unsigned -> "t_unsigned"
      | SignedNeutral -> "t_signed_neutral")
       ^ "(" ^ (string_of_int si) ^ ")"
  | TyTStruct (_, name) -> "t_struct_" ^ name
  | TyTFloat k -> float_type_to_string k
  | TyTUnknown -> "t_top"
  | TyBottom -> "t_bottom"


let type_term_to_string (t: type_term_t) =
  match t with
  | TyVariable v -> type_variable_to_string v
  | TyConstant c -> type_constant_to_string c


let type_constraint_to_string (c: type_constraint_t) =
  match c with
  | TyVar t -> "VAR " ^ (type_term_to_string t)
  | TySub (t1, t2) ->
     (type_term_to_string t1) ^ " <: " ^ (type_term_to_string t2)
  | TyGround (t1, t2) ->
     (type_term_to_string t1) ^ " <:> " ^ (type_term_to_string t2)
  | TyZeroCheck t -> "ZeroCheck(" ^ (type_term_to_string t) ^ ")"


let mk_intvalue_type_constant (i: int): type_constant_t option =
  if i < 0 || i > 0xfe then
    None
  else
    if i = 0 then
      Some TyZero
    else if i >= 0x30 && i <= 0x39 then
      Some TyAsciiDigit
    else if i >= 0x41 && i <= 0x5a then
      Some TyAsciiCapsLetter
    else if i >= 0x61 && i <= 0x7a then
      Some TyAsciiSmallLetter
    else if i <= 0x1f then
      Some TyAsciiControl
    else if i >= 0x20 && i <= 0x7e then
      Some TyAsciiPrintable
    else if i <= 0x7f then
      Some TyAscii
    else
      Some TyExtendedAscii


let mk_int_type_constant (signedness: signedness_t) (size: int): type_constant_t =
  TyTInt (signedness, size)


let mk_float_type_constant (fkind: fkind_t): type_constant_t =
  TyTFloat fkind


let mk_struct_type_constant (key: int) (name: string): type_constant_t =
  TyTStruct (key, name)


let join_tc_fkind (fk1: fkind_t) (fk2: fkind_t) =
  match fk1, fk2 with
  | FComplexLongDouble,
    (FComplexFloat | FComplexDouble | FComplexLongDouble) ->
     TyTFloat FComplexLongDouble
  | FComplexLongDouble, _ -> TyTUnknown
  | (FComplexFloat | FComplexDouble), FComplexLongDouble ->
     TyTFloat FComplexLongDouble
  | _, FComplexLongDouble -> TyTUnknown
  | FComplexDouble, (FComplexFloat | FComplexDouble) -> TyTFloat FComplexDouble
  | FComplexFloat, FComplexDouble -> TyTFloat FComplexDouble
  | FComplexFloat, FComplexFloat -> TyTFloat FComplexFloat
  | FLongDouble, (FLongDouble | FDouble | FFloat) -> TyTFloat FLongDouble
  | (FDouble | FFloat), FLongDouble -> TyTFloat FLongDouble
  | FDouble, (FDouble | FFloat) -> TyTFloat FDouble
  | FFloat, FDouble -> TyTFloat FDouble
  | FFloat , FFloat -> TyTFloat FFloat
  | _, _ -> TyTUnknown


let join_tc_integer
      (s1: (signedness_t * int)) (s2: signedness_t * int)
    : (signedness_t * int) option =
  match s1, s2 with
  | (sg1, size1), (sg2, size2) when sg1 = sg2 -> Some (sg1, max size1 size2)
  | (Signed, size1), (SignedNeutral, size2) when size1 >= size2 ->
     Some (Signed, size1)
  | (SignedNeutral, size1), (Signed, size2) when size1 <= size2 ->
     Some (Signed, size2)
  | (Unsigned, size1), (SignedNeutral, size2) when size1 >= size2 ->
     Some (Unsigned, size1)
  | (SignedNeutral, size1), (Unsigned, size2) when size1 <= size2 ->
     Some (Unsigned, size2)
  | (Signed, size1), (Unsigned, size2) when size1 > size2 ->
     Some (Signed, size1)
  | (Unsigned, size1), (Signed, size2) when size1 < size2 ->
     Some (Signed, size2)
  | _ -> None


let join_tc (t1: type_constant_t) (t2: type_constant_t): type_constant_t =
  match t1, t2 with
  | TyBottom, _ -> t2
  | _, TyBottom -> t1
  | TyTUnknown, _ -> TyTUnknown
  | _, TyTUnknown -> TyTUnknown
  | TyTStruct (i, _), TyTStruct (j, _) when i=j -> t1
  | TyTStruct (i, _), TyTStruct (j, _) when is_sub_struct i j -> t2
  | TyTStruct (i, _), TyTStruct (j, _) when is_sub_struct j i -> t1
  | TyTStruct _, _ -> TyTUnknown
  | _, TyTStruct _ -> TyTUnknown
  | TyTFloat fk1, TyTFloat fk2 -> join_tc_fkind fk1 fk2
  | TyTFloat _, _ -> TyTUnknown
  | _, TyTFloat _ -> TyTUnknown
  | TyTInt (sg1, s1), TyTInt (sg2, s2) ->
     (match join_tc_integer (sg1, s1) (sg2, s2) with
      | Some (sg, si) -> TyTInt (sg, si)
      | _ -> TyTUnknown)
  | TyTInt _, _ -> t1
  | _, TyTInt _ -> t2
  | _, _ -> TyTInt (SignedNeutral, 8)


let type_constant_join (cl: type_constant_t list): type_constant_t =
  List.fold_left (fun acc c -> join_tc acc c) TyBottom cl


let mk_type_basevar (basevar: type_base_variable_t): type_variable_t =
  {tv_basevar = basevar; tv_capabilities = []}


let mk_function_typevar (faddr: string): type_variable_t =
  mk_type_basevar (FunctionType faddr)


let mk_data_address_typevar (gaddr: string): type_variable_t =
  mk_type_basevar (DataAddressType gaddr)


let mk_global_variable_typevar (gaddr: string): type_variable_t =
  mk_type_basevar (GlobalVariableType gaddr)


let mk_reglhs_typevar (reg: register_t) (faddr: string) (iaddr: string)
    : type_variable_t =
  mk_type_basevar (RegisterLhsType (reg, faddr, iaddr))


let mk_localstack_lhs_typevar (off: int) (faddr: string) (iaddr: string)
    : type_variable_t =
  mk_type_basevar (LocalStackLhsType (off, faddr, iaddr))


let add_capability (caps: type_cap_label_t list) (tv: type_variable_t)
    :type_variable_t =
  {tv with tv_capabilities = tv.tv_capabilities @ caps}


let drop_capability (cap: type_cap_label_t) (tv: type_variable_t)
    : type_variable_t =
  {tv with tv_capabilities =
             match List.rev tv.tv_capabilities with
             | tvcap :: _ when (type_cap_label_compare cap tvcap) = 0 ->
                List.rev (List.tl (List.rev tv.tv_capabilities))
             | _ -> tv.tv_capabilities}


let pop_capability (t: type_term_t): (type_term_t * type_cap_label_t) option =
  match t with
  | TyConstant _ -> None
  | TyVariable tv ->
     match tv.tv_capabilities with
     | [] -> None
     | _ ->
        let cap = List.hd (List.rev tv.tv_capabilities) in
        let caps = List.rev (List.tl (List.rev tv.tv_capabilities)) in
        let newvar = {tv_basevar = tv.tv_basevar; tv_capabilities = caps} in
        Some (TyVariable newvar, cap)


let add_load_capability ?(size = 4) ?(offset = 0) (tv: type_variable_t)
    :type_variable_t =
  add_capability [Load; OffsetAccess (size, offset)] tv


let add_store_capability ?(size = 4) ?(offset = 0) (tv: type_variable_t)
    :type_variable_t =
  add_capability [Store; OffsetAccess (size, offset)] tv


let add_array_access_capability ?(offset = 0) (size: int) (tv: type_variable_t)
    :type_variable_t =
  add_capability [OffsetAccessA (size, offset)] tv


let add_deref_capability (tv: type_variable_t): type_variable_t =
  add_capability [Deref] tv


let drop_deref_capability (tv: type_variable_t): type_variable_t =
  drop_capability Deref  tv


let add_return_capability (tv: type_variable_t): type_variable_t =
  add_capability [FReturn] tv


let add_freg_param_capability (register: register_t) (tv: type_variable_t)
    :type_variable_t =
  add_capability [FRegParameter register] tv


let add_fstack_param_capability ?(size = 4) (offset: int) (tv: type_variable_t)
    :type_variable_t =
  add_capability [FStackParameter (size, offset)] tv


let add_stack_address_capability (offset: int) (tv: type_variable_t)
    : type_variable_t =
  add_capability [FLocStackAddress offset] tv


let mk_cty_term (c: type_constant_t): type_term_t = TyConstant c


let mk_vty_term (v: type_variable_t): type_term_t = TyVariable v


let has_reg_lhs_basevar
      (reg: register_t) (faddr: string) (iaddr: string) (t: type_term_t) =
  match t with
  | TyVariable tv ->
     (match tv.tv_basevar with
      | RegisterLhsType (r, f, i) ->
         (bd#index_register reg) = (bd#index_register r)
         && faddr = f
         && iaddr = i
      | _ -> false)
  | _ -> false


let has_stack_lhs_basevar
      (offset: int) (faddr: string) (t: type_term_t): bool =
  match t with
  | TyVariable tv ->
     (match tv.tv_basevar with
      | LocalStackLhsType (o, f, _) -> offset = o && faddr = f
      | _ -> false)
  | _ -> false


let has_same_function_basevar (tv1: type_variable_t) (tv2: type_variable_t) =
  let get_function (tv: type_variable_t) =
    match tv.tv_basevar with
    | FunctionType f -> Some f
    | DataAddressType _ -> None
    | GlobalVariableType _ -> None
    | RegisterLhsType (_, f, _) -> Some f
    | LocalStackLhsType (_, f, _) -> Some f in
  match (get_function tv1, get_function tv2) with
  | (Some f1, Some f2) -> f1 = f2
  | _ -> false


let ikind_to_signedsize (k: ikind_t): (signedness_t * int) =
  match k with
  | IChar -> (SignedNeutral, 8)
  | ISChar -> (Signed, 8)
  | IUChar -> (Unsigned, 8)
  | IWChar -> (Unsigned, 16)
  | IBool -> (Unsigned, 1)
  | IInt -> (Signed, 32)
  | IUInt -> (Unsigned, 32)
  | IShort -> (Signed, 16)
  | IUShort -> (Unsigned, 16)
  | ILong -> (Signed, 32)
  | IULong -> (Unsigned, 32)
  | ILongLong -> (Signed, 64)
  | IULongLong -> (Unsigned, 64)
  | IInt128 -> (Signed, 128)
  | IUInt128 -> (Unsigned, 128)
  | INonStandard (true, size) -> (Signed, size)
  | INonStandard (false, size) -> (Unsigned, size)


let rec mk_btype_constraint (tv: type_variable_t) (ty: btype_t)
        : type_constraint_t option =
  match (resolve_type ty) with
  | Error e ->
     begin
       log_error_result __FILE__ __LINE__ e;
       None
     end
  | Ok ty ->
     match ty with
     | TInt (ikind, _) ->
        let (signedness, size) = ikind_to_signedsize ikind in
        Some (TyGround
                (TyVariable tv, TyConstant (mk_int_type_constant signedness size)))
     | TFloat (fkind, _, _) ->
        Some (TyGround (TyVariable tv, TyConstant (mk_float_type_constant fkind)))
     | TComp (key, _) ->
        let cinfo = bcfiles#get_compinfo key in
        Some (TyGround (TyVariable tv, TyConstant (TyTStruct (key, cinfo.bcname))))
     | TPtr (pty, _) ->
        let ptv = add_deref_capability tv in
        mk_btype_constraint ptv pty
     | TArray (elty, Some (Const (CInt (i64, _, _))), _) ->
        let size = Int64.to_int i64 in
        let atv = add_array_access_capability size tv in
        mk_btype_constraint atv elty
     | TArray (elty, _, _) ->
        let size_r = size_of_btype elty in
        (match size_r with
         | Ok size ->
            let atv = add_array_access_capability size tv in
            mk_btype_constraint atv elty
         | Error e ->
            begin
              log_warning
                "Unable to create array access capability (no size): %s [%s:%d]"
                (String.concat "; " e)
                __FILE__ __LINE__;
              None
            end)
     | rty ->
        begin
          log_result
            __FILE__ __LINE__
            ["make btype constraint not yet supported for "
             ^ (btype_to_string ty)
             ^ " (" ^ (btype_to_string rty) ^ ")"];
          None
        end


let signedsize_to_ikind (sg: signedness_t) (size: int): ikind_t =
  match sg, size with
  | SignedNeutral, 8 -> IChar
  | (SignedNeutral | Signed), _ ->
     (match size with
      | 1 -> IBool
      | 8 -> ISChar
      | 16 -> IShort
      | 32 -> IInt
      | 64 -> ILongLong
      | 128 -> IInt128
      | _ ->
         raise (BCH_failure (LBLOCK [STR "Invalid wordsize: "; INT size])))
  | Unsigned, _ ->
     (match size with
      | 1 -> IBool
      | 8 -> IUChar
      | 16 -> IUShort
      | 32 -> IUInt
      | 64 -> IULongLong
      | 128 -> IUInt128
      | _ ->
         raise (BCH_failure (LBLOCK [STR "Invalid wordsize: "; INT size])))


let type_constant_to_btype (tc: type_constant_t) =
  match tc with
  | TyAsciiDigit
    | TyAsciiCapsLetter
    | TyAsciiSmallLetter
    | TyAsciiControl
    | TyAsciiPrintable
    | TyAscii
    | TyExtendedAscii -> t_char
  | TyZero -> t_int
  | TyTInt (signedness, size) ->
     let ikind = signedsize_to_ikind signedness size in
     TInt (ikind, [])
  | TyTStruct (key, _) -> get_compinfo_struct_type (bcfiles#get_compinfo key)
  | TyTFloat fkind -> TFloat (fkind, FScalar, [])
  | TyBottom -> t_unknown
  | TyTUnknown -> t_unknown


let type_constraint_terms (c: type_constraint_t): type_term_t list =
  match c with
  | TySub (t1, t2)
    | TyGround (t1, t2) -> [t1; t2]
  | TyZeroCheck t -> [t]
  | TyVar _ -> []


let type_term_prefix_closure (t: type_term_t): type_term_t list =
  match t with
  | TyConstant _ -> [t]
  | TyVariable tv ->
     let tvv = {tv_basevar = tv.tv_basevar; tv_capabilities = []} in
     let (_, newterms) =
       (List.fold_left (fun (prev, acc) cap ->
            let newtv = add_capability [cap] prev in
            (newtv, (TyVariable (newtv)) :: acc)) (tvv, []) tv.tv_capabilities) in
     (TyVariable tvv) :: newterms


let join_integer_btypes (btypes: btype_t list): btype_t option =
  match btypes with
  | [] -> None
  | [t] -> Some t
  | _ ->
     let t0 = List.hd btypes in
     match t0 with
     | TInt (ikind, _) ->
        let (signedness, size) = ikind_to_signedsize ikind in
        let tc0 = mk_int_type_constant signedness size in
        let tc =
          List.fold_left (fun acc ty ->
              match acc with
              | None -> None
              | Some tc ->
                 (match ty with
                  | TInt (ikind, _) ->
                     let (signedness, size) = ikind_to_signedsize ikind in
                     let tc' = mk_int_type_constant signedness size in
                     let tc'' = join_tc tc tc' in
                     (match tc'' with
                      | TyTInt _ -> Some tc''
                      | _ -> None)
                  | _ -> None)) (Some tc0) btypes in
        (match tc with
         | Some tc -> Some (type_constant_to_btype tc)
         | _ -> None)
     | _ -> None
