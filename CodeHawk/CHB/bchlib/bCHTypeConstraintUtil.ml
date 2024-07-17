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

(* bchlib *)
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
  | TyTInt k -> int_type_to_string k
  | TyTStruct (_, name) -> "t_struct_" ^ name
  | TyTFloat k -> float_type_to_string k
  | TyTUnknown -> "t_top"


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


let mk_int_type_constant (ikind: ikind_t): type_constant_t =
  TyTInt ikind


let mk_float_type_constant (fkind: fkind_t): type_constant_t =
  TyTFloat fkind


let mk_struct_type_constant (key: int) (name: string): type_constant_t =
  TyTStruct (key, name)


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


let add_array_access_capability ?(size = 1) ?(offset = 0) (tv: type_variable_t)
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


let rec mk_btype_constraint (tv: type_variable_t) (ty: btype_t)
        : type_constraint_t option =
  match ty with
  | TInt (ikind, _) ->
     Some (TyGround (TyVariable tv, TyConstant (mk_int_type_constant ikind)))
  | TFloat (fkind, _, _) ->
     Some (TyGround (TyVariable tv, TyConstant (mk_float_type_constant fkind)))
  | TComp (key, _) ->
     let cinfo = bcfiles#get_compinfo key in
     Some (TyGround (TyVariable tv, TyConstant (TyTStruct (key, cinfo.bcname))))
  | TPtr (pty, _) ->
     let ptv = add_deref_capability tv in
     mk_btype_constraint ptv pty
  | TArray (elty, _, _) ->
     let atv = add_array_access_capability tv in
     mk_btype_constraint atv elty
  | _ ->
     begin
       chlog#add
         "make btype constraint"
         (LBLOCK [STR "Not yet supported: "; btype_to_pretty ty]);
       None
     end


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
  | TyTInt ikind -> TInt (ikind, [])
  | TyTStruct (key, _) -> get_compinfo_struct_type (bcfiles#get_compinfo key)
  | TyTFloat fkind -> TFloat (fkind, FScalar, [])
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
