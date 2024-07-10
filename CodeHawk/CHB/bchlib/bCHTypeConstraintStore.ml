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
open BCHCPURegisters
open BCHLibTypes

module H = Hashtbl

let tcd = BCHTypeConstraintDictionary.type_constraint_dictionary


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
  | TyTStruct (key, name) -> "t_struct_" ^ name
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


class type_constraint_store_t: type_constraint_store_int =
object (self)

  val store = H.create 5

  method add_constraint (c: type_constraint_t) =
    let index = tcd#index_type_constraint c in
    if H.mem store index then
      ()
    else
      H.add store index c

  method add_var_constraint (tyvar: type_variable_t) =
    self#add_constraint (TyVar (TyVariable tyvar))

  method add_term_constraint (t: type_term_t) =
    match t with
    | TyVariable tv -> self#add_var_constraint tv
    | _ -> ()

  method add_zerocheck_constraint (tyvar: type_variable_t) =
    begin
      self#add_var_constraint tyvar;
      self#add_constraint (TyZeroCheck (TyVariable tyvar))
    end

  method add_subtype_constraint (t1: type_term_t) (t2: type_term_t) =
    begin
      self#add_term_constraint t1;
      self#add_term_constraint t2;
      self#add_constraint (TySub (t1, t2))
    end

  method add_ground_constraint (t1: type_term_t) (t2: type_term_t) =
    begin
      self#add_term_constraint t1;
      self#add_term_constraint t2;
      self#add_constraint (TyGround (t1, t2))
    end

  method toPretty =
    let constraints = ref [] in
    let _ =
      H.iter
        (fun _ v ->
          constraints :=
            (type_constraint_to_string v) :: !constraints) store in
    let constraints = List.sort Stdlib.compare !constraints in
    STR (String.concat "\n" constraints)

end


let mk_type_constraint_store () = new type_constraint_store_t


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


let add_load_capability ?(size = 4) ?(offset = 0) (tv: type_variable_t)
    :type_variable_t =
  add_capability [Load; OffsetAccess (size, offset)] tv


let add_store_capability ?(size = 4) ?(offset = 0) (tv: type_variable_t)
    :type_variable_t =
  add_capability [Store; OffsetAccess (size, offset)] tv


let add_deref_capability (tv: type_variable_t): type_variable_t =
  add_capability [Deref] tv


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
  | _ ->
     begin
       chlog#add
         "make btype constraint"
         (LBLOCK [STR "Not yet supported: "; btype_to_pretty ty]);
       None
     end
