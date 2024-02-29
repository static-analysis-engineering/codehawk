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
   
(* bchlib *)
open BCHBCTypePretty
open BCHCPURegisters
open BCHLibTypes

module H = Hashtbl

let tcd = BCHTypeConstraintDictionary.type_constraint_dictionary


let type_cap_label_to_string (c: type_cap_label_t) =
  match c with
  | FRegParameter r -> "param_" ^ (register_to_string r)
  | FStackParameter offset -> "param_off_" ^ (string_of_int offset)
  | FLocStackAddress offset -> "stackaddr_" ^ (string_of_int offset)
  | FReturn -> "rtn"
  | Load -> "load"
  | Store -> "store"
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

  method add_zerocheck_constraint (tyvar: type_variable_t) =
    self#add_constraint (TyZeroCheck (TyVariable tyvar))

  method add_subtype_constraint
           (tyvar1: type_variable_t) (tyvar2: type_variable_t) =
    self#add_constraint (TySub (TyVariable tyvar1, TyVariable tyvar2))

  method add_vc_subtype_constraint
           (tyvar: type_variable_t) (tycst: type_constant_t) =
    self#add_constraint (TySub (TyVariable tyvar, TyConstant tycst))

  method add_cv_subtype_constraint
           (tycst: type_constant_t) (tyvar: type_variable_t) =
    self#add_constraint (TySub (TyConstant tycst, TyVariable tyvar))

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
  

let mk_data_address_load_typevar
      ?(size = 4) ?(offset = 0) (dw: doubleword_int): type_variable_t =
  let capabilities = [Load; OffsetAccess (size, offset)] in
  let basevar = DataAddressType dw#to_hex_string in
  {tv_basevar = basevar; tv_capabilities = capabilities}
  
                                
let mk_data_address_store_typevar
      ?(size = 4) ?(offset = 0) (dw: doubleword_int): type_variable_t =
  let capabilities = [Store; OffsetAccess (size, offset)] in
  let basevar = DataAddressType dw#to_hex_string in
  {tv_basevar = basevar; tv_capabilities = capabilities}


let mk_gvar_type_var (dw: doubleword_int): type_variable_t =
  let basevar = GlobalVariableType dw#to_hex_string in
  {tv_basevar = basevar; tv_capabilities = []}


let mk_function_return_typevar (dw: doubleword_int): type_variable_t =
  let basevar = FunctionType dw#to_hex_string in
  {tv_basevar = basevar; tv_capabilities = [FReturn]}


let mk_function_return_load_typevar
      ?(size = 4) ?(offset = 0) (dw: doubleword_int): type_variable_t =
  let basevar = FunctionType dw#to_hex_string in
  let capabilities = [FReturn; Load; OffsetAccess (size, offset)] in
  {tv_basevar = basevar; tv_capabilities = capabilities}


let mk_function_return_caps_typevar
      ?(caps = []) (dw: doubleword_int): type_variable_t =
  {tv_basevar = FunctionType dw#to_hex_string; tv_capabilities = caps}

  
let mk_function_return_store_typevar
      ?(size = 4) ?(offset = 0) (dw: doubleword_int): type_variable_t =
  let basevar = FunctionType dw#to_hex_string in
  let capabilities = [FReturn; Store; OffsetAccess (size, offset)] in
  {tv_basevar = basevar; tv_capabilities = capabilities}
  

let mk_regparam_typevar (faddr: doubleword_int) (reg: register_t) =
  let basevar = FunctionType faddr#to_hex_string in
  {tv_basevar = basevar; tv_capabilities = [FRegParameter reg]}


let mk_regparam_load_typevar
      ?(size = 4) ?(offset = 0) (faddr: doubleword_int) (reg: register_t) =
  let basevar = FunctionType faddr#to_hex_string in
  let capabilities = [FRegParameter reg; Load; OffsetAccess (size, offset)] in
  {tv_basevar = basevar; tv_capabilities = capabilities}


let mk_regparam_load_array_typevar
      ?(size = 4) ?(offset = 0) (faddr: doubleword_int) (reg: register_t) =
  let basevar = FunctionType faddr#to_hex_string in
  let capabilities = [FRegParameter reg; Load; OffsetAccessA (size, offset)] in
  {tv_basevar = basevar; tv_capabilities = capabilities}
  

let mk_regparam_store_typevar
      ?(size = 4) ?(offset = 0) (faddr: doubleword_int) (reg: register_t) =
  let basevar = FunctionType faddr#to_hex_string in
  let capabilities = [FRegParameter reg; Store; OffsetAccess (size, offset)] in
  {tv_basevar = basevar; tv_capabilities = capabilities}


let mk_regparam_store_array_typevar
      ?(size = 4) ?(offset = 0) (faddr: doubleword_int) (reg: register_t) =
  let basevar = FunctionType faddr#to_hex_string in
  let capabilities = [FRegParameter reg; Store; OffsetAccessA (size, offset)] in
  {tv_basevar = basevar; tv_capabilities = capabilities}
  
  
let mk_stackaddress_typevar (faddr: doubleword_int) (offset: int) =
  let basevar = FunctionType faddr#to_hex_string in
  let capabilities = [FLocStackAddress offset] in
  {tv_basevar = basevar; tv_capabilities = capabilities}
