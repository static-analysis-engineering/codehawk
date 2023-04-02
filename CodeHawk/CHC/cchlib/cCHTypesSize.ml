(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
 * Differences:                                                                   *
 * (1) size and alignment expressions are computed symbolically instead of with   *
 *     grounded values extracted from the local machine;                          *
 * (2) bitfields are not handled; the size of a struct that contains bitfields is *
 *     an unknown expression.
 * ============================================================================== *)

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open Xsimplify

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

exception SizeOfError of string * typ

let pr_expr = xpr_formatter#pr_expr

let c0 = zero_constant_expr
let c1 = int_constant_expr 1
let c8 = int_constant_expr 8


type offset_accumulator_t = {
  oa_first_free : xpr_t ;           (* the first free byte *)
  oa_last_field_start : xpr_t ;     (* byte where the last field started *)
  oa_last_field_width : xpr_t ;     (* width of the previous field (without padding) *)
}
  
let start_oa = {
  oa_first_free = c0 ;
  oa_last_field_start = c0 ;
  oa_last_field_width = c0 ;
}
  
let random_oa = {
  oa_first_free = random_constant_expr ;
  oa_last_field_start = random_constant_expr ;
  oa_last_field_width = random_constant_expr
  }

let oa_to_pretty (oa:offset_accumulator_t) =
  LBLOCK [ STR "oa_ff: " ; xpr_formatter#pr_expr oa.oa_first_free ;
           STR "; oa_lfs: " ; xpr_formatter#pr_expr oa.oa_last_field_start ;
           STR "; oa_lfw: " ; xpr_formatter#pr_expr oa.oa_last_field_width ]
  
(* with ground values: (numBytes + roundto - 1) land (lnot (roundto - 1)) *
 * adapted to ((numBytes + roundto - 1) / roundto) * roundto              *)
let add_trailing (numBytes:xpr_t) (roundto:xpr_t) : xpr_t =
  let bound = XOp (XMinus, [ XOp (XPlus, [ numBytes ; roundto ]) ; c1 ]) in
  let divr = XOp (XDiv, [ bound ; roundto ]) in
  XOp (XMult, [ divr ; roundto ])
    
let byte_size_of_int (m:machine_sizes_t) (ik:ikind) : xpr_t =
  match ik with
  | IChar | ISChar | IUChar -> c1
  | IBool -> m.sizeof_bool
  | IInt | IUInt -> m.sizeof_int
  | IShort | IUShort -> m.sizeof_short
  | ILong | IULong -> m.sizeof_long
  | ILongLong | IULongLong -> m.sizeof_longlong
    
let alignof_int (m:machine_sizes_t) (ik:ikind) : xpr_t =
  match ik with
  | IChar | ISChar | IUChar -> c1
  | IBool -> m.alignof_bool
  | IInt | IUInt -> m.alignof_int
  | IShort | IUShort -> m.alignof_short
  | ILong | IULong -> m.alignof_long
  | ILongLong | IULongLong -> m.alignof_longlong
    
let byte_size_of_float (m:machine_sizes_t) (fk:fkind) : xpr_t =
  match fk with
  | FFloat -> m.sizeof_float
  | FDouble -> m.sizeof_double
  | FLongDouble -> m.sizeof_longdouble
    
let alignof_float (m:machine_sizes_t) (fk:fkind) : xpr_t =
  match fk with
  | FFloat -> m.alignof_float
  | FDouble -> m.alignof_double
  | FLongDouble -> m.alignof_longdouble
    
(* ignoring alignment attributes *)
let rec alignof_type (env:file_environment_int) (t:typ) : xpr_t =
  let m = env#get_machine_sizes in
  let align = 
    match t with
    | TInt (ik,_) -> alignof_int m ik
    | TEnum (name,_) -> alignof_type env (TInt ((env#get_enum name).ekind, []))
    | TFloat (fk,_) -> alignof_float m fk
    | TNamed (name,_) -> alignof_type env (env#get_type name)
    | TComp (ckey,_) -> alignof_comp env (env#get_comp ckey)
    | TArray (tt,_,_) -> alignof_type env tt
    | TPtr _ | TBuiltin_va_list _ -> m.alignof_ptr
    | TVoid _ as t -> raise (SizeOfError ("void", t))
    | TFun _ as t -> raise (SizeOfError ("function", t)) in
  simplify_xpr align
    
and alignof_comp (env:file_environment_int) (comp:compinfo) : xpr_t =
  let aligns = List.map (fun finfo -> alignof_type env finfo.ftype) comp.cfields in
  let maxalign = List.fold_left (fun mx a ->
                     match mx with
                     | None -> None
                     | Some mx ->
                        match a with
                        | XConst (IntConst n) -> if mx#gt n then Some mx else Some n
                        | _ -> None) (Some numerical_zero) aligns in
  match maxalign with
  | Some mx -> num_constant_expr mx
  | _ -> simplify_xpr (XOp (Xf "max", aligns))
    
    
and byte_size_of_typ (env:file_environment_int) (t:typ) : xpr_t =
  let m = env#get_machine_sizes in
  let size = 
    match t with
    | TInt (ik,_) -> byte_size_of_int m ik 
    | TFloat (fk,_) -> byte_size_of_float m fk
    | TEnum (name,_) -> byte_size_of_typ env (TInt ((env#get_enum name).ekind , []))
    | TPtr _ -> m.sizeof_ptr 
    | TBuiltin_va_list _ -> m.sizeof_ptr 
    | TNamed (name,_) -> byte_size_of_typ env (env#get_type name)
    | TComp (ckey,_) -> byte_size_of_comp env t (env#get_comp ckey)
    | TArray (tt, Some len, _) -> byte_size_of_array env tt len
    | TArray (_, None, _) -> zero_constant_expr
    | TVoid _ -> m.sizeof_void 
    | TFun _ -> m.sizeof_fun in
  simplify_xpr size
    
and byte_size_of_comp env t comp : xpr_t = 
  if comp.cstruct then    (* struct *)
    let lastoff = List.fold_left (fun acc finfo -> offset_of_field_acc env ~finfo ~acc)
      start_oa comp.cfields in
    let size = add_trailing lastoff.oa_first_free (alignof_type env (TComp (comp.ckey,[]))) in
    begin
      chlog#add "comp size"
                (LBLOCK [ STR "ckey: " ; INT comp.ckey ; STR " ; size: " ;
                          xpr_formatter#pr_expr size ]) ;
      size
    end
  else   (* union *)
    let max = XOp (Xf "max",
                   List.map (fun finfo -> byte_size_of_typ env finfo.ftype) comp.cfields) in
    begin
      chlog#add "union size"
                (LBLOCK [ STR "ckey: " ; INT comp.ckey ; STR " ; size: " ;
                          xpr_formatter#pr_expr max ]) ;
      add_trailing max (alignof_type env t)
    end
      
and byte_size_of_array env t len =
  let rec getlen e =
    match e with
    | Const (CInt (i64,_,_)) -> num_constant_expr (mkNumericalFromInt64 i64)
    | BinOp (PlusA, e1, e2, _) ->
       simplify_xpr (XOp (XPlus, [ getlen e1 ; getlen e2 ]))
    | BinOp (MinusA, e1, e2, _) ->
       simplify_xpr (XOp (XMinus, [ getlen e1 ; getlen e2 ]))
    | SizeOf t -> byte_size_of_typ env t
    | _ -> random_constant_expr in
  let arraylength = getlen len in
  let elsize = byte_size_of_typ env t in
  let elsize = add_trailing elsize (alignof_type env t) in
  let size = XOp (XMult, [ elsize ; arraylength ]) in
  let size = simplify_xpr size in
  size
  
(* offset in bytes 
 * returns random expr for bitfields
 *)
and offset_of_field_acc env ~(finfo:fieldinfo) ~(acc:offset_accumulator_t) : offset_accumulator_t =
  let ftype = env#get_type_unrolled finfo.ftype in
  let ftypeAlign = alignof_type env ftype in
  let ftypeByteSize = byte_size_of_typ env ftype in
  let _ = match finfo.fbitfield with
    | Some n ->
       chlog#add "bitfield in struct"
                 (LBLOCK [ STR "struct " ; INT finfo.fckey ; STR ": bitfield : " ; INT n ;
                           STR "; ftypeAlign: " ; pr_expr ftypeAlign ;
                           STR "; ftypeByteSize: " ; pr_expr ftypeByteSize ])
    | _ -> () in
  let newStart = add_trailing acc.oa_first_free ftypeAlign in
  { oa_first_free = simplify_xpr (XOp (XPlus, [ newStart ; ftypeByteSize ])) ;
    oa_last_field_start = newStart ;
    oa_last_field_width = ftypeByteSize
  }
      
