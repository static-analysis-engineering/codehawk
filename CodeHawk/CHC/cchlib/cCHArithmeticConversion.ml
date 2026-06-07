(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024-2026 Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHTraceResult

(* cchlib *)
open CCHBasicTypes
open CCHTypesToPretty
open CCHUtilities


let p2s = CHPrettyUtil.pretty_to_string

let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)
let elocm (line: int): string = (eloc line) ^ ": "


let get_integer_promotion (ty: typ): typ =
  let promote_ikind (ik: ikind): ikind =
    match ik with
    | IChar | ISChar | IUChar | IShort | IBool -> IInt
    | IUShort -> IUInt
    | _ -> ik in

  match ty with
  | TInt (ik, _) -> TInt (promote_ikind ik, [])
  | TEnum (ename, _) ->
     let einfo = CCHFileEnvironment.file_environment#get_enum ename in
     TInt (promote_ikind einfo.ekind, [])
  | _ ->
     let _ =
       log_diagnostics_result
         ~tag:"get_integer_promotion: unexpected type"
         __FILE__ __LINE__
         [p2s (typ_to_pretty ty)] in
     ty


let usual_arithmetic_conversion (ty1: typ) (ty2: typ): typ traceresult =
  
  let convert_float (fk1: fkind) (fk2: fkind): fkind =
    let is_complex (fk: fkind) =
      match fk with
      | FComplexLongDouble | FComplexDouble | FComplexFloat -> true
      | _ -> false in
    match fk1, fk2 with
    | FComplexLongDouble, _ -> FComplexLongDouble
    | _, FComplexLongDouble -> FComplexLongDouble
    | FComplexDouble, _ -> FComplexDouble
    | _, FComplexDouble -> FComplexDouble
    | FComplexFloat, _ -> FComplexFloat
    | _, FComplexFloat -> FComplexFloat
    | FLongDouble, other when is_complex other -> FComplexLongDouble
    | other, FLongDouble when is_complex other -> FComplexLongDouble
    | FLongDouble, _ | _, FLongDouble -> FLongDouble
    | FDouble, other when is_complex other -> FComplexDouble
    | other, FDouble when is_complex other -> FComplexDouble
    | FDouble, _ | _, FDouble -> FDouble
    | FFloat, FFloat -> FFloat in

  let convert_int (ik1: ikind) (ik2: ikind): ikind =
    match ik1, ik2 with
    | IInt, ILong | ILong, IInt -> ILong
    | IInt, ILongLong | ILongLong, IInt -> ILongLong
    | ILong, ILongLong | ILongLong, ILong -> ILongLong
    | IUInt, IULong | IULong, IUInt -> IULong
    | _, IULongLong | IULongLong, _ -> IULongLong
    | IInt, IUInt | IUInt, IInt -> IUInt
    | ILong, IULong | IULong, ILong -> IULong
    | IInt, IULong | IULong, IInt -> IULong
    | ILong, IUInt | IUInt, ILong -> ILong
    | ILongLong, IUInt | IUInt, ILongLong -> ILongLong
    | IUInt128, _ | _, IUInt128 -> IUInt128
    | IInt128, _ | _, IInt128 -> IInt128
    | _ ->
       (* this should not happen *)
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Missing case in integer promotion: ";
                 STR (int_type_to_string ik1);
                 STR " and ";
                 STR (int_type_to_string ik2)])) in                 

  match ty1, ty2 with
  | TFloat (fk1, _), TFloat (fk2, _) -> Ok (TFloat (convert_float fk1 fk2, []))
  | TFloat _, _ -> Ok ty1
  | _, TFloat _ -> Ok ty2
  | _ ->
     let pty1 = get_integer_promotion ty1 in
     let pty2 = get_integer_promotion ty2 in
     match pty1, pty2 with
     | TInt (ik1, _), TInt (ik2, _) when ik1 = ik2 -> Ok (TInt (ik1, []))
     | TInt (ik1, _), TInt (ik2, _) -> Ok (TInt (convert_int ik1 ik2, []))
     | _ ->
        Error [(elocm __LINE__)
               ^ "not an arithmetic type: "
               ^ (p2s (typ_to_pretty ty1))
               ^ " or "
               ^ (p2s (typ_to_pretty ty2))]
