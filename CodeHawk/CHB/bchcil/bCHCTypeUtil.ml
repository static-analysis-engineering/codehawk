(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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
open CHCommon
open CHPretty

(* chutil *)
open CHLogger

(* bchil *)
open BCHBCFiles
open BCHBCUtil
open BCHCBasicTypes


let ikind_type_size (k: ikind_t) =
  match k with
  | IChar | ISChar | IUChar -> 1
  | IWChar -> 2
  | IBool -> 4
  | IInt | IUInt -> 4
  | IShort | IUShort -> 2
  | ILong | IULong -> 4
  | ILongLong | IULongLong -> 8
  | IInt128 | IUInt128 -> 16
  | INonStandard (_, s) -> s


let alignof_int (k: ikind_t): int =
  match k with
  | IChar | ISChar | IUChar -> 1
  | IWChar -> 2
  | IBool -> 4
  | IInt | IUInt -> 4
  | IShort | IUShort -> 2
  | ILong | IULong -> 4
  | ILongLong | IULongLong -> 8
  | IInt128 | IUInt128 -> 16
  | INonStandard (_, s) -> s


let fkind_type_size (k: fkind_t) =
  match k with
  | FFloat -> 4
  | FDouble -> 8
  | FLongDouble -> 16
  | FComplexFloat -> 8
  | FComplexDouble -> 16
  | FComplexLongDouble -> 32


let alignof_float (k: fkind_t): int =
  match k with
  | FFloat -> 4
  | FDouble -> 8
  | FLongDouble -> 16
  | FComplexFloat -> 8
  | FComplexDouble -> 16
  | FComplexLongDouble -> 32


let resolve_type (ty: btype_t) =
  let has_typedef = bcfiles#has_typedef in
  let get_typedef = bcfiles#get_typedef in
  let rec aux (t: btype_t) =
  match t with
  | TVoid _
    | TInt _
    | TFloat _
    | THandle _
    | TComp _
    | TEnum _
    | TCppComp _
    | TCppEnum _
    | TClass _
    | TBuiltin_va_list _
    | TVarArg _
    | TUnknown _ -> t
  | TPtr (tt, a) -> TPtr (aux tt, a)
  | TRef (tt, a) -> TRef (aux tt, a)
  | TArray (tt, e, a) -> TArray (aux tt, e, a)
  | TFun (tt, fs, b, a) -> TFun (aux tt, auxfs fs, b, a)
  | TNamed (name, a) when has_typedef name ->
     aux (add_attributes (get_typedef name) a)
  | TNamed (name, _) ->
     begin
       ch_diagnostics_log#add
         "unknown typedef"
         (LBLOCK [STR "Named type "; STR name; STR " not defined"]);
       t
     end

  and auxfs (fs: bfunarg_t list option): bfunarg_t list option =
    match fs with
    | None -> None
    | Some l -> Some (List.map (fun (s, t, a) -> (s, aux t, a)) l)

  in
  aux ty


type offset_accumulator_t = {
    oa_first_free: int;         (* the first free byte *)
    oa_last_field_start: int;   (* byte where the last field started *)
    oa_last_field_width: int    (* width of the previous field without padding *)
  }


let start_oa = {
    oa_first_free = 0;
    oa_last_field_start = 0;
    oa_last_field_width = 0
  }


let oa_to_pretty (oa: offset_accumulator_t) =
  LBLOCK [
      STR "oa_ff: ";
      INT oa.oa_first_free;
      STR "; oa_lfs: ";
      INT oa.oa_last_field_start;
      STR "; oa_lfw: ";
      INT oa.oa_last_field_width]


let add_trailing (numBytes: int) (roundto: int): int =
  (numBytes + roundto - 1) land (lnot (roundto - 1))


let rec alignof_type (t: btype_t): int =
  match t with
  | TInt (k, _) -> alignof_int k
  | TEnum (name, _) when bcfiles#has_enuminfo name ->
     alignof_type (TInt ((bcfiles#get_enuminfo name).bekind, []))
  | TEnum (name, _) ->
     let _ = chlog#add "unknown enum" (LBLOCK [STR "align: "; STR name]) in
     alignof_type (TInt (IUInt, []))
  | TFloat (fk, _, _) -> alignof_float fk
  | TNamed (name, _) -> alignof_type (resolve_type t)
  | TComp (ckey, _) when bcfiles#has_compinfo ckey ->
     alignof_comp (bcfiles#get_compinfo ckey)
  | TComp (ckey, _) ->
     let _ = chlog#add "unknown compinfo" (LBLOCK [STR "align: "; INT ckey]) in
     alignof_type (TInt (IUInt, []))
  | TArray (tt, _, _) -> alignof_type tt
  | TPtr _
    | TRef _
    | THandle _
    | TCppComp _
    | TCppEnum _
    | TClass _
    | TBuiltin_va_list _
    | TVarArg _
    | TUnknown _ -> 4   (* all systems are 32-bit for now *)
  | TVoid _ -> raise (CHFailure (LBLOCK [STR "Alignof error: tvoid"]))
  | TFun _ -> raise (CHFailure (LBLOCK [STR "Alignof error: tfun"]))


and alignof_comp (comp: bcompinfo_t): int =
  let aligns = List.map (fun finfo -> alignof_type finfo.bftype) comp.bcfields in
  List.fold_left (fun mx a -> if a > mx then mx else a) 0 aligns


and byte_size_of_typ (t: btype_t): int =
  match t with
  | TInt (ik, _) -> ikind_type_size ik
  | TFloat (fk, _, _) -> fkind_type_size fk
  | TEnum (name, _) when bcfiles#has_enuminfo name ->
     byte_size_of_typ (TInt ((bcfiles#get_enuminfo name).bekind, []))
  | TEnum (name, _) ->
     let _ = chlog#add "unknown enum" (LBLOCK [STR "size: "; STR name]) in
     byte_size_of_typ (TInt (IUInt, []))
  | TArray (tt, Some len, _) -> byte_size_of_array tt len
  | TArray (tt, _, _) -> 0
  | TComp (ckey, _) when bcfiles#has_compinfo ckey ->
     byte_size_of_comp (bcfiles#get_compinfo ckey)
  | TComp (ckey, _) ->
     let _ = chlog#add "unknown compinfo" (LBLOCK [STR "size: "; INT ckey]) in 0
  | TNamed _ -> byte_size_of_typ (resolve_type t)
  | TPtr _
    | TRef _
    | THandle _
    | TCppComp _
    | TCppEnum _
    | TClass _
    | TBuiltin_va_list _
    | TVarArg _
    | TUnknown _ -> 4   (* all systems are 32-bit for now *)
  | TVoid _ -> raise (CHFailure (LBLOCK [STR "Type size error: tvoid"]))
  | TFun _ -> raise (CHFailure (LBLOCK [STR "Type size error: tfun"]))


and byte_size_of_array (t: btype_t) (len: bexp_t) =
  let rec getlen e =
    match e with
    | Const (CInt64 (i64, _, _)) -> Int64.to_int i64
    | BinOp (PlusA, e1, e2, _) -> (getlen e1) + (getlen e2)
    | BinOp (MinusA, e1, e2, _) -> (getlen e1) - (getlen e2)
    | SizeOf t -> byte_size_of_typ t
    | _ ->
       let _ =
         ch_diagnostics_log#add
           "array size expression" (STR (exp_to_string e)) in 0 in
  let arraylen = getlen len in
  let elementsize = byte_size_of_typ t in
  let elementsize = add_trailing elementsize (alignof_type t) in
  arraylen * elementsize


and byte_size_of_comp (comp: bcompinfo_t): int =
  if comp.bcstruct then
    let lastoff =
      List.fold_left (fun acc finfo ->
          offset_of_field_acc ~finfo ~acc) start_oa comp.bcfields in
    let size =
      add_trailing lastoff.oa_first_free (alignof_type (TComp (comp.bckey, []))) in
    let _ =
      ch_diagnostics_log#add
        "struct size"
        (LBLOCK [
             STR "ckey: ";
             INT comp.bckey;
             STR " ; size: ";
             INT size]) in
    size
  else    (* union *)
    let size =
      List.fold_left (fun mx finfo ->
          let fsize = byte_size_of_typ finfo.bftype in
          if fsize > mx then
            fsize
          else
            mx) 0 comp.bcfields in
    let _ =
      ch_diagnostics_log#add
        "union size"
        (LBLOCK [
             STR "ckey: ";
             INT comp.bckey;
             STR " ; size: ";
             INT size]) in
    size


and offset_of_field_acc ~(finfo: bfieldinfo_t) ~(acc: offset_accumulator_t) =
  let ftype = resolve_type finfo.bftype in
  let falign = alignof_type ftype in
  let fsize = byte_size_of_typ ftype in
  let newstart = add_trailing acc.oa_first_free falign in
  {oa_first_free = newstart + fsize;
   oa_last_field_start = newstart;
   oa_last_field_width = fsize
  }


let has_field_layout (comp: bcompinfo_t): bool =
  List.for_all
    (fun f -> match f.bfieldlayout with Some _ -> true | _ -> false)
    comp.bcfields


let layout_fields (comp: bcompinfo_t): bcompinfo_t =
  if has_field_layout comp then
    comp
  else
    if comp.bcstruct then
      let (_, newfields) =
        List.fold_left (fun (acc, fields) finfo ->
            let fieldoffset = offset_of_field_acc ~finfo ~acc in
            let fieldlayout =
              Some (fieldoffset.oa_last_field_start,
                    fieldoffset.oa_last_field_width) in
            (fieldoffset, {finfo with bfieldlayout = fieldlayout} :: fields))
          (start_oa, []) comp.bcfields in
      {comp with bcfields = List.rev newfields}
    else   (* union *)
      let newfields =
        List.map (fun finfo ->
            let fieldlayout = Some (0, byte_size_of_typ finfo.bftype) in
            {finfo with bfieldlayout = fieldlayout}) comp.bcfields in
      {comp with bcfields = newfields}
