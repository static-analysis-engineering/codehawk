(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchcil *)
open BCHCBasicTypes


let cil_ikind_to_ikind (ik: Cil.ikind): ikind_t =
  match ik with
  | Cil.IChar -> IChar
  | Cil.ISChar -> ISChar
  | Cil.IUChar -> IUChar
  | Cil.IBool -> IBool
  | Cil.IInt -> IInt
  | Cil.IUInt -> IUInt
  | Cil.IShort -> IShort
  | Cil.IUShort -> IUShort
  | Cil.ILong -> ILong
  | Cil.IULong -> IULong
  | Cil.ILongLong -> ILongLong
  | Cil.IULongLong -> IULongLong
  | Cil.IInt128 -> IInt128
  | Cil.IUInt128 -> IUInt128
       

let cil_fkind_to_fkind (fk: Cil.fkind): fkind_t =
  match fk with
  | Cil.FFloat -> FFloat
  | Cil.FDouble -> FDouble
  | Cil.FLongDouble -> FLongDouble
  | Cil.FComplexFloat -> FComplexFloat
  | Cil.FComplexDouble -> FComplexDouble
  | Cil.FComplexLongDouble -> FComplexLongDouble


let cil_storage_to_bstorage (s: Cil.storage): bstorage_t =
  match s with
  | Cil.NoStorage -> NoStorage
  | Cil.Static -> Static
  | Cil.Register -> Register
  | Cil.Extern -> Extern


let cil_unop_to_unop (op: Cil.unop): unop_t =
  match op with
  | Cil.Neg -> Neg
  | Cil.BNot -> BNot
  | Cil.LNot -> LNot
                                                

let cil_binop_to_binop (op: Cil.binop): binop_t =
  match op with
  | Cil.PlusA -> PlusA
  | Cil.PlusPI -> PlusPI
  | Cil.IndexPI -> IndexPI
  | Cil.MinusA -> MinusA
  | Cil.MinusPI -> MinusPI
  | Cil.MinusPP -> MinusPP
  | Cil.Mult -> Mult
  | Cil.Div -> Div
  | Cil.Mod -> Mod
  | Cil.Shiftlt -> Shiftlt
  | Cil.Shiftrt -> Shiftrt
  | Cil.Lt -> Lt
  | Cil.Gt -> Gt
  | Cil.Le -> Le
  | Cil.Ge -> Ge
  | Cil.Eq -> Eq
  | Cil.Ne -> Ne
  | Cil.BAnd -> BAnd
  | Cil.BXor -> BXor
  | Cil.BOr -> BOr
  | Cil.LAnd -> LAnd
  | Cil.LOr -> LOr


let rec cil_typ_to_btype (t: Cil.typ): btype_t =
  let ca = cil_attributes_to_b_attributes in
  let ce = cil_exp_to_bexp in
  let ct = cil_typ_to_btype in
  let cf = List.map cil_funarg_to_bfunarg in
  match t with
  | Cil.TVoid a -> TVoid (ca a)
  | Cil.TInt (ik, a) -> TInt (cil_ikind_to_ikind ik, ca a)
  | Cil.TFloat (fk, a) -> TFloat (cil_fkind_to_fkind fk, FScalar, ca a)
  | Cil.TPtr (t, a) -> TPtr (ct t, ca a)
  | Cil.TArray (t, Some e, a) -> TArray (ct t, Some (ce e), ca a)
  | Cil.TArray (t, None, a) -> TArray (ct t, None, ca a)
  | Cil.TFun (t, Some fl, b, a) -> TFun (ct t, Some (cf fl), b, ca a)
  | Cil.TFun (t, None, b, a) -> TFun (ct t, None, b, ca a)
  | Cil.TNamed (ti, a) -> TNamed (ti.tname, ca a)
  | Cil.TComp (c, a) -> TComp (c.ckey, ca a)
  | Cil.TEnum (e, a) -> TEnum (e.ename, ca a)
  | Cil.TBuiltin_va_list a -> TBuiltin_va_list (ca a)


and cil_funarg_to_bfunarg (f: (string * Cil.typ * Cil.attributes)): bfunarg_t =
  let (name, t, a) = f in
  (name, cil_typ_to_btype t, cil_attributes_to_b_attributes a)


and cil_attrparam_to_b_attrparam (a: Cil.attrparam): b_attrparam_t =
  let cp = cil_attrparam_to_b_attrparam in
  let ct = cil_typsig_to_btypsig in
  let cl = List.map cp in
  match a with
  | Cil.AInt i -> AInt i
  | Cil.AStr s -> AStr s
  | Cil.ACons (s, l) -> ACons (s, cl l)
  | Cil.ASizeOf t -> ASizeOf (cil_typ_to_btype t)
  | Cil.ASizeOfE p -> ASizeOfE (cp p)
  | Cil.ASizeOfS ts -> ASizeOfS (ct ts)
  | Cil.AAlignOf t -> AAlignOf (cil_typ_to_btype t)
  | Cil.AAlignOfE p -> AAlignOfE (cp p)
  | Cil.AAlignOfS ts -> AAlignOfS (ct ts)
  | Cil.AUnOp (op, p) -> AUnOp (cil_unop_to_unop op, cp p)
  | Cil.ABinOp (op, p1, p2) ->
     ABinOp (cil_binop_to_binop op, cp p1, cp p2)
  | Cil.ADot (p, s) -> ADot (cp p, s)
  | Cil.AStar p -> AStar (cp p)
  | Cil.AAddrOf p -> AAddrOf (cp p)
  | Cil.AIndex (p1, p2) -> AIndex (cp p1, cp p2)
  | Cil.AQuestion (p1, p2, p3) -> AQuestion (cp p1, cp p2, cp p3)


and cil_typsig_to_btypsig (t: Cil.typsig): btypsig_t =
  let cal = List.map cil_attribute_to_b_attribute in
  let ct = cil_typsig_to_btypsig in
  match t with
  | Cil.TSArray (t, i, al) -> TSArray (ct t, i, cal al)
  | Cil.TSPtr (t, al) -> TSPtr(ct t, cal al)
  | Cil.TSComp (b, s, al) -> TSComp (b, s, cal al)
  | Cil.TSFun (t, Some tl, b, al) ->
     TSFun (ct t, Some (List.map ct tl), b, cal al)
  | Cil.TSFun (t, None, b, al) -> TSFun (ct t, None, b, cal al)
  | Cil.TSEnum (s, al) -> TSEnum (s, cal al)
  | Cil.TSBase t -> TSBase (cil_typ_to_btype t)


and cil_location_to_b_location (l: Cil.location): b_location_t = {
    line = l.line;
    file = l.file;
    byte = l.byte
  }


and cil_attribute_to_b_attribute (a: Cil.attribute): b_attribute_t =
  match a with
  | Cil.Attr (s, l) -> Attr (s, List.map cil_attrparam_to_b_attrparam l)


and cil_attributes_to_b_attributes (a: Cil.attributes): b_attributes_t =
  List.map cil_attribute_to_b_attribute a


and cil_compinfo_to_bcompinfo (c: Cil.compinfo): bcompinfo_t = {
    bcstruct = c.cstruct;
    bcname = c.cname;
    bckey = c.ckey;
    bcfields = List.map cil_fieldinfo_to_bfieldinfo c.cfields;
    bcattr = cil_attributes_to_b_attributes c.cattr
  }


and cil_fieldinfo_to_bfieldinfo (f: Cil.fieldinfo): bfieldinfo_t = {
    bfckey = f.fcomp.ckey;
    bfname = f.fname;
    bftype = cil_typ_to_btype f.ftype;
    bfbitfield = f.fbitfield;
    bfattr = cil_attributes_to_b_attributes f.fattr;
    bfloc = cil_location_to_b_location f.floc;
    bfieldlayout = None
  }


and cil_eitem_to_beitem (i: (string * Cil.exp * Cil.location)): beitem_t =
  let (ename, eexp, eloc) = i in
  (ename, cil_exp_to_bexp eexp, cil_location_to_b_location eloc)


and cil_enuminfo_to_benuminfo (e: Cil.enuminfo): benuminfo_t = {
    bename = e.ename;
    beitems = List.map cil_eitem_to_beitem e.eitems;
    beattr = cil_attributes_to_b_attributes e.eattr;
    bekind = cil_ikind_to_ikind e.ekind
  }


and cil_typeinfo_to_btypeinfo (t: Cil.typeinfo): btypeinfo_t = {
    btname = t.tname;
    bttype = cil_typ_to_btype t.ttype
  }


and cil_varinfo_to_bvarinfo (v: Cil.varinfo): bvarinfo_t = {
    bvname = v.vname;
    bvtype = cil_typ_to_btype v.vtype;
    bvstorage = cil_storage_to_bstorage v.vstorage;
    bvglob = v.vglob;
    bvinline = v.vinline;
    bvdecl = cil_location_to_b_location v.vdecl;
    bvinit = cil_initinfo_to_binitinfo v.vinit;
    bvid = v.vid;
    bvattr = cil_attributes_to_b_attributes v.vattr;
    bvaddrof = v.vaddrof;
    bvparam = 0
  }


and cil_exp_to_bexp (e: Cil.exp): bexp_t =
  let ce = cil_exp_to_bexp in
  let ct = cil_typ_to_btype in
  let cl = cil_lval_to_blval in
  match e with
  | Cil.Const c -> Const (cil_constant_to_bconstant c)
  | Cil.Lval l -> Lval (cl l)
  | Cil.SizeOf t -> SizeOf (ct t)
  | Cil.Real e -> Real (ce e)
  | Cil.Imag e -> Imag (ce e)
  | Cil.SizeOfE e -> SizeOfE (ce e)
  | Cil.SizeOfStr s -> SizeOfStr s
  | Cil.AlignOf t -> AlignOf (ct t)
  | Cil.AlignOfE e -> AlignOfE (ce e)
  | Cil.UnOp (op, e, t) -> UnOp (cil_unop_to_unop op, ce e, ct t)
  | Cil.BinOp (op, e1, e2, t) -> BinOp (cil_binop_to_binop op, ce e1, ce e2, ct t)
  | Cil.Question (e1, e2, e3, t) -> Question (ce e1, ce e2, ce e3, ct t)
  | Cil.CastE (t, e) -> CastE (ct t, ce e)
  | Cil.AddrOf l -> AddrOf (cl l)
  | Cil.AddrOfLabel s -> AddrOfLabel (!s).sid
  | Cil.StartOf l -> StartOf (cl l)


and cil_constant_to_bconstant (c: Cil.constant): bconstant_t =
  match c with
  | Cil.CInt64 (i64, ik, s) -> CInt64 (i64, cil_ikind_to_ikind ik, s)
  | Cil.CStr s -> CStr s
  | Cil.CWStr il -> CWStr il
  | Cil.CChr c -> CChr c
  | Cil.CReal (f, fk, s) -> CReal (f, cil_fkind_to_fkind fk, s)
  | Cil.CEnum (e, s1, i) -> CEnum (cil_exp_to_bexp e, s1, i.ename)


and cil_lval_to_blval (lv: (Cil.lhost * Cil.offset)) =
  let (h, o) = lv in
  (cil_lhost_to_blhost h, cil_offset_to_boffset o)


and cil_lhost_to_blhost (h: Cil.lhost) =
  match h with
  | Cil.Var v -> Var (v.vname, v.vid)
  | Cil.Mem e -> Mem (cil_exp_to_bexp e)


and cil_offset_to_boffset (o: Cil.offset) =
  let co = cil_offset_to_boffset in
  match o with
  | Cil.NoOffset -> NoOffset
  | Cil.Field (f, oo) -> Field ((f.fname, f.fcomp.ckey), co oo)
  | Cil.Index (e, oo) -> Index (cil_exp_to_bexp e, co oo)

    
and cil_init_to_binit (i: Cil.init): binit_t =
  match i with
  | Cil.SingleInit e -> SingleInit (cil_exp_to_bexp e)
  | Cil.CompoundInit (t, l) ->
     CompoundInit
       (cil_typ_to_btype t,
        List.map (fun (o, i) ->
            (cil_offset_to_boffset o, cil_init_to_binit i)) l)


and cil_initinfo_to_binitinfo (i: Cil.initinfo): binitinfo_t =
  match i.init with
  | Some init -> Some (cil_init_to_binit init)
  | _ -> None
                                                                 

let rec cil_block_to_bblock (b: Cil.block): bblock_t = {
    battrs = cil_attributes_to_b_attributes b.battrs;
    bstmts = List.map cil_stmt_to_bstmt b.bstmts
  }


and cil_stmt_to_bstmt (s: Cil.stmt): bstmt_t = {
    labels = List.map cil_label_to_blabel s.labels;
    skind = cil_stmtkind_to_bstmtkind s.skind;
    sid = s.sid;
    succs = List.map (fun (st: Cil.stmt) -> st.sid) s.succs;
    preds = List.map (fun (st: Cil.stmt) -> st.sid) s.preds
  }


and cil_label_to_blabel (l: Cil.label): blabel_t =
  let ce = cil_exp_to_bexp in
  let cl = cil_location_to_b_location in
  match l with
  | Cil.Label (s, l, b) -> Label (s, cl l, b)
  | Cil.Case (e, l) -> Case (ce e, cl l)
  | Cil.CaseRange (e1, e2, l) -> CaseRange (ce e1, ce e2, cl l)
  | Cil.Default l -> Default (cl l)


and cil_stmtkind_to_bstmtkind (k: Cil.stmtkind): bstmtkind_t =
  let cb = cil_block_to_bblock in
  let ce = cil_exp_to_bexp in
  let cl = cil_location_to_b_location in
  let cs (s: Cil.stmt option) =
    match s with Some stmt -> Some (stmt.sid) | _ -> None in
  match k with
  | Cil.Instr l -> Instr (List.map cil_instr_to_binstr l)
  | Cil.Return (Some e, l) -> Return (Some (ce e), cl l)
  | Cil.Return (None, l) -> Return (None, cl l)
  | Cil.Goto (s, l) -> Goto (!s.sid, cl l)
  | Cil.ComputedGoto (e, l) -> ComputedGoto (ce e, cl l)
  | Cil.Break l -> Break (cl l)
  | Cil.Continue l -> Continue (cl l)
  | Cil.If (e, b1, b2, l) -> If (ce e, cb b1, cb b2, cl l)
  | Cil.Switch (e, b, il, l) ->
     Switch (ce e, cb b, List.map (fun (s: Cil.stmt) -> s.sid) il, cl l)
  | Cil.Loop (b, l, s1, s2) -> Loop (cb b, cl l, cs s1, cs s2)
  | Cil.Block b -> Block (cb b)
  | Cil.TryFinally (b1, b2, l) -> TryFinally (cb b1, cb b2, cl l)
  | Cil.TryExcept (b1, (il, e), b2, l) ->
     TryExcept(
         cb b1,
         (List.map cil_instr_to_binstr il, ce e),
         cb b2,
         cl l)


and cil_instr_to_binstr (i: Cil.instr): binstr_t =
  let cl = cil_location_to_b_location in
  let ce = cil_exp_to_bexp in
  let cv = cil_lval_to_blval in
  match i with
  | Cil.Set (lv, e, l) -> Set (cv lv, ce e, cl l)
  | Cil.Call (Some lv, e, el, l) ->
     Call (Some (cv lv), ce e, List.map ce el, cl l)
  | Cil.Call (None, e, el, l) -> Call (None, ce e, List.map ce el, cl l)
  | Cil.VarDecl (v, l) -> VarDecl ((v.vname, v.vid), cl l)
  | Cil.Asm (a, il1, bo, bi, il2, l) ->
     Asm (cil_attributes_to_b_attributes a,
          il1,
          List.map cil_asm_output_to_b_asm_output bo,
          List.map cil_asm_input_to_b_asm_input bi,
          il2,
          cl l)


and cil_asm_output_to_b_asm_output
(o: (string option * string * Cil.lval)):b_asm_output_t =
  let (optname, constr, lv) = o in
  (optname, constr, cil_lval_to_blval lv)


and cil_asm_input_to_b_asm_input
(i: (string option * string * Cil.exp)):b_asm_input_t =
  let (optname, constr, e) = i in
  (optname, constr, cil_exp_to_bexp e)


let cil_fundec_to_bcfundec (f: Cil.fundec): bcfundec_t = {
    bsvar = cil_varinfo_to_bvarinfo f.svar;
    bsformals = List.map cil_varinfo_to_bvarinfo f.sformals;
    bslocals = List.map cil_varinfo_to_bvarinfo f.slocals;
    bsbody = cil_block_to_bblock f.sbody
  }


let cil_global_to_bglobal (g: Cil.global): bglobal_t =
  let cc = cil_compinfo_to_bcompinfo in
  let ce = cil_enuminfo_to_benuminfo in
  let cl = cil_location_to_b_location in
  let cv = cil_varinfo_to_bvarinfo in
  let ct = cil_typeinfo_to_btypeinfo in
  match g with
  | Cil.GType (t, l) -> GType (ct t, cl l)
  | Cil.GCompTag (c, l) -> GCompTag (cc c, cl l)
  | Cil.GCompTagDecl (c, l) -> GCompTagDecl (cc c, cl l)
  | Cil.GEnumTag (e, l) -> GEnumTag (ce e, cl l)
  | Cil.GEnumTagDecl (e, l) -> GEnumTagDecl (ce e, cl l)
  | Cil.GVarDecl (v, l) -> GVarDecl (cv v, cl l)
  | Cil.GVar (v, b, l) -> GVar (cv v, cil_initinfo_to_binitinfo b, cl l)
  | Cil.GFun (f, l) -> GFun (cil_fundec_to_bcfundec f, cl l)
  | Cil.GAsm (s, l) -> GAsm (s, cl l)
  | Cil.GPragma (a, l) -> GPragma (cil_attribute_to_b_attribute a, cl l)
  | Cil.GText s -> GText s


let cil_file_to_bcfile (f: Cil.file): bcfile_t = {
    bfilename = f.fileName;
    bglobals = List.map cil_global_to_bglobal f.globals
  }
