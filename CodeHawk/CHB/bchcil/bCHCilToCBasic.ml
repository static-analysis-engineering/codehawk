(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs LLC

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

(* bchlib *)
open BCHBCTypes


let cil_ikind_to_ikind (ik: GoblintCil.ikind): ikind_t =
  match ik with
  | GoblintCil.IChar -> IChar
  | GoblintCil.ISChar -> ISChar
  | GoblintCil.IUChar -> IUChar
  | GoblintCil.IBool -> IBool
  | GoblintCil.IInt -> IInt
  | GoblintCil.IUInt -> IUInt
  | GoblintCil.IShort -> IShort
  | GoblintCil.IUShort -> IUShort
  | GoblintCil.ILong -> ILong
  | GoblintCil.IULong -> IULong
  | GoblintCil.ILongLong -> ILongLong
  | GoblintCil.IULongLong -> IULongLong
  | GoblintCil.IInt128 -> IInt128
  | GoblintCil.IUInt128 -> IUInt128
       

let cil_fkind_to_fkind (fk: GoblintCil.fkind): fkind_t =
  match fk with
  | GoblintCil.FFloat -> FFloat
  | GoblintCil.FDouble -> FDouble
  | GoblintCil.FLongDouble -> FLongDouble
  | GoblintCil.FFloat128 -> FLongDouble   (* to be changed to new type *)
  | GoblintCil.FComplexFloat -> FComplexFloat
  | GoblintCil.FComplexFloat128 -> FComplexFloat (* to be changed to new type *)
  | GoblintCil.FComplexDouble -> FComplexDouble
  | GoblintCil.FComplexLongDouble -> FComplexLongDouble


let cil_storage_to_bstorage (s: GoblintCil.storage): bstorage_t =
  match s with
  | GoblintCil.NoStorage -> NoStorage
  | GoblintCil.Static -> Static
  | GoblintCil.Register -> Register
  | GoblintCil.Extern -> Extern


let cil_unop_to_unop (op: GoblintCil.unop): unop_t =
  match op with
  | GoblintCil.Neg -> Neg
  | GoblintCil.BNot -> BNot
  | GoblintCil.LNot -> LNot
                                                

let cil_binop_to_binop (op: GoblintCil.binop): binop_t =
  match op with
  | GoblintCil.PlusA -> PlusA
  | GoblintCil.PlusPI -> PlusPI
  | GoblintCil.IndexPI -> IndexPI
  | GoblintCil.MinusA -> MinusA
  | GoblintCil.MinusPI -> MinusPI
  | GoblintCil.MinusPP -> MinusPP
  | GoblintCil.Mult -> Mult
  | GoblintCil.Div -> Div
  | GoblintCil.Mod -> Mod
  | GoblintCil.Shiftlt -> Shiftlt
  | GoblintCil.Shiftrt -> Shiftrt
  | GoblintCil.Lt -> Lt
  | GoblintCil.Gt -> Gt
  | GoblintCil.Le -> Le
  | GoblintCil.Ge -> Ge
  | GoblintCil.Eq -> Eq
  | GoblintCil.Ne -> Ne
  | GoblintCil.BAnd -> BAnd
  | GoblintCil.BXor -> BXor
  | GoblintCil.BOr -> BOr
  | GoblintCil.LAnd -> LAnd
  | GoblintCil.LOr -> LOr


let rec cil_typ_to_btype (t: GoblintCil.typ): btype_t =
  let ca = cil_attributes_to_b_attributes in
  let ce = cil_exp_to_bexp in
  let ct = cil_typ_to_btype in
  let cf = List.map cil_funarg_to_bfunarg in
  match t with
  | GoblintCil.TVoid a -> TVoid (ca a)
  | GoblintCil.TInt (ik, a) -> TInt (cil_ikind_to_ikind ik, ca a)
  | GoblintCil.TFloat (fk, a) -> TFloat (cil_fkind_to_fkind fk, FScalar, ca a)
  | GoblintCil.TPtr (t, a) -> TPtr (ct t, ca a)
  | GoblintCil.TArray (t, Some e, a) -> TArray (ct t, Some (ce e), ca a)
  | GoblintCil.TArray (t, None, a) -> TArray (ct t, None, ca a)
  | GoblintCil.TFun (t, Some fl, b, a) -> TFun (ct t, Some (cf fl), b, ca a)
  | GoblintCil.TFun (t, None, b, a) -> TFun (ct t, None, b, ca a)
  | GoblintCil.TNamed (ti, a) -> TNamed (ti.tname, ca a)
  | GoblintCil.TComp (c, a) -> TComp (c.ckey, ca a)
  | GoblintCil.TEnum (e, a) -> TEnum (e.ename, ca a)
  | GoblintCil.TBuiltin_va_list a -> TBuiltin_va_list (ca a)


and cil_funarg_to_bfunarg (f: (string * GoblintCil.typ * GoblintCil.attributes)): bfunarg_t =
  let (name, t, a) = f in
  (name, cil_typ_to_btype t, cil_attributes_to_b_attributes a)


and cil_attrparam_to_b_attrparam (a: GoblintCil.attrparam): b_attrparam_t =
  let cp = cil_attrparam_to_b_attrparam in
  let ct = cil_typsig_to_btypsig in
  let cl = List.map cp in
  match a with
  | GoblintCil.AInt i -> AInt i
  | GoblintCil.AStr s -> AStr s
  | GoblintCil.ACons (s, l) -> ACons (s, cl l)
  | GoblintCil.ASizeOf t -> ASizeOf (cil_typ_to_btype t)
  | GoblintCil.ASizeOfE p -> ASizeOfE (cp p)
  | GoblintCil.ASizeOfS ts -> ASizeOfS (ct ts)
  | GoblintCil.AAlignOf t -> AAlignOf (cil_typ_to_btype t)
  | GoblintCil.AAlignOfE p -> AAlignOfE (cp p)
  | GoblintCil.AAlignOfS ts -> AAlignOfS (ct ts)
  | GoblintCil.AUnOp (op, p) -> AUnOp (cil_unop_to_unop op, cp p)
  | GoblintCil.ABinOp (op, p1, p2) ->
     ABinOp (cil_binop_to_binop op, cp p1, cp p2)
  | GoblintCil.ADot (p, s) -> ADot (cp p, s)
  | GoblintCil.AStar p -> AStar (cp p)
  | GoblintCil.AAddrOf p -> AAddrOf (cp p)
  | GoblintCil.AIndex (p1, p2) -> AIndex (cp p1, cp p2)
  | GoblintCil.AQuestion (p1, p2, p3) -> AQuestion (cp p1, cp p2, cp p3)


and cil_typsig_to_btypsig (t: GoblintCil.typsig): btypsig_t =
  let cal = List.map cil_attribute_to_b_attribute in
  let ct = cil_typsig_to_btypsig in
  match t with
  | GoblintCil.TSArray (t, i, al) -> TSArray (ct t, Option.map GoblintCil.Cilint.int64_of_cilint i, cal al)
  | GoblintCil.TSPtr (t, al) -> TSPtr(ct t, cal al)
  | GoblintCil.TSComp (b, s, al) -> TSComp (b, s, cal al)
  | GoblintCil.TSFun (t, Some tl, b, al) ->
     TSFun (ct t, Some (List.map ct tl), b, cal al)
  | GoblintCil.TSFun (t, None, b, al) -> TSFun (ct t, None, b, cal al)
  | GoblintCil.TSEnum (s, al) -> TSEnum (s, cal al)
  | GoblintCil.TSBase t -> TSBase (cil_typ_to_btype t)


and cil_location_to_b_location (l: GoblintCil.location): b_location_t = {
    line = l.line;
    file = l.file;
    byte = l.byte
  }


and cil_attribute_to_b_attribute (a: GoblintCil.attribute): b_attribute_t =
  match a with
  | GoblintCil.Attr (s, l) -> Attr (s, List.map cil_attrparam_to_b_attrparam l)


and cil_attributes_to_b_attributes (a: GoblintCil.attributes): b_attributes_t =
  List.map cil_attribute_to_b_attribute a


and cil_compinfo_to_bcompinfo (c: GoblintCil.compinfo): bcompinfo_t = {
    bcstruct = c.cstruct;
    bcname = c.cname;
    bckey = c.ckey;
    bcfields = List.map cil_fieldinfo_to_bfieldinfo c.cfields;
    bcattr = cil_attributes_to_b_attributes c.cattr
  }


and cil_fieldinfo_to_bfieldinfo (f: GoblintCil.fieldinfo): bfieldinfo_t = {
    bfckey = f.fcomp.ckey;
    bfname = f.fname;
    bftype = cil_typ_to_btype f.ftype;
    bfbitfield = f.fbitfield;
    bfattr = cil_attributes_to_b_attributes f.fattr;
    bfloc = cil_location_to_b_location f.floc;
    bfieldlayout = None
  }


and cil_eitem_to_beitem (i: (string * GoblintCil.exp * GoblintCil.location)): beitem_t =
  let (ename, eexp, eloc) = i in
  (ename, cil_exp_to_bexp eexp, cil_location_to_b_location eloc)


and cil_enuminfo_to_benuminfo (e: GoblintCil.enuminfo): benuminfo_t = {
    bename = e.ename;
    beitems = List.map cil_eitem_to_beitem e.eitems;
    beattr = cil_attributes_to_b_attributes e.eattr;
    bekind = cil_ikind_to_ikind e.ekind
  }


and cil_typeinfo_to_btypeinfo (t: GoblintCil.typeinfo): btypeinfo_t = {
    btname = t.tname;
    bttype = cil_typ_to_btype t.ttype
  }


and cil_varinfo_to_bvarinfo (v: GoblintCil.varinfo): bvarinfo_t = {
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


and cil_exp_to_bexp (e: GoblintCil.exp): bexp_t =
  let ce = cil_exp_to_bexp in
  let ct = cil_typ_to_btype in
  let cl = cil_lval_to_blval in
  match e with
  | GoblintCil.Const c -> Const (cil_constant_to_bconstant c)
  | GoblintCil.Lval l -> Lval (cl l)
  | GoblintCil.SizeOf t -> SizeOf (ct t)
  | GoblintCil.Real e -> Real (ce e)
  | GoblintCil.Imag e -> Imag (ce e)
  | GoblintCil.SizeOfE e -> SizeOfE (ce e)
  | GoblintCil.SizeOfStr s -> SizeOfStr s
  | GoblintCil.AlignOf t -> AlignOf (ct t)
  | GoblintCil.AlignOfE e -> AlignOfE (ce e)
  | GoblintCil.UnOp (op, e, t) -> UnOp (cil_unop_to_unop op, ce e, ct t)
  | GoblintCil.BinOp (op, e1, e2, t) -> BinOp (cil_binop_to_binop op, ce e1, ce e2, ct t)
  | GoblintCil.Question (e1, e2, e3, t) -> Question (ce e1, ce e2, ce e3, ct t)
  | GoblintCil.CastE (t, e) -> CastE (ct t, ce e)
  | GoblintCil.AddrOf l -> AddrOf (cl l)
  | GoblintCil.AddrOfLabel s -> AddrOfLabel (!s).sid
  | GoblintCil.StartOf l -> StartOf (cl l)


and cil_constant_to_bconstant (c: GoblintCil.constant): bconstant_t =
  match c with
  | GoblintCil.CInt (i64, ik, s) -> CInt (GoblintCil.Cilint.int64_of_cilint i64, cil_ikind_to_ikind ik, s)
  | GoblintCil.CStr (s, _todo_encoding) -> CStr s
  | GoblintCil.CWStr (il, _todo_encoding) -> CWStr il
  | GoblintCil.CChr c -> CChr c
  | GoblintCil.CReal (f, fk, s) -> CReal (f, cil_fkind_to_fkind fk, s)
  | GoblintCil.CEnum (e, s1, i) -> CEnum (cil_exp_to_bexp e, s1, i.ename)


and cil_lval_to_blval (lv: (GoblintCil.lhost * GoblintCil.offset)) =
  let (h, o) = lv in
  (cil_lhost_to_blhost h, cil_offset_to_boffset o)


and cil_lhost_to_blhost (h: GoblintCil.lhost) =
  match h with
  | GoblintCil.Var v -> Var (v.vname, v.vid)
  | GoblintCil.Mem e -> Mem (cil_exp_to_bexp e)


and cil_offset_to_boffset (o: GoblintCil.offset) =
  let co = cil_offset_to_boffset in
  match o with
  | GoblintCil.NoOffset -> NoOffset
  | GoblintCil.Field (f, oo) -> Field ((f.fname, f.fcomp.ckey), co oo)
  | GoblintCil.Index (e, oo) -> Index (cil_exp_to_bexp e, co oo)

    
and cil_init_to_binit (i: GoblintCil.init): binit_t =
  match i with
  | GoblintCil.SingleInit e -> SingleInit (cil_exp_to_bexp e)
  | GoblintCil.CompoundInit (t, l) ->
     CompoundInit
       (cil_typ_to_btype t,
        List.map (fun (o, i) ->
            (cil_offset_to_boffset o, cil_init_to_binit i)) l)


and cil_initinfo_to_binitinfo (i: GoblintCil.initinfo): binitinfo_t =
  match i.init with
  | Some init -> Some (cil_init_to_binit init)
  | _ -> None
                                                                 

let rec cil_block_to_bblock (b: GoblintCil.block): bblock_t = {
    battrs = cil_attributes_to_b_attributes b.battrs;
    bstmts = List.map cil_stmt_to_bstmt b.bstmts
  }


and cil_stmt_to_bstmt (s: GoblintCil.stmt): bstmt_t = {
    labels = List.map cil_label_to_blabel s.labels;
    skind = cil_stmtkind_to_bstmtkind s.skind;
    sid = s.sid;
    succs = List.map (fun (st: GoblintCil.stmt) -> st.sid) s.succs;
    preds = List.map (fun (st: GoblintCil.stmt) -> st.sid) s.preds
  }


and cil_label_to_blabel (l: GoblintCil.label): blabel_t =
  let ce = cil_exp_to_bexp in
  let cl = cil_location_to_b_location in
  match l with
  | GoblintCil.Label (s, l, b) -> Label (s, cl l, b)
  | GoblintCil.Case (e, l, _todo_col) -> Case (ce e, cl l)
  | GoblintCil.CaseRange (e1, e2, l, _todo_col) -> CaseRange (ce e1, ce e2, cl l)
  | GoblintCil.Default (l, _todo_col) -> Default (cl l)


and cil_stmtkind_to_bstmtkind (k: GoblintCil.stmtkind): bstmtkind_t =
  let cb = cil_block_to_bblock in
  let ce = cil_exp_to_bexp in
  let cl = cil_location_to_b_location in
  let cs (s: GoblintCil.stmt option) =
    match s with Some stmt -> Some (stmt.sid) | _ -> None in
  match k with
  | GoblintCil.Instr l -> Instr (List.map cil_instr_to_binstr l)
  | GoblintCil.Return (Some e, l, _el) -> Return (Some (ce e), cl l)
  | GoblintCil.Return (None, l, _el) -> Return (None, cl l)
  | GoblintCil.Goto (s, l) -> Goto (!s.sid, cl l)
  | GoblintCil.ComputedGoto (e, l) -> ComputedGoto (ce e, cl l)
  | GoblintCil.Break l -> Break (cl l)
  | GoblintCil.Continue l -> Continue (cl l)
  | GoblintCil.If (e, b1, b2, l, _todo_col) -> If (ce e, cb b1, cb b2, cl l)
  | GoblintCil.Switch (e, b, il, l, _todo_col) ->
     Switch (ce e, cb b, List.map (fun (s: GoblintCil.stmt) -> s.sid) il, cl l)
  | GoblintCil.Loop (b, l, _todo_col, s1, s2) -> Loop (cb b, cl l, cs s1, cs s2)
  | GoblintCil.Block b -> Block (cb b)


and cil_instr_to_binstr (i: GoblintCil.instr): binstr_t =
  let cl = cil_location_to_b_location in
  let ce = cil_exp_to_bexp in
  let cv = cil_lval_to_blval in
  match i with
  | GoblintCil.Set (lv, e, l, _todo_col) -> Set (cv lv, ce e, cl l)
  | GoblintCil.Call (Some lv, e, el, l, _todo_col) ->
     Call (Some (cv lv), ce e, List.map ce el, cl l)
  | GoblintCil.Call (None, e, el, l, _todo_col) -> Call (None, ce e, List.map ce el, cl l)
  | GoblintCil.VarDecl (v, l) -> VarDecl ((v.vname, v.vid), cl l)
  | GoblintCil.Asm (a, il1, bo, bi, il2, l) ->
     Asm (cil_attributes_to_b_attributes a,
          il1,
          List.map cil_asm_output_to_b_asm_output bo,
          List.map cil_asm_input_to_b_asm_input bi,
          il2,
          cl l)


and cil_asm_output_to_b_asm_output
(o: (string option * string * GoblintCil.lval)):b_asm_output_t =
  let (optname, constr, lv) = o in
  (optname, constr, cil_lval_to_blval lv)


and cil_asm_input_to_b_asm_input
(i: (string option * string * GoblintCil.exp)):b_asm_input_t =
  let (optname, constr, e) = i in
  (optname, constr, cil_exp_to_bexp e)


let cil_fundec_to_bcfundec (f: GoblintCil.fundec): bcfundec_t = {
    bsvar = cil_varinfo_to_bvarinfo f.svar;
    bsformals = List.map cil_varinfo_to_bvarinfo f.sformals;
    bslocals = List.map cil_varinfo_to_bvarinfo f.slocals;
    bsbody = cil_block_to_bblock f.sbody
  }


let cil_global_to_bglobal (g: GoblintCil.global): bglobal_t =
  let cc = cil_compinfo_to_bcompinfo in
  let ce = cil_enuminfo_to_benuminfo in
  let cl = cil_location_to_b_location in
  let cv = cil_varinfo_to_bvarinfo in
  let ct = cil_typeinfo_to_btypeinfo in
  match g with
  | GoblintCil.GType (t, l) -> GType (ct t, cl l)
  | GoblintCil.GCompTag (c, l) -> GCompTag (cc c, cl l)
  | GoblintCil.GCompTagDecl (c, l) -> GCompTagDecl (cc c, cl l)
  | GoblintCil.GEnumTag (e, l) -> GEnumTag (ce e, cl l)
  | GoblintCil.GEnumTagDecl (e, l) -> GEnumTagDecl (ce e, cl l)
  | GoblintCil.GVarDecl (v, l) -> GVarDecl (cv v, cl l)
  | GoblintCil.GVar (v, b, l) -> GVar (cv v, cil_initinfo_to_binitinfo b, cl l)
  | GoblintCil.GFun (f, l) -> GFun (cil_fundec_to_bcfundec f, cl l)
  | GoblintCil.GAsm (s, l) -> GAsm (s, cl l)
  | GoblintCil.GPragma (a, l) -> GPragma (cil_attribute_to_b_attribute a, cl l)
  | GoblintCil.GText s -> GText s


let cil_file_to_bcfile (f: GoblintCil.file): bcfile_t = {
    bfilename = f.fileName;
    bglobals = List.map cil_global_to_bglobal f.globals
  }
