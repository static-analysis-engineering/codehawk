(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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

(* extchlib *)
open CHPretty

(* cchlib *)
open CCHBasicTypes

module H = Hashtbl

let list_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
  let length = List.length in
  if (length l1) < (length l2) then
    -1
  else if (length l1) > (length l2) then
    1
  else
    List.fold_right2 (fun e1 e2 a -> if a = 0 then (f e1 e2) else a) l1 l2 0

let list_table_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
  let length = List.length in
  if (length l1) < (length l2) then
    -1
  else if (length l1) > (length l2) then
    1
  else
    List.fold_right2 (fun e1 e2 a -> if a = 0 then (f e1 e2) else a) l1 l2 0

let option_compare  (x1:'a option) (x2:'a option) (f:'a -> 'a -> int): int =
  match (x1,x2) with
  | (Some s1, Some s2) -> f s1 s2
  | (Some _, _) -> -1
  | (_, Some _) -> 1
  | _ -> 0
    
let pair_compare
      (p1:('a * 'b))
      (p2:('a * 'b))
      (f1:'a -> 'a -> int)
      (f2:'b -> 'b -> int):int =
  let l0 = f1 (fst p1) (fst p2) in
  if l0 = 0 then f2 (snd p1) (snd p2) else l0

let triple_compare
      (p1:('a * 'b * 'c))
      (p2:('a * 'b * 'c))
      (f1:'a -> 'a -> int)
      (f2:'b -> 'b -> int)
      (f3:'c -> 'c -> int) =
  let (x1,y1,z1) = p1 in
  let (x2,y2,z2) = p2 in
  let l0 = f1 x1 x2 in
  if l0 = 0 then
    let l1 = f2 y1 y2 in
    if l1 = 0 then
      f3 z1 z2
    else l1
  else l0

let varuse_compare (v1: varuse) (v2: varuse) = Stdlib.compare v1 v2

let fielduse_compare (f1: fielduse) (f2: fielduse) = Stdlib.compare f1 f2

let table_to_pretty t =
  let p = ref [] in
  let _ =
    H.iter (fun k v ->
        p := (LBLOCK [INT k; STR " -> "; INT v; NL]) :: !p) t in
  LBLOCK [STR "table: "; NL; INDENT (3,LBLOCK !p); NL]

let location_compare (loc1:location) (loc2:location) =
  let l0 = Stdlib.compare loc1.byte loc2.byte in
  if l0 = 0 then
    let l1 = Stdlib.compare loc1.line loc2.line in
    if l1 = 0 then
      Stdlib.compare loc1.file loc2.file
    else
      l1
  else
    l0

let rec typ_compare 
    ?(ctable:(int,int) H.t option)
    ?(constr:(int,int) H.t option)
    (t1:typ) (t2:typ) =
  let funarg_list_compare (a1:funarg list) (a2:funarg list) = 
    let length = List.length in
    if (length a1) < (length a2) then
      -1
    else if (length a1) > (length a2) then
      1
    else 
      List.fold_right2 
	(fun (_,at1,_) (_,at2,_) a ->
          if a = 0 then
	    typ_compare ?ctable ?constr at1 at2
          else
            a) a1 a2 0 in
  match (t1,t2) with
  | (TVoid _, TVoid _) -> 0
  | (TVoid _, _) -> -1
  | (_, TVoid _) -> 1
  | (TInt (k1,_), TInt (k2,_)) -> Stdlib.compare k1 k2
  | (TInt _, _) -> -1
  | (_, TInt _) -> 1
  | (TFloat (k1,_), TFloat (k2,_)) -> Stdlib.compare k1 k2
  | (TFloat _, _) -> -1
  | (_, TFloat _) -> 1
  | (TPtr (t1,_) , TPtr (t2,_)) -> typ_compare ?ctable ?constr t1 t2
  | (TPtr _, _) -> -1
  | (_, TPtr _) -> 1
  | (TArray (t1,e1,_), TArray (t2,e2,_)) ->
    let l0 = typ_compare ?ctable ?constr t1 t2 in 
    if l0 = 0 then option_compare e1 e2 exp_compare else l0
  | (TArray _, _) -> -1
  | (_, TArray _) -> 1
  | (TFun (rt1,a1,v1,_), TFun (rt2,a2,v2,_)) ->
    let l0 = typ_compare ?ctable ?constr rt1 rt2 in
    if l0 = 0 then
      let l1 = match (a1,a2) with 
	| (Some al1,Some al2) -> funarg_list_compare al1 al2 
	| (Some _, _) -> -1
	| (_, Some _) -> 1
	| (None,None) -> 0 in
      if l1 = 0 then Stdlib.compare v1 v2
      else l1
    else 0
  | (TFun _, _) -> -1
  | (_, TFun _) -> 1
  | (TNamed (n1,_), TNamed (n2,_)) -> Stdlib.compare n1 n2
  | (TNamed _, _) -> -1
  | (_, TNamed _) -> 1
  | (TComp (l1,_), TComp (g2,_)) ->
    begin
      match (ctable,constr) with
	(Some t, Some c) ->
	  if H.mem t l1 then Stdlib.compare (H.find t l1) g2
	  else begin H.add c l1 g2 ; 0 end
      | _ -> Stdlib.compare l1 g2
    end
  | (TComp _, _) -> -1
  | (_, TComp _) -> 1
  | (TEnum (n1,_), TEnum (n2,_)) -> Stdlib.compare n1 n2
  | (TEnum _, _) -> -1
  | (_, TEnum _) -> 1
  | (TBuiltin_va_list _, TBuiltin_va_list _) -> 0
    
and constant_compare (c1:constant) (c2:constant) =
  match (c1,c2) with
  | (CInt (i1,_,_), CInt(i2,_,_)) -> Int64.compare i1 i2
  | (CInt _, _) -> -1
  | (_, CInt _) -> 1
  | (CStr s1, CStr s2) -> Stdlib.compare s1 s2
  | (CStr _, _) -> -1
  | (_, CStr _) -> 1
  | (CWStr l1, CWStr l2) -> list_compare l1 l2 Int64.compare
  | (CWStr _, _) -> -1
  | (_, CWStr _) -> 1
  | (CChr c1, CChr c2) -> Char.compare c1 c2
  | (CChr _, _) -> -1
  | (_, CChr _) -> 1
  | (CReal (f1,_,_), CReal (f2,_,_)) -> Stdlib.compare f1 f2
  | (CReal _, _) -> -1
  | (_, CReal _) -> 1
  | (CEnum (e1,iname1,ename1), CEnum (e2,iname2,ename2)) ->
    let l0 = Stdlib.compare iname1 iname2 in
    if l0 = 0 then 
      let l1 = Stdlib.compare ename1 ename2 in
      if l1 = 0 then
	exp_compare e1 e2
      else l1
    else l0
      
and offset_compare (o1:offset) (o2:offset) =
  match (o1,o2) with
  | (NoOffset, NoOffset) -> 0
  | (NoOffset, _) -> -1
  | (_, NoOffset) -> 1
  | (Field (f1,o1), Field (f2,o2)) ->
    let l0 = fielduse_compare f1 f2 in if l0 = 0 then offset_compare o1 o2 else l0
  | (Field _, _) -> -1
  | (_, Field _) -> 1
	| (Index (e1,o1), Index (e2,o2)) ->
	  let l0 = exp_compare e1 e2 in if l0 = 0 then offset_compare o1 o2 else l0
	      
and lhost_compare (h1:lhost) (h2:lhost) =
  match (h1,h2) with
  | (Var v1, Var v2) -> varuse_compare v1 v2
  | (Var _, _) -> -1
  | (_, Var _) -> 1
  | (Mem e1, Mem e2) -> exp_compare e1 e2
    
and lval_compare (v1:lval) (v2:lval) =
  let l0 = lhost_compare (fst v1) (fst v2) in if l0 = 0 then offset_compare (snd v1) (snd v2) else l0

and opt_exp_compare e1 e2 =
  match (e1,e2) with
  | (Some e1,Some e2) -> exp_compare e1 e2
  | (Some _,None) -> -1
  | (None,Some _) -> 1
  | (None,None) -> 0
    
and exp_compare (e1:exp) (e2:exp) =
  match (e1,e2) with
  | (Const c1, Const c2) -> constant_compare c1 c2
  | (Const _, _) -> -1
  | (_, Const _) -> 1
  | (Lval l1, Lval l2) -> lval_compare l1 l2
  | (Lval _, _) -> -1
  | (_, Lval _) -> 1
  | (SizeOf t1, SizeOf t2) -> typ_compare t1 t2
  | (SizeOf _, _) -> -1
  | (_, SizeOf _) -> 1
  | (SizeOfE e1, SizeOfE e2) -> exp_compare e1 e2
  | (SizeOfE _, _) -> -1
  | (_, SizeOfE _) -> 1
  | (SizeOfStr s1, SizeOfStr s2) -> Stdlib.compare s1 s2
  | (SizeOfStr _, _) -> -1
  | (_, SizeOfStr _) -> 1
  | (AlignOf t1, AlignOf t2) -> typ_compare t1 t2
  | (AlignOf _, _) -> -1
  | (_, AlignOf _) -> 1
  | (AlignOfE e1, AlignOfE e2) -> exp_compare e1 e2
  | (AlignOfE _, _) -> -1
  | (_, AlignOfE _) -> 1
  | (UnOp (op1,e1,t1), UnOp (op2,e2,t2)) ->
    let l0 = Stdlib.compare op1 op2 in
    if l0 = 0 then 
      let l1 = exp_compare e1 e2 in
      if l1 = 0 then typ_compare t1 t2
      else l1
    else l0
  | (UnOp _, _) -> -1
  | (_, UnOp _) -> 1
  | (BinOp (op1,x1,y1,t1), BinOp (op2,x2,y2,t2)) ->
    let l0 = Stdlib.compare op1 op2 in
    if l0 = 0 then
      let l1 = exp_compare x1 x2 in
      if l1 = 0 then 
	let l2 = exp_compare y1 y2 in
	if l2 = 0 then
	  typ_compare t1 t2
	else l2
      else l1
    else l0
  | (BinOp _, _) -> -1
  | (_, BinOp _) -> 1
  | (Question (x1,y1,z1,t1), Question (x2,y2,z2,t2)) ->
    let l0 = exp_compare x1 x2 in
    if l0 = 0 then
      let l1 = exp_compare y1 y2 in
      if l1 = 0 then
	let l2 = exp_compare z1 z2 in
	if l2 = 0 then
	  typ_compare t1 t2
	else l2
      else l1
    else l0
  | (Question _, _) -> -1
  | (_, Question _) -> 1
  | (CastE (t1,e1), CastE (t2,e2)) ->	
    let l0 = typ_compare t1 t2 in if l0 = 0 then exp_compare e1 e2 else l0
  | (CastE _, _) -> -1
  | (_, CastE _) -> 1
  | (AddrOf l1, AddrOf l2) -> lval_compare l1 l2
  | (AddrOf _, _) -> -1
  | (_, AddrOf _) -> 1
  | (AddrOfLabel l1, AddrOfLabel l2) -> Stdlib.compare l1 l2
  | (AddrOfLabel _, _) -> -1
  | (_, AddrOfLabel _) -> 1
  | (StartOf l1, StartOf l2) -> lval_compare l1 l2
  | (StartOf _,_) -> -1
  | (_, StartOf _) -> 1
  | (FnApp (loc1,e1,el1), FnApp (loc2,e2,el2)) ->
    let l0 = location_compare loc1 loc2 in
    if l0 = 0 then
      let l1 = exp_compare e1 e2 in
      if l1 = 0 then list_compare el1 el2 opt_exp_compare else l1
    else l0
  | (FnApp _,_) -> -1
  | (_,FnApp _) -> 1
  | (CnApp (s1,el1,t1),CnApp (s2,el2,t2)) ->
    let l0 = Stdlib.compare s1 s2 in
    if l0 = 0 then
      list_compare el1 el2 opt_exp_compare
    else
      l0
      
and eitem_compare (eitem1:eitem) (eitem2:eitem) =
  let (iname1,iexp1,_) = eitem1 in
  let (iname2,iexp2,_) = eitem2 in
  let l0 = Stdlib.compare iname1 iname2 in
  if l0 = 0 then
    exp_compare iexp1 iexp2
  else
    l0
      
and fieldinfo_structural_compare 
    (ctable:(int,int) H.t)
    (constr:(int,int) H.t)
    (finfo1:fieldinfo) (finfo2:fieldinfo) =
  let l0 = Stdlib.compare finfo1.fname finfo2.fname in
  if l0 = 0 then
    typ_compare ~ctable ~constr finfo1.ftype finfo2.ftype
  else
    l0
    
and enuminfo_structural_compare einfo1 einfo2 : int = 
  list_compare einfo1.eitems einfo2.eitems eitem_compare
    
and compinfo_structural_compare
    (ctable:(int,int) H.t)
    (cinfo1:compinfo) (cinfo2:compinfo) =
  let constr = H.create 3 in
  let l0 = Stdlib.compare cinfo1.cstruct cinfo2.cstruct in
  let result =
    if l0 = 0 then	
      list_compare cinfo1.cfields cinfo2.cfields 
	(fieldinfo_structural_compare ctable constr) else l0 in
  (result, constr)

and fieldinfo_compare (finfo1:fieldinfo) (finfo2:fieldinfo) =
  let l0 = Stdlib.compare finfo1.fname finfo2.fname in
  if l0 = 0 then typ_compare finfo1.ftype finfo2.ftype else l0
    
and compinfo_compare (cinfo1:compinfo) (cinfo2:compinfo) =
  let l0 = Stdlib.compare cinfo1.cstruct cinfo2.cstruct in
  if l0 = 0 then
    let h1 = H.create 3 in
    let h2 = H.create 3 in
    list_compare cinfo1.cfields cinfo2.cfields (fieldinfo_structural_compare h1 h2)
  else
    l0
      
let varinfo_compare (vinfo1:varinfo) (vinfo2:varinfo) =
  match (vinfo1.vstorage,vinfo2.vstorage) with
  | (Static,Static) ->
    let l0 = Stdlib.compare vinfo1.vname vinfo2.vname in
    if l0 = 0 then Stdlib.compare vinfo1.vdecl.file vinfo2.vdecl.file else l0
  | (Static,_) -> -1
  | (_, Static) -> 1
  | _ -> Stdlib.compare vinfo1.vname vinfo2.vname
    
