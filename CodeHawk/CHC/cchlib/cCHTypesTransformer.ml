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

(* chlib *)
open CHUtils
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

class exp_transformer_t:exp_transformer_int =
object (self)

  method transform_exp (exp:exp) = 
    let tx = self#transform_type in
    let lx = self#transform_lval in
    let ex = self#transform_exp in
    let elx = List.map (fun a -> 
      match a with Some e -> Some (ex e) | _ -> None) in
    match exp with
    | Lval lval -> Lval (lx lval)
    | SizeOf t -> SizeOf (tx t)
    | SizeOfE e -> SizeOfE (ex e)
    | AlignOf t -> AlignOf (tx t)
    | AlignOfE e -> AlignOfE (ex e)
    | UnOp (unop,e,t) -> UnOp (unop, ex e, tx t)
    | BinOp (binop,e1,e2,t) -> BinOp (binop,ex e1, ex e2, tx t)
    | Question (e1,e2,e3,t) -> Question (ex e1, ex e2, ex e3, tx t)
    | CastE (t,e) -> CastE (tx t, ex e)
    | AddrOf lval -> AddrOf (lx lval)
    | StartOf lval -> StartOf (lx lval)
    | FnApp (loc,e,el) -> FnApp (loc, ex e, elx el)
    | CnApp (s,el,t) -> CnApp (s, elx el, tx t)
    | _ -> exp

  method transform_type (typ:typ) = 
    let tx = self#transform_type in
    let ex = self#transform_exp in
    let oex o = match o with Some e -> Some (ex e) | _ -> None in
    let fx (n,t,attr) = (n, tx t, attr) in
    let oelx o = match o with Some el -> Some (List.map fx el) | _ -> None in
    match typ with
    | TPtr (t,attr) -> TPtr (tx t, attr)
    | TArray (t,e,attr) -> TArray (tx t, oex e, attr)
    | TFun (t,ol,b,attr) -> TFun (tx t, oelx ol, b, attr)
    | _ -> typ

  method transform_lval (lval:lval) = 
    (self#transform_lhost (fst lval), self#transform_offset (snd lval))

  method transform_lhost (lhost:lhost) =
    let ex = self#transform_exp in
    match lhost with
    | Var _ -> lhost
    | Mem e -> Mem (ex e)

  method transform_offset (offset:offset) = 
    let ex = self#transform_exp in
    let ox = self#transform_offset in
    match offset with
    | Index (e,offset) -> Index (ex e, ox offset)
    | _ -> offset

end

class exp_walker_t =
object (self)

  method walk_exp (exp:exp) =
    let tx = self#walk_type in
    let ex = self#walk_exp in
    let lx = self#walk_lval in
    let elx = List.iter (fun o -> match o with Some e -> ex e | _ -> ()) in
    match exp with
    | Lval lval | AddrOf lval | StartOf lval -> lx lval
    | SizeOf t | AlignOf t -> tx t
    | SizeOfE e | AlignOfE e -> ex e
    | UnOp (_,e,t) -> begin ex e ; tx t end
    | BinOp (_,e1,e2,t) -> begin ex e1 ; ex e2 ; tx t end
    | Question (e1,e2,e3,t) -> begin ex e1 ; ex e2 ; ex e3 ; tx t end
    | CastE (t,e) -> begin tx t ; ex e end
    | FnApp (_,e,el) -> begin ex e ; elx el end
    | CnApp (_,el,t) -> begin elx el ; tx t end
    | _ -> ()

  method walk_lval (lhost,offset) = 
    begin self#walk_lhost lhost ; self#walk_offset offset end

  method walk_lhost (lhost:lhost) =
    let ex = self#walk_exp in
    match lhost with
    | Var _ -> ()
    | Mem e -> ex e
  
  method walk_offset (offset:offset) =
    let ex = self#walk_exp in
    let ox = self#walk_offset in
    match offset with
    | Index (e,offset) -> begin ex e ; ox offset end
    | Field (_,offset) -> ox offset
    | _ -> ()

  method walk_type (typ:typ) =
    let tx = self#walk_type in
    let ex = self#walk_exp in
    let oex o = match o with Some e -> ex e | _ -> () in
    let fx (_,t,_) = tx t in
    let oelx o = match o with Some el -> List.iter fx el | _ -> () in
    match typ with
    | TPtr (t,_) -> tx t
    | TArray (t,e,_) -> begin tx t ; oex e end
    | TFun (t,ol,_,_) -> begin tx t ; oelx ol end
    | _ -> ()

end


class block_walker_t =
object (self)

  method walk_block (b:block) =
    List.iter self#walk_stmt b.bstmts

  method walk_stmt (s:stmt) =
    begin
      List.iter self#walk_label s.labels ;
      self#walk_stmtkind s.skind
    end

  method walk_label (l:label) =
    match l with
    | Label _ -> ()
    | Case (e,_) -> self#walk_rhs e
    | CaseRange (e1,e2,_) ->
       begin self#walk_rhs e1 ; self#walk_rhs e2 end
    | Default _ -> ()

  method walk_stmtkind (k:stmtkind) =
    match k with
    | Instr l -> List.iter self#walk_instr l
    | Return (Some e,_) -> self#walk_rhs e
    | Return _ -> ()
    | Goto _ -> ()
    | ComputedGoto (e,_) -> self#walk_rhs e
    | Break _ -> ()
    | Continue _ -> ()
    | If (e,b1,b2,_) ->
       begin
         self#walk_rhs e ;
         self#walk_block b1 ;
         self#walk_block b2
       end
    | Switch (e,b,_,_) ->
       begin
         self#walk_rhs e ;
         self#walk_block b
       end
    | Loop (b,_,_,_) -> self#walk_block b
    | Block b -> self#walk_block b
    | TryFinally _ -> ()
    | TryExcept _ -> ()

  method walk_instr (i:instr) =
    match i with
    | Set (lhs,rhs,_) ->
       begin
         self#walk_lhs lhs;
         self#walk_rhs rhs;
       end
    | Call (Some lhs,f,el,_) ->
       begin
         self#walk_lhs lhs ;
         self#walk_rhs f ;
         List.iter self#walk_arg el
       end
    | Call (None,f,el,_) ->
       begin
         self#walk_calltarget f ;
         List.iter self#walk_arg el
       end
    | Asm _ -> ()

  method walk_rhs (e:exp) = ()

  method walk_lhs (v:lval) = ()

  method walk_arg (e:exp) = ()

  method walk_calltarget (e:exp) = ()

end

class exp_variable_collector_t =
object (self)

  inherit exp_walker_t as super
     
  val vars = new IntCollections.set_t

  method walk_lhost (lhost:lhost) =
    match lhost with
    | Var (_,vid) -> vars#add vid
    | Mem e -> self#walk_exp e

  method get_vars = vars#toList

end

let get_exp_variables (e:exp) =
  let walker = new exp_variable_collector_t in
  let _ = walker#walk_exp e in
  walker#get_vars


class block_variable_collector_t =
object (self)

  inherit block_walker_t as super

  val vars = new IntCollections.set_t       (* vid's *)

  method private add (e:exp) = vars#addList (get_exp_variables e)

  method walk_rhs (e:exp) = self#add e

  method walk_lhs (v:lval) = self#add (Lval v)

  method walk_arg (e:exp) = self#add e

  method walk_calltarget (e:exp) = self#add e

  method get_vars = vars#toList

end 


let get_block_variables (b:block) =
  let walker = new block_variable_collector_t in
  let _ = walker#walk_block b in
  walker#get_vars
