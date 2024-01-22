(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* cchlib *)
open CCHBasicTypes
open CCHTypesCompare


class code_walker_t =
object (self:_)

  method walk_code (f:fundec) =
    begin
      self#walk_varinfo f.svar;
      List.iter self#walk_varinfo f.sdecls#get_formals;
      List.iter self#walk_varinfo f.sdecls#get_locals;
      self#walk_block f.sbody
    end

  method walk_varinfo (_v:varinfo) = ()

  method walk_block (b:block) = List.iter self#walk_stmt b.bstmts

  method walk_stmt (s:stmt) =
    match s.skind with
    | Instr l -> List.iter self#walk_instruction l
    | Return (optExp,loc) ->
      begin
	(match optExp with Some e -> self#walk_exp e | _ -> ());
	self#walk_location loc
      end
    | Goto (_, loc) -> self#walk_location loc
    | ComputedGoto (_, loc)
    | Break loc
    | Continue loc -> self#walk_location loc
    | If (exp, b1, b2, loc) ->
      begin
	self#walk_exp exp;
	self#walk_block b1;
	self#walk_block b2;
	self#walk_location loc
      end
    | Switch (exp, b, _, loc) ->
      begin
	self#walk_exp exp;
	self#walk_block b;
	self#walk_location loc;
      end
    | Loop (b, loc, _, _) ->
      begin self#walk_block b; self#walk_location loc end
    | Block b -> self#walk_block b
    | TryFinally (b1, b2, loc) ->
      begin
	self#walk_block b1;
	self#walk_block b2;
	self#walk_location loc
      end
    | TryExcept (b1, (l, e), b2, loc) ->
      begin
	self#walk_block b1;
	List.iter (fun i -> self#walk_instruction i) l;
	self#walk_exp e;
	self#walk_block b2;
	self#walk_location loc
      end

  method walk_instruction (i:instr) =
    match i with
    | Set (lval, exp, loc) ->
      begin
	self#walk_lval lval;
	self#walk_exp exp;
	self#walk_location loc
      end
    | Call (optLval, f, l, loc) ->
      begin
	(match optLval with Some lval -> self#walk_lval lval | _ -> ());
	self#walk_exp f;
	List.iter (fun e -> self#walk_exp e) l;
	self#walk_location loc
      end
    | Asm (_,_,_,_,_,loc) -> self#walk_location loc

  method walk_lval (l:lval) =
    begin
      (match fst l with Mem e -> self#walk_exp e | _ -> () );
      self#walk_offset (snd l)
    end

  method walk_offset (o:offset) =
    match o with
    | NoOffset -> ()
    | Field (_, fo) -> self#walk_offset fo
    | Index (i, io) ->
       begin
         self#walk_exp i;
         self#walk_offset io
       end

  method walk_exp (e:exp) =
    match e with
    | Const c -> self#walk_constant c
    | Lval lval -> self#walk_lval lval
    | SizeOf t -> self#walk_typ t
    | SizeOfE e -> self#walk_exp e
    | SizeOfStr s -> self#walk_string s
    | AlignOf t -> self#walk_typ t
    | AlignOfE e -> self#walk_exp e
    | UnOp (_, e, t) ->
       begin
         self#walk_exp e;
         self#walk_typ t
       end
    | BinOp (_, e1, e2, t) ->
       begin
         self#walk_exp e1;
         self#walk_exp e2;
         self#walk_typ t
       end
    | Question (e1, e2, e3, t) ->
      begin
	self#walk_exp e1;
	self#walk_exp e2;
	self#walk_exp e3;
	self#walk_typ t
      end
    | CastE (t,e) ->
       begin
         self#walk_typ t;
         self#walk_exp e
       end
    | AddrOf lval -> self#walk_lval lval
    | AddrOfLabel _ -> ()
    | StartOf lval -> self#walk_lval lval
    | FnApp (loc, f, l) ->
      begin
	self#walk_location loc;
	self#walk_exp f;
	List.iter
          (fun o -> match o with Some e -> self#walk_exp e | _ -> ()) l
      end
    | CnApp (_, l, t) ->
      begin
	List.iter
          (fun o -> match o with Some e -> self#walk_exp e | _ -> ()) l;
	self#walk_typ t
      end

  method walk_typ (t:typ) =
    match t with
    | TPtr (tt,_) -> self#walk_typ tt
    | TArray (tt,o,_) ->
      begin
	self#walk_typ tt;
	match o with Some e -> self#walk_exp e | _ -> ()
      end
    | TFun (tt,optArgs,_,_) ->
      begin
	self#walk_typ tt;
	match optArgs with
	| Some args -> List.iter (fun (_,tt,_) -> self#walk_typ tt) args
	| _ -> ()
      end
    | _ -> ()

  method walk_constant (c:constant) =
    match c with
    | CStr s -> self#walk_string s
    | _ -> ()

  method walk_location (_loc:location) = ()

  method walk_string (_s:string) = ()

end


class call_collector_t =
object

  inherit code_walker_t

  val mutable calls = []

  method! walk_instruction i =
    match i with Call _ -> calls <- i :: calls | _ -> ()

  method get_calls = calls
end


let collect_all_callees (f:fundec) =
  let collector = new call_collector_t in
  let _ = collector#walk_code f in
  collector#get_calls


let collect_callees (f:fundec) =
  let calls = collect_all_callees f in
  List.fold_left (fun acc c ->
    match c with
    | Call (_, e, _,_ ) ->
       if List.exists (fun ee -> (exp_compare e ee) = 0) acc then
         acc else e::acc
    | _ -> acc) [] calls



class addrof_checker_t (v:varinfo) =
object

  inherit code_walker_t as super

  val mutable result = false

  method! walk_exp (e:exp) =
    match e with
    | StartOf (Var (_, vid), _)
      | AddrOf (Var (_, vid), _) when v.vid = vid ->
       result <- true
    | _ -> super#walk_exp e

  method get_result = result

end

let check_vaddrof (f:fundec) (v:varinfo) =
  let checker = new addrof_checker_t v in
  let _ = checker#walk_code f in
  checker#get_result
