(* =============================================================================
   CodeHawk C Analyzer
   Author: Alexander Bakst
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026      Aarno Labs LLC

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
open CHUtils

(* chtuil *)
open CHLogger
open CHTimingLog
open CHTraceResult

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHBasicUtil
open CCHDeclarations
open CCHLibTypes
open CCHFileContract
open CCHSettings

(* cchpre *)
open CCHPreFileIO
open CCHPreTypes
open CCHProofScaffolding

module H = Hashtbl
module TR = CHTraceResult

let (let* ) x f = CHTraceResult.tbind f x

let result_of_option (msg: string) (o: 'a option): ('a, string list) result =
  match o with
  | None -> Error [msg]
  | Some r -> Ok r

(* let p2s = CHPrettyUtil.pretty_to_string *)

let fenv = CCHFileEnvironment.file_environment

let is_errno_location_call (e:exp): bool =
  match e with
  | Lval (Var ("__errno_location", _), NoOffset) -> true
  | _ -> false

let is_int_ptr (env: cfundeclarations_int) (v: int): bool =
  TR.tfold
    ~ok:(fun vinfo ->
      let ty = vinfo.vtype in
      let ty_unroll = CCHFileEnvironment.file_environment#get_type_unrolled ty in
      match ty_unroll with
      | TPtr (TInt _, _) -> true
      | _ -> false)
    ~error:(fun err ->
      begin
        log_error_result
          ~tag:"is_int_ptr"
          ~msg:env#functionname
          __FILE__ __LINE__
          [String.concat ", " err];
        false
      end)
    (env#get_varinfo_by_vid v)

(* Collect all pointers `x` from a target expression that have non-deref uses *)
class pointer_use_expr_walker_t (env:cfundeclarations_int) =
object
  inherit CCHTypesTransformer.exp_walker_t as super

  val vars = new IntCollections.set_t

  method get_vars = vars#toList

  method! walk_lval (l:lval) =
    match l with
    | Mem (Lval (Var _, NoOffset)), NoOffset -> ()
    | Var x, _ when is_int_ptr env (snd x) -> vars#add (snd x)
    | _ -> super#walk_lval l
end


(* All pointers `x` in `e` that have non-deref uses *)
let blacklistable_pointers_of_exp (env: cfundeclarations_int) (e: exp): int list =
  let walker = new pointer_use_expr_walker_t env in
  let _ = walker#walk_exp e in
  walker#get_vars

(* Collect all variables that must alias __errno_location(). This fails if
   we see anything that makes this analysis non-trivial,
   like x = __errno_location(); y = x; ... *)
class errno_location_block_walker_t (env:cfundeclarations_int) =
object (self)
  inherit CCHTypesTransformer.block_walker_t as super

  (* vids *)
  val errno_pointers = new IntCollections.set_t

  (*
     These are vids of pointers, x, whose uses in the program are anything _EXCEPT_
     1) x = __errno_location()
     2) *x

     e.g. the following instructions or expressions would result in adding x
     to this set:
     y = x, x + 1,
  *)
  val blacklist_pointers = new IntCollections.set_t

  method invalid_errno_uses: IntCollections.set_t =
     errno_pointers#inter blacklist_pointers

  method errno_pointers: IntCollections.set_t = errno_pointers

  method! walk_instr (i:instr) =
    match i with
    | Call (Some (Var x, _), f, [], _) when is_errno_location_call f ->
      self#add_errno_pointer (snd x);
      super#walk_instr i

    | _ ->
      super#walk_instr i

  method! walk_rhs (e:exp) = self#blacklist_exp_ptrs e

  method! walk_arg (e:exp) = self#blacklist_exp_ptrs e

  method private blacklist_exp_ptrs (e:exp) =
    blacklistable_pointers_of_exp env e
    |> List.iter self#add_blacklist

  method private add_errno_pointer (ptr:int) =
    errno_pointers#add ptr

  method private add_blacklist(ptr:int) =
    blacklist_pointers#add ptr

end

(* Check that we can easily track aliases of __errno_location() *)
let check_errno_pointer_uses_in_block (env: cfundeclarations_int) (b: block) =
  let block_walker = new errno_location_block_walker_t env in
  let _ = block_walker#walk_block b in
  if (block_walker#invalid_errno_uses)#isEmpty then
    Some (block_walker#errno_pointers)
  else
    None

(* At every *read* of errno, check that we *must* observe a known local write, where
   such a write is either:
   1) a direct assignment (e.g. errno = 0)
   2) a write due to a library call (e.g. fopen in the branch where fopen returned NULL)
*)
class po_creator_t
        (f:fundec) (errno_aliases: IntCollections.set_t) =
object (self)
  method private f = f
  method private fname = self#f.svar.vname

  method create_proof_obligations: unit =
    self#create_po_block (mk_program_context ()) self#f.sbody

  method private create_po_block (context: program_context_int) (b: block): unit=
    List.iter (fun s -> self#create_po_stmt (context#add_stmt s.sid) s) b.bstmts

  method private create_po_stmt (context: program_context_int) (s: stmt): unit =
    self#create_po_stmtkind context s.skind

  method private create_po_stmtkind (context: program_context_int): stmtkind -> unit = function
  | Instr l ->
    List.iteri
      (fun i instr -> self#create_po_instr (context#add_instr i) instr) l
  | Return (Some e, loc) ->
    self#create_po_exp context#add_return e loc
  | Return (None, _) ->
    ()
  | If (e, b1, b2, loc) ->
    begin
      self#create_po_exp context#add_if_expr e loc;
      self#create_po_block context#add_if_then b1;
      self#create_po_block context#add_if_else b2;
    end
  | Switch (e, b, _, loc) ->
    begin
      self#create_po_exp context#add_switch_expr e loc;
      self#create_po_block context b;
    end
  | Loop (b, _, _, _) ->
    begin
      self#create_po_block context b;
    end
  | ComputedGoto (e, l) ->
    self#create_po_exp context#add_goto e l
  | Block b -> self#create_po_block context b
  | Break _
  | Continue _
  | Goto _ -> ()
  | TryFinally _
  | TryExcept _  ->
    pr_debug [ STR "Errno analysis does not currently support TryFinally or TryExcept "]

  method private create_po_instr (context: program_context_int) (i: instr): unit =
    match i with
    | Set (_, e, loc) -> self#create_po_exp context#add_rhs e loc
    | Call (ret, callee, args, loc) ->
      begin
        self#create_po_exp context#add_ftarget callee loc;
        (match ret with
        | None -> ()
        | Some r -> self#create_po_lval context#add_lhs r loc);
        List.iteri (fun i e -> self#create_po_exp (context#add_arg (i+1)) e loc) args;
      end
    | VarDecl _
    | Asm _ -> ()

  method create_po_exp (context: program_context_int) (e: exp) (loc: location) =
    match e with
    | Lval (Mem (Lval (Var x, NoOffset)), NoOffset) when errno_aliases#has (snd x) ->
      self#add_ppo PErrnoWritten loc context;
    | Lval (Mem e, _) -> self#create_po_exp context#add_lval#add_mem e loc
    | Lval (Var _, _) -> ()
    | UnOp (_, e, _) -> self#create_po_exp context#add_unop e loc
    | BinOp (_, e1, e2, _) ->
      begin
        self#create_po_exp (context#add_binop 1) e1 loc;
        self#create_po_exp (context#add_binop 2) e2 loc;
      end
    | Question (c, e1, e2, _) ->
      begin
        self#create_po_exp (context#add_question 1) c loc;
        self#create_po_exp (context#add_question 2) e1 loc;
        self#create_po_exp (context#add_question 3) e2 loc;
      end
    | CastE (_, e) -> self#create_po_exp context#add_cast e loc
    | AddrOf lval -> self#create_po_lval context#add_addrof lval loc
    | StartOf lval -> self#create_po_lval context#add_startof lval loc
    | CnApp _
    | FnApp _ -> () (* thus defined in undefined bx analysis*)
    | Const _
    | SizeOf _
    | AlignOf _
    | AlignOfE _
    | SizeOfStr _
    | AddrOfLabel _
    | SizeOfE _ -> ()

  method private create_po_lval context lval loc: unit =
    match lval with
    | (Var _, _) -> ()
    | (Mem e, _) -> self#create_po_exp context#add_mem e loc

  method private add_ppo
                  (pred: po_predicate_t)
                  (loc: location)
                  (ctxt: program_context_int) =
    (proof_scaffolding#get_ppo_manager self#fname)#add_ppo loc ctxt pred
end

let process_function (fname:string): unit traceresult =
  let _ = log_info "Process function %s [%s:%d]" fname __FILE__ __LINE__ in
  let fundec = read_function_semantics fname in
  let _ = read_proof_files fname fundec.sdecls in
  let* errnos = check_errno_pointer_uses_in_block fundec.sdecls fundec.sbody
             |> result_of_option "Can not run errno analysis, found code we can not analyze"
  in
  let _ = (new po_creator_t fundec errnos)#create_proof_obligations in
  let _ = CCHCheckValid.process_function fname in
  let _ = save_analysis_digests fname in
  let _ = save_proof_files fname in
  let _ = save_api fname in
  Ok ()


let errno_po_process_file () =
  try
    let cfilename = system_settings#get_cfilename in
    let _ = read_cfile_dictionary () in
    let _ = read_cfile_interface_dictionary () in
    let cfile = read_cfile () in
    let _ = fenv#initialize cfile in
    let _ = cdeclarations#index_location call_sink in
    let functions = fenv#get_application_functions in
    let _ =
      log_info
        "Cfile %s initialized with %d functions [%s:%d]"
        cfilename (List.length functions)
        __FILE__ __LINE__ in
    let _ = read_cfile_contract () in
    let _ = file_contract#collect_file_attributes in
    let u_r =
      List.fold_left (fun acc f ->
          tbind (fun () -> process_function f.vname) acc) (Ok ()) functions in
    tbind (fun () ->
        begin
          save_cfile_assignment_dictionary ();
          save_cfile_predicate_dictionary ();
          save_cfile_interface_dictionary();
          save_cfile_dictionary ();
          Ok (save_cfile_context ())
        end)
      u_r
  with
  | CHXmlReader.IllFormed ->
     Error [__FILE__ ^ ":" ^ (string_of_int __LINE__);
            "ill-formed content: " ^ system_settings#get_cfilename]
