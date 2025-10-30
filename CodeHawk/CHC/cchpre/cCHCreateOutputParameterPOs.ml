(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2025  Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHTimingLog

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHContext
open CCHDeclarations
open CCHFileContract
open CCHLibTypes
open CCHSettings
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHPreFileIO
open CCHPreTypes
open CCHProofScaffolding


let fenv = CCHFileEnvironment.file_environment


class po_creator_t (f:fundec) (pointer_parameters: varinfo list) =
object (self)

  method private f = f

  method private ftype = self#f.svar.vtype

  method private fname = self#f.svar.vname
                       
  method private pointer_parameters = pointer_parameters

  method private env = self#f.sdecls

  method private spomanager = proof_scaffolding#get_spo_manager self#fname

  method private add_ppo
                   (pred: po_predicate_t)
                   (loc: location)
                   (ctxt: program_context_int) =
    (proof_scaffolding#get_ppo_manager self#fname)#add_ppo loc ctxt pred

  method create_proof_obligations =
    self#create_po_block (mk_program_context ()) self#f.sbody

  method private create_po_block (context: program_context_int) (b: block) =
    List.iter (fun s -> self#create_po_stmt (context#add_stmt s.sid) s) b.bstmts

  method private create_po_stmt (context: program_context_int) (s: stmt) =
    self#create_po_stmtkind context s.skind

  method private create_po_stmtkind (context: program_context_int) (k: stmtkind) =
    match k with
    | Instr l ->
       List.iteri
         (fun i instr -> self#create_po_instr (context#add_instr i) instr) l

    | Return (e, loc) -> self#create_po_return context e loc

    | ComputedGoto (e, loc) -> self#create_po_computed_goto context e loc

    | If (e, thenblock, elseblock, loc) ->
       self#create_po_if context e thenblock elseblock loc

    | Switch (e, b, _, loc) -> self#create_po_switch context e b loc

    | Loop (b, loc, _, _) -> self#create_po_loop context#add_loop b loc

    | Block b -> self#create_po_block context b

    | Goto _ | Break _ | Continue _ -> ()

    | TryFinally _ | TryExcept _ ->
       pr_debug [
           STR "proof obligations for TryFinally/TryExcept not supported"; NL]

  method private create_po_loop
                   (context: program_context_int) (b: block) (_loc: location) =
    self#create_po_block context b

  method private create_po_switch
                   (context: program_context_int)
                   (e: exp)
                   (b: block)
                   (loc: location) =
    begin
      self#create_po_exp context#add_switch_expr e loc;
      self#create_po_block context b
    end

  method private create_po_if
                   (context: program_context_int)
                   (e: exp)
                   (tb: block)
                   (eb: block)
                   (loc: location) =
    begin
      self#create_po_exp context#add_if_expr e loc;
      self#create_po_block context#add_if_then tb;
      self#create_po_block context#add_if_else eb
    end

  method private create_po_computed_goto
                   (context: program_context_int) (e: exp) (loc: location) =
    self#create_po_exp context#add_goto e loc

  method private create_po_return
                   (context: program_context_int) (e:exp option) (loc: location) =
    let _ = self#spomanager#add_return loc context#add_return e in
    begin
      (match e with
       | Some x -> self#create_po_exp context#add_return x loc
       | _ -> ());
      (List.iter (fun vinfo ->
           begin
             self#add_ppo
               (POutputParameterInitialized vinfo) loc context#add_return;
             self#add_ppo
               (POutputParameterUnaltered vinfo) loc context#add_return
           end)
         self#pointer_parameters)
    end

  method private create_po_instr (context: program_context_int) (i: instr) =
    match i with
    | Set (lval, e, loc) -> self#create_po_assignment context lval e loc
    | Call (lval_o, e, el, loc) -> self#create_po_call context lval_o e el loc
    | Asm _ -> ()
    | VarDecl _ -> ()

  method private create_po_assignment
                   (context: program_context_int)
                   (lval: lval)
                   (e: exp)
                   (loc: location) =
    begin
      self#create_po_lval context#add_lhs lval loc;
      self#create_po_exp context#add_rhs e loc
    end

  method private create_po_call
                   (context: program_context_int)
                   (lval_o: lval option)
                   (e: exp)
                   (el: exp list)
                   (loc: location) =
    begin
      (match lval_o with
       | Some lval -> self#create_po_lval context#add_lhs lval loc
       | _ -> ());
      (match e with
       | Lval (Var (_vname, vid), NoOffset) ->
          self#spomanager#add_direct_call
            loc context (self#env#get_varinfo_by_vid vid) el;
       | _ ->
          begin
            self#create_po_exp context#add_ftarget e loc;
            self#spomanager#add_indirect_call loc context e el
          end);
      (List.iteri (fun i x ->
           let newcontext = context#add_arg (i + 1) in
           self#create_po_exp newcontext x loc) el)
    end

  method private create_po_exp
                   (context: program_context_int)
                   (x: exp)
                   (loc: location) =
    let has_struct_type vid =
      let vinfo = self#env#get_varinfo_by_vid vid in
      match fenv#get_type_unrolled vinfo.vtype with
      | TComp _ -> true
      | _ -> false in
    match x with
    | Const _ -> ()

    | Lval (Var (vname, vid), NoOffset) when has_struct_type vid ->
       let vinfo = self#env#get_varinfo_by_vid vid in
       begin
         match fenv#get_type_unrolled vinfo.vtype with
         | TComp (tckey, _) ->
            let cinfo = fenv#get_comp tckey in
            begin
              List.iter (fun f ->
                  self#add_ppo
                    (PInitialized
                       (Var (vname, vid), Field ((f.fname, f.fckey), NoOffset)))
                    loc
                    context)
                cinfo.cfields;
              self#create_po_lval context#add_lval (Var (vname, vid), NoOffset) loc
            end
         | _ -> ()
       end

    | Lval ((Var _, NoOffset) as lval) ->
       self#add_ppo (PInitialized lval) loc context

    | Lval lval ->
       begin
         (List.iter (fun vinfo ->
             self#add_ppo (PLocallyInitialized (vinfo, lval)) loc context)
            self#pointer_parameters);
         self#create_po_lval context#add_lval lval loc
       end

    | SizeOf _ | SizeOfE _ | SizeOfStr _ -> ()

    | AlignOf _ | AlignOfE _ -> ()

    | UnOp (_, e, _t) -> self#create_po_exp context#add_unop e loc

    | BinOp (binop, e1, e2, t) ->
       begin
         self#create_po_exp (context#add_binop 1) e1 loc;
         self#create_po_exp (context#add_binop 2) e2 loc;
         self#create_po_binop context binop e1 e2 t loc
       end

    | Question (e1, e2, e3, _t) ->
       begin
         self#create_po_exp (context#add_question 1) e1 loc;
         self#create_po_exp (context#add_question 2) e2 loc;
         self#create_po_exp (context#add_question 3) e3 loc
       end

    | CastE (_t, e) -> self#create_po_exp context#add_cast e loc

    | AddrOf l -> self#create_po_lval context#add_addrof l loc

    | AddrOfLabel _ -> ()

    | StartOf l -> self#create_po_lval context#add_startof l loc

    | FnApp _ | CnApp _ -> ()

  method private create_po_lval
                   (context: program_context_int)
                   ((host, offset): lval)
                   (loc: location) =
    match host with
    | Var (_vname, vid) ->
       let ty = (self#env#get_varinfo_by_vid vid).vtype in
       self#create_po_offset context#add_var offset ty loc
    | Mem e -> self#create_po_exp context#add_mem e loc

  method private create_po_offset
                   (context: program_context_int)
                   (o: offset)
                   (hosttyp: typ)
                   (loc: location) =
    match o with
    | NoOffset -> ()

    | Field ((fname, ckey), oo) ->
       (match fenv#get_type_unrolled hosttyp with
        | TComp (tckey, _) ->
           if tckey = ckey then
             let ftype = fenv#get_field_type ckey fname in
             self#create_po_offset (context#add_field_offset fname) oo ftype loc
           else
             ()
        | _ -> ())
      
    | Index (exp, oo) ->
       (match fenv#get_type_unrolled hosttyp with
        | TArray (tt, Some _len, _) ->
           begin
             self#create_po_exp context#add_index exp loc;
             self#create_po_offset context#add_index_offset oo tt loc
           end
        | _ -> ())
            
  method private create_po_binop
                   (_context: program_context_int)
                   (_binop: binop)
                   (_e1: exp)
                   (_e2: exp)
                   (_t: typ)
                   (_loc:location) =
    ()

end
 

let process_function (fname:string) =
  let _ = log_info "Process function %s [%s:%d]" fname __FILE__ __LINE__ in
  try
    let fundec = read_function_semantics fname in
    let fdecls = fundec.sdecls in
    let ftype = fundec.svar.vtype in
    let pointer_parameters =
      match ftype with
      | TFun (_, Some funargs, _, _) | TPtr (TFun (_, Some funargs, _, _), _) ->
         List.filter (fun (_, ty, _) ->
             (not (has_const_attribute ty))
             && (match ty with
                 | TPtr (tgt, _) -> not (has_const_attribute tgt)
                 | _ -> false)) funargs
      | _ -> [] in
    let pointer_parameters =
      List.map (fun (vname, _, _) ->
          fdecls#get_varinfo_by_name vname) pointer_parameters in
    if (List.length pointer_parameters) > 0 then
      begin
        read_proof_files fname fdecls;
        (new po_creator_t fundec pointer_parameters)#create_proof_obligations;
        CCHCheckValid.process_function fname;
        save_proof_files fname;
        save_api fname;
      end
  with
  | CCHFailure p ->
     begin
       pr_debug [
           STR "Error in processing function "; STR fname; STR ": "; p; NL];
       ch_error_log#add
         "failure" (LBLOCK [STR "function "; STR fname; STR ": "; p])
     end
  | Invalid_argument s ->
     ch_error_log#add
       "failure" (LBLOCK [ STR "function "; STR fname; STR ": "; STR s])


let output_parameter_po_process_file () =
  try
    let cfilename = system_settings#get_cfilename in
    let _ = read_cfile_dictionary () in
    let _ = read_cfile_interface_dictionary () in
    let cfile = read_cfile () in
    let _ = fenv#initialize cfile in
    let _ = cdeclarations#index_location call_sink in
    let functions = fenv#get_application_functions in
    let functions = List.filter (fun f -> not (f.vname = "main")) functions in
    let _ =
      log_info
        "Cfile %s initialized with %d functions [%s:%d]"
        cfilename (List.length functions)
        __FILE__ __LINE__ in
    let _ = read_cfile_contract () in
    let _ = file_contract#collect_file_attributes in
    begin
      List.iter (fun f -> process_function f.vname) functions;
      (*  List.iter process_global cfile.globals; *)
      save_cfile_assignment_dictionary ();
      save_cfile_predicate_dictionary ();
      save_cfile_interface_dictionary();
      save_cfile_dictionary ();
      save_cfile_context ();
    end
  with
  | CHXmlReader.IllFormed ->
      ch_error_log#add "ill-formed content" (STR system_settings#get_cfilename)
