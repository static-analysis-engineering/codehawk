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
open CHTraceResult

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHContext
open CCHDeclarations
open CCHFileContract
open CCHLibTypes
open CCHSettings
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHPreFileIO
open CCHPreTypes
open CCHProofScaffolding

module H = Hashtbl

let (let* ) x f = CHTraceResult.tbind f x

let p2s = CHPrettyUtil.pretty_to_string

let fenv = CCHFileEnvironment.file_environment


class po_creator_t
        (f:fundec) (analysisdigest: output_parameter_analysis_digest_int) =
object (self)

  method private analysisdigest = analysisdigest

  method private f = f

  method private ftype = self#f.svar.vtype

  method private fname = self#f.svar.vname

  method private active_params =
    analysisdigest#active_parameter_varinfos

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

  method private create_output_parameter_po_s
                   (context: program_context_int)
                   (loc: location) =
    (List.iter (fun vinfo ->
         let vty = fenv#get_type_unrolled vinfo.vtype in
         (match vty with
          | TPtr (ty, _) ->
             if is_integral_type ty then
               begin
                 self#add_ppo
                   (POutputParameterInitialized (vinfo, NoOffset))
                   loc context;
                 self#add_ppo
                   (POutputParameterUnaltered (vinfo, NoOffset))
                   loc context
               end
             else if is_scalar_struct_type ty then
               let offsets = get_scalar_struct_offsets ty in
               List.iter (fun offset ->
                   begin
                     self#add_ppo
                       (POutputParameterInitialized (vinfo, offset))
                       loc context;
                     self#add_ppo
                       (POutputParameterUnaltered (vinfo, offset))
                       loc context
                   end) offsets
          | _ -> ())) self#active_params)

  method private create_po_return
                   (context: program_context_int) (e:exp option) (loc: location) =
    let _ = self#spomanager#add_return loc context#add_return e in
    let _ = self#analysisdigest#add_returnsite loc context#add_return  e in
    begin
      (match e with
       | Some x ->
          begin
            self#create_po_exp context#add_return x loc;
            (match type_of_exp self#env x with
             | TPtr _ -> self#add_ppo (PValidMem x) loc context#add_return
             | _ -> ())
          end
       | _ -> ());
      self#create_output_parameter_po_s context#add_return loc
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
    let vname =
      match e with
      | Lval (Var (vname, _), _) -> vname
      | _ -> "?" in
    let _ =
      ch_info_log#add "create_po_call" (STR vname) in
    let is_ref_arg (arg: exp) =
      is_pointer_type (fenv#get_type_unrolled (type_of_exp self#env arg)) in
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
      (if List.exists is_ref_arg el then
         begin
           self#create_output_parameter_po_s context loc;
           self#analysisdigest#add_call_dependency loc context e;
           self#analysisdigest#add_callee_callsite loc context e;
           ch_info_log#add "add_callee_callsite"
             (LBLOCK [STR "context: "; STR context#to_string])
         end);
      (List.iteri (fun i x ->
           let newcontext = context#add_arg (i + 1) in
           begin
             self#create_po_exp newcontext x loc;
             (match fenv#get_type_unrolled (type_of_exp self#env x) with
              | TPtr _ ->
                 begin
                   self#add_ppo (PValidMem x) loc newcontext;
                   begin
                     self#add_ppo (POutputParameterArgument x) loc newcontext;
                     (List.iter (fun vinfo ->
                          self#add_ppo
                            (POutputParameterNoEscape (vinfo, x)) loc newcontext)
                        self#active_params);
                     self#analysisdigest#add_callee_callsite_arg
                       loc context newcontext x;
                     self#analysisdigest#add_call_dependency_arg
                       loc context newcontext x;
                     ch_info_log#add
                       "add_callee_callsite_arg"
                       (LBLOCK [STR vname; STR ": "; INT i])
                   end
                 end
              | _ -> ())
           end) el)
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
    let _ =
      List.iter (fun vinfo ->
          self#add_ppo (POutputParameterScalar (vinfo, x)) loc context)
        self#active_params in
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
                  begin
                    self#add_ppo
                      (PInitialized
                         (Var (vname, vid), Field ((f.fname, f.fckey), NoOffset)))
                      loc
                      context;
                    (List.iter (fun pvinfo ->
                         self#add_ppo
                           (PLocallyInitialized
                              (pvinfo,
                               (Var (vname, vid),
                                Field ((f.fname, f.fckey), NoOffset)))) loc context)
                       self#active_params)
                  end) cinfo.cfields;
              self#create_po_lval context#add_lval (Var (vname, vid), NoOffset) loc
            end
         | _ -> ()
       end

    | Lval ((Var _, NoOffset) as lval) ->
       self#add_ppo (PInitialized lval) loc context

    | Lval lval ->
       begin
         self#add_ppo (PInitialized lval) loc context;
         (List.iter (fun vinfo ->
             self#add_ppo (PLocallyInitialized (vinfo, lval)) loc context)
            self#active_params);
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
    | Mem e ->
       let tgttyp =
         let t = type_of_exp self#env e in
         match t with
         | TPtr (tt, _) -> tt
         | _ -> TVoid [] in
       begin
         self#create_po_exp context#add_mem e loc;
         self#create_po_dereference context#add_mem e loc;
         self#create_po_offset context#add_mem offset tgttyp loc
       end

  method private create_po_dereference
                   (context: program_context_int) (e: exp) (loc: location) =
      self#add_ppo (PValidMem e) loc context

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


let get_pointer_parameters (fundec: fundec): (int * varinfo) list =
  let fdecls = fundec.sdecls in
  match fundec.svar.vtype with
  | TFun (_, Some funargs, _, _) | TPtr (TFun (_, Some funargs, _, _), _) ->
     let funargs = List.mapi (fun i a -> (i, a)) funargs in
     List.fold_left (fun acc (i, (vname, ty, _)) ->
         match ty with
         | TPtr _ -> (i + 1, fdecls#get_varinfo_by_name vname) :: acc
         | _ -> acc) [] funargs
  | _ -> []


(* exclude pointer parameters that can be syntactically shown to not satisfy
   the conditions posed on output parameters based on their types.*)
let initialize_output_parameters
      (analysisdigest: output_parameter_analysis_digest_int)
      (ptrparams: (int * varinfo) list): unit traceresult =
  List.fold_left (fun acc (paramindex, ptrparam) ->
      match acc with
      | Error _ -> acc
      | _ ->
         let* _ = analysisdigest#add_new_parameter paramindex ptrparam in
         let pname = ptrparam.vname in
         let ptype = fenv#get_type_unrolled ptrparam.vtype in
         if has_const_attribute ptype then
           (* parameter is read-only *)
           analysisdigest#reject_parameter pname (OpConstQualifier ptype)
         else if has_deref_const_attribute ptype then
           (* pointed-to object is read-only *)
           analysisdigest#reject_parameter pname (OpConstQualifier ptype)
         else if is_char_star_type ptype then
           (* parameter is probably an array, excluded for now *)
           analysisdigest#reject_parameter pname (OpArrayType ptype)
         else if is_void_ptr_type ptype then
           (* parameter target has undetermined type, excluded for now *)
           analysisdigest#reject_parameter pname OpVoidPointer
         else
           match ptype with
           | TPtr (tgt, _) ->
              (match tgt with
               | TPtr _ ->
                  (* parameter is pointer to pointer, excluded for now *)
                  analysisdigest#reject_parameter pname (OpPointerPointer ptype)
               | TComp (ckey, _) when is_system_struct tgt ->
                  (* structs created by a system library, such as _IO__FILE_ *)
                  let compinfo = fenv#get_comp ckey in
                  analysisdigest#reject_parameter pname (OpSystemStruct compinfo)
               | TComp (ckey, _) when not (is_scalar_struct_type tgt) ->
                  (* struct has embedded arrays, excluded for now *)
                  let compinfo = fenv#get_comp ckey in
                  analysisdigest#reject_parameter pname (OpArrayStruct compinfo)
               | _ -> (* accept *) Ok ())
           | _ ->
              Error [__FILE__ ^ ":" ^ (string_of_int __LINE__);
                     "validate output parameters: unexpected non-pointer type: ";
                     (p2s (typ_to_pretty ptype))]) (Ok ()) ptrparams


let (let*) x f = CHTraceResult.tbind f x;;


let process_function (fname:string): unit traceresult =
  let _ = log_info "Process function %s [%s:%d]" fname __FILE__ __LINE__ in
  let fundec = read_function_semantics fname in
  let ptrparams = get_pointer_parameters fundec in
  let _ = read_proof_files fname fundec.sdecls in
  let* _ = proof_scaffolding#initialize_output_parameter_analysis fname in
  let* analysisdigest = proof_scaffolding#get_output_parameter_analysis fname in
  let* _ = initialize_output_parameters analysisdigest ptrparams in
  let _ = (new po_creator_t fundec analysisdigest)#create_proof_obligations in
  let _ = CCHCheckValid.process_function fname in
  let _ = save_analysis_digests fname in
  let _ = save_proof_files fname in
  let _ = save_api fname in
  Ok ()


let output_parameter_po_process_file (): unit traceresult =
  try
    let cfilename = system_settings#get_cfilename in
    let _ = read_cfile_dictionary () in
    let _ = read_cfile_interface_dictionary () in
    let cfile = read_cfile () in
    let _ = fenv#initialize cfile in
    let _ = cdeclarations#index_location call_sink in
    let functions = fenv#get_application_functions in
    (* let functions = List.filter (fun f -> not (f.vname = "main")) functions in *)
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
      (*  List.iter process_global cfile.globals; *)
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
