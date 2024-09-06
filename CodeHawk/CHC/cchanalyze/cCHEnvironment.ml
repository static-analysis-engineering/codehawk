(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHStack
open CHNumerical
open CHLanguage
open CHOnlineCodeSet

(* chutil *)
open CHLogger

(* xprlib *)
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHContext
open CCHLibTypes
open CCHFileEnvironment
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHMemoryBase
open CCHPreTypes
open CCHProofScaffolding

(* cchanalyze *)
open CCHAnalysisTypes

module EU = CCHEngineUtil
module H = Hashtbl


module NumericalCollections = CHCollections.Make
  (struct
    type t = numerical_t
    let compare x y = x#compare y
    let toPretty n = n#toPretty
   end)

module ProgramContextCollections =
  CHCollections.Make
    (struct
      type t = program_context_int
      let compare c1 c2 = c1#compare c2
      let toPretty c = c#toPretty
    end)


let fenv = CCHFileEnvironment.file_environment


class c_environment_t (f:fundec) (varmgr:variable_manager_int):c_environment_int =
object(self)

  val mutable current_location:location = unknown_location

  val scope: scope_t =
    let s = EU.mkScope () in
    begin
      ignore (s#mkVariable (new symbol_t "sizeof_ptr") NUM_VAR_TYPE);
      s
    end

  val mutable current_stmt_id: int = 0
  val mutable return_var: varinfo option = None
  val return_contexts = new ProgramContextCollections.set_t

  val vmgr = varmgr
  val memregmgr = varmgr#memregmgr

  (* context -> list of augmentation call variables *)
  val callvariables = H.create 3

  val p_entry_sym = new symbol_t "$p-entry"

  method get_p_entry_sym = p_entry_sym

  method get_xpr_dictionary = vmgr#vard#xd

  method get_variable_manager = vmgr

  method get_fdecls = f.sdecls

  method get_varinfo (vid:int) = f.sdecls#get_varinfo_by_vid vid

  method get_functionname = f.svar.vname

  method get_scope = scope

  method set_current_stmt_id (id:int) = current_stmt_id <- id

  method get_current_stmt_id = current_stmt_id

  method get_current_stmt_id_label = EU.numbersymbol current_stmt_id "stmt"

  method set_current_location (c_loc:location) =  current_location <- c_loc

  method get_current_location = current_location

  (* requests for proper program variables ------------------------------------- *)

  val chifvars = Hashtbl.create 5        (* indexed by c_variable index *)

  method private add_chifvar (v:c_variable_int) (vt:variable_type_t) =
    if H.mem chifvars v#index then
      H.find chifvars v#index
    else
      let vname = new symbol_t ~seqnr:v#index v#get_name in
      let cvar = scope#mkVariable vname vt in
      begin
        H.add chifvars v#index cvar;
        cvar
      end

  method private has_chifvar index = H.mem chifvars index

  method private get_chifvar index =
    if H.mem chifvars index then H.find chifvars index else
      raise  (CCHFailure (LBLOCK [STR "Variable not found: "; INT index]))

  method mk_program_var (vinfo:varinfo) (offset:offset) (vt:variable_type_t) =
    if vinfo.vglob && vinfo.vaddrof then
      let vtype = type_of_offset self#get_fdecls vinfo.vtype offset in
      self#mk_global_memory_variable vinfo offset vtype vt
    else if vinfo.vaddrof then
      let vtype = type_of_offset self#get_fdecls vinfo.vtype offset in
      self#mk_stack_memory_variable vinfo offset vtype  vt
    else if vinfo.vglob then
      let cvar = vmgr#mk_global_variable vinfo offset in
      self#add_chifvar cvar vt
    else
      let cvar = vmgr#mk_local_variable vinfo offset in
      self#add_chifvar cvar vt

  method register_function_return (typ:typ) (vtype:variable_type_t) =
    match typ with
    | TFun (TVoid _, _, _, _) -> ()
    | TFun (t, _, _, _) -> let _ = self#mk_return_var t vtype in ()
    | _ -> ()

  method add_return_context (c:program_context_int) = return_contexts#add c

  method get_return_contexts = return_contexts#toList

  method mk_memory_variable (memrefindex:int) (offset:offset) (vt:variable_type_t) =
    let cvar = vmgr#mk_memory_variable memrefindex offset in
    self#add_chifvar cvar vt

  method mk_return_var (typ:typ) (vt:variable_type_t) =
    let cVar = vmgr#mk_return_variable typ in
    self#add_chifvar cVar vt

  method has_return_var =
    H.fold (fun k _v acc ->
        acc ||
          match (vmgr#get_variable k)#get_denotation with
          | ReturnVariable _ -> true | _ -> false) chifvars false

  method get_return_var =
    let result = H.fold (fun k v acc ->
      match acc with Some _ -> acc | _ ->
      match (vmgr#get_variable k)#get_denotation with
      | ReturnVariable _ -> Some v | _ -> None) chifvars None in
    match result with
    | Some v -> v
    | _ -> raise (CCHFailure (LBLOCK [STR "No return variable found"]))

  method get_pointer_variables (vt:variable_type_t) =
    H.fold (fun k v acc ->
        if v#getType = vt then
          if self#is_program_variable v
             && not (vmgr#is_check_variable v#getName#getSeqNumber) then
            match vmgr#get_variable_type k with
            | TPtr _ -> v :: acc
            | _ -> acc
          else
            acc
        else
          acc) chifvars []

  method mk_symbolic_value_var (x:xpr_t) (t:typ) (vt:variable_type_t) =
    let cVar = vmgr#mk_symbolic_value x t in
    self#add_chifvar cVar vt

  method mk_base_variable
           (_v:xpr_t) (_offset:offset) (_typ:typ) (vtype:variable_type_t) =
    self#get_temp vtype   (* TBD, see ref *)

  method mk_formal_ptr_base_variable (vinfo:varinfo) (vt:variable_type_t) =
    let cVar = vmgr#mk_local_variable vinfo NoOffset in
    let chifvar = self#add_chifvar cVar vt in
    let vInit = self#mk_initial_value chifvar vinfo.vtype vt  in
    vInit

  method mk_par_deref_init
           (vinfo:varinfo) (offset:offset) (ttyp:typ) (vt:variable_type_t) =
    let cVar = vmgr#mk_local_variable vinfo NoOffset in
    let chifvar = self#add_chifvar cVar vt in
    let vInit = self#mk_initial_value chifvar vinfo.vtype vt in
    let memref = vmgr#memrefmgr#mk_external_reference vInit vinfo.vtype in
    let memvar = vmgr#mk_memory_variable memref#index offset in
    let chifmemvar = self#add_chifvar memvar vt in
    let chifmemaddr = self#mk_memory_address_value memref#index NoOffset in
    let memvarinit = self#mk_initial_value chifmemvar ttyp vt in
    (chifvar,  chifmemaddr, chifmemvar, memvarinit)

  method mk_struct_par_deref
           (vinfo:varinfo) (ttyp:typ) (ckey:int) (vt:variable_type_t) =
    try
      let cVar = vmgr#mk_local_variable vinfo NoOffset in
      let chifvar = self#add_chifvar cVar vt in
      let vInit = self#mk_initial_value chifvar vinfo.vtype vt in
      let cinfo = fenv#get_comp ckey in
      List.map (fun field ->
          let fuse = (field.fname,ckey) in
          let offset = Field (fuse,NoOffset) in
          let memref = vmgr#memrefmgr#mk_external_reference
                         vInit vinfo.vtype in
          let memvar = vmgr#mk_memory_variable memref#index offset in
          let memvar = self#add_chifvar memvar vt in
          let memvarInit = self#mk_initial_value memvar field.ftype vt in
          (memvar,memvarInit)) cinfo.cfields
    with
    | Invalid_argument s ->
       begin
         ch_error_log#add
           "struct not found"
           (LBLOCK [
                STR self#get_functionname;
                STR ": ";
                STR vinfo.vname;
                STR ": ";
                typ_to_pretty ttyp;
                STR ": ";
                STR s]);
         raise (CCHFailure (LBLOCK [STR self#get_functionname; STR ": "; STR s]))
       end

  method mk_check_variable
           (l:(bool * int * int) list) (vtyp:typ) (vtype:variable_type_t) =
    let cVal = vmgr#mk_check_variable l vtyp in
    self#add_chifvar cVal vtype

  method mk_augmentation_variable
           (name:string) (purpose:string) (index:int) (vt:variable_type_t) =
    let cVal = vmgr#mk_augmentation_variable name purpose index in
    self#add_chifvar cVal vt

  method mk_call_var (name:string) (index:int) =
    self#mk_augmentation_variable name "call" index SYM_VAR_TYPE

  method private mk_fn_entry_call_var =
    self#mk_call_var "$fn-entry$" (-1)

  method get_fn_entry_call_var = self#mk_fn_entry_call_var

  method mk_call_vars =
    let directcallsites =
      proof_scaffolding#get_direct_callsites self#get_functionname in
    begin
      List.iter (fun dc ->
          let vinfo = dc#get_callee in
          let args = dc#get_arguments in
          let context = dc#get_context in
          let location = dc#get_location in
          let returntype =
            match fenv#get_type_unrolled vinfo.vtype with
            | TFun (ty, _, _, _) -> ty
            | _ ->
               raise
                 (CCHFailure
                    (LBLOCK [
                         STR "Unexpected type for function: ";
                         STR vinfo.vname;
                         STR "; ";
                         typ_to_pretty vinfo.vtype])) in
          let fnxargs = List.map (fun _ -> None) args in
          let (_, septrvars) =
            List.fold_left (fun (counter,acc) arg ->
                match fenv#get_type_unrolled (type_of_exp self#get_fdecls arg) with
                | TPtr (((TPtr _) as ty),_) ->
                   let sevar =
                     self#mk_function_sideeffect_value
                       location context vinfo fnxargs counter ty in
                   (counter + 1, sevar :: acc)
                | _ -> (counter + 1, acc)) (1,[]) args in
          let ptrvars =
            match returntype with
            | TPtr _ ->
               let fnrvar =
                 self#mk_function_return_value location context vinfo fnxargs in
               fnrvar :: septrvars
            | _ -> septrvars in
          let callname = vinfo.vname ^ "@" ^ (string_of_int location.line) in
          let callvars =
            List.map (fun v ->
                self#mk_call_var callname v#getName#getSeqNumber) ptrvars in
          let _ =
            chlog#add
              "call variables"
              (LBLOCK [
                   STR self#get_functionname; STR ": ";
                   pretty_print_list callvars (fun v -> v#toPretty) "[" "," "]"]) in
          H.add
            callvariables
            (ccontexts#index_context context) callvars) directcallsites;
      (*  TODO: add indirect callsite *)
      self#mk_fn_entry_call_var
    end

  method get_site_call_vars (context:program_context_int) =
    let ictxt = ccontexts#index_context context in
    let sitevars =
      if H.mem callvariables ictxt then H.find callvariables ictxt else [] in
    let xsitevars =
      H.fold (fun k v acc -> if k = ictxt then acc else v @ acc) callvariables [] in
    let xsitevars = self#mk_fn_entry_call_var :: xsitevars in
    (sitevars,xsitevars)

  method get_call_vars =
    let callvars = H.fold (fun _ v acc -> v @ acc) callvariables [] in
    self#mk_fn_entry_call_var :: callvars

  method private mk_initial_value (v:variable_t) (t:typ) (vt:variable_type_t) =
    let aVal = vmgr#mk_initial_value v t in
    self#add_chifvar aVal vt

  method mk_stack_address_value (vinfo:varinfo) (offset:offset) (_t:typ) =
    let lvar = vmgr#mk_local_variable vinfo NoOffset in
    let cvar = self#add_chifvar lvar NUM_VAR_TYPE in
    let memref = vmgr#memrefmgr#mk_stack_reference cvar vinfo.vtype in
    let addrvar = vmgr#mk_memory_address memref#index offset in
    self#add_chifvar addrvar NUM_VAR_TYPE

  method mk_stack_memory_variable
           (vinfo:varinfo) (offset:offset) (_t:typ) (vt:variable_type_t) =
    let lvar = vmgr#mk_local_variable vinfo NoOffset in
    let cvar = self#add_chifvar lvar vt in
    let memref = vmgr#memrefmgr#mk_stack_reference cvar vinfo.vtype in
    self#mk_memory_variable memref#index offset vt

  method mk_global_address_value (vinfo:varinfo) (offset:offset) (_t:typ) =
    let gvar = vmgr#mk_global_variable vinfo NoOffset in
    let cvar = self#add_chifvar gvar NUM_VAR_TYPE in
    let memref = vmgr#memrefmgr#mk_global_reference cvar vinfo.vtype in
    let addrvar = vmgr#mk_memory_address memref#index offset in
    self#add_chifvar addrvar NUM_VAR_TYPE

  method mk_base_address_value (v:variable_t) (offset:offset) (t:typ) =
    let memref = vmgr#memrefmgr#mk_external_reference v t in
    let addrvar = vmgr#mk_memory_address memref#index offset in
    self#add_chifvar addrvar NUM_VAR_TYPE

  method mk_global_memory_variable
           (vinfo:varinfo) (offset:offset) (_t:typ) (vt:variable_type_t) =
    let gvar = vmgr#mk_global_variable vinfo NoOffset in
    let cvar = self#add_chifvar gvar vt in
    let memref = vmgr#memrefmgr#mk_global_reference cvar vinfo.vtype in
    self#mk_memory_variable memref#index offset vt

  method mk_memory_address_value (memrefindex:int) (offset:offset) =
    let addrvar = vmgr#mk_memory_address memrefindex offset in
    self#add_chifvar addrvar NUM_VAR_TYPE

  method mk_string_address (s:string) (offset:offset) (t:typ) =
    let cvar = vmgr#mk_string_address s offset t in
    self#add_chifvar cvar NUM_VAR_TYPE

  method mk_function_return_value
           (loc:location)
           (pctxt:program_context_int)
           (callee:varinfo)
           (args:xpr_t option list) =
    let rvar = vmgr#mk_function_return_value loc pctxt callee args in
    self#add_chifvar rvar NUM_VAR_TYPE

  method mk_function_sideeffect_value
           (loc:location)
           (pctxt:program_context_int)
           (callee:varinfo)
           (args:xpr_t option list)
           (argindex:int) (argtype:typ) =
    let sevar =
      vmgr#mk_function_sideeffect_value loc pctxt callee args argindex argtype in
    self#add_chifvar sevar NUM_VAR_TYPE

  method mk_tainted_value
           (v:variable_t) (xopt1:xpr_t option) (xopt2:xpr_t option) (t:typ) =
    let tvar = vmgr#mk_tainted_value v xopt1 xopt2 t in
    self#add_chifvar tvar NUM_VAR_TYPE

  method mk_byte_sequence (v:variable_t) (xoptlen:xpr_t option) =
    let cvar = vmgr#mk_byte_sequence v xoptlen in
    self#add_chifvar cvar NUM_VAR_TYPE

  method mk_exp_return_value
           (loc:location)
           (pctxt:program_context_int)
           (callee:xpr_t)
           (args:xpr_t option list)
           (t:typ) =
    let rvar = vmgr#mk_exp_return_value loc pctxt callee args t in
    self#add_chifvar rvar NUM_VAR_TYPE

  method private register_formal (vinfo:varinfo) (vt:variable_type_t) =
    match file_environment#get_type_unrolled vinfo.vtype with
    | TComp (ckey,_) ->
       let cinfo = file_environment#get_comp ckey in
       List.map (fun f ->
           let offset = Field ((f.fname,f.fckey),NoOffset) in
           let cVar = vmgr#mk_local_variable vinfo offset in
           let chifvar = self#add_chifvar cVar vt in
           let vInit = self#mk_initial_value chifvar f.ftype vt in
           (cVar#get_name,f.ftype,chifvar,vInit)) cinfo.cfields
    | t ->
       let cVar = vmgr#mk_local_variable vinfo NoOffset  in
       let chifvar = self#add_chifvar cVar vt in
       let vInit = self#mk_initial_value chifvar vinfo.vtype vt in
       [(vinfo.vname,t,chifvar,vInit)]

  method register_formals (formals: varinfo list) (vt:variable_type_t) =
    List.concat (List.map (fun v -> self#register_formal v vt) formals)

  method private register_global (vinfo:varinfo) (vt:variable_type_t) =
    match file_environment#get_type_unrolled vinfo.vtype with
    | TComp (ckey,_) ->
       let cinfo = file_environment#get_comp ckey in
       List.map (fun f ->
           let offset  = Field ((f.fname,f.fckey),NoOffset) in
           let cVar = vmgr#mk_local_variable vinfo offset in
           let chifvar = self#add_chifvar cVar vt in
           let vInit = self#mk_initial_value chifvar f.ftype vt in
           (cVar#get_name,f.ftype,chifvar,vInit)) cinfo.cfields
    | t ->
       let cVar = vmgr#mk_global_variable vinfo NoOffset in
       let chifvar = self#add_chifvar cVar vt in
       let vInit = self#mk_initial_value chifvar vinfo.vtype vt in
       [(vinfo.vname,t,chifvar,vInit)]

  method register_globals (globals:varinfo list) (vt:variable_type_t) =
    List.concat (List.map (fun v -> self#register_global v vt) globals)

  method register_program_locals (locals:varinfo list) (vt:variable_type_t) =
    let rec compose_offset base offset =
      match base with
      | NoOffset -> offset
      | Field (fuse, NoOffset) ->  Field (fuse,offset)
      | Field (fuse, foffset) -> Field (fuse, compose_offset foffset offset)
      | Index _ ->
         begin
           ch_error_log#add
             "compose offset"
             (LBLOCK [
                  STR "base: ";
                  offset_to_pretty base;
                  STR "; offset: ";
                  offset_to_pretty offset]);
           NoOffset
         end in
    let rec register_fields v baseoffset comp =
      List.iter (fun f ->
             let foffset = Field ((f.fname,f.fckey),NoOffset) in
             let offset = compose_offset baseoffset foffset in
             begin
               ignore (self#mk_program_var v offset vt);
               match fenv#get_type_unrolled f.ftype  with
               | TComp (ckey,_) ->
                  let comp = fenv#get_comp ckey  in
                  register_fields v offset comp
               | _ -> ()
             end) comp.cfields in
    List.iter (fun v  ->
        begin
          ignore (self#mk_program_var v NoOffset vt);
          match fenv#get_type_unrolled v.vtype with
          | TComp (ckey,_) ->
             let comp = fenv#get_comp ckey in
             register_fields v NoOffset comp
          | _ -> ()
        end) locals

  method private get_variables_filtered f =
    let result = ref [] in
    let _ = H.iter (fun k v -> if f k then result := v :: !result) chifvars in
    !result

  method get_memory_variables =
    self#get_variables_filtered vmgr#is_memory_variable

  method get_memory_variables_with_base (v:variable_t) =
    let memvars = self#get_memory_variables in
    if self#is_memory_address v || self#is_memory_variable v then
      let memref = self#get_memory_reference v in
      List.filter (fun mv ->
          memref#index = (self#get_memory_reference mv)#index) memvars
    else
      memvars

  method get_parameters =
    self#get_variables_filtered vmgr#is_fixed_value

  method get_vinfo_offset (v:variable_t) (vinfo:varinfo) =
    if self#is_local_variable v then
      let (vvinfo,offset) = self#get_local_variable v in
      if vvinfo.vid = vinfo.vid then
        Some offset
      else
        None
    else if self#is_global_variable v then
      let (vvinfo,offset) = self#get_global_variable v in
      if vvinfo.vid = vinfo.vid then
        Some offset
      else
        None
    else if self#is_memory_variable v then
      let (memref,offset) = self#get_memory_variable v in
      match memref#get_base with
      | CStackAddress stackvar when self#is_local_variable stackvar ->
         let (vvinfo,voffset) = self#get_local_variable stackvar in
         if vvinfo.vid = vinfo.vid then
           match offset with
           | NoOffset -> Some voffset
           | _ -> None
         else
           None
      | _ -> None
    else
      None

  method get_symbolic_dereferences = [] (* TBD, see ref:get_frozen_dereferences *)

  method get_external_addresses = [] (* TBD, see ref *)

  (* memory region manager services ------------------------------------------- *)

  method get_region_name (index:int) =
    let rec aux i =
      let reg = memregmgr#get_memory_region i in
      let rec pr_offset o =
        match o with
        | NoOffset -> ""
        | Field ((fname,_),oo) -> "." ^ fname ^ (pr_offset oo)
        | Index (Const (CInt (i64,_,_)),oo) ->
           "[" ^ (Int64.to_string i64) ^ "]" ^ (pr_offset oo)
        | Index (_,oo) -> "[.]" ^ (pr_offset oo) in
      match reg#get_memory_base with
      | CNull (-1) -> "null"
      | CNull i ->  (aux i) ^ "#null"
      | CStringLiteral s -> ((string_of_int (String.length s)) ^ "-char string")
      | CStackAddress v ->
         if vmgr#is_local_variable v#getName#getSeqNumber then
           let (vinfo,offset) = vmgr#get_local_variable v#getName#getSeqNumber in
           "stack variable " ^ vinfo.vname ^ (pr_offset offset)
         else if self#is_memory_variable v then
           let (memref,offset) = self#get_memory_variable v in
           match memref#get_base with
           | CBaseVar v ->
              let (vinfo,voffset) =
                vmgr#get_local_variable v#getName#getSeqNumber in
              "stack variable "
              ^ vinfo.vname
              ^ (pr_offset voffset)
              ^ (pr_offset offset)
           | base ->
              raise
                (CCHFailure
                   (LBLOCK [
                        STR "unexpected base variable of stack address region: ";
                        v#toPretty;
                        memory_base_to_pretty base]))
         else
           raise
             (CCHFailure
                (LBLOCK [
                     STR "stack address region of non-local-variable: ";
                     v#toPretty]))
      | CGlobalAddress v ->
         if vmgr#is_global_variable v#getName#getSeqNumber then
           let (vinfo, offset) = vmgr#get_global_variable v#getName#getSeqNumber in
           "global variable " ^ vinfo.vname ^ (pr_offset offset)
         else
           raise
             (CCHFailure
                (LBLOCK [
                     STR "global address region of non-global-variable: ";
                     v#toPretty]))
      | CBaseVar v -> "basevar " ^ v#getName#getBaseName
      | CUninterpreted s -> "unknown:" ^ s in
    aux index

  (* variable manager services ------------------------------------------------ *)

  method private get_seqnr (v:variable_t) = v#getName#getSeqNumber

  method get_variable_type (v:variable_t) =
    let seqnr = self#get_seqnr v in
    if seqnr >= 0 then
      vmgr#get_variable_type seqnr
    else
      raise
        (CCHFailure (LBLOCK [STR "Cannot determine type of temp variable"]))

  method is_augmentation_variable v =
    vmgr#is_augmentation_variable (self#get_seqnr v)

  method is_call_var v =
    self#is_augmentation_variable v
    && (vmgr#get_purpose  (self#get_seqnr v)) = "call"

  method get_indicator v = vmgr#get_indicator (self#get_seqnr v)

  method get_parameter_exp v = vmgr#get_parameter_exp (self#get_seqnr v)

  method get_global_exp v = vmgr#get_global_exp (self#get_seqnr v)

  method get_callvar_callee v =  vmgr#get_callee (self#get_seqnr v)

  method get_callsym_callee s  = vmgr#get_callee s#getSeqNumber

  method get_callvar_args v = vmgr#get_callee_args (self#get_seqnr v)

  method get_callsym_args s = vmgr#get_callee_args s#getSeqNumber

  method get_callvar_context v = vmgr#get_callee_context (self#get_seqnr v)

  method get_callsym_context s = vmgr#get_callee_context s#getSeqNumber

  method get_callsym_location s = vmgr#get_callee_location s#getSeqNumber

  method get_tainted_value_origin v =
    vmgr#get_tainted_value_origin (self#get_seqnr v)

  method get_tainted_value_bounds v =
    vmgr#get_tainted_value_bounds (self#get_seqnr v)

  method get_byte_sequence_origin v =
    vmgr#get_byte_sequence_origin (self#get_seqnr v)

  method get_memory_reference v = vmgr#get_memory_reference (self#get_seqnr v)

  method get_memory_region s = vmgr#memregmgr#get_memory_region s#getSeqNumber

  method is_program_variable v = vmgr#is_program_variable (self#get_seqnr v)

  method is_local_variable v = vmgr#is_local_variable (self#get_seqnr v)

  method is_global_variable v = vmgr#is_global_variable (self#get_seqnr v)

  method get_local_variable v = vmgr#get_local_variable (self#get_seqnr v)

  method get_global_variable v = vmgr#get_global_variable (self#get_seqnr v)

  method get_memory_variable v = vmgr#get_memory_variable (self#get_seqnr v)

  method get_memory_address v = vmgr#get_memory_address (self#get_seqnr v)

  method is_fixed_value v = vmgr#is_fixed_value (self#get_seqnr v)

  method is_initial_value v = vmgr#is_initial_value (self#get_seqnr v)

  method is_initial_parameter_value v =
    vmgr#is_initial_parameter_value (self#get_seqnr v)

  method is_initial_parameter_deref_value v =
    vmgr#is_initial_parameter_deref_value (self#get_seqnr v)

  method is_initial_global_value v =
    vmgr#is_initial_global_value (self#get_seqnr v)

  method get_initial_value_variable v =
    vmgr#get_initial_value_variable (self#get_seqnr v)

  method is_function_return_value v =
    vmgr#is_function_return_value (self#get_seqnr v)

  method is_function_return_value_sym s =
    vmgr#is_function_return_value s#getSeqNumber

  method is_function_sideeffect_value v =
    vmgr#is_function_sideeffect_value (self#get_seqnr v)

  method is_function_sideeffect_value_sym s =
    vmgr#is_function_sideeffect_value s#getSeqNumber

  method is_tainted_value v = vmgr#is_tainted_value (self#get_seqnr v)

  method is_byte_sequence v = vmgr#is_byte_sequence (self#get_seqnr v)

  method has_constant_offset v = vmgr#has_constant_offset (self#get_seqnr v)

  method is_memory_address v = vmgr#is_memory_address (self#get_seqnr v)

  method is_memory_variable v = vmgr#is_memory_variable (self#get_seqnr v)

  method check_variable_applies_to_po
           (v:variable_t) ?(argindex=(-1)) (isppo:bool) (po_id:int) =
    vmgr#applies_to_po (self#get_seqnr v) ~argindex isppo po_id

  method is_fixed_xpr (x:xpr_t) =
    match x with
    | XVar v -> self#is_fixed_value v
    | XConst _ -> true
    | XOp (_,l) -> List.for_all self#is_fixed_xpr l
    | XAttr (_,x) -> self#is_fixed_xpr x

  method get_declared_type_value_range (v:variable_t) =
    if self#is_local_variable v || self#is_global_variable v then
      let (vinfo,offset) =
        if self#is_local_variable v then
          self#get_local_variable v
        else
          self#get_global_variable v in
      match offset with
      | NoOffset ->
         let ty = vinfo.vtype in
         let typerange = range_of_type self#get_fdecls ty in
         (Some typerange#min, Some typerange#max)
      | _ -> (None,None)
    else
      (None,None)

  (* transactions and requests for transaction variables ---------------------   *)

  val mutable tmps_requested = 0
  val mutable in_transaction = false
  val mutable constant_table = new NumericalCollections.table_t

  method private within_transaction = in_transaction

  method start_transaction =
    if in_transaction then
      raise
        (CCHFailure (STR "Attempt to start transaction while within transaction"))
    else
      begin
	tmps_requested <- 0;
	scope#startTransaction;
	in_transaction <- true
      end

  method end_transaction =
    let constant_assignments =
      constant_table#fold (fun a num tmp -> (ASSIGN_NUM (tmp, NUM num)) :: a) [] in
    begin
      scope#endTransaction;
      in_transaction <- false;
      constant_table <- new NumericalCollections.table_t;
      (tmps_requested > 0, List.rev constant_assignments)
    end

  method mk_num_temp =
    let v = scope#requestNumTmpVariable in
    begin tmps_requested <- tmps_requested + 1; v end

  method mk_sym_temp =
    let v = scope#requestSymTmpVariable in
    begin tmps_requested <- tmps_requested + 1; v end

  method mk_temp (t:variable_type_t):variable_t =
    if self#within_transaction then
      if is_numerical_type t then self#mk_num_temp else self#mk_sym_temp
    else
      let _ = self#start_transaction in
      let tmp =
        if is_numerical_type t then self#mk_num_temp else self#mk_sym_temp in
      let _ = self#end_transaction in
      tmp

  method private get_temp (vt:variable_type_t):variable_t =
    if self#within_transaction then
      self#mk_temp vt
    else
      let _ = self#start_transaction in
      let tmp = self#mk_temp vt in
      let _ = self#end_transaction in
      tmp

  method private enter_constant (constant:numerical_t) =
    let tmp = self#mk_num_temp in begin constant_table#set constant tmp; tmp end

  method mk_num_constant (constant:numerical_t) =
    match constant_table#get constant with
    | Some v -> v
    | _ -> self#enter_constant constant

  (* breakout blocks  --------------------------------------------------------- *)

  val break_stack = new stack_t
  val loop_stack = new stack_t

  method get_function_break_label = "function_block"

  method private loop_block_name i = "loop_block_" ^ (string_of_int i)
  method private switch_block_name i = "switch_block_" ^ (string_of_int i)

  method private push_break =
    let top = try break_stack#top with CHFailure _ -> 0 in
    break_stack#push (top+1)

  method private pop_break = ignore (break_stack#pop)

  method get_break_label =
    if loop_stack#top then                  (* Break in loop *)
      let l = break_stack#listFromTop in
      let subtop =
	try
	  List.nth l 1
	with
	  Failure _ ->
	    begin
	      ch_error_log#add "invocation error"
		(STR "Cannot access subtop in getBreakLabel");
	      raise (CCHFailure (STR "environment#getBreakLabel"))
	    end in
      self#loop_block_name subtop
    else                                    (* Break in switch *)
      let top = break_stack#top in
      self#switch_block_name top

  method get_continue_label =
    let break_list = break_stack#listFromTop in
    let loop_list = loop_stack#listFromTop in
    let rec findlabel bl ll =
      match (bl,ll) with
	([],_ )
      | (_ ,[]) ->
	begin
	  ch_error_log#add
            "invocation error"
	    (STR "Unexpected request for ContinueLabel");
	  raise (CCHFailure (STR "environment#getContinueLabel"))
	end
      | (i::_,true::_) ->
	 self#loop_block_name i
      | ( _::bt, _::lt ) ->
	 findlabel bt lt in
    findlabel break_list loop_list

  method start_loop =
    begin
      self#push_break;
      self#push_break;
      loop_stack#push true
    end

  method end_loop =
    begin
      self#pop_break;
      self#pop_break;
      ignore(loop_stack#pop)
    end

  method start_switch =
    begin
      self#push_break;
      loop_stack#push false
    end

  method end_switch =
    begin
      self#pop_break;
      ignore (loop_stack#pop)
    end

end


let mk_c_environment = new c_environment_t
