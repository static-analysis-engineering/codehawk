(* =============================================================================
   CodeHawk Binary Analyzer
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
open CHPretty

(* chutil *)
open CHFormatStringParser
open CHLogger
open CHUtil
open CHXmlDocument

(* bchlib *)
open BCHARMFunctionInterface
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeTransformer
open BCHBCTypeUtil
open BCHBCTypeXml
open BCHCPURegisters
open BCHDemangler
open BCHFtsParameter
open BCHLibTypes
open BCHSystemSettings


let id = BCHInterfaceDictionary.interface_dictionary


let is_stack_parameter (p: fts_parameter_t): bool =
  match p.apar_location with
  | [StackParameter _] -> true
  | _ -> false


let is_register_parameter (p: fts_parameter_t): bool =
  match p.apar_location with
  | [RegisterParameter _] -> true
  | _ -> false


let rec fill_in_stack_parameters
          (nextindex: int)
          (nextoffset: int)
          (endoffset: int)
          (accparams: fts_parameter_t list): (int * fts_parameter_t list) =
  if nextoffset = endoffset then
    (nextindex, List.rev accparams)
  else
    if endoffset - nextoffset < 4 then
      let par =
        mk_indexed_stack_parameter
          ~size:(endoffset - nextoffset)
          nextoffset
          nextindex in
      (nextindex + 1, List.rev (par :: accparams))
    else
      let par = mk_indexed_stack_parameter ~size:4 nextoffset nextindex in
      fill_in_stack_parameters
        (nextindex + 1) (nextoffset + 4) endoffset (par :: accparams)


(* Register arguments are currently not handled, just stack arguments *)
let get_x86_fts_parameters (fname: string) (locs: parameter_location_t list) =
  let (_, _, params) =
    List.fold_left (fun (nextindex, nextoffset, params) loc ->
        match loc with
        | StackParameter (offset, pd) when offset = nextoffset ->
           let par =
             mk_indexed_stack_parameter
               ~btype:pd.pld_type ~size:pd.pld_size offset nextindex in
           (nextindex + 1, offset + pd.pld_size, par :: params)
        | StackParameter (offset, pd) when offset > nextoffset ->
           let (nxtindex, fillinpars) =
             fill_in_stack_parameters nextindex nextoffset offset [] in
           let _ =
             chlog#add
               "x86 fill-in arguments"
               (LBLOCK [
                    STR fname;
                    STR ": ";
                    pretty_print_list
                      fillinpars fts_parameter_to_pretty " (" ", " ")"]) in
           let par =
             mk_indexed_stack_parameter
             ~btype:pd.pld_type
             ~size:pd.pld_size
             offset
             nxtindex in
           (nxtindex + 1, offset + pd.pld_size, par :: (fillinpars @ params))
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "x86-fts_parameters: location not recognized: ";
                     STR (parameter_location_to_string loc)]))) (1, 4, []) locs in
  params


type mips_argument_state_t = {
    mas_next_arg_reg: mips_reg_t option;
    mas_next_offset: int option
  }


let mas_start_state = {
    mas_next_arg_reg = Some MRa0;
    mas_next_offset = None
  }


let get_next_mips_arg_reg (r: mips_reg_t) =
  match r with
  | MRa0 -> Some MRa1
  | MRa1 -> Some MRa2
  | MRa2 -> Some MRa3
  | _ -> None


let rec get_fillin_mips_arg_regs
          (nxtindex: int)
          (nxtreg: mips_reg_t)
          (reg: mips_reg_t)
          (accparams: fts_parameter_t list): (int * fts_parameter_t list) =
  if nxtreg = reg then
    (nxtindex, List.rev accparams)
  else
    let register = register_of_mips_register nxtreg in
    let optnextreg = get_next_mips_arg_reg nxtreg in
    match optnextreg with
    | Some nextreg ->
       let par = mk_indexed_register_parameter register nxtindex in
       get_fillin_mips_arg_regs (nxtindex + 1) nextreg reg (par :: accparams)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in get_fillin_mips_arg_regs"]))


let rec get_all_reg_fillin_mips_arg_regs
          (nxtindex: int)
          (optnxtreg: mips_reg_t option)
          (accparams: fts_parameter_t list): (int * fts_parameter_t list) =
  match optnxtreg with
  | Some nxtreg ->
     let register = register_of_mips_register nxtreg in
     let par = mk_indexed_register_parameter register nxtindex in
     get_all_reg_fillin_mips_arg_regs
       (nxtindex + 1) (get_next_mips_arg_reg nxtreg) (par :: accparams)
  | _ ->
     (nxtindex, accparams)


let get_mips_fts_parameters (fname: string) (locs: parameter_location_t list) =
  let (_, _, params) =
    List.fold_left (fun (nextindex, ma_state, params) loc ->
        match loc with
        | RegisterParameter (MIPSRegister reg, pd) ->
           (match ma_state.mas_next_arg_reg with
            | Some nxtreg when reg = nxtreg ->
               let par =
                 mk_indexed_register_parameter
                   ~btype:pd.pld_type
                   ~size:pd.pld_size
                   (register_of_mips_register reg)
                   nextindex in
               let ncr = get_next_mips_arg_reg reg in
               let nmas =
                 match ncr with
                 | Some _ -> {ma_state with mas_next_arg_reg = ncr}
                 | _ ->
                    { mas_next_arg_reg = None;
                      mas_next_offset = Some 16
                    } in
               (nextindex + 1, nmas, par :: params)
            | Some nxtreg ->
               let (nextindex, fillinparams) =
                 get_fillin_mips_arg_regs nextindex nxtreg reg [] in
               let par =
                 mk_indexed_register_parameter
                   ~btype:pd.pld_type
                   ~size:pd.pld_size
                   (register_of_mips_register reg)
                   nextindex in
               let ncr = get_next_mips_arg_reg reg in
               let nmas =
                 match ncr with
                 | Some _ -> {ma_state with mas_next_arg_reg = ncr}
                 | _ ->
                    { mas_next_arg_reg = None;
                      mas_next_offset = Some 16
                    } in
               (nextindex + 1, nmas, par :: (fillinparams @ params))
            | _ ->
               raise
                 (BCH_failure
                    (LBLOCK [
                         STR "Unexpected register parameter in locations: ";
                         STR (mipsreg_to_string reg)])))
        | StackParameter (offset, pd) ->
           (match ma_state.mas_next_arg_reg with
            | Some nxtreg ->
               let (nextindex, rfillinparams) =
                 get_all_reg_fillin_mips_arg_regs nextindex (Some nxtreg) [] in
               if offset = 16 then
                 let par =
                   mk_indexed_stack_parameter
                     ~btype:pd.pld_type
                     ~size:pd.pld_size
                     16
                     nextindex in
                 let nmas = {
                     mas_next_arg_reg = None;
                     mas_next_offset = Some (16 + pd.pld_size)
                   } in
                 (nextindex + 1, nmas, par :: (rfillinparams @ params))
               else
                 let (nextindex, sfillinparams) =
                   fill_in_stack_parameters nextindex 16 offset [] in
                 let par =
                   mk_indexed_stack_parameter
                     ~btype:pd.pld_type
                     ~size:pd.pld_size
                     offset
                     nextindex in
                 let nmas = {
                     mas_next_arg_reg = None;
                     mas_next_offset = Some (16 + pd.pld_size)
                   } in
                 (nextindex + 1,
                  nmas,
                  par :: (rfillinparams @ sfillinparams @ params))
            | _ ->
               match ma_state.mas_next_offset with
               | Some nxtoffset when offset = nxtoffset ->
                  let par =
                    mk_indexed_stack_parameter
                      ~btype:pd.pld_type
                      ~size:pd.pld_size
                      nxtoffset
                      nextindex in
                  let nmas =
                    { ma_state with
                      mas_next_offset = Some (nxtoffset + pd.pld_size)} in
                  (nextindex + 1, nmas, par :: params)
               | Some nxtoffset when offset > nxtoffset ->
                  let (nextindex, sfillinparams) =
                    fill_in_stack_parameters nextindex nxtoffset offset [] in
                  let par =
                    mk_indexed_stack_parameter
                      ~btype:pd.pld_type
                      ~size:pd.pld_size
                      offset
                      nextindex in
                  let nmas =
                    { ma_state with
                      mas_next_offset = Some (offset + pd.pld_size)} in
                  (nextindex + 1, nmas, par :: (sfillinparams @ params))
               | _ ->
                  raise
                    (BCH_failure
                       (LBLOCK [
                            STR "Error in get_mips_fts_parameters ";
                            STR fname])))
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Unexpected parameter location: ";
                     STR fname;
                     STR ": ";
                     STR (parameter_location_to_string loc)]))
      ) (1, mas_start_state, []) locs in
  params


let get_arm_fts_parameters (_fname: string) (_locs: parameter_location_t list) =
  []



let get_fts_parameters (fintf: function_interface_t): fts_parameter_t list =
  match fintf.fintf_bctype with
  | Some _ ->
     (* signature was obtained from header file or summary library, so
        the parameters in the signature are considered the authorative source
      *)
     let fsig = fintf.fintf_type_signature in
     let fsigparams = fsig.fts_parameters in
     List.sort fts_parameter_compare fsigparams
  | _ ->
     (* signature was inferrred from analysis results, hence the parameters
        are constructed from the parameter locations collected in the
        function interface.
      *)
     try
       let paramlocs = fintf.fintf_parameter_locations in
       let paramlocs = List.sort parameter_location_compare paramlocs in
       let fname = fintf.fintf_name in
       let params =
         match system_settings#get_architecture with
         | "x86" -> get_x86_fts_parameters fname paramlocs
         | "mips" -> get_mips_fts_parameters fname paramlocs
         | "arm" -> get_arm_fts_parameters fname paramlocs
         | arch ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "get-fts_parameters: not yet supported for ";
                      STR arch])) in
       List.sort fts_parameter_compare params
     with
     | BCH_failure p ->
        begin
          ch_error_log#add
            "get_fts_parameters" (LBLOCK [STR fintf.fintf_name; STR ": "; p]);
          []
        end


let get_stack_parameters (fintf: function_interface_t): fts_parameter_t list =
  List.filter is_stack_parameter (get_fts_parameters fintf)


let get_register_parameters (fintf: function_interface_t): fts_parameter_t list =
  List.filter is_register_parameter (get_fts_parameters fintf)


let get_register_parameter_for_register
      (fintf: function_interface_t) (reg: register_t): fts_parameter_t option =
  let regpars = get_register_parameters fintf in
  List.fold_left (fun acc p ->
      match acc with
      | Some _ -> acc
      | _ ->
         if is_register_parameter_for_register p reg then
           Some p
         else
           acc) None regpars


let get_stack_parameter_at_offset
      (fintf: function_interface_t) (offset: int): fts_parameter_t option =
  let stackpars = get_stack_parameters fintf in
  List.fold_left (fun acc p ->
      match acc with
      | Some _ -> acc
      | _ ->
         if is_stack_parameter_at_offset p offset then
           Some p
         else
           acc) None stackpars


let get_fintf_name (fintf: function_interface_t): string =
  fintf.fintf_name


let get_fintf_fts (fintf: function_interface_t): function_signature_t =
  match fintf.fintf_bctype with
  | Some _bctype -> fintf.fintf_type_signature
  | _ ->
     let params = get_fts_parameters fintf in
     let returntype =
       match btype_meet fintf.fintf_returntypes with
       | Some t -> t
       | _ -> t_unknown in
     {fintf.fintf_type_signature with
       fts_returntype = returntype; fts_parameters = params}


let get_fts_returntype (fintf: function_interface_t): btype_t =
  (get_fintf_fts fintf).fts_returntype


let get_fts_stack_adjustment (fintf: function_interface_t): int option =
  (get_fintf_fts fintf).fts_stack_adjustment


(* ----------------------------------------------------------------- printing *)

let function_interface_to_prototype_string
      ?(fullname=None) (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  let name =
    match fullname with
    | Some n -> n
    | _ -> fintf.fintf_name in
  let stackPars = List.fold_left (fun a p ->
    match p.apar_location with
    | [StackParameter (offset, _)] -> (offset, p.apar_name, p.apar_type)::a
    | _ -> a) [] fts.fts_parameters in
  let stackPars =
    List.sort (fun (off1, _, _) (off2, _, _) ->
        Stdlib.compare off1 off2) stackPars in
  let par_string (_, name, ty) = (btype_to_string ty) ^ " " ^ name in
  (btype_to_string fts.fts_returntype)
  ^ " "
  ^ name
  ^ "("
  ^ (String.concat ", " (List.map par_string stackPars))
  ^ ")"


let function_interface_to_pretty (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  LBLOCK [
      STR fintf.fintf_name ;
      STR ": ";
      btype_to_pretty fts.fts_returntype;
      STR " ";
      pretty_print_list
        fts.fts_parameters fts_parameter_to_pretty " (" ", " ")"]

(* ----------------------------------------------------------------- read xml *)

let read_xml_registers_preserved (node:xml_element_int) =
  List.map (fun n ->
    let get = n#getAttribute in
    (register_from_string (get "name"))) (node#getTaggedChildren "reg")


let get_stack_adjustment (calling_convention:string) (npars:int) =
  match calling_convention with
  | "stdcall" -> 4 * npars
  | "cdecl" -> 0
  | s ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "calling convention ";
               STR s;
	       STR " not recognized"]))


let convert_xml_fts_parameter_mips (p: fts_parameter_t): fts_parameter_t =
  (* first four arguments are in $a0-$a3, subsequent arguments are
     on the stack, starting at offset 16.*)
  match p.apar_location with
  | [StackParameter (offset, _pdef)] when offset <= 16 ->
     let index = offset / 4 in
     let reg =
       (match offset with
        | 4 -> MRa0
        | 8 -> MRa1
        | 12 -> MRa2
        | 16 -> MRa3
        | _ -> raise (BCH_failure (STR "Internal error"))) in
     let register = register_of_mips_register reg in
     mk_indexed_register_parameter
       ~btype:p.apar_type
       ~name:p.apar_name
       ~desc:p.apar_desc
       ~roles:p.apar_roles
       ~io:p.apar_io
       ~size:p.apar_size
       ~fmt:p.apar_fmt
       register
       index
  | [StackParameter (stackoffset, _pdef)] ->
     let index = stackoffset / 4 in
     let offset = stackoffset - 4 in
     mk_indexed_stack_parameter
       ~btype:p.apar_type
       ~name:p.apar_name
       ~desc:p.apar_desc
       ~roles:p.apar_roles
       ~io:p.apar_io
       ~size:p.apar_size
       ~fmt:p.apar_fmt
       offset
       index
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "mips: convert_xml_fts_parameter: not supported: ";
               fts_parameter_to_pretty p]))


let convert_xml_fts_parameter_arm (p: fts_parameter_t): fts_parameter_t =
  (* first four arguments are in R0-R3, subsequent arguments are on the
     stack, starting at offset 0.
     Currently ceilf is the only function with a float argument in
     so_functions, which allows simple allocation to S0, and does not
     require applying the stateful argument allocation algorithm used
     below for arbitrary header-provided signatures.
   *)
  match p.apar_location with
  | [StackParameter (offset, _pdef)] when offset <= 16 ->
     let index = offset / 4 in
     let btype = p.apar_type in
     let register =
       if is_float btype then
         register_of_arm_extension_register (mk_arm_sp_reg (index - 1))
       else
         let reg =
           (match index with
            | 1 -> AR0
            | 2 -> AR1
            | 3 -> AR2
            | 4 -> AR3
            | _ -> raise (BCH_failure (STR "internal error"))) in
         register_of_arm_register reg in
     mk_indexed_register_parameter
       ~btype:p.apar_type
       ~name:p.apar_name
       ~desc:p.apar_desc
       ~roles:p.apar_roles
       ~io:p.apar_io
       ~size:p.apar_size
       ~fmt:p.apar_fmt
       register
       index
  | [StackParameter (stackoffset, _pdef)] ->
     let index = stackoffset / 4 in
     let offset = stackoffset - 20 in
     mk_indexed_stack_parameter
       ~btype:p.apar_type
       ~name:p.apar_name
       ~desc:p.apar_desc
       ~roles:p.apar_roles
       ~io:p.apar_io
       ~size:p.apar_size
       ~fmt:p.apar_fmt
       offset
       index
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "arm: convert_xml_fts_parameter: not supported: ";
               fts_parameter_to_pretty p]))



let convert_xml_fts_parameter (p: fts_parameter_t): fts_parameter_t =
  match system_settings#get_architecture with
  | "x86" -> p
  | "mips" -> convert_xml_fts_parameter_mips p
  | "arm" -> convert_xml_fts_parameter_arm p
  | arch ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "fts parameter conversion not yet supported for ";
               STR arch]))


let read_xml_function_interface (node:xml_element_int):function_interface_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let getcc = node#getTaggedChildren in
  let hasc = node#hasOneTaggedChild in
  let find l default =
    List.fold_left (fun acc s ->
        if hasc s then read_xml_returntype (getc s) else acc) default l in
  let rvtype = find ["returntype"; "returnbtype"] t_void in
  let parameters = List.map read_xml_fts_parameter (getcc "par") in
  let parameters = List.map convert_xml_fts_parameter parameters in
  let bctype =
    t_fsignature rvtype (List.map get_parameter_signature parameters) in
  let varargs = has "varargs" && ((get "varargs") = "yes") in
  let cc = get "cc" in
  let stackadj = if cc = "stdcall" || cc = "cdecl" then
      Some (get_stack_adjustment cc (List.length parameters))
    else
      None in
  let fts = {
      fts_parameters = parameters;
      fts_varargs = varargs;
      fts_va_list = None;
      fts_returntype = rvtype;
      fts_rv_roles =
        (if hasc "rv-roles" then read_xml_roles (getc "rv-roles") else []);
      fts_calling_convention = cc;
      fts_stack_adjustment = if has "adj" then Some (geti "adj") else stackadj;
      fts_registers_preserved =
        if hasc "registers-preserved" then
          read_xml_registers_preserved (getc "registers-preserved")
        else
          []
    } in
  { fintf_name = get "name";
    fintf_jni_index = if has "jni" then Some (geti "jni") else None;
    fintf_syscall_index = if has "syscall" then Some (geti "syscall") else None;
    fintf_type_signature = fts;
    fintf_bctype = Some bctype;
    fintf_parameter_locations = [];
    fintf_returntypes = []
  }


let write_xml_function_interface
      (node: xml_element_int) (fintf: function_interface_t) =
  begin
    id#write_xml_function_interface node fintf;
    id#write_xml_function_signature node (get_fintf_fts fintf)
  end

(* ---------------------------------------------------------------- operators *)

let modify_function_interface
      (f: type_transformer_t) (name: string) (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  let newfts = {
      fts with
      fts_parameters = List.map (modify_types_par f) fts.fts_parameters;
      fts_returntype = modify_type f fts.fts_returntype
    } in
  { fintf with
    fintf_name = name ;
    fintf_type_signature = newfts
  }


let set_function_interface_returntype
      (fintf: function_interface_t) (ty: btype_t): function_interface_t =
  match fintf.fintf_bctype with
  | None ->
     let rtypes = fintf.fintf_returntypes in
     {fintf with fintf_returntypes = ty :: rtypes}
  | Some bctype ->
     let _ =
       chlog#add
         "add-function-register-parameter-location"
         (LBLOCK [
              STR "Location not added; bctype is fixed: ";
              STR (btype_to_string bctype)]) in
     fintf


let add_function_register_parameter_location
      (fintf: function_interface_t)
      (reg: register_t)
      (ty: btype_t)
      (size: int): function_interface_t =
  match fintf.fintf_bctype with
  | None ->
     let locdetail = default_parameter_location_detail ~ty size in
     let loc = RegisterParameter (reg, locdetail) in
     let eq (loc1: parameter_location_t) (loc2: parameter_location_t): bool =
       match (loc1, loc2) with
       | (RegisterParameter (r1, _), RegisterParameter (r2, _)) ->
          register_equal r1 r2
       | _ -> false in
     let better (loc1: parameter_location_t) (loc2: parameter_location_t): bool =
       match (loc1, loc2) with
       | (RegisterParameter (r1, pd1), RegisterParameter (r2, pd2))
            when register_equal r1 r2 ->
          if btype_equal pd1.pld_type pd2.pld_type then
            false
          else if is_unknown_type pd1.pld_type then
            false
          else
            true
       | _ -> false in
     let newlocations =
       if List.exists (fun l ->
              match l with
              | RegisterParameter (r, _) -> register_equal r reg
              | _ -> false) fintf.fintf_parameter_locations then
         list_update fintf.fintf_parameter_locations loc eq better
       else
         loc :: fintf.fintf_parameter_locations in
     {fintf with fintf_parameter_locations = newlocations}
  | Some bctype ->
     let _ =
       chlog#add
         "add-function-register-parameter-location"
         (LBLOCK [
              STR "Location not added; bctype is fixed: ";
              STR (btype_to_string bctype)]) in
     fintf


let add_function_stack_parameter_location
      (fintf: function_interface_t)
      (offset: int)
      (ty: btype_t)
      (size: int): function_interface_t =
  match fintf.fintf_bctype with
  | None ->
     let locdetail = default_parameter_location_detail ~ty size in
     let loc = StackParameter (offset, locdetail) in
     let eq (loc1: parameter_location_t) (loc2: parameter_location_t): bool =
       match (loc1, loc2) with
       | (StackParameter (o1, _), StackParameter (o2, _)) -> o1 = o2
       | _ -> false in
     let better (loc1: parameter_location_t) (loc2: parameter_location_t): bool =
       match (loc1, loc2) with
       | (StackParameter (o1, pd1), StackParameter (o2, pd2)) when o1 = o2 ->
          if btype_equal pd1.pld_type pd2.pld_type then
            false
          else if is_unknown_type pd1.pld_type then
            false
          else
            true
       | _ -> false in
     let newlocations =
       if List.exists (fun l ->
              match l with
              | StackParameter (o, _) -> o = offset
              | _ -> false) fintf.fintf_parameter_locations then
         list_update fintf.fintf_parameter_locations loc eq better
       else
         loc :: fintf.fintf_parameter_locations in
     {fintf with fintf_parameter_locations = newlocations}
  | Some bctype ->
     let _ =
       chlog#add
         "add-function-stack-parameter-location"
         (LBLOCK [
              STR "Location not added; bctype is fixed: ";
              STR (btype_to_string bctype)]) in
     fintf


let add_function_global_parameter_location
      (fintf: function_interface_t)
      (gaddr: doubleword_int)
      (ty: btype_t)
      (size: int): function_interface_t =
  match fintf.fintf_bctype with
  | None ->
     let locdetail = default_parameter_location_detail ~ty size in
     let loc = GlobalParameter (gaddr, locdetail) in
     let eq (loc1: parameter_location_t) (loc2: parameter_location_t): bool =
       match (loc1, loc2) with
       | (GlobalParameter (dw1, _), GlobalParameter (dw2, _)) -> dw1#equal dw2
       | _ -> false in
     let better (loc1: parameter_location_t) (loc2: parameter_location_t): bool =
       match (loc1, loc2) with
       | (GlobalParameter (dw1, pd1), GlobalParameter (dw2, pd2))
            when dw1#equal dw2 ->
          if btype_equal pd1.pld_type pd2.pld_type then
            false
          else if is_unknown_type pd1.pld_type then
            false
          else
            true
       | _ -> false in
     let newlocations =
       if List.exists (fun l ->
              match l with
              | GlobalParameter (dw, _) -> dw#equal gaddr
              | _ -> false) fintf.fintf_parameter_locations then
         list_update fintf.fintf_parameter_locations loc eq better
       else
         loc :: fintf.fintf_parameter_locations in
     {fintf with fintf_parameter_locations = newlocations}
  | Some bctype ->
     let _ =
       chlog#add
         "add-function-global-parameter-location"
         (LBLOCK [
              STR "Location not added; bctype is fixed: ";
              STR (btype_to_string bctype)]) in
     fintf


let get_stack_parameter (fintf: function_interface_t) (index:int) =
  let fts = fintf.fintf_type_signature in
  try
    List.find (fun p ->
        match p.apar_location with
        | [StackParameter (n, _)] -> n = index
        | _ -> false) fts.fts_parameters
  with
    Not_found ->
      raise (BCH_failure
	       (LBLOCK [
                    STR "No stack parameter found with index: ";
                    INT index]))


let get_stack_parameter_name (fintf: function_interface_t) (index:int) =
  (get_stack_parameter fintf index).apar_name


let get_stack_parameter_names (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2)
    (List.fold_left (fun acc p ->
      match p.apar_location with
      | [StackParameter (i, _)] -> (i,p.apar_name) :: acc
      | _ -> acc) [] fts.fts_parameters)


let get_stack_parameter_count (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  List.length
    (List.filter
       (fun p ->
         match p.apar_location with
         | [StackParameter _] -> true | _ -> false) fts.fts_parameters)

let has_fmt_parameter (fintf: function_interface_t) =
  List.exists is_formatstring_parameter fintf.fintf_type_signature.fts_parameters


let get_fmt_parameter_index (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  let (result,_) =
    List.fold_left
      (fun (acc,c) p ->
        match acc with
        | Some _ -> (acc,0)
        | _ ->
           if is_formatstring_parameter p then (Some c, 0) else (None, c+1))
      (None, 0) fts.fts_parameters in
  match result with
  | Some c -> c
  | _ ->
     raise (BCH_failure
              (LBLOCK [STR "no format argument found in function signature"]))


let demangled_name_to_function_interface (dm: demangled_name_t) =
  let stack_adjustment = match dm.dm_calling_convention with
    | "__cdecl" -> Some 0
    | "__thiscall"
    | "__stdcall" -> Some (4 * (List.length dm.dm_parameter_types))
    | _ -> None in
  let returntype =
    match dm.dm_returntype with Some t -> t | _ -> t_void in
  let locdetail ty = default_parameter_location_detail ~ty (size_of_btype ty) in
  let make_parameter index ty = {
      apar_index = None;
    apar_name = templated_btype_to_name ty (index + 1) ;
    apar_type = ty ;
    apar_desc = "" ;
    apar_roles = [] ;
    apar_io = ArgReadWrite ;
    apar_location = [StackParameter (index + 1, locdetail ty)];
    apar_size = size_of_btype ty;
    apar_fmt = NoFormat
    } in
  let fts =
    { fts_parameters = List.mapi make_parameter dm.dm_parameter_types;
      fts_varargs = false;   (* TBD: to be investigated *)
      fts_va_list = None;
      fts_returntype = returntype;
      fts_rv_roles = [];
      fts_stack_adjustment = stack_adjustment;
      fts_calling_convention = dm.dm_calling_convention;
      fts_registers_preserved = []
    } in
  {
    fintf_name = tname_to_string dm.dm_name;
    fintf_jni_index = None;
    fintf_syscall_index = None;
    fintf_type_signature = fts;
    fintf_parameter_locations = [];
    fintf_bctype = None;
    fintf_returntypes = []
  }


let default_function_interface
      ?(cc="cdecl")
      ?(adj=0)
      ?(bctype=None)
      ?(bc_returntype=t_unknown)
      ?(bc_fts_parameters=[])
      ?(varargs=false)
      ?(locations=[])
      ?(returntypes=[])
      (name:string): function_interface_t =
  let fts = {
      fts_parameters = bc_fts_parameters;
      fts_varargs = varargs;
      fts_va_list = None;
      fts_returntype = bc_returntype;
      fts_rv_roles = [];
      fts_stack_adjustment = Some adj;
      fts_calling_convention = cc;
      fts_registers_preserved = [];
    } in
  {
    fintf_name = name;
    fintf_jni_index = None;
    fintf_syscall_index = None;
    fintf_type_signature = fts;
    fintf_parameter_locations = locations;
    fintf_bctype = bctype;
    fintf_returntypes = returntypes
  }


let fintf_add_stack_adjustment (fintf: function_interface_t) (adj: int) =
  let fts = get_fintf_fts fintf in
  let fts =
    if adj > 0 then
      if get_stack_parameter_count fintf = 0 then
        let params =
          List.map
            (fun i -> mk_indexed_stack_parameter (i * 4) i)
            (List.init (adj / 4) (fun i -> i + 1)) in
        {fts with fts_stack_adjustment = Some adj;
                  fts_calling_convention = "stdcall";
                  fts_parameters = params}
      else
        {fts with fts_stack_adjustment = Some adj;
                  fts_calling_convention = "stdcall"}
    else
      fts in
  {fintf with fintf_type_signature = fts}



(* --------------------------------- conversion of external type signature -- *)

let x86_cdecl_params (funargs: bfunarg_t list): fts_parameter_t list =
  let (_, _, params) =
    List.fold_left
      (fun (index, offset, params) (name, btype, _) ->
        let tysize = size_of_btype btype in
        let size = if tysize < 4 then 4 else tysize in
        let par: fts_parameter_t =
          mk_indexed_stack_parameter ~btype ~name ~size offset index in
           (index + 1, offset + size, par :: params)) (1, 4, []) funargs in
  params


let mips_params (funargs: bfunarg_t list): fts_parameter_t list =
  let (_, _, params) =
    List.fold_left
      (fun (index, ma_state, params) (name, btype, _) ->
        let tysize = size_of_btype btype in
        let size = if tysize < 4 then 4 else tysize in
        let (param, nmas) =
          match ma_state.mas_next_arg_reg with
          | Some reg ->
             let register = register_of_mips_register reg in
             let par: fts_parameter_t =
               mk_indexed_register_parameter ~btype ~name ~size register index in
             let ncr = get_next_mips_arg_reg reg in
             let nmas =
               match ncr with
               | Some _ -> {ma_state with mas_next_arg_reg = ncr}
               | _ ->
                  { mas_next_arg_reg = None;
                    mas_next_offset = Some 16
                  } in
             (par, nmas)
          | _ ->
             (match ma_state.mas_next_offset with
              | Some offset ->
                 let par: fts_parameter_t =
                   mk_indexed_stack_parameter ~btype ~name ~size offset index in
                 let nmas =
                   {ma_state with mas_next_offset = Some (offset + size)} in
                 (par, nmas)
              | _ ->
                 raise
                   (BCH_failure
                      (LBLOCK [
                           STR "mips_params: inconsistent state: ";
                           STR " both next core register and stackoffset ";
                           STR "are None"]))) in
        (index + 1, nmas, param :: params)) (1, mas_start_state, []) funargs in
  params


let bfuntype_to_function_interface
      (vname: string) (vtype: btype_t): function_interface_t =
  match vtype with
  | TFun (returntype, fargs, varargs, attrs)
    | TPtr (TFun (returntype, fargs, varargs, _), attrs) ->
     let params: fts_parameter_t list =
       match fargs with
       | None -> []
       | Some funargs ->
          (match system_settings#get_architecture with
           | "arm" -> arm_vfp_params funargs
           | "x86" -> x86_cdecl_params funargs
           | "mips" -> mips_params funargs
           | arch ->
              raise
                (BCH_failure
                   (LBLOCK [
                        STR "function_summary_of_bvarinfo: ";
                        STR arch;
                        STR " not (yet) supported"]))) in
     let _ =
       match attrs with
       | [] -> ()
       | _ ->
          chlog#add
            "function attributes"
            (LBLOCK [STR vname; STR "; "; STR (attributes_to_string attrs)]) in
     let params =
       List.sort
         (fun p1 p2 -> Stdlib.compare p1.apar_index p2.apar_index)
         params in
     if is_stdcall vtype then
       let _ =
         chlog#add
           "stdcall function interface"
           (LBLOCK [STR vname; STR ": "; STR (btype_to_string vtype)]) in
       let adj = 4 * (List.length params) in
       default_function_interface
         ~bc_returntype:returntype
         ~bc_fts_parameters:params
         ~varargs
         ~adj
         ~cc:"stdcall"
         ~bctype:(Some vtype)
       vname
     else
       default_function_interface
         ~bc_returntype:returntype
         ~bc_fts_parameters:params
         ~varargs
         ~bctype:(Some vtype)
       vname
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "Unexpected type for function ";
               STR vname;
               STR ": ";
               btype_to_pretty vtype]))


let bvarinfo_to_function_interface (vinfo: bvarinfo_t): function_interface_t =
  let vname = vinfo.bvname in
  let vtype = vinfo.bvtype in
  bfuntype_to_function_interface vname vtype


(* Note: this currently works correctly only if the function interface has been
   constructed from a header file or function summary, because the parameters
   are added to the type signature. To support the general case requires the
   addition of (inferred) parameters to the function interface itself.*)
let add_format_spec_parameters
      (fintf: function_interface_t)
      (argspecs: argspec_int list): function_interface_t =
  let pars = get_fts_parameters fintf in
  let fmtpars =
    match system_settings#get_architecture with
    | "arm" -> get_arm_format_spec_parameters pars argspecs
    | arch ->
       let _ =
         ch_error_log#add
           "add_format_spec_parameters"
           (LBLOCK [STR "Not yet implemented for "; STR arch]) in
       [] in
  let fts = fintf.fintf_type_signature in
  let newpars = fts.fts_parameters @ fmtpars in
  let newfts = {fts with fts_parameters = newpars} in
  {fintf with fintf_type_signature = newfts}
