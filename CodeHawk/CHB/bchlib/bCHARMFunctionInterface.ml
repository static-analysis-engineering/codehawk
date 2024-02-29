(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023  Aarno Labs LLC

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

(* chutil *)
open CHFormatStringParser
open CHLogger
open CHUtil

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHFtsParameter
open BCHLibTypes


(* Reference:
     ARM Procedure Call Standard for the ARM Architecture
     Document number: ARM IHI 0042D, current through ABI release 2.08
     Date of issue: 16th October 2009

   This document describes the allocation of registers and stack locations for
   function parameters (arguments).

   Some notable features:
   - vararg arguments are never allocated to the floating point registers
      (S0-S31 and D0-D15); vararg floats are promoted to doubles
   - the registers S0-S31 and D0-D15 occupy the same memory area (that is,
      S0, S1 overlap exactly with D0), which means that when, e.g., S0 is
      allocated for a float, D0 is not available for a double any more.
      However, back-filling is employed to avoid empty holes. For example,
      the type signature (float x, double y, float z) would be allocated
      as follows:
         x: S0
         y: D1
         z: S1

   Unit tests for some of these cases are provided in
   CHT/CHB_tests/bchlib_tests/txbchlib/bCHFunctionInterfaceTest.ml
 *)
type arm_argument_state_t =
  { aas_next_core_reg: arm_reg_t option;
    aas_next_core_reg_byteoffset: int;
    aas_next_sp_reg: arm_extension_register_t option;
    aas_next_dp_reg: arm_extension_register_t option;
    aas_next_offset: int option;    (* stack offset *)
    aas_next_position: pld_position_t list;  (* used for struct/array parameters *)
    aas_fp_slots_available: int list
  }


let aas_start_state =
  { aas_next_core_reg = Some AR0;
    aas_next_core_reg_byteoffset = 0;
    aas_next_sp_reg = Some (mk_arm_sp_reg 0);
    aas_next_dp_reg = Some (mk_arm_dp_reg 0);
    aas_next_offset = None;
    aas_next_position = [];
    aas_fp_slots_available = List.init 32 (fun i -> i)
  }


let push_field_pos (state: arm_argument_state_t) (finfo: bfieldinfo_t) =
  match get_struct_field_offset finfo with
  | Some foffset ->
     let fieldpos =
       mk_field_position finfo.bfckey foffset (get_struct_field_name finfo) in
     {state with aas_next_position = fieldpos :: state.aas_next_position}
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "push_field_pos: no offset found"]))


let pop_pos (state: arm_argument_state_t): arm_argument_state_t =
  match state.aas_next_position with
  | [] ->
     raise
       (BCH_failure
          (LBLOCK [STR "pop_pos: Arm argument state with empty position"]))
  | h :: tl -> {state with aas_next_position = tl}


let update_field_pos (state: arm_argument_state_t) (finfo: bfieldinfo_t) =
  push_field_pos (pop_pos state) finfo


let mk_arm_argument_state
      ?(nextreg=None)
      ?(nextreg_byteoffset=0)
      ?(nextspreg=None)
      ?(nextdpreg=None)
      ?(nextoffset=None)
      ?(nextpos=[])
      ?(fpslots=[])
      () =
  { aas_next_core_reg = nextreg;
    aas_next_core_reg_byteoffset = nextreg_byteoffset;
    aas_next_sp_reg = nextspreg;
    aas_next_dp_reg = nextdpreg;
    aas_next_offset = nextoffset;
    aas_next_position = nextpos;
    aas_fp_slots_available = fpslots
  }


let opteq ?(f=Stdlib.compare) a b = (optvalue_compare a b f) = 0


let arm_argument_state_equal
      (a1: arm_argument_state_t) (a2: arm_argument_state_t) =
  (opteq a1.aas_next_core_reg a2.aas_next_core_reg)
  && (a1.aas_next_core_reg_byteoffset = a2.aas_next_core_reg_byteoffset)
  && (opteq a1.aas_next_sp_reg a2.aas_next_sp_reg)
  && (opteq a1.aas_next_dp_reg a2.aas_next_dp_reg)
  && (opteq a1.aas_next_offset a2.aas_next_offset)
  && ((list_compare a1.aas_next_position a2.aas_next_position pld_pos_compare) = 0)
  && ((list_compare
         a1.aas_fp_slots_available a2.aas_fp_slots_available Stdlib.compare) = 0)


let arm_argument_state_to_string (a: arm_argument_state_t) =
  ("ncr:"
   ^ (match a.aas_next_core_reg with
      | Some reg -> armreg_to_string reg
      | _ -> "_")
   ^ (if a.aas_next_core_reg_byteoffset = 0 then
        ""
      else
        "; ncrb:" ^ (string_of_int a.aas_next_core_reg_byteoffset))
   ^ (match a.aas_next_sp_reg with
      | Some reg -> "; nsp:" ^ arm_extension_reg_to_string reg
      | _ -> "")
   ^ (match a.aas_next_dp_reg with
      | Some reg -> "; ndp:" ^ arm_extension_reg_to_string reg
      | _ -> "")
   ^ "; noff:"
   ^ (match a.aas_next_offset with
      | Some off -> string_of_int off
      | _ -> "_")
   ^ (match a.aas_next_position with
      | [] -> ""
      | l ->
         ";[" ^ (String.concat ", " (List.map pld_position_to_string l)) ^ "]")
   ^ (if (List.length a.aas_fp_slots_available) = 32 then
        ""
      else
        "; fp-slots:["
        ^ (String.concat "," (List.map string_of_int a.aas_fp_slots_available))))


let get_next_core_reg (r: arm_reg_t): arm_reg_t option =
  match r with
  | AR0 -> Some AR1
  | AR1 -> Some AR2
  | AR2 -> Some AR3
  | _ -> None


let get_next_sp_reg_naas
      (aas: arm_argument_state_t): arm_argument_state_t =
  let slots = aas.aas_fp_slots_available in
  match slots with
  | [] ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "get_next_sp_reg_naas: inconsistent state: ";
               STR "no floating point slots available"]))
  | [hd] ->
     { aas with
       aas_next_sp_reg = None;
       aas_next_dp_reg = None;
       aas_next_offset =
         (match aas.aas_next_offset with
         | Some i -> Some i
         | _ -> Some 0);
       aas_fp_slots_available = []
     }
  | hd1 :: hd2 :: tl ->
     { aas with
       aas_next_sp_reg = Some (mk_arm_sp_reg hd2);
       aas_next_dp_reg =
         (if hd2 mod 2 = 0 then
           Some (mk_arm_dp_reg (hd2 / 2))
         else
           match tl with
           | [] -> None
           | hd3 :: _ -> Some (mk_arm_dp_reg (hd3/ 2)));
       aas_fp_slots_available = hd2 :: tl
     }


let get_next_dp_reg_naas
      (aas: arm_argument_state_t): arm_argument_state_t =
  let slots = aas.aas_fp_slots_available in
  match slots with
  | [hd1; hd2] ->
     { aas with
       aas_next_sp_reg = None;
       aas_next_dp_reg = None;
       aas_next_offset =
         (match aas.aas_next_offset with
         | Some i -> Some i
         | _ -> Some 0);
       aas_fp_slots_available = []
     }
  | hd1 :: hd2 :: hd3 :: tl when (hd1 mod 2) = 0 ->  (* no backfill slots *)
     { aas with
       aas_next_sp_reg = Some (mk_arm_sp_reg hd3);
       aas_next_dp_reg = Some (mk_arm_dp_reg (hd3 / 2));
       aas_next_offset =
         (match aas.aas_next_offset with
         | Some i -> Some i
         | _ -> Some 0);
       aas_fp_slots_available = hd3 :: tl
     }
  | hd1 :: hd2 :: hd3 :: tl ->   (* hd1 is a backfill slot *)
     { aas with
       aas_next_dp_reg =
         (match tl with
          | [] -> None
          | hhd :: _ ->
             Some {armxr_type = XDouble; armxr_index = hhd / 2});
       aas_fp_slots_available = hd1 :: tl
     }
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "get_next_dp_reg: not yet supported"]))


let get_float_param_next_state
      (size: int)
      (name: string)
      (btype: btype_t)
      (aa_state: arm_argument_state_t)
      (index: int): (fts_parameter_t * arm_argument_state_t) =
  match btype with
  | TFloat (FFloat, _, _) ->
     (match aa_state.aas_next_sp_reg with
      | Some reg ->
         let register = register_of_arm_extension_register reg in
         let par: fts_parameter_t =
           mk_indexed_register_parameter ~btype ~name ~size register index in
         let naas = get_next_sp_reg_naas aa_state in
         (par, naas)
      | _ ->
         (match aa_state.aas_next_offset with
          | Some offset ->
             let par: fts_parameter_t =
               mk_indexed_stack_parameter ~btype ~name offset index in
             let naas =
               {aa_state with aas_next_offset = Some (offset + size)} in
             (par, naas)
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Inconsistent arm-argument-state: ";
                       STR "both next sp-reg and offset are None"]))))
  | TFloat (FDouble, _, _) ->
     (match aa_state.aas_next_dp_reg with
      | Some reg ->
         let register = register_of_arm_extension_register reg in
         let par: fts_parameter_t =
           mk_indexed_register_parameter ~btype ~name ~size register index in
         let naas = get_next_dp_reg_naas aa_state in
         (par, naas)
      | _ ->
         (match aa_state.aas_next_offset with
          | Some offset ->
             let par: fts_parameter_t =
               mk_indexed_stack_parameter ~btype ~name offset index in
             let naas =
               {aa_state with aas_next_offset = Some (offset + size)} in
             (par, naas)
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Inconsistent arm-argument-state: ";
                       STR "both next sp-reg and offset are None"]))))
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "not yet supported"]))


let get_int_paramloc_next_state
      (size: int)
      (btype: btype_t)
      (aa_state: arm_argument_state_t): (parameter_location_t * arm_argument_state_t) =
  match aa_state.aas_next_core_reg with
  | Some reg ->
     let register = register_of_arm_register reg in
     let paramloc =
       mk_register_parameter_location
         ~btype
         ~size
         ~position:aa_state.aas_next_position
         register in
     let ncr = get_next_core_reg reg in
     let naas =
       match ncr with
       | Some r -> {aa_state with aas_next_core_reg = ncr}
       | _ ->
          {aa_state with
            aas_next_core_reg = None; aas_next_offset = Some 0} in
     (paramloc, naas)
  | _ ->
     match aa_state.aas_next_offset with
     | Some offset ->
        let paramloc = mk_stack_parameter_location ~btype ~size offset in
        let naas = {aa_state with aas_next_offset = Some (offset + size)} in
        (paramloc, naas)
     | _ ->
        raise
          (BCH_failure
             (LBLOCK [
                  STR "Inconsistent arm-argument state: ";
                  STR "both next register and offset are None"]))


let get_int_paramlocpart_next_state
      (size: int)
      (btype: btype_t)
      (fldoffset: int)
      (aa_state: arm_argument_state_t): (parameter_location_t * arm_argument_state_t) =
  let alignment = fldoffset mod 4 in
  match (aa_state.aas_next_core_reg, aa_state.aas_next_core_reg_byteoffset) with
  | (Some reg, roffset) ->
     if alignment = roffset then
       let register = register_of_arm_register reg in
       let paramloc =
         mk_register_parameter_location
           ~btype ~size ~extract:(Some (roffset, size)) register in
       let naas =
         if roffset + size < 4 then
           {aa_state with aas_next_core_reg_byteoffset = roffset + size}
         else if roffset + size = 4 then
           let ncr = get_next_core_reg reg in
           (match ncr with
            | Some r ->
               {aa_state with
                 aas_next_core_reg = ncr; aas_next_core_reg_byteoffset = 0}
            | _ ->
               {aa_state with
                 aas_next_core_reg = None; aas_next_offset = Some 0})
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Misalignment in struct parameter: ";
                     btype_to_pretty btype;
                     STR " with size: ";
                     INT size;
                     STR " and offset: ";
                     INT roffset])) in
       (paramloc, naas)
     else
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Alignment failure in struct param location: ";
                 STR "alignment: ";
                 INT alignment;
                 STR "; byte offset: ";
                 INT roffset]))
  | _ ->
       match aa_state.aas_next_offset with
       | Some offset ->
          let paramloc = mk_stack_parameter_location ~btype ~size offset in
          let naas = {aa_state with aas_next_offset = Some (offset + size)} in
          (paramloc, naas)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "Inconsistent struct arm-argument state: ";
                    btype_to_pretty btype]))


let get_int_param_next_state
      (size: int)
      (name: string)
      (btype: btype_t)
      (aa_state: arm_argument_state_t)
      (index: int): (fts_parameter_t * arm_argument_state_t) =
  match aa_state.aas_next_core_reg with
  | Some reg ->
     let register = register_of_arm_register reg in
     let par: fts_parameter_t =
       mk_indexed_register_parameter ~btype ~name ~size register index in
     let ncr = get_next_core_reg reg in
     let naas =
       match ncr with
       | Some r -> {aa_state with aas_next_core_reg = ncr}
       | _ ->
          {aa_state with
           aas_next_core_reg = None;
           aas_next_offset = Some 0
         } in
     (par, naas)
  | _ ->
     (match aa_state.aas_next_offset with
      | Some offset ->
         let par: fts_parameter_t =
           mk_indexed_stack_parameter ~btype ~name offset index in
         let naas =
           {aa_state with aas_next_offset = Some (offset + size)} in
         (par, naas)
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Inconsistent arm-argument-state: ";
                   STR "both next register and offset are None"])))


let get_long_int_param_next_state
      (size: int)
      (name: string)
      (btype: btype_t)
      (aa_state: arm_argument_state_t)
      (index: int): (fts_parameter_t * arm_argument_state_t) =
  match aa_state.aas_next_core_reg with
  | Some AR0 ->
     let register = register_of_arm_double_register AR0 AR1 in
     let par: fts_parameter_t =
       mk_indexed_register_parameter ~btype ~name ~size register index in
     let naas = {aa_state with aas_next_core_reg = Some AR2} in
     (par, naas)
  | Some (AR1 | AR2) ->
     let register = register_of_arm_double_register AR2 AR3 in
     let par: fts_parameter_t =
       mk_indexed_register_parameter ~btype ~name ~size register index in
     let naas =
       {aa_state with aas_next_core_reg = None; aas_next_offset = Some 0} in
     (par, naas)
  | Some AR3 ->
     let par: fts_parameter_t =
       mk_indexed_stack_parameter ~btype ~name 0 index in
     let naas =
       {aa_state with aas_next_core_reg = None; aas_next_offset = Some size} in
     (par, naas)
  | Some _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Inconsistent state in get_long_int_param_next_state"]))
  | _ ->
     match aa_state.aas_next_offset with
     | Some offset ->
        let par: fts_parameter_t =
          mk_indexed_stack_parameter ~btype ~name offset index in
        let naas =
          {aa_state with aas_next_offset = Some (offset + size)} in
        (par, naas)
     | _ ->
        raise
          (BCH_failure
             (LBLOCK [
                  STR "Inconsistent arm-argument-state: ";
                  STR "both next register and offset are None"]))


let rec get_arm_struct_field_locations
          (bfinfo: bfieldinfo_t)
          (aa_state: arm_argument_state_t):
          (parameter_location_t list * arm_argument_state_t) =
  let fieldstate = aa_state in
  let bftype = resolve_type (get_struct_field_type bfinfo) in
  let (bfsize, bfoffset) =
    match (get_struct_field_size bfinfo,
           get_struct_field_offset bfinfo) with
    | (Some s, Some o) -> (s, o)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "get_arm_struct_field_locations: ";
                 STR "no layout provided: ";
                 fieldinfo_to_pretty bfinfo])) in
  if (is_int bftype || is_pointer bftype) && bfsize = 4 then
    let (loc, naas) =
      get_int_paramloc_next_state bfsize bftype fieldstate in
    ([loc], naas)
  else if is_int bftype && bfsize < 4 then
    let (loc, naas) =
      get_int_paramlocpart_next_state bfsize bftype bfoffset fieldstate in
    ([loc], naas)
  else if is_array_type bftype then
    get_arm_array_locations bfsize bftype bfoffset fieldstate
  else
    raise
      (BCH_failure
         (LBLOCK [
              STR "get_arm_struct_field_locations: ";
              STR "not yet implemented: ";
              btype_to_pretty bftype]))


and get_arm_array_locations
(size: int)
(eltype: btype_t)
(offset: int)
(aa_state: arm_argument_state_t):
      (parameter_location_t list * arm_argument_state_t) =
  ([], aa_state)


let rec get_arm_struct_param_next_state
      (size: int)
      (name: string)
      (btype: btype_t)
      (aa_state: arm_argument_state_t)
      (index: int): (fts_parameter_t * arm_argument_state_t) =
  let fields = get_struct_type_fields btype in
  let fieldstate =
    try
      push_field_pos aa_state (List.hd fields)
    with
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Failure in get_arm_struct_param_next_state: List.hd. ";
                 STR (btype_to_string btype)])) in
  let (naas, paramlocations) =
    List.fold_left
      (fun (aa_state, paramlocs) bfinfo ->
        let fldstate = update_field_pos aa_state bfinfo in
        let (locs, new_state) =
          get_arm_struct_field_locations bfinfo fldstate in
        (new_state, locs @ paramlocs)) (fieldstate, []) fields in
  let naas = pop_pos naas in
  let paramlocations = List.sort parameter_location_compare paramlocations in
  let param =
    mk_indexed_multiple_locations_parameter
      ~btype ~name ~size paramlocations index in
  (param, naas)


let arm_vfp_params (funargs: bfunarg_t list): fts_parameter_t list =
  let (_, _, params) =
    List.fold_left
      (fun (index, aa_state, params) (name, btype, _) ->
        let btype = resolve_type btype in
        let tysize = size_of_btype btype in
        (* assume no packing at the argument top level *)
        let size = if tysize < 4 then 4 else tysize in
        let (param, new_state) =
          if (is_int btype || is_pointer btype) && size = 4 then
            get_int_param_next_state size name btype aa_state index
          else if (is_int btype || is_pointer btype) then
            get_long_int_param_next_state size name btype aa_state index
          else if is_float btype then
            get_float_param_next_state size name btype aa_state index
          else if (is_struct_type btype )
                  && (get_struct_type_compinfo btype).bcstruct then
            get_arm_struct_param_next_state size name btype aa_state index
          else
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "vfp_params: Not yet implemented; ";
                      btype_to_pretty btype])) in
        (index + 1, new_state, param :: params))
      (1, aas_start_state, []) funargs in
  params


let get_arm_format_spec_parameters
      (cpars: fts_parameter_t list)
      (argspecs: argspec_int list): fts_parameter_t list =
  let nextindex = (List.length cpars) + 1 in
  let update_core_reg aas (r: arm_reg_t) =
    match aas.aas_next_core_reg with
    | Some reg when r = reg ->
       let nxtreg = get_next_core_reg r in
       (match nxtreg with
        | Some nxtreg -> {aas with aas_next_core_reg = Some nxtreg}
        | _ ->
           {aas with aas_next_core_reg = None; aas_next_offset = Some 0})
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "get_arm_format_spec_parameters: core"])) in
  let update_core_double_reg aas (r1: arm_reg_t) (r2: arm_reg_t) =
    match aas.aas_next_core_reg with
    | Some reg when r1 = reg ->
       let nxtreg = get_next_core_reg r2 in
       (match nxtreg with
        | Some nxtreg -> {aas with aas_next_core_reg = Some nxtreg}
        | _ ->
           {aas with aas_next_core_reg = None; aas_next_offset = Some 0})
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "get_arm_format_spec_parameters: core-double"])) in
  let update_extension_reg aas (r: arm_extension_register_t) =
    match r.armxr_type with
    | XSingle ->
       (match aas.aas_next_sp_reg with
        | Some xreg when xreg.armxr_index = r.armxr_index ->
           get_next_sp_reg_naas aas
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [STR "get_arm_format_spec_parameters: sp"])))
    | XDouble ->
       (match aas.aas_next_dp_reg with
        | Some xreg when xreg.armxr_index = r.armxr_index ->
           get_next_dp_reg_naas aas
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [STR "get_arm_format_spec_parameters: dp"])))
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "get_arm_format_spec_parameters: not supported"])) in
  let update_stack_offset aas (offset: int) (size: int) =
    match aas.aas_next_offset with
    | Some nxtoffset when offset = nxtoffset ->
       {aas with aas_next_offset = Some (offset + size)}
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "get_arm_format_spec_parameters: stack"])) in
  let fmtaas =
    List.fold_left
      (fun aas p ->
        match p.apar_location with
        | [RegisterParameter (ARMRegister r, _)] ->
           update_core_reg aas r
        | [RegisterParameter (ARMDoubleRegister (r1, r2), _)] ->
           update_core_double_reg aas r1 r2
        | [RegisterParameter (ARMExtensionRegister r, _)] ->
           update_extension_reg aas r
        | [StackParameter (offset, pld)] ->
           update_stack_offset aas offset pld.pld_size
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "get_arm_format_spec_parameters: ";
                     STR "no or multiple locations"])))
      aas_start_state cpars in
  let (_, pars, _, _) =
    List.fold_left (fun (aas, accpars, varargindex, nxtindex) argspec ->
        let ftype = get_fmt_spec_type argspec in
        let ftype =
          if is_float ftype then
            promote_float ftype
          else if is_int ftype then
            promote_int ftype
          else
            ftype in
        let size = size_of_btype ftype in
        let name = "vararg_" ^ (string_of_int varargindex) in
        let (param, new_state) =
          match size with
          | 4 -> get_int_param_next_state size name ftype aas nxtindex
          | 8 -> get_long_int_param_next_state size name ftype aas varargindex
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Var-arg size: "; INT size; STR " not supported"])) in
        (new_state, param :: accpars, varargindex + 1, nxtindex + 1))
      (fmtaas, [], 1, nextindex) argspecs in
  pars
