(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHFtsParameter
open BCHLibTypes


type mips_argument_state_t =
  { mas_next_core_reg: mips_reg_t option;
    mas_next_offset: int option  (* stack offset *)
  }

let mas_start_state =
  { mas_next_core_reg = Some MRa0;
    mas_next_offset = None
  }


let get_next_core_reg (r: mips_reg_t): mips_reg_t option =
  match r with
  | MRa0 -> Some MRa1
  | MRa1 -> Some MRa2
  | MRa2 -> Some MRa3
  | _ -> None


let get_mips_int_param_next_state
      (size: int)
      (name: string)
      (btype: btype_t)
      (ma_state: mips_argument_state_t)
      (index: int): (fts_parameter_t * mips_argument_state_t) =
  match ma_state.mas_next_core_reg with
  | Some reg ->
     let register = register_of_mips_register reg in
     let par: fts_parameter_t =
       mk_indexed_register_parameter ~btype ~name ~size register index in
     let ncr = get_next_core_reg reg in
     let nmas =
       match ncr with
       | Some _ -> {ma_state with mas_next_core_reg = ncr}
       | _ -> {mas_next_core_reg = None; mas_next_offset = Some 16} in
     (par, nmas)
  | _ ->
     (match ma_state.mas_next_offset with
      | Some offset ->
         let par: fts_parameter_t =
           mk_indexed_stack_parameter ~btype ~name offset index in
         let nmas =
           {ma_state with mas_next_offset = Some (offset + size)} in
         (par, nmas)
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Inconsistent mips-argument-state: ";
                   STR "both next register and offset are None"])))


let get_mips_format_spec_parameters
      (cpars: fts_parameter_t list)
      (argspecs: argspec_int list): fts_parameter_t list =
  let nextindex = (List.length cpars) + 1 in
  let update_core_reg mas (r: mips_reg_t) =
    match mas.mas_next_core_reg with
    | Some reg when r = reg ->
       let nxtreg = get_next_core_reg r in
       (match nxtreg with
        | Some nxtreg -> {mas with mas_next_core_reg = Some nxtreg}
        | _ ->
           {mas_next_core_reg = None; mas_next_offset = Some 16})
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "get_mips_format_spec_parameters: core"])) in
  let update_stack_offset mas (offset: int) (size: int) =
    match mas.mas_next_offset with
    | Some nxtoffset when offset = nxtoffset ->
       {mas with mas_next_offset = Some (offset + size)}
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "get_mips_format_spec_parameters: stack"])) in
  let fmtmas =
    List.fold_left
      (fun mas p ->
        match p.apar_location with
        | [RegisterParameter (MIPSRegister r, _)] ->
           update_core_reg mas r
        | [StackParameter (offset, pld)] ->
           update_stack_offset mas offset pld.pld_size
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "get_mips_format_spec_parameters: ";
                     STR "no or multiple locations"])))
      mas_start_state cpars in
  let (_, pars, _, _) =
    List.fold_left (fun (mas, accpars, varargindex, nxtindex) argspec ->
        let ftype = get_fmt_spec_type argspec in
        let size_r = size_of_btype ftype in
        let name = "vararg_" ^ (string_of_int varargindex) in
        let (param, new_state) =
          match size_r with
          | Ok 4 -> get_mips_int_param_next_state 4 name ftype mas nxtindex
          | Ok size ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Var-arg size: "; INT size; STR " not supported"]))
          | Error e ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Error in mips_format_spec_parameters: ";
                       STR (String.concat "; " e)])) in
        (new_state, param :: accpars, varargindex + 1, nxtindex + 1))
      (fmtmas, [], 1, nextindex) argspecs in
  pars
