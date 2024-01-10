(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs, LLC

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

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHDoubleword
open BCHLibTypes
open BCHStrings

(* bchlibelf *)
open BCHELFHeader

(* bchlibpower32 *)
open BCHPowerTypes


module TR = CHTraceResult


let get_string_reference (floc:floc_int) (xpr:xpr_t) =
  try
    match xpr with
    | XConst (IntConst num) ->
       log_tfold_default
         (mk_tracelog_spec
            ~tag:"get_string_reference"
            (floc#cia ^": constant: " ^ num#toString))
         (fun address ->
           begin
	     match elf_header#get_string_at_address address with
	     | Some str ->
	        begin
	          string_table#add_xref address str floc#fa floc#cia;
                  (if collect_diagnostics () then
                     ch_diagnostics_log#add
                       "add string" (LBLOCK [floc#l#toPretty; STR "; "; STR str]));
	          Some str
	        end
	     | _ ->
                begin
                  (if collect_diagnostics () then
                     ch_diagnostics_log#add
                       "no string found"
                       (LBLOCK [floc#l#toPretty; STR ": "; address#toPretty]));
                  None
                end
           end)
         None
         (numerical_to_doubleword num)
    | XOp (XPlus, [XVar v; XConst (IntConst num)]) ->
      if floc#env#has_initialized_string_value v num#toInt then
	Some (floc#env#get_initialized_string_value v num#toInt)
      else
	None
    | _ -> None
  with
  | _ -> None


let is_unconditional_nia_target_branch
      (instr: pwr_assembly_instruction_int): bool =
  match instr#get_opcode with
  | BranchConditionalLink (_, _, bo, _, tgt, _)
       when tgt#is_absolute_address
            && bo = 20
            && tgt#get_absolute_address#to_int
               = (instr#get_address#to_int + 4) -> true
  | _ -> false


let opt_absolute_branch_target
      (instr: pwr_assembly_instruction_int): doubleword_int option =
  match instr#get_opcode with
  (* Special case that unconditionally jumps to the next instruction *)
  | BranchConditionalLink _ when is_unconditional_nia_target_branch instr ->
     None

  | Branch (_, tgt)
    | BranchConditional (_, _, _, _, tgt)
    | BranchConditionalLink (_, _, _, _, tgt, _)
    | CBranchDecrementNotZero (_, _, _, _, _, tgt, _)
    | CBranchDecrementZero (_, _, _, _, _, tgt, _)
    | CBranchEqual (_, _, _, _, _, _, tgt)
    | CBranchGreaterThan (_, _, _, _, _, _, tgt)
    | CBranchLessEqual (_, _, _, _, _, _, tgt)
    | CBranchLessThan (_, _, _, _, _, _, tgt)
    | CBranchNotEqual (_, _, _, _, _, _, tgt) when tgt#is_absolute_address ->
     Some tgt#get_absolute_address
  | _ -> None


let is_absolute_branch_target
      (instr: pwr_assembly_instruction_int): bool =
  match opt_absolute_branch_target instr with
  | Some _ -> true
  | _ -> false


let opt_conditional_absolute_branch_target
      (instr: pwr_assembly_instruction_int): doubleword_int option =
  match instr#get_opcode with
  | BranchConditionalLink _ when is_unconditional_nia_target_branch instr ->
     None

  | BranchConditional (_, _, _, _, tgt)
    | BranchConditionalLink (_, _, _, _, tgt, _)
    | CBranchEqual (_, _, _, _, _, _, tgt)
    | CBranchGreaterThan (_, _, _, _, _, _, tgt)
    | CBranchLessEqual (_, _, _, _, _, _, tgt)
    | CBranchLessThan (_, _, _, _, _, _, tgt)
    | CBranchNotEqual (_, _, _, _, _, _, tgt) when tgt#is_absolute_address ->
     Some tgt#get_absolute_address

  | _ -> None


let is_conditional_absolute_branch_target
      (instr: pwr_assembly_instruction_int): bool =
  match opt_conditional_absolute_branch_target instr with
  | Some _ -> true
  | _ -> false
