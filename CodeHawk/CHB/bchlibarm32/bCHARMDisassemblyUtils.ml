(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs, LLC

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


(* Documentation reference:
 * ========================
 * ARM Architecture Reference Manual
 * ARMv7-A and ARMv7-R edition, March 29, 2018
 *)

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStrings
open BCHSystemSettings

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMPseudocode
open BCHARMTypes

module TR = CHTraceResult


(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16


let rec pow2 n =
  match n with
  | 0 -> 1
  | 1 -> 2
  | n -> 
    let b = pow2 (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else 2)


let stri = string_of_int


let get_interrupt_flags (n: int): interrupt_flags_t =
  match n with
  | 0 -> IFlag_None
  | 1 -> IFlag_F
  | 2 -> IFlag_I
  | 3 -> IFlag_IF
  | 4 -> IFlag_A
  | 5 -> IFlag_AF
  | 6 -> IFlag_AI
  | 7 -> IFlag_AIF
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Unexpected value for interrupt_flags: "; INT n]))


let get_it_condition_list (firstcond:int) (mask:int) =
  let fc0 = firstcond mod 2 in
  let elsecond = if fc0 = 1 then firstcond - 1 else firstcond + 1 in
  let thencc = ("T", get_opcode_cc firstcond) in
  let elsecc = ("E", get_opcode_cc elsecond) in
  let xyz =
    match (mask, fc0) with
    | (8, _) -> []
    | (4, 0) -> [thencc]
    | (4, 1) -> [elsecc]
    | (12, 0) -> [elsecc]
    | (12, 1) -> [thencc]
    | (2, 0) -> [thencc; thencc]
    | (2, 1) -> [elsecc; elsecc]
    | (10, 0) -> [elsecc; thencc]
    | (10, 1) -> [thencc; elsecc]
    | (6, 0) -> [thencc; elsecc]
    | (6, 1) -> [elsecc; thencc]
    | (14, 0) -> [elsecc; elsecc]
    | (14, 1) -> [thencc; thencc]
    | (1, 0) -> [thencc; thencc; thencc]
    | (1, 1) -> [elsecc; elsecc; elsecc]
    | (9, 0) -> [elsecc; thencc; thencc]
    | (9, 1) -> [thencc; elsecc; elsecc]
    | (5, 0) -> [thencc; elsecc; thencc]
    | (5, 1) -> [elsecc; thencc; elsecc]
    | (13, 0) -> [elsecc; elsecc; thencc]
    | (13, 1) -> [thencc; thencc; elsecc]
    | (3, 0) -> [thencc; thencc; elsecc]
    | (3, 1) -> [elsecc; elsecc; thencc]
    | (11, 0) -> [elsecc; thencc; elsecc]
    | (11, 1) -> [thencc; elsecc; thencc]
    | (7, 0) -> [thencc; elsecc; elsecc]
    | (7, 1) -> [elsecc; thencc; thencc]
    | (15, 0) -> [elsecc; elsecc; elsecc]
    | (15, 1) -> [thencc; thencc; thencc]
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Unexpected values in get_it_condition_list: ";
                 STR "mask: ";
                 INT mask;
                 STR "; fc0: ";
                 INT fc0])) in
  thencc::xyz


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
