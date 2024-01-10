(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHLocation

(* bchlibpower32 *)
open BCHPowerTypes


class pwr_code_pc_t (block: pwr_assembly_block_int): pwr_code_pc_int =
object

  val mutable instruction_list = block#get_instructions
  val ctxtloc = block#location

  (* testloc, jumploc, then successor_add, else_successor_addr, testexpr *)
  val mutable conditional_successor_info = None

  method get_next_instruction =
    match instruction_list with
    | [] ->
       let msg =
         LBLOCK [
             block#first_address#toPretty;
             STR ": ";
             STR "pwr_code_pc#get_next_instruction"] in
       begin
         ch_error_log#add "cfg error" msg;
         raise (BCH_failure msg)
       end
    | h::tl ->
       let ctxtiaddr = (make_i_location ctxtloc h#get_address)#ci in
       begin
         instruction_list <- tl;
         (ctxtiaddr, h)
       end

  method block_successors = block#successors

  method get_block_successor =
    match block#successors with
    | [succ] -> succ
    | [] ->
       let msg =
         LBLOCK [
             block#first_address#toPretty;
             STR ": ";
             STR "get_block_successor has no successor"] in
       begin
         ch_error_log#add "cfg error" msg;
         raise (BCH_failure msg)
       end
    | _ ->
       let msg =
         LBLOCK [
             block#first_address#toPretty;
             STR ": ";
             STR "get_block_successor has multiple successors"] in
       begin
         ch_error_log#add "cfg error" msg;
         raise (BCH_failure msg)
       end

  method get_false_branch_successor =
    match block#successors with
    | [fb] | [fb; _] -> fb
    | bsucc ->
       let msg =
         LBLOCK [
             block#first_address#toPretty;
             NL;
             block#toPretty;
             NL;
             INDENT (
                 3,
                 LBLOCK [
                     STR "get_false_branch_successor has ";
                     INT (List.length bsucc);
                     STR " successors"])] in
       begin
         ch_error_log#add "cfg error" msg;
         raise (BCH_failure msg)
       end

  method get_true_branch_successor =
    match block#successors with
    | [_; tb] -> tb
    | bsucc ->
       let msg =
         LBLOCK [
             block#first_address#toPretty;
             NL;
             block#toPretty;
             NL;
             INDENT (
                 3,
                 LBLOCK [
                     STR "get_true_branch successor has ";
                     INT (List.length bsucc);
                     STR " successors; expected two successors"])] in
       begin
         ch_error_log#add "cfg error" msg;
         raise (BCH_failure msg)
       end

  method has_more_instructions =
    match instruction_list with [] -> false | _ -> true

  method has_conditional_successor =
    match conditional_successor_info with Some _ -> true | _ -> false

  method get_conditional_successor_info =
    match conditional_successor_info with
    | Some i -> i
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "No conditional jump info found for block at address: ";
                 block#first_address#toPretty;
                 STR " in function ";
                 block#faddr#toPretty]))
end


let make_pwr_code_pc (block: pwr_assembly_block_int) =
  new pwr_code_pc_t block
