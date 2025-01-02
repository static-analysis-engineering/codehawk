(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs LLC

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

(* bchlib *)
open BCHFloc
open BCHLibTypes
open BCHLocation

(* bchlibarm32 *)
open BCHARMLoopStructure
open BCHARMOpcodeRecords
open BCHARMTypes

module TR = CHTraceResult


let get_arm_op_metrics (f:arm_assembly_function_int) (finfo:function_info_int) =
  let faddr = f#get_address in
  let reads = ref 0 in
  let qreads = ref 0 in
  let writes = ref 0 in
  let qwrites = ref 0 in
  let is_memory_op op =
    match op#get_kind with
    | ARMMemMultiple _
      | ARMOffsetAddress _ -> true
    | _ -> false in
  let is_loc_unknown floc (op: arm_operand_int) =
    match op#get_kind with
    | ARMMemMultiple _ ->
       TR.tfold_default
         (fun (vlist, _) ->
          match vlist with
          | v::_ -> v#isTmp || (finfo#env#is_unknown_memory_variable v)
          | _ -> true)
         true
         (op#to_multiple_lhs floc)
    | ARMOffsetAddress _ ->
       TR.tfold_default
         (fun (v, _) -> v#isTmp || (finfo#env#is_unknown_memory_variable v))
         true
         (op#to_lhs floc)
    | _ -> false in
  let add_read floc (op: arm_operand_int) =
    if is_memory_op op then
      begin
        reads := !reads + 1;
        if is_loc_unknown floc op then qreads := !qreads + 1
      end in
  let add_write floc (op: arm_operand_int) =
    if is_memory_op op then
      begin
        writes := !writes + 1;
        if is_loc_unknown floc op then qwrites := !qwrites + 1
      end in
  let _ =
    f#iteri (fun _ ctxtiaddr instr ->
        let ops = get_arm_operands instr#get_opcode in
        match ops with
        | [] -> ()
        | _ ->
           let loc = ctxt_string_to_location faddr ctxtiaddr in
           let floc = get_floc loc in
           List.iter (fun (op: arm_operand_int) ->
               match op#get_mode with
               | RD -> add_read floc op
               | WR -> add_write floc op
               | RW ->
                  begin
                    add_read floc op;
                    add_write floc op
                  end) ops) in
  (!reads,!qreads,!writes,!qwrites)

let get_arm_stackpointer_metrics
      (f: arm_assembly_function_int) (_finfo: function_info_int) =
  let faddr = f#get_address in
  let esptop = ref 0 in
  let esprange = ref 0 in
  let _ =
    f#iteri
      (fun _ ctxtiaddr _ ->
        let loc = ctxt_string_to_location faddr ctxtiaddr in
        let floc = get_floc loc in
        let (_,range) = floc#get_stackpointer_offset "arm" in
        if range#isTop then
          esptop := !esptop + 1
        else match range#singleton with
               Some _ -> () | _ -> esprange := !esprange + 1) in
  (!esptop,!esprange)


let get_arm_memory_access_metrics
      (f: arm_assembly_function_int) (finfo: function_info_int) =
  let (reads,qreads,writes,qwrites) = get_arm_op_metrics f finfo in
  let (esptop,esprange) = get_arm_stackpointer_metrics f finfo in
  { mmem_reads = reads ;
    mmem_qreads = qreads ;
    mmem_writes = writes ;
    mmem_qwrites = qwrites ;
    mmem_esptop = esptop ;
    mmem_esprange = esprange
  }

let get_arm_cfg_metrics
      (f: arm_assembly_function_int) (_env: function_environment_int) =
  let _ = record_arm_loop_levels f#get_address in
  { mcfg_instrs = f#get_instruction_count ;
    mcfg_bblocks = f#get_block_count ;
    mcfg_loops = get_arm_loop_count_from_table f ;
    mcfg_loopdepth = get_arm_loop_depth_from_table f ;
    mcfg_complexity = 0 ;
    mcfg_vc_complexity = 0.0
  }
