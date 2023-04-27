(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma and Andrew McGraw
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

(* bchlib *)
open BCHFloc
open BCHLibTypes
open BCHLocation
open BCHMetricsHandler

(* bchlibpower32 *)
open BCHPowerOpcodeRecords
open BCHPowerTypes


let get_pwr_op_metrics
      (f: pwr_assembly_function_int) (finfo: function_info_int) =
  (0, 0, 0, 0)


let get_pwr_stackpointer_metrics
      (f: pwr_assembly_function_int) (finfo: function_info_int) =
  let faddr = f#faddr in
  let sptop = ref 0 in
  let sprange = ref 0 in
  let _ =
    f#iteri
      (fun _ ctxtiaddr _ ->
       let loc = ctxt_string_to_location faddr ctxtiaddr in
       let floc = get_floc loc in
       let (_, range) = floc#get_stackpointer_offset "pwr" in
       if range#isTop then
         sptop := !sptop + 1
       else
         match range#singleton with
         | Some _ -> () | _ -> sprange := !sprange + 1) in
  (!sptop, !sprange)


let get_pwr_memory_access_metrics
      (f: pwr_assembly_function_int) (finfo: function_info_int) =
  let (reads, qreads, writes, qwrites) = get_pwr_op_metrics f finfo in
  let (esptop, esprange) = get_pwr_stackpointer_metrics f finfo in
  { mmem_reads = reads;
    mmem_qreads = qreads;
    mmem_writes = writes;
    mmem_qwrites = qwrites;
    mmem_esptop = esptop;
    mmem_esprange = esprange
  }

let get_pwr_cfg_metrics
      (f: pwr_assembly_function_int) (env: function_environment_int) =
  (* let _ = record_arm_loop_levels f#get_address in *)
  { mcfg_instrs = f#get_instruction_count;
    mcfg_bblocks = f#get_block_count;
    mcfg_loops = 0; (* get_arm_loop_count_from_table f; *)
    mcfg_loopdepth = 0; (* get_arm_loop_depth_from_table f; *)
    mcfg_complexity = 0;
    mcfg_vc_complexity = 0.0
  }

