(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs

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
open CHXmlDocument

(* bchlib *)
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHLocation
open BCHLibTypes
open BCHMetricsHandler
open BCHPreFileIO
open BCHSystemInfo

module H = Hashtbl
module P = Pervasives

module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)

let get_userdata_metrics () =
  { um_function_entry = functions_data#get_user_provided_count ;
    um_data_block = system_info#get_user_data_block_count ;
    um_struct = system_info#get_user_struct_count ;
    um_nonreturning = system_info#get_user_nonreturning_count ;
    um_class = system_info#get_user_class_count
  }

let get_vars_metrics (env:function_environment_int) = {
    mvars_count = env#get_var_count ;
    mvars_global = env#get_globalvar_count ;
    mvars_args = env#get_argvar_count ;
    mvars_return = env#get_returnvar_count ;
    mvars_sideeff = env#get_sideeffvar_count
}

let get_calls_metrics (finfo:function_info_int) = {
    mcalls_count = finfo#get_call_count ;
    mcalls_dll = finfo#get_call_category_count "dll" ;
    mcalls_app = finfo#get_call_category_count "app"  ;
    mcalls_jni = finfo#get_call_category_count "jni" ;
    mcalls_arg = finfo#get_call_category_count "arg" ;
    mcalls_arg_x = finfo#get_call_category_count "arg-no-targets" ;
    mcalls_global = finfo#get_call_category_count "global"  ;
    mcalls_global_x = finfo#get_call_category_count "global-no-targets" ;
    mcalls_unr = finfo#get_call_category_count "unresolved" ;
    mcalls_nosum = finfo#get_call_category_count "dll-no-sum" ;
    mcalls_inlined = finfo#get_call_category_count "inlined" ;
    mcalls_staticdll = finfo#get_call_category_count "static-dll" ;
    mcalls_staticlib = finfo#get_call_category_count "static-lib";
    mcalls_appwrapped = finfo#get_call_category_count "app-wrapped" ;
    mcalls_dllwrapped = finfo#get_call_category_count "dll_wrapped"
  }
                                                
let get_jumps_metrics (finfo:function_info_int) = 
  let faddr = finfo#get_address in
  let jts = finfo#get_jumptable_jumps in
  let norange =
    List.fold_left
      (fun acc ctxtiaddr ->
        let loc = ctxt_string_to_location faddr ctxtiaddr in
        let floc = get_floc loc in
        match floc#get_jump_successors with
        | [] -> acc + 1 | _ -> acc) 0 jts in
  { mjumps_indirect = finfo#get_indirect_jumps_count ;
    mjumps_jumptable = finfo#get_jumptable_count ;
    mjumps_jumptable_norange = norange ;
    mjumps_offsettable = finfo#get_offsettable_count ;
    mjumps_global = finfo#get_global_jump_count ;
    mjumps_argument = finfo#get_argument_jump_count ;
    mjumps_unknown = finfo#get_unknown_jumps_count ;
    mjumps_dll = finfo#get_dll_jumps_count ;
  }
  
let get_cc_metrics (finfo:function_info_int) = {
    mcc_instrs = finfo#get_num_conditions_associated;
    mcc_assoc = finfo#get_num_conditions_associated;
    mcc_test = finfo#get_num_test_expressions
  }
                                             
let get_invs_metrics (invio:invariant_io_int) = {
    minvs_table = 0 (* invio#get_table_size *) ;
    minvs_count = invio#get_invariant_count
}

let get_tinvs_metrics (tinvio:type_invariant_io_int) = {
    mtinvs_table = tinvio#get_table_size ;
    mtinvs_count = tinvio#get_invariant_count
}


let get_result_metrics
      (finfo:function_info_int)
      (memacc_metrics:memacc_metrics_t)
      (cfg_metrics:cfg_metrics_t) =
  let prec_metrics_handler = mk_prec_metrics_handler memacc_metrics in
  {
    mres_prec = prec_metrics_handler#calc cfg_metrics.mcfg_instrs;
    mres_memacc = memacc_metrics ;
    mres_cfg = cfg_metrics ;
    mres_vars = get_vars_metrics finfo#env ;
    mres_calls = get_calls_metrics finfo ;
    mres_jumps = get_jumps_metrics finfo ;
    mres_cc = get_cc_metrics finfo ;
    mres_invs = get_invs_metrics finfo#finv ;
    mres_tinvs = get_tinvs_metrics finfo#ftinv
  }


let combine_results index skip nonrel reset time 
    (presults:function_results_t) (r:result_metrics_t) =
  let stable =
    (not reset)
    (* && r.mres_calls.mcalls_unr = 0 *)
    && ((presults.fres_results.mres_invs.minvs_count = r.mres_invs.minvs_count)
        && (presults.fres_results.mres_vars.mvars_count = r.mres_vars.mvars_count)) in
  let pinstrs = presults.fres_results.mres_cfg.mcfg_instrs in
  let pvars = presults.fres_results.mres_vars.mvars_count in
  let pinvs = presults.fres_results.mres_invs.minvs_count in
  let get_unresolved (d:jumps_metrics_t) =
    d.mjumps_jumptable_norange + d.mjumps_global + d.mjumps_argument + d.mjumps_unknown in
  let fnRun = {
    frun_index = index ;
    frun_time = time ;
    frun_skip = skip ;
    frun_nonrel = nonrel ;
    frun_reset = reset ;
    frun_delta_instrs = r.mres_cfg.mcfg_instrs - pinstrs ;
    frun_unresolved_calls = r.mres_calls.mcalls_unr ;
    frun_unresolved_jumps = get_unresolved r.mres_jumps ;
    frun_delta_vars = r.mres_vars.mvars_count - pvars ;
    frun_delta_invs = r.mres_invs.minvs_count - pinvs
  } in
 { fres_addr = presults.fres_addr ;
   fres_stable = stable ;
   fres_time = presults.fres_time +. time ;
   fres_runs = fnRun :: presults.fres_runs ;
   fres_results = r }

let compute_totals (l:result_metrics_t list) = 
  let m = List.fold_left result_metrics_handler#add result_metrics_handler#init_value l in
  let prec_metrics_handler = mk_prec_metrics_handler m.mres_memacc in
  { m with
    mres_prec = prec_metrics_handler#calc m.mres_cfg.mcfg_instrs }
    

let compute_aggregate_metrics (l:result_metrics_t list) = 
  let len = List.length l in
  let avg l t = 
    (float_of_int (List.fold_left (fun acc v -> acc + v) 0 l)) /. (float_of_int t) in 
  let median l = 
    match l with
    | [] -> 0
    | _ -> List.nth (List.sort P.compare l) (len / 2) in
  let max l = List.fold_left (fun acc v -> P.max acc v) 0 l in
  let maxf l = List.fold_left (fun acc v -> if v > acc then v else acc) 0.0 l in
  {
    agg_avg_function_size = avg (List.map (fun r -> r.mres_cfg.mcfg_instrs) l) len ;
    agg_max_function_size = max (List.map (fun r -> r.mres_cfg.mcfg_instrs) l) ;
    agg_avg_block_count = avg (List.map (fun r -> r.mres_cfg.mcfg_bblocks) l) len ;
    agg_avg_cfgc = avg (List.map (fun r -> r.mres_cfg.mcfg_complexity) l) len ;
    agg_max_cfgc = max (List.map (fun r -> r.mres_cfg.mcfg_complexity) l) ;
    agg_max_vc_complexity = maxf (List.map (fun r -> r.mres_cfg.mcfg_vc_complexity) l) ;
    agg_median_function_size = median (List.map (fun r -> r.mres_cfg.mcfg_instrs) l) ;
    agg_median_block_count = median (List.map (fun r -> r.mres_cfg.mcfg_bblocks) l) ;
    agg_median_cfgc = median (List.map (fun r -> r.mres_cfg.mcfg_complexity) l) ;
    agg_loop_activity = 
      (float_of_int (List.fold_left (fun acc r -> acc + r.mres_cfg.mcfg_complexity) 0 l)) /.
        (float_of_int (List.fold_left (fun acc r -> acc + r.mres_cfg.mcfg_bblocks) 0 l))
  }


class file_metrics_t:file_metrics_int =
object (self)

  val table = H.create 13
  val mutable index = 1
  val mutable runtime = 0.0
  val mutable totaltime = 0.0
  val mutable runs = []
  val mutable skips = 0
  val mutable nonrelational = 0
  val mutable resets = 0
  val mutable fns_analyzed = 0
  val mutable propagation_time = 0.0
  val mutable disassembly_metrics = disassembly_metrics_handler#init_value
  val idafe = new DoublewordCollections.set_t  (* function entry points from IDA *)

  method get_index = index

  method set_disassembly_results (d:disassembly_metrics_t) =
    disassembly_metrics <- d

  method record_results
           ?(skip=false)
           ?(nonrel=false)
           ?(reset=false)
           (faddr:doubleword_int)
           (time:float)
           (memacc_metrics:memacc_metrics_t)
           (cfg_metrics:cfg_metrics_t) =
    let _ = fns_analyzed <- fns_analyzed + 1 in
    let finfo = get_function_info faddr in
    let faddr = faddr#to_hex_string in
    let function_results_handler = mk_function_results_handler faddr in
    let prevResults = 
      if H.mem table faddr then
        H.find table faddr
      else
        function_results_handler#init_value in
    let results = get_result_metrics finfo memacc_metrics cfg_metrics in
    let newResults = combine_results index skip nonrel reset time prevResults results  in
    let _ = if skip then skips <- skips + 1 in
    let _ = if nonrel then nonrelational <- nonrelational + 1 in
    let _ = if reset then resets <- resets + 1 in
    H.replace table faddr newResults

  method record_runtime (f:float) = runtime <- f

  method record_propagation_time (f:float) = propagation_time <- f

  method is_stable (faddr:string) (callees:string list)=
    if H.mem table faddr then
      let fres = H.find table faddr in 
      fres.fres_stable && 
	List.for_all (fun c -> (c = faddr) || 
	    ((self#is_stable c []) && 
	       (let cfinfo = get_function_info (string_to_doubleword c) in
		(not cfinfo#sideeffects_changed) && 
		  (not cfinfo#call_targets_were_set)))) callees
    else
      false

  method private get_delta_instrs =
    let delta = ref 0 in
    let _ = H.iter (fun _ v ->
      List.iter (fun r -> 
	if r.frun_index = index then delta := !delta + r.frun_delta_instrs) v.fres_runs)
      table in
    !delta

  method private get_delta_vars =
    let delta = ref 0 in
    let _ = H.iter (fun _ v ->
      List.iter (fun r ->
	if r.frun_index = index then delta := !delta + r.frun_delta_vars) v.fres_runs)
      table in
    !delta

  method private get_delta_invs =
    let delta = ref 0 in
    let _ = H.iter (fun _ v ->
      List.iter (fun r ->
	if r.frun_index = index then delta := !delta + r.frun_delta_invs) v.fres_runs)
      table in
    !delta

  method get_unresolved_calls =
    let unrcalls = ref 0 in
    let _ = H.iter (fun _ v -> 
      unrcalls := !unrcalls + v.fres_results.mres_calls.mcalls_unr) table in
    !unrcalls

  method get_dll_calls_no_sum =
    let nosumcalls = ref 0 in
    let _ = H.iter (fun _ v ->
      nosumcalls := !nosumcalls + v.fres_results.mres_calls.mcalls_nosum) table in
    !nosumcalls

  method private get_unresolved_jumps =
    let get_unresolved (d:jumps_metrics_t) =
      d.mjumps_jumptable_norange + d.mjumps_global + d.mjumps_argument + d.mjumps_unknown in
    let unrjumps = ref 0 in
    let _ = H.iter (fun _ v ->
      unrjumps := !unrjumps + (get_unresolved v.fres_results.mres_jumps)) table in
    !unrjumps

  method private get_vc_complexity =
    let vc = ref 0.0 in
    let _ = H.iter (fun _ v -> vc := !vc +. v.fres_results.mres_cfg.mcfg_vc_complexity) table in
    !vc

  method private get_function_runtime =
    let frt = ref 0.0 in
    let _ = H.iter (fun _ v -> 
      List.iter (fun r ->
	if r.frun_index = index then frt := !frt +. r.frun_time) v.fres_runs) table in
    !frt

  method private get_ida_function_entry_points =
    begin
      idafe#addList system_info#get_ida_function_entry_points ;
      idafe#toList
    end

  method load_xml =
    match load_resultmetrics_file () with
    | Some node -> self#read_xml node
    | _ -> ()

  method read_xml (node:xml_element_int) =
    let data = file_results_handler#read_xml node in
    begin
      List.iter (fun f -> H.add table f.fres_addr f) data.ffres_functions ;
      runs <- data.ffres_runs ;
      totaltime <- data.ffres_time ;
      index <- (List.length data.ffres_runs) + 1 ;
      idafe#addList data.ffres_idadata.ida_function_entry_points
    end 

  method private get_file_results = 
    let fnResults = ref [] in
    let _ = H.iter (fun _ v -> fnResults := v :: !fnResults) table in
    let fnResults = 
      List.sort (fun r1 r2 -> P.compare r2.fres_addr r1.fres_addr) !fnResults in
    let fileRun = {
      ffrun_index = index ;
      ffrun_time = runtime ;
      ffrun_propagation_time = propagation_time ;
      ffrun_ftime = self#get_function_runtime ;
      ffrun_fns_analyzed = fns_analyzed ; 
      ffrun_vc_complexity = self#get_vc_complexity ;
      ffrun_skips = skips ;
      ffrun_resets = resets ;
      ffrun_nonrel = nonrelational ;
      ffrun_fns = List.length functions_data#get_function_entry_points ;
      ffrun_delta_instrs = self#get_delta_instrs ;
      ffrun_unresolved_calls = self#get_unresolved_calls ;
      ffrun_unresolved_jumps = self#get_unresolved_jumps ;
      ffrun_delta_vars = self#get_delta_vars ;
      ffrun_delta_invs = self#get_delta_invs 
    } in
    let metricsLst = List.map (fun f -> f.fres_results) fnResults in
    { ffres_stable = (fns_analyzed = 0) ;
      ffres_time = totaltime +. runtime  ;
      ffres_runs = fileRun :: runs ;
      ffres_functions = fnResults ;
      ffres_totals = compute_totals metricsLst ;
      ffres_aggregate = compute_aggregate_metrics metricsLst ;
      ffres_disassembly = disassembly_metrics ;
      ffres_userdata = get_userdata_metrics () ;
      ffres_idadata = { ida_function_entry_points = self#get_ida_function_entry_points}
    }

  method write_xml_analysis_stats (node:xml_element_int) =
    let d = self#get_file_results in
    result_metrics_handler#write_xml node d.ffres_totals

  method write_xml (node:xml_element_int) =
    file_results_handler#write_xml node self#get_file_results
      
  method function_to_pretty (faddr:string) =
    if H.mem table faddr then
      let fresults = H.find table faddr in
      let function_results_handler = mk_function_results_handler faddr in
      function_results_handler#toPretty fresults
    else
      LBLOCK [ STR "No results available for " ; STR faddr ]

  method toPretty =
    file_results_handler#toPretty self#get_file_results
		          
end

let file_metrics = new file_metrics_t
            
let save_file_results () =
  let rNode = xmlElement "results" in
  begin
    file_metrics#write_xml rNode ;
    save_resultmetrics rNode
  end

