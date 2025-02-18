(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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
open CHLanguage
open CHPretty
open CHUtils

(* jchlib *)
open JCHBasicTypes

(* jchpre *)
open JCHIFSystem

(* jchsys *)
open JCHPrintUtils

module H = Hashtbl

module F = CHOnlineCodeSet.LanguageFactory

class jsystem_t =
  object (self: 'a)

    val original_chif = ref (None : system_int option)

    val transformed_chif = ref (None : system_int option)

    (* methods which failed in translation, etc *)
    val not_analyzed_bad = ref (new IntCollections.set_t)

    (* methods that do not need to be analyzed *)
    val not_analyzed_good = ref (new IntCollections.set_t)

    val call_graph_manager = ref (None : JCHCallGraph.call_graph_manager_t option)

    val proc_to_jproc_info = ref (H.create 0)

    val stats = ref []

    val number_procs = ref 0

    method get_original_chif = Option.get !original_chif

    method get_transformed_chif = Option.get !transformed_chif

    method get_procedures = (Option.get !transformed_chif)#getProcedures

    method get_call_graph_manager = Option.get !call_graph_manager

    method get_jproc_info (proc_name: symbol_t) =
      try
	H.find !proc_to_jproc_info proc_name#getSeqNumber
      with
      | Not_found ->
	raise
          (JCH_failure
             (LBLOCK [ STR "jproc " ; proc_name#toPretty ;
		       STR " not found in JCHSystem.get_jproc_info" ]))

    method get_jproc_info_seq_no (proc_name_seq_num) =
      try
	H.find !proc_to_jproc_info proc_name_seq_num
      with
      | Not_found ->
	raise
          (JCH_failure
             (LBLOCK [ STR "jproc " ; INT proc_name_seq_num ;
		       STR " not found in JCHSystem.get_jproc_info_seq_no" ]))

    method not_analyzed_bad cmsix = !not_analyzed_bad#has cmsix

    method get_not_analyzed_bad = !not_analyzed_bad

    method get_not_analyzed_good = !not_analyzed_good

    method not_analyzed cmsix =
      !not_analyzed_bad#has cmsix || !not_analyzed_good#has cmsix

    method get_number_procs = !number_procs

    method private transform_proc system proc_name proc =
      (* adds an entry state. It has to be before other transformations *)
      let _ = JCHCodeTransformers.add_method_entry proc in
      let cfg = JCHSystemUtils.get_CFG proc in
      let dominance_info = JCHDominance.find_dominance_frontier proc_name cfg in
      let (ssa_proc, aliases, rvar_to_pc_to_versions) =
	JCHSSA.make_ssa proc cfg dominance_info in
      let (aliases, orig_phi_to_vars, rep_proc) =
        JCHVarRepresentative.reduce_to_rep ~system ~proc:ssa_proc ~aliases in
      (dominance_info,
       rep_proc, aliases,
       rvar_to_pc_to_versions,
       orig_phi_to_vars)

    method set system =
      original_chif := Some system ;
      let tr_system =
	let copy_system = JCHSystemUtils.copy_system system in
	let new_system = F.mkSystem copy_system#getName in
	let procedures = copy_system#getProcedures in
	proc_to_jproc_info := H.create (List.length procedures) ;
	let transform_proc proc_name =
	  let proc = copy_system#getProcedure proc_name in
	  let (dom_info,
               tr_proc,
               aliases,
               rvar_to_pc_to_versions,
               orig_phi_to_vars) =
	    self#transform_proc copy_system proc_name proc in
	  let (wto_infos, proc_wto, depth) =
            JCHLoopUtils.get_sccs_proc tr_proc proc_name in
	  let extra_assert_vars =
            JCHAnalysisSetUp.add_operations tr_proc wto_infos in
	  new_system#addProcedure tr_proc ;
	  JCHTypeSetsDomainNoArrays.add_types_to_stack_layout
            system proc_name ;
	  let jproc_info =
	    JCHProcInfo.make_jproc_info
              ~proc_name
              ~proc:tr_proc
              ~wto:proc_wto
              ~wto_infos
              ~loop_depth:depth
              ~dom_info
	      ~aliases
              ~rvar_to_pc_to_versions
              ~orig_phi_to_vars
              ~extra_assert_vars
              ~jproc_info_opt:None in
          (* This has to be done at the end as it also simplifies the code *)
	  JCHAnalysisSetUp.add_array_length_operations
            tr_proc jproc_info#get_jvar_infos ;
	  let jproc_info =
	    JCHProcInfo.make_jproc_info
              ~proc_name
              ~proc:tr_proc
              ~wto:proc_wto
              ~wto_infos
              ~loop_depth:depth
              ~dom_info
	      ~aliases
              ~rvar_to_pc_to_versions
              ~orig_phi_to_vars
              ~extra_assert_vars
              ~jproc_info_opt:(Some jproc_info) in
	  H.add !proc_to_jproc_info proc_name#getSeqNumber jproc_info in
	List.iter transform_proc procedures ;
	new_system in

      transformed_chif := Some tr_system ;
      JCHSystemUtils.add_timing
        "transforming CHIF, collecting variable and method info, type analysis" ;

      let add_failed_in_translation cms =
	let proc_name = make_procname cms#index in
	!not_analyzed_bad#add proc_name#getSeqNumber in

      List.iter
        add_failed_in_translation chif_system#get_method_translation_failures ;

      let all_procs = tr_system#getProcedures in
      number_procs := List.length all_procs ;

      let chif_syst_call_graph = JCHCallgraphBase.get_app_callgraph () in
      let new_call_graph_manager =
	pr__debug [STR "methods not analyzed because of failure in translation: ";
                   !not_analyzed_bad#toPretty; NL] ;
	pr__debug [STR "new methods found safe: "; !not_analyzed_good#toPretty; NL] ;
	let not_analyzed = (IntCollections.set_of_list !not_analyzed_bad#toList) in
	not_analyzed#addSet !not_analyzed_good ;
	new JCHCallGraph.call_graph_manager_t all_procs not_analyzed chif_syst_call_graph in
      call_graph_manager := Some new_call_graph_manager ;
      pr__debug [STR "Finished finding the call graph"; NL];

      JCHSystemUtils.add_timing "making the call graph"

    method add_stats title (info: pretty_t) =
      stats := (title, info) :: (List.remove_assoc title !stats)

    method get_stats title =
      try
	Some (List.assoc title !stats)
      with _ -> None

    method stats_to_pretty =
      let out (title, info) =
	LBLOCK [STR (title ^ ": ") ; info; NL] in
      LBLOCK [STR "System statistics "; NL; INDENT (5, LBLOCK (List.map out !stats))]

    method toPretty =
      LBLOCK [STR "system "; NL]

  end

let jsystem = new jsystem_t
