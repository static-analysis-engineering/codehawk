(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny Sipma

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
open CHNumerical
open CHPretty
open CHNonRelationalDomainValues

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm

(* jchpre *)
open JCHCostBoundsModel
open JCHPreAPI
open JCHUserData
open JCHXmlUtil

(* jchsys *)
open JCHPrintUtils
  
(* jchcost *)
open JCHCostBounds

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory

let dbg = ref false

let invariants = H.create 3

let sinkinvariants = H.create 3    (*  (int,int) atlas_t H.t *)

let issinkvar (name:string) =
  (String.length name) > 4 &&
    (String.sub name 0 4) = "sink"

let get_sink_edge (s:symbol_t) =
  match s#getAttributes with
  | [ decpc ; predpc ; "exit" ] ->
     (int_of_string decpc, int_of_string predpc, (-1))
  | [ decpc ; predpc ; obspc ] ->
     (int_of_string decpc, int_of_string predpc, int_of_string obspc)
  | _ -> raise (JCH_failure (LBLOCK [ STR "Invalid sink name: " ; s#toPretty ] ))

let get_bounds (v:non_relational_domain_value_t) : cost_bounds_t = 
  match v#getValue with
  | EXTERNAL_VALUE b -> b
  | TOP_VAL -> top_cost_bounds
  | BOTTOM_VAL -> bottom_cost_bounds
  | _ -> raise (JCH_failure (STR "Cost bounds expected"))

let getloopexitvalue (v:variable_t) (pc:int):cost_bounds_t =
  if H.mem invariants ("loopexit", pc) then
    let (domain: CHDomain.domain_int) =
      (H.find invariants ("loopexit",pc))#getDomain "cost_bounds" in
    if domain#isBottom then
      bottom_cost_bounds
    else
      let varObserver = domain#observer#getNonRelationalVariableObserver in
      get_bounds (varObserver v)
  else
    cost_bounds_from_num numerical_zero

let adjustbounds cmsix costmodel bv lh =
  if costmodel#has_loopbound cmsix lh then
    let it = costmodel#get_loopbound cmsix lh in
    match it#to_constant with
    | Some it ->
       let it = it#toInt in
      if it = 1 then
	cost_bounds_from_num numerical_zero
      else
	let d = cost_bounds_from_num (mkNumerical it) in
	let m = cost_bounds_from_num (mkNumerical (it - 1)) in
	mult_cost_bounds (div_cost_bounds bv d) m
    | _ -> bv
  else
    bv

let getloopsinkvalues cmsix v costmodel loopstructure (pc:int):cost_bounds_t =
  let loopheads = loopstructure#get_pc_loopheads pc in
  let add acc lh = 
    let loopexitvalue = getloopexitvalue v lh in
    let xvalue = adjustbounds cmsix costmodel loopexitvalue lh in
    add_cost_bounds acc xvalue in
  List.fold_left add (cost_bounds_from_num numerical_zero) loopheads

let get_sinks cmsix costmodel loopstructure =
  H.iter (fun (decpc,predpc,obspc) inv ->
    let domain = inv#getDomain "cost_bounds" in
    if domain#isBottom then
      pr__debug [ INT decpc ; STR " - " ; INT obspc ; STR ": bottom" ; NL ]
    else
      let vars = domain#observer#getObservedVariables in
      let varObserver = domain#observer#getNonRelationalVariableObserver in
      let svars = List.filter (fun v -> issinkvar v#getName#getBaseName) vars in
      List.iter (fun v ->
	let loopxinv = getloopsinkvalues cmsix v costmodel loopstructure obspc in 
	let tgtinv = get_bounds (varObserver v) in
	let inv = add_cost_bounds tgtinv loopxinv in
        begin
          costmodel#set_sidechannelcost cmsix decpc predpc obspc inv ;
	  pr__debug [ STR "Sink " ; v#toPretty ; STR ": " ;
		     INT decpc ; STR " - " ; INT obspc ; STR ": " ;
		     inv#toPretty ; NL ]
        end) svars) sinkinvariants


let get_methodexit_bounds () =
  let domain = (H.find invariants ("methodexit",(-1)))#getDomain "cost_bounds" in
  let vars = domain#observer#getObservedVariables in
  let varObserver = domain#observer#getNonRelationalVariableObserver in
  let cvars = List.filter (fun v -> v#getName#getBaseName = "costvar") vars in
  match cvars with
  | [ cvar ] ->
      let cost = get_bounds (varObserver cvar) in
      if !dbg then
        pr__debug [
            STR "get_methodexit_bounds cost before simplifying ";
            NL;
            cost#toPretty;
            NL];
      let (lbs, ubs, inf_lb, inf_ub) = JCHCostBounds.get_bounds cost in
      new cost_bounds_t
        ~bottom:cost#isBottom
        ~simplify:true
        ~inflb:inf_lb
        ~infub:inf_ub
        ~lbounds:lbs#toList
        ~ubounds:ubs#toList
  | _ ->
     top_cost_bounds


let default_opsemantics
      domain
      cmsix
      hpc_opt:CHIterator.op_semantics_t =
  fun ~invariant ~stable ~fwd_direction ~context ~operation ->
    match operation.op_name#getBaseName with
    | "invariant" ->
	if stable then 
	  begin
	    match operation.op_name#getAttributes with
	    | [ "methodexit" ] ->
	       if !dbg then
                 pr__debug [STR "op methodexit"; NL; invariant#toPretty; NL] ;
	       if invariant#isBottom then
                 (* the method does not ever reach the exit *)
		 begin
		    let cvar = JCHCostUtils.get_cost_var () in
		    let set_to_inf_op =
		      {op_name = new symbol_t ~atts:["0"] "set_to_inf" ;
			op_args = [("dst", cvar, WRITE)] } in

		    let invariant =
                      invariant#mkEmpty#analyzeFwd (OPERATION set_to_inf_op) in
		    H.add invariants ("methodexit",(-1)) invariant ;
		    chlog#add
                      "methods that do not reach exit"
		      (LBLOCK [STR "m_"; INT cmsix; STR ": ";
                               (retrieve_cms cmsix)#toPretty]);
		  end
		else
		  (* substitute out sym_lp and sym_call, and simplify the cost *)
		  let cvar = JCHCostUtils.get_cost_var () in
		    let subst_op =
		      {op_name = new symbol_t ~atts:[] "subst_at_exit" ;
			op_args = [("dst", cvar, WRITE)] } in
		  let invariant = invariant#clone#analyzeFwd (OPERATION subst_op) in
		  H.add invariants ("methodexit",(-1)) invariant
	    | [ "loopexit" ; pc ] ->
		if !dbg then pr__debug [STR "op loopexit"; NL] ;
		H.add invariants ("loopexit", int_of_string pc) invariant 
	    | _ -> ()
	  end ;
	invariant
    | "sink" ->
	if stable then
	  begin
	    let sinkid = get_sink_edge operation.op_name in
	    H.add sinkinvariants sinkid invariant
	  end ;
	invariant
    | "add_loop_cost" ->
	let is_other_loop =
	  match hpc_opt with
	  | Some hpc ->
             not ((int_of_string (List.hd operation.op_name#getAttributes)) = hpc)
	  | _ -> true in
	if is_other_loop then
	  if fwd_direction then invariant#analyzeFwd (OPERATION operation)
	  else invariant
	else invariant
    | "block_cost" ->
	let pc = int_of_string (List.hd operation.op_name#getAttributes) in
	JCHCostBounds.set_instr_pc pc ;
	invariant#analyzeFwd (OPERATION operation)
    | "set_to_0"
    | "add_block_cost" -> invariant#analyzeFwd (OPERATION operation)
    | _ -> pr_debug [STR "unknown operation"; NL]; invariant

let analyze_procedure_with_cost_bounds
      cmsix
      (hpc_opt: int option)
      (get_loop_cost: int -> cost_bounds_t)
      (get_block_cost: int -> cost_bounds_t)
      (record_final_cost: cost_bounds_t -> unit)
      (userdata: userdata_int)
      (proc: procedure_int) (system:system_int) =
  if !dbg then
    pr__debug [STR "analyze_procedure_with_cost_bounds "; INT cmsix; STR " ";
               proc#toPretty; NL] ;
  JCHCostBoundsDomainNoArrays.current_proc_is_loop := Option.is_some hpc_opt ;
  let analysis_setup = CHAnalysisSetup.mk_analysis_setup () in
  let get_loop_cost_user pc =
    if userdata#has_loopbound cmsix pc then
      begin
	let jtermrange = userdata#get_loopbound cmsix pc in
	Some (JCHCostBounds.cost_bounds_from_jterm_range jtermrange)
      end
    else None in
  begin
    analysis_setup#addDomain
      "cost_bounds"
      (new JCHCostBoundsDomainNoArrays.cost_bounds_domain_no_arrays_t
	   ~cmsix
           ~get_loop_cost
           ~get_loop_cost_user
           ~get_block_cost
           ~record_final_cost) ;
    analysis_setup#setOpSemantics (default_opsemantics "cost_bounds" cmsix hpc_opt) ;
    analysis_setup#analyze_procedure ~do_loop_counters:false system proc 
  end

let analyze_bounds_cost (costmodel:costmodel_t) (mInfo:method_info_int) =
  if mInfo#has_bytecode then
    begin
      let _ = JCHCostUtils.start_cost_analysis () in
      let _ = H.clear sinkinvariants in
      let cms = mInfo#get_class_method_signature in
      let cmsix = cms#index in
      JCHCostBoundsDomainNoArrays.dbg := !dbg;  
      JCHCostBoundsModel.dbg := !dbg ; 
      pr__debug [NL; NL; NL; NL; STR "analyze_cost_bounds ";
                 INT cmsix; STR " "; mInfo#get_class_method_signature#toPretty; NL] ;
      if !dbg then
        pr__debug [STR "bytecode: "; NL; mInfo#get_bytecode#toPretty; NL];
      JCHCostBounds.set_cmsix cmsix;
      let basicblocks = JCHCostModelUtil.get_basic_blocks mInfo#get_bytecode in
      let costabstractor =
        new JCHMethodCostBoundsAbstractor.method_cost_abstractor_t
            ~cmsix ~basicblocks ~costmodel in
      let (proc_opt, loop_procs, str) =
	try
	  let (p, lps) = costabstractor#to_chifproc in
	  let res = (Some p, List.map (fun lp -> Some lp) lps, "") in
	  res
	with JCHCostUtils.JCH_cost_out_of_time str -> (None, [], str) in 
      let analyze_proc hpc_opt p_opt =
	let cost = 
	  match p_opt with
	  | Some p ->
	      begin
		let csystem = LF.mkSystem (new symbol_t "costmodel") in
		csystem#addProcedure p ;
		try
		  analyze_procedure_with_cost_bounds
                    cmsix
                    hpc_opt
                    (costmodel#get_loop_cost cmsix)
		    (costmodel#get_block_cost cmsix)
                    (costmodel#add_to_coststore_final cmsix)
                    userdata
                    p
                    csystem ;
		  get_methodexit_bounds ()
		with JCHCostUtils.JCH_cost_out_of_time str ->
		  begin
		    chlog#add
                      "methods that could not be analyzed "
		      (LBLOCK [STR "m_"; INT cmsix; STR ": ";
                               (JCHDictionary.retrieve_cms cmsix)#toPretty]);
		    pr_debug [STR str; NL];
		    let jterm = 
		      match hpc_opt with
		      | Some hpc -> 
			 JSymbolicConstant
                           ((TBasic Int),
                            (Some (mkNumerical 100)),
                            None,
                            "default_method_cost_loop_"
                            ^(string_of_int cmsix)^"_"^(string_of_int hpc))
		      | _ ->
			 JSymbolicConstant
                           ((TBasic Int),
                            (Some (mkNumerical 100)),
                            None,
                            "default_method_cost_"^(string_of_int cmsix)) in
		    bounds_from_jterms false [jterm] [jterm]
		  end
	      end
	  | None ->
	      begin
		chlog#add
                  "methods that could not be analyzed "
		  (LBLOCK [STR "m_"; INT cmsix; STR ": ";
                           (retrieve_cms cmsix)#toPretty]);
		pr_debug [STR str; NL];
		let jterm =
                  JSymbolicConstant
                    ((TBasic Int),
                     (Some (mkNumerical 100)),
                     None, "default_method_cost_"^(string_of_int cmsix)) in
		bounds_from_jterms false [jterm] [jterm]
	      end in
	match hpc_opt with
	| Some hpc ->
	    pr__debug [ NL; STR "loop@"; INT hpc; STR " cost: "; NL; 
			cost#toPretty] ; 
	    costmodel#set_loop_cost cmsix hpc cost
	| _ ->
	    pr__debug [ NL; STR "method cost for "; 
			mInfo#get_class_method_signature#toPretty ; 
			STR " (" ; INT cmsix ; STR ") is " ; NL ;
			cost#toPretty] ; 
	    costmodel#set_methodcost cmsix cost in
      List.iter (fun pair_opt ->
	match pair_opt with
	| Some (hpc, loop_proc) -> analyze_proc (Some hpc) (Some loop_proc)
	| None -> analyze_proc None proc_opt) loop_procs ;
      analyze_proc None proc_opt
    end

let create_bounds_cost_model use_symbolic_defaults =
  JCHCostBoundsModel.set_symbolic_defaults use_symbolic_defaults;
  let scchecks = ref [] in
  let _ = List.iter (fun (cmsix,checks) ->
              List.iter (fun (decpc,obspc) ->
                  let check = new sidechannelcheck_t cmsix decpc obspc in
                  scchecks :=
                    check :: !scchecks) checks) userdata#get_sidechannelchecks in
  let costmodel = new costmodel_t !scchecks in
  begin
    JCHCallgraphBase.callgraph_base#bottomup_iter
      (fun m -> if m#has_bytecode then analyze_bounds_cost costmodel m);
    JCHCostUtils.record_not_pos_jterms ();
    costmodel#print_cost_stores () ;
    List.iter costmodel#save_xml_class JCHApplication.app#get_classes ;
    List.iter costmodel#save_xml_atlas_class JCHApplication.app#get_classes
  end

