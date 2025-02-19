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
open CHCommon
open CHPretty
open CHNumerical
open CHLanguage
open CHNonRelationalDomainValues

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchsys *)
open JCHPrintUtils

(* jchcost *)
open JCHCostBounds
open JCHCostUtils

let dbg = ref false

let string_dom_name = "cost_bounds"

let st_cost_bounds_opt = ref None
let set_st_cost_bounds cost_bounds = st_cost_bounds_opt := Some cost_bounds
let get_st_cost_bounds () = Option.get !st_cost_bounds_opt

let current_proc_is_loop = ref false

class cost_bounds_domain_no_arrays_t
    ~(cmsix: int)
    ~(get_loop_cost: int -> cost_bounds_t)
    ~(get_loop_cost_user: int -> cost_bounds_t option)
    ~(get_block_cost: int -> cost_bounds_t)
    ~(record_final_cost: cost_bounds_t -> unit) =
object (self: 'a)

  inherit CHNonRelationalDomainNoArrays.non_relational_domain_t

  method private getValue' v : cost_bounds_t =
    match (self#getValue v)#getValue with
      | EXTERNAL_VALUE b -> b
      | TOP_VAL -> top_cost_bounds
      | BOTTOM_VAL -> bottom_cost_bounds
      | _ -> raise (CHFailure (STR "Cost bounds expected"))

  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (EXTERNAL_VALUE x))

  method private importValue v =
      match v#getValue with
      |	EXTERNAL_VALUE _ -> v
      |	TOP_VAL -> topNonRelationalDomainValue
      |	BOTTOM_VAL -> bottomNonRelationalDomainValue
      |	_ ->
         raise
           (JCH_failure
              (STR "JCHCostBoundsDomainNoArrays.importValue expected external_value_int"))

  method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
    if !dbg then
      pr__debug [STR "CostBounds.analyzeFwd "; command_to_pretty 0 cmd; NL;
		 STR "table: "; self#toPretty; NL] ;
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
	if !dbg then
          pr__debug [STR "  after analyzeFwd, table': "; NL; table'#toPretty; NL] ;
	{< table = table' >}
      in
	match cmd with
	| OPERATION {op_name; op_args} ->
	   if !dbg then
             pr__debug [STR "op_name = "; STR op_name#getBaseName; NL] ;
	   begin
	     match op_name#getBaseName with
	     | "set_to_0" ->
		let dst = JCHSystemUtils.get_arg_var "dst" op_args in
		self#setValue' table' dst (cost_bounds_from_num numerical_zero);
		default ()
	     | "set_to_inf" ->
		let dst = JCHSystemUtils.get_arg_var "dst" op_args in
		self#setValue' table' dst inf_lb_cost_bounds;
		default ()
	     | "subst_at_exit" ->
		let dst = JCHSystemUtils.get_arg_var "dst" op_args in
		if !current_proc_is_loop then
		  begin
		    let cost_bounds = self#getValue' dst in
		    let new_cost_bounds = subst_pos_bounds (-1) cost_bounds true in
		    self#setValue' table' dst new_cost_bounds ;
		  end
		else
		  begin
		    let cost_bounds = make_small_divs (self#getValue' dst) in
		    let new_cost_bounds =
		      if is_const_range cost_bounds then
			subst_pos_bounds (-1) cost_bounds false
		      else
			begin
			  let no_lps_cost_bounds =
                            subst_pos_bounds (-1) cost_bounds true in
			  if !dbg then
                            pr__debug [STR "no_lps_cost_bounds = ";
                                       no_lps_cost_bounds#toPretty; NL] ;
			  make_small_divs
                            (subst_pos_bounds (-1) no_lps_cost_bounds false)
			end in
		    let cost_bounds_final =
                      subst_pos_bounds_final (-1) new_cost_bounds in
		    record_final_cost cost_bounds_final ;
		    self#setValue' table' dst new_cost_bounds
		  end ;
		JCHCostUtils.check_cost_analysis_time
                  (" while analyzing " ^ (string_of_int cmsix)) ;
		default()
	     | "add_block_cost" ->
		begin
		  let dst = JCHSystemUtils.get_arg_var "dst_src" op_args in
		  let block = JCHSystemUtils.get_arg_var "src" op_args in
		  let dst_b = self#getValue' dst in
		  let block_b = self#getValue' block in
		  if not block_b#isBottom then
		    self#setValue' table' dst (add_cost_bounds dst_b block_b);
		  default ()
		end
	     | "add_loop_cost" ->
		let hpc = int_of_string (List.hd op_name#getAttributes) in
		let v = JCHSystemUtils.get_arg_var "dst" op_args in
		let v_b = self#getValue' v in

		let cost_one_iteration =
		  let cost = get_loop_cost hpc in
		  if is_const_range cost then cost
		  else
		    begin
		      let cost_no_lps = subst_pos_bounds hpc cost true in
		      if !dbg then
                        pr__debug [STR "cost_no_lps = "; cost_no_lps#toPretty; NL];
		      let lp_jterm =
                        make_sym_lp cmsix hpc (find_const_lb true cost_no_lps) in
		      add_pos_jterm hpc lp_jterm cost_no_lps;
		      bounds_from_jterms false [lp_jterm] [lp_jterm]
		    end in
		if !dbg then
                  pr__debug [STR "cost_one_iteration = "; NL;
                             cost_one_iteration#toPretty; NL] ;

		let nb_iterations = self#get_loop_iterations hpc in
		pr__debug [STR "loop@"; INT hpc; STR " nb iterations: "; NL;
                           nb_iterations#toPretty; NL] ;

		let cost = mult_cost_bounds nb_iterations cost_one_iteration in
		if !dbg then pr__debug [STR "after mult_cost_bounds "; NL];

		let v_b' = add_cost_bounds v_b cost in
		self#setValue' table' v v_b';
		default ()
	     | "block_cost" ->
		let pc = int_of_string (List.hd op_name#getAttributes) in
		let v = JCHSystemUtils.get_arg_var "dst" op_args in
		let cost = get_block_cost pc in
		self#setValue' table' v cost ;
		default ()
	     | _ ->
		default ()
	   end
	| _ ->
	   pr_debug [STR "unknown operation ";
                     INT (JCHCostBounds.get_instr_pc ()); STR " ";
                     command_to_pretty 0 cmd; NL];
	   default ()

  method private get_loop_iterations hpc =
    let (iteration_lbs, iteration_ubs) =
      match get_loop_cost_user hpc with
      | Some bound ->
	  if !dbg then pr__debug [STR "user provided iteration"; NL] ;
	  let (it_lbs, it_ubs, _, _) = get_bounds bound in
	  (List.map (fun b -> b#to_jterm) it_lbs#toList,
           List.map (fun b -> b#to_jterm) it_ubs#toList)
      | _ ->
	  JCHNumericAnalysis.get_iteration_bounds cmsix hpc in
    if !dbg then
      pr__debug [STR "get_loop_iterations iteration_lbs: ";
                 pp_list_jterm iteration_lbs; NL;
		 STR "iteration_ubs: ";
                 pp_list_jterm iteration_ubs; NL];
    let (const_iteration_lbs, non_const_iteration_lbs) =
      List.partition is_const iteration_lbs in
    let (const_iteration_ubs, non_const_iteration_ubs) =
      List.partition is_const iteration_ubs in
    let (_large_const_iteration_ubs, small_const_iteration_ubs) =
      match get_loop_cost_user hpc with
      | Some _ -> ([], const_iteration_ubs)
      | _ ->
         List.partition is_large_const const_iteration_ubs in

    let const_lbound = ref (Some numerical_zero) in
    let const_ubound = ref None in
    let check_const is_lb const_bound jt =
      match (!const_bound, jt) with
      | (None, JConstant m) -> const_bound := Some m
      | (Some n, JConstant m) ->
	  if is_lb && m#gt n || not is_lb && m#lt n then const_bound := Some m
      | _ -> () in
    List.iter (check_const true const_lbound) const_iteration_lbs ;
    List.iter (check_const false const_ubound) const_iteration_ubs ;

    let iteration_lbs = const_iteration_lbs @ non_const_iteration_lbs in
    let iteration_ubs = small_const_iteration_ubs @ non_const_iteration_ubs in

    if !dbg then
      pr__debug [STR "iteration_bounds "; INT hpc; STR ": [ ";
		 pp_list_jterm iteration_lbs ; STR "; ";
                 pp_list_jterm iteration_ubs; STR "]"; NL] ;

    let sym_lc = make_sym_lc cmsix hpc (Option.get !const_lbound) !const_ubound in
    let sym_lbs_opt = ref None in
    let sym_ubs_opt = ref None in

    let lbounds =
      if non_const_iteration_lbs = [] then
	[JConstant (Option.get !const_lbound)]
      else
	begin
	  sym_lbs_opt := Some iteration_lbs ;
	  [sym_lc]
	end in

    let ubounds =
      if small_const_iteration_ubs != [] && non_const_iteration_ubs = [] then
	[JConstant (Option.get !const_ubound)]
      else
	begin
	  sym_ubs_opt := Some iteration_ubs ;
	  [sym_lc]
	end in

    if !dbg then
      pr__debug [STR "lbounds = "; pp_list_jterm lbounds; NL;
                 STR "ubounds = "; pp_list_jterm ubounds; NL];

    (match (!sym_lbs_opt, !sym_ubs_opt) with
    | (Some sym_lbs, Some sym_ubs) ->
	let bounds = bounds_from_jterms false sym_lbs sym_ubs in
	add_pos_jterm hpc sym_lc bounds
    | (Some sym_lbs, None) ->
	let bounds = bounds_from_jterms false sym_lbs [] in
	add_pos_jterm hpc sym_lc bounds
    | (None, Some sym_ubs) ->
	let bounds = bounds_from_jterms false [] sym_ubs in
	add_pos_jterm hpc sym_lc bounds
    | _ -> () ) ;

    bounds_from_jterms false lbounds ubounds


  method private analyzeBwd' (_cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      {< table = table' >}

  method special (cmd: string) (_args: domain_cmd_arg_t list) : 'a =
    match cmd with
    | "set_cost_bounds" ->
	let cvar = get_cost_var () in
	set_st_cost_bounds (self#getValue' cvar) ;
	{< >}
    | _ -> {< >}

end

let get_cost_bounds (cost_bounds_dom: CHDomain.domain_int) =
  let _ = cost_bounds_dom#special "set_cost_bounds" [] in
  get_st_cost_bounds ()
