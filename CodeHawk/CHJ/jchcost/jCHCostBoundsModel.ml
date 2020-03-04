(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma and Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHLogger 
open CHLoopStructure
open CHPrettyUtil 
open CHXmlDocument 

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHJTDictionary
open JCHJTerm

(* jchpre *)
open JCHApplication
open JCHCallgraphBase
open JCHCodegraph
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHPreAPI
open JCHPreFileIO
open JCHStackSlotValue
open JCHSystemSettings
open JCHUserData

open JCHPrintUtils
  
(* jchcost *)
open JCHCostAPI
open JCHOpcodeCosts
open JCHCostUtils
open JCHCostBound
open JCHCostBounds

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory
module P = Pervasives
module Q = Queue

let dbg = ref false
    
let use_symbolic_defaults = ref false
let set_symbolic_defaults b = use_symbolic_defaults := b

let default_function_lbound = cost_bound_from_num true (mkNumerical 100)
let default_function_ubound = cost_bound_from_num false (mkNumerical 100)

let default_funcall_cost name =
  let range = 
    if !use_symbolic_defaults then 
      JSymbolicConstant ((TBasic Int),(Some (mkNumerical 100)), None, name)
    else
      (JConstant (mkNumerical 100)) in
  mk_jterm_jterm_range range 

let default_libcall_cost name =
    let range = 
      if !use_symbolic_defaults then 
	JSymbolicConstant ((TBasic Int), (Some (mkNumerical 100)), None, name)
      else
        (JConstant (mkNumerical 100)) in
    mk_jterm_jterm_range range

let default_size =
  mk_jterm_range [JConstant numerical_zero] [JConstant (mkNumerical 100)]

let precanned_time_costs = H.create 5

let _ =
  List.iter (fun (classname,methodname,cost) ->
      H.add precanned_time_costs (classname,methodname) cost)
            [ ("java.util.Iterator", "hasNext", 20) ;
              ("java.util.Iterator", "next", 20) ]

let has_precanned_time_cost (cms:class_method_signature_int) =
  H.mem precanned_time_costs (cms#class_name#name,cms#name)

let get_precanned_time_cost (cms:class_method_signature_int) =
  if has_precanned_time_cost cms then
    let cost = H.find precanned_time_costs (cms#class_name#name,cms#name) in
    mk_intconstant_jterm_range (mkNumerical cost)
  else
    raise (JCH_failure (LBLOCK [ STR "Method " ; cms#toPretty ;
                                 STR " does not have a precanned cost" ]))
  
      
class timecost_diagnostics_t =
object (self)

  val missingcost = H.create 1
  val topcost = H.create 1
  val expcost = H.create 1

  method record_missing (cms:class_method_signature_int) =
    let index = cms#index in
    let entry =
      if H.mem missingcost index then H.find missingcost index else 0 in
    H.replace missingcost index (entry + 1)

  method record_top
           (caller:class_method_signature_int)
           (pc:int)
           (callee:class_method_signature_int) =
    H.replace topcost (caller#index,pc) callee

  method record_jterm
           (caller:class_method_signature_int)
           (pc:int)
           (callee:class_method_signature_int)
           (cost:jterm_range_int) =
    H.replace expcost (caller#index,pc,callee#index) cost

  method private get_missing =
    let missing =
      H.fold (fun index count acc ->
          (retrieve_cms index,count) :: acc) missingcost [] in
    List.sort (fun (_,c1) (_,c2) -> Pervasives.compare c1 c2) missing

  method private get_top =
    let top = H.fold (fun (caller,pc) callee acc ->
                  (retrieve_cms caller, pc, callee) :: acc) topcost [] in
    List.sort
      (fun (c1,p1,_) (c2,p2,_) -> P.compare (c1#index,p1) (c2#index,p2)) top

  method private get_jterms =
    H.fold (fun (caller,pc,callee) cost acc ->
        (retrieve_cms caller, pc, retrieve_cms callee, cost) :: acc) expcost []

  method private write_xml_cms_counts l =
    List.map (fun (cmsix, count) ->
        let n = xmlElement "n" in
        let cms = retrieve_cms cmsix in
        let set = n#setAttribute in
        let seti = n#setIntAttribute in
        begin
          seti "ix" cmsix ;
          seti "n" count ;
          set "s" cms#class_method_signature_string ;
          n
        end) l
             
  method private write_xml_missing (node:xml_element_int) =
    let l = H.fold (fun k v a -> (k,v) :: a) missingcost [] in
    let l = List.sort P.compare l in
    node#appendChildren (self#write_xml_cms_counts l)

  method private write_xml_covered (node:xml_element_int) =
    let table = H.create 3 in
    let _ =
      H.iter (fun (_,_,callee) _ ->
          let _ = if H.mem table callee then () else H.add table callee 0 in
          H.replace table callee ((H.find table callee) + 1)) expcost in
    let l = H.fold (fun k v a -> (k,v) :: a) table [] in
    let l = List.sort P.compare l in
    node#appendChildren (self#write_xml_cms_counts l)

  method write_xml (node:xml_element_int) =
    let mNode = xmlElement "missing" in
    let cNode = xmlElement "covered" in
    begin
      self#write_xml_covered cNode ;
      self#write_xml_missing mNode ;
      node#appendChildren [ cNode ; mNode ]
    end

  method toPretty =
    let pmissing =
      LBLOCK
        (List.map (fun (cms,count) ->
             LBLOCK [ (fixed_length_pretty ~alignment:StrRight (INT count) 8) ;
                      STR "  " ; cms#toPretty ; NL ]) self#get_missing) in
    let ptop =
      match self#get_top with
      | [] -> STR ""
      | l ->
         LBLOCK
           [ NL ; NL ; STR "Cost evaluates to top for: " ; NL ;
             LBLOCK (List.map (fun (caller,pc,callee) ->
                         LBLOCK [ caller#toPretty ; STR " @pc " ; INT pc ; STR ": " ;
                                  callee#toPretty ; NL ]) l) ] in
    let pjterms =
      LBLOCK
        (List.map (fun (caller,pc,callee,cost) ->
             LBLOCK [ caller#toPretty ; STR " @pc " ; INT pc ; STR ": " ;
                      callee#toPretty ; STR ": " ; cost#toPretty ; NL ])
                  self#get_jterms) in
    LBLOCK [ NL ; NL ; STR "No cost found for " ; NL ; pmissing ; NL ; NL ;
             ptop ; STR "Cost expressions: " ; NL ; pjterms ; NL ]

end

let timecost_diagnostics = new timecost_diagnostics_t

let get_timecost_diagnostics () = timecost_diagnostics#toPretty

let save_timecost_diagnostics () =
  let node = xmlElement "time-cost-diagnostics" in
  begin
    timecost_diagnostics#write_xml node ;
    save_timecost_diagnostics node
  end
  

class sidechannelcheck_t (cmsix:int) (decisionpc:int) (observationpc:int) =

object (self:_)
  val costs = H.create 3  (* (int, cost_bounds_t) H.t : predecessor-pc -> cost *)

  method get_cmsix = cmsix

  method get_decision_pc = decisionpc

  method get_observation_pc = observationpc

  method get_path_pcs =
    let keys = ref [] in
    let _ = H.iter (fun k _ -> keys := k :: !keys) costs in
    !keys

  method get_path_cost (predecessorpc:int) =
    if H.mem costs predecessorpc then
      H.find costs predecessorpc
    else
      raise (JCH_failure
               (LBLOCK [ STR "Predecessor pc " ; INT predecessorpc ;
                         STR " not found in " ; INT cmsix ]))

  method private get_path_costs =
    let lst = ref [] in
    let _ = H.iter (fun k v -> lst := (k,v) :: !lst) costs in
    List.sort (fun (pc1,_) (pc2,_) -> P.compare pc1 pc2) !lst
    

  method set_path_cost (predecessorpc:int) (cost: cost_bounds_t) =
    H.replace costs predecessorpc cost

  method write_xml (node:xml_element_int) =
    let seti = node#setIntAttribute in
    let ppNode = xmlElement "paths" in
    begin
      ppNode#appendChildren
        (List.map (fun (predpc, cost) ->
             let pNode = xmlElement "path" in
             begin
               pNode#setIntAttribute "pred" predpc ;
               self#write_xml_cost pNode cost;
               pNode
             end) self#get_path_costs) ;
      node#appendChildren [ ppNode ] ;
      seti "cmsix" cmsix ;
      seti "decision-pc" decisionpc ;
      seti "observation-pc" observationpc
    end

  method write_xml_cost
           ?(tag="ibcost") (node:xml_element_int) (c:cost_bounds_t) =
    write_xml_bounds ~tag c node

  method toPretty =
    let pairs = ref [] in
    let _ = H.iter (fun k v -> pairs := (k,v):: !pairs) costs in              
    LBLOCK [ STR "decision-pc   : " ; INT decisionpc ;
             STR "observation-pc: " ; INT observationpc ;
             pretty_print_list
               !pairs (fun (k,v) ->
                 LBLOCK [ INT k ; STR ": " ; v#toPretty ; NL ]) "" "" "" ;
             NL ]
end
                    
module IntListCollections = CHCollections.Make
    (struct
      type t = int list 
      let compare is1 is2 =
	let rec comp is1 is2 =
	  match (is1, is2) with
	  | ([], []) -> 0
	  | (i1 :: rest_is1, i2 :: rest_is2) ->
	      if i1 = i2 then comp rest_is1 rest_is2
	      else compare i1  i2
	  | ([], _) -> -1
	  | (_, []) -> 1 in
	comp (List.sort compare is1) (List.sort compare is2)
      let toPretty is = pp_list_int is
    end)

class costmodel_t (scchecks:(sidechannelcheck_t) list) =
object (self:_)

  val methodcoststore = H.create 3
  (* (int, cost_bounds_t) H.t *)
                      
  val blockcoststore = H.create 3
  (* (int, (int, cost_bounds_t) H.t) H.t ; only used for reporting *)
                     
  val loopstructures = H.create 3
  (* (int, loop_structure_int) H.t *)
                     
  val loopcoststore = H.create 3
  (* (int, (int, cost_bounds_t) H.t) H.t; cmsix -> looop head -> cost of loop *)
                    
  val sidechannelchecks =
    (* (int, ((int, int), sidechannelcheck_t) H.t) H.t *)
    let t = H.create 3 in
    let _ =
      List.iter (fun sc ->
          let cmsix = sc#get_cmsix in
          let cmsentry =
            if H.mem t cmsix then
              H.find t cmsix
            else
              let tt = H.create 3 in
              begin H.add t cmsix tt ; tt end in
          H.replace cmsentry (sc#get_decision_pc, sc#get_observation_pc) sc)
                scchecks in
    t

  val coststore_final = new IntListCollections.table_t
  (* list of callee indices -> join of method costs with symbolic costs substituted *)

  method mk_bottom = bottom_cost_bounds

  method mk_top = top_cost_bounds

  method add_to_coststore_final cmsix cost =
    coststore_final#set [cmsix] cost

  method write_xml_cost ?(tag="ibcost") (node:xml_element_int) (b:cost_bounds_t) = 
    write_xml_bounds ~tag b node

  method read_xml_cost ?(tag="ibcost") (node:xml_element_int) =
    JCHCostBounds.read_xml_bounds ~tag node

  method has_loopbound = userdata#has_loopbound

  method get_loopbound = userdata#get_loopbound

  method get_sidechannelspecs (cmsix:int) =
    if H.mem sidechannelchecks cmsix then
      let checks = ref [] in
      let _ =
        H.iter (fun k _ -> checks := k :: !checks) (H.find sidechannelchecks cmsix) in
      !checks
    else []

  method set_methodcost (cmsix:int) (cost: cost_bounds_t) =
    H.replace methodcoststore cmsix cost

  method set_sidechannelcost
           (cmsix:int)
           (decpc:int)
           (predpc:int)
           (obspc:int)
           (cost: cost_bounds_t):unit =
    if H.mem sidechannelchecks cmsix then
      let cmschecks = H.find sidechannelchecks cmsix in
      if H.mem cmschecks (decpc,obspc) then
        let scheck = H.find cmschecks (decpc,obspc) in
        scheck#set_path_cost predpc cost
      else
        raise
          (JCH_failure
             (LBLOCK [ STR "No side channel check found in " ; INT cmsix ;
                       STR " for decision-pc = " ; INT decpc ;
                       STR " and observation-pc = " ; INT obspc ]))
    else
      raise (JCH_failure
               (LBLOCK [ STR "No side channel checks found for " ; INT cmsix ]))

  method set_loopstructure (cmsix:int) (ls:loop_structure_int) =
    H.replace loopstructures cmsix ls

  method private set_block_cost (cmsix:int) (pc:int) (cost: cost_bounds_t) =
    let _ = if H.mem blockcoststore cmsix then () else
	H.add blockcoststore cmsix (H.create 3) in
    let t = H.find blockcoststore cmsix in
    H.replace t pc cost

  method set_loop_cost (cmsix:int) (pc:int) (cost: cost_bounds_t) =
    let _ = if H.mem loopcoststore cmsix then () else
	H.add loopcoststore cmsix (H.create 3) in
    let t = H.find loopcoststore cmsix in
    H.replace t pc cost

  method get_loop_cost (cmsix:int) (pc:int) : cost_bounds_t =
    let t = H.find loopcoststore cmsix in
    H.find t pc 

  method get_block_cost (cmsix: int) (pc: int) : cost_bounds_t =
    let t = H.find blockcoststore cmsix in
    let cost = H.find t pc in
    cost

  method private compute_blockcost
                   (cmsix:int) (firstpc:int) (lastpc:int): cost_bounds_t =
    if !dbg then
      pr__debug [STR "compute_blockcost "; INT firstpc; STR " ";
                 INT lastpc; NL] ;
    let res = 
      let cms = retrieve_cms cmsix in
      let mInfo = app#get_method cms in
      let cost =
        if mInfo#has_bytecode then
	  begin
	    let code = mInfo#get_bytecode#get_code in
	    let cost: cost_bounds_t ref =
	      ref (self#get_instr_cost cmsix firstpc (code#at firstpc)) in
            
	    (if !dbg then
               pr__debug [STR "compbute_blockcost cost = "; !cost#toPretty; NL]) ;
            
	    let i = ref firstpc in
	    while !i < lastpc do
	      match code#next !i with
	      | Some j ->
                 
	         (if !dbg then
                    pr__debug [STR "add instr cost at "; INT j; NL]) ;
                 
	         let opcode = code#at j in
	         i := j ;
	         cost := add_cost_bounds !cost (self#get_instr_cost cmsix j opcode);
	         JCHCostUtils.check_cost_analysis_time
                   (" while computing block costs for " ^ (string_of_int cmsix)) ;
                 
	         (if !dbg then
                    pr__debug [STR "after add_cost,  cost = "; !cost#toPretty; NL]) ;
                 
	      | _ -> ()
	    done ;
	    !cost
	  end
        else
	  self#mk_bottom in
      
      begin
        self#set_block_cost cmsix firstpc cost ;
        cost
      end in
    
    (if !dbg then
       pr__debug [STR "compute_blockcost "; INT firstpc; STR " ";
                  INT lastpc; STR " res = "; res#toPretty; NL]) ;
    res 
	   
  method compute_block_cost
           (cmsix:int) (firstpc:int) (lastpc:int): cost_bounds_t =
    if userdata#has_blockcost cmsix firstpc then
      cost_bounds_from_jterm_range (userdata#get_blockcost cmsix firstpc)
    else
      self#compute_blockcost cmsix firstpc lastpc

  method private get_opcode_cost (opcode:opcode_t):jterm_range_int =
    mk_intconstant_jterm_range (mkNumerical (get_opcode_cost opcode))

  (* cost_bound are bounds for the cost of a call as a function of callee 
   * arguments, fields, and symbolic constants.
   * This method uses the default_map and the argument bounds from the 
   * numeric analysis to find a bound that depends on the parameters of 
   * the caller function, fields, and symbolic constants *)
  method private change_methodcall_cost
                   (cost_bounds: cost_bounds_t)
                   (caller_cmsix: int)
                   (pc: int)
                   (default_map: (int * int) list): cost_bounds_t =
    
    (if !dbg then
       pr__debug [STR "change_methodcall_cost ";
                  INT caller_cmsix; STR " ";
                  INT pc; NL; STR "   ";
                  cost_bounds#toPretty; NL;
                  pp_assoc_list_ints default_map; NL]) ;
    
    let (arg_lbounds, arg_ubounds) =
      JCHNumericAnalysis.get_method_arg_bounds caller_cmsix pc in
    
    (if !dbg then
       begin
         pr__debug [STR "JCHNumericAnalysis "; INT caller_cmsix; STR"@";
                    INT pc; NL] ;
         pr__debug [STR "arg_lbouds: "; NL];
         List.iter (fun (jt, ls) ->
             pr__debug [jterm_to_pretty jt; STR ": "; pp_list_jterm ls; NL])
                   arg_lbounds;
         pr__debug [STR "arg_ubounds: "; NL];
         List.iter (fun (jt, ls) ->
             pr__debug [jterm_to_pretty jt; STR ": "; pp_list_jterm ls; NL])
                   arg_ubounds
       end) ;

    (* make the constants close to max_int max_long into 
     * max_int(max_long) + or i small integer *)
    let max_int_lb = max_int_num#sub margin_num in
    let max_int_ub = max_int_num#add margin_num in
    
    let max_long_lb = max_int_num#sub margin_num in
    let max_long_ub = max_int_num#add margin_num in

    let change_bounds b =
      match b with
      | JConstant i when i#geq max_int_lb && i#leq max_int_ub -> 
	  let diff = i#sub max_int_num in
	  JArithmeticExpr (JPlus, sym_max_int, JConstant diff)
      | JConstant i when i#geq max_long_lb && i#leq max_long_ub -> 
	  let diff = i#sub max_long_num in
	  JArithmeticExpr (JPlus, sym_max_long, JConstant diff)
      | _ -> b in
    let arg_lbounds =
      List.map (fun (jt, ls) -> (jt, List.map change_bounds ls)) arg_lbounds in
    let arg_ubounds =
      List.map (fun (jt, ls) -> (jt, List.map change_bounds ls)) arg_ubounds in

    (* add default costs from the default_map *)
    let add_default_pair bounds (index, cost) =
      let is_index (jt, _) = jtdictionary#index_jterm jt = index in
      if not (List.exists is_index bounds) then
	(jtdictionary#get_jterm index, [JConstant (mkNumerical cost)]) :: bounds
      else bounds in
    let (arg_lbounds, arg_ubounds) =
      (List.fold_left add_default_pair arg_lbounds default_map,
       List.fold_left add_default_pair arg_ubounds default_map) in

    let jterms = get_jterms cost_bounds in

    (* add default costs for size (args) *)
    let add_size_default is_lb bounds jt =
      match jt with
      | JSize _ -> 
	  if (List.exists (fun (jt', _) -> jterm_compare jt' jt = 0) bounds) then
            bounds
	  else
	    let b =
              if is_lb then
                default_size#get_lowerbounds
              else
                default_size#get_upperbounds in
	    (jt, b) :: bounds
      | _ -> bounds in
    let (arg_lbounds, arg_ubounds) =
      (List.fold_left (add_size_default true) arg_lbounds jterms,
       List.fold_left (add_size_default false) arg_ubounds jterms) in

    (if !dbg then
      begin
	pr__debug [NL; STR "after default values, arg_lbounds: "; NL];
	List.iter (fun (jt, ls) ->
            pr__debug [jterm_to_pretty jt; STR ": "; pp_list_jterm ls; NL])
                  arg_lbounds; 
	pr__debug [STR "after default values, arg_ubounds: "; NL];
	List.iter (fun (jt, ls) ->
            pr__debug [jterm_to_pretty jt; STR ": "; pp_list_jterm ls; NL])
                  arg_ubounds
      end) ;

    (* check if all the jterms in cost_bounds have an argument bound *)
    let no_lbound = ref false in
    let no_ubound = ref false in
    let arg_lbounds =
      let ls = ref [] in
      let add_jterm jterm =
        
	(if !dbg then
           pr__debug [NL; STR "JCHCostBoundsModel.add_jterm ";
                      jterm_to_pretty jterm; NL]) ;
	let lbs =
	  try
	    let res =
              snd (List.find (fun (jt, _) -> compare jt jterm = 0) arg_lbounds) in
            
	    (if !dbg then
               pr__debug [STR "found in arg_lbounds "; NL]) ;
	    res
	  with _ ->  [] in
	if lbs = [] then
	  if no_local_vars jterm then
            (if !dbg then
               pr__debug [STR "not found in arg_lbounds but not local_var "; NL])
	  else if is_length jterm then
            (if !dbg then
               pr__debug [STR "not found in arg_lbounds but length local_var "; NL];
             ls := (jterm, [JConstant numerical_zero]) :: !ls)
	  else
            (if !dbg then
               pr__debug [STR "local_var not found in arg_ubounds"; NL]; no_lbound := true)
	else
          (if !dbg then
             pr__debug [STR "found in arg_lbounds "; NL]; ls := (jterm, lbs) :: !ls) ;
	try
	  let _= List.find (fun (jt, _) -> compare jt jterm = 0) arg_ubounds in
	  if !dbg then pr__debug [STR "found in arg_ubounds "; NL]
	with _ ->
	  if no_local_vars jterm then
            (if !dbg then
               pr__debug [STR "not found in arg_ubounds but not local_var"; NL]; ())
	  else
	    (if !dbg then
               pr__debug [STR "local_var not found in arg_ubounds"; NL];
             no_ubound := true) in
      begin
        List.iter add_jterm jterms ;
        !ls
      end in

    if !dbg then
      begin
	pr__debug [STR "after checking jterms in cost_bounds, arg_lbounds: "; NL];
	List.iter (fun (jt, ls) ->
            pr__debug [jterm_to_pretty jt; STR ": "; pp_list_jterm ls; NL]) arg_lbounds;
	pr__debug [STR "after checking jterms in cost_bounds, arg_ubounds: "; NL];
	List.iter (fun (jt, ls) ->
            pr__debug [jterm_to_pretty jt; STR ": "; pp_list_jterm ls; NL]) arg_ubounds
      end ;

    (* use default values if there are no argument bounds and if there are no 
     * default values use the default function bounds *)
    let (cost_bounds, arg_lbounds, arg_ubounds) =
      let (lbs, ubs, inf_lb, inf_ub) = get_bounds cost_bounds in
      match (!no_lbound, !no_ubound) with
      | (true, true) ->
	  begin
	    let method_name =
              (retrieve_cms caller_cmsix)#class_method_signature_string in
	    let pp = LBLOCK [ STR method_name; STR " @ "; INT pc;
                              STR " used default function bounds "; NL;
			      STR "          method call cost";
                              cost_bounds#toPretty; NL] in
	    chlog#add
              "cost loss of precision"
              (LBLOCK [STR (pretty_to_string pp)]) ;
            
	    pr__debug [STR "cost loss of precision "; pp] ;
	    
	    (new cost_bounds_t
                 ~bottom:cost_bounds#isBottom
                 ~simplify:false
                 ~inflb:inf_lb
                 ~infub:inf_ub
                 ~lbounds:[default_function_lbound]
                 ~ubounds:[default_function_ubound],
             [],
             [])
	  end
      | (true, false) ->
	  let const = find_const_lb true cost_bounds in
	  let const_lb = cost_bound_from_num false const in

	  let method_name =
            (retrieve_cms caller_cmsix)#class_method_signature_string in
	  let pp =
            LBLOCK [ STR method_name; STR " @ "; INT pc;
                     STR " method call with problematic lower bounds "; NL; 
		     STR "          lower bounds ";
                     pretty_print_list
                       lbs#toList (fun b -> STR b#to_string) "{" "; " "}"; NL] in
	  chlog#add "cost loss of precision" (LBLOCK [STR (pretty_to_string pp)]) ;
          
	  pr__debug [STR "cost loss of precision "; pp] ;
	  
	  (new cost_bounds_t
               ~bottom:cost_bounds#isBottom
               ~simplify:false
               ~inflb:inf_lb
               ~infub:inf_ub
               ~lbounds:[const_lb]
               ~ubounds:ubs#toList,
           [],
           arg_ubounds)
      | (false, true) ->
	  begin
	    if !dbg then
              pr__debug [STR "there are lower bounds but no upper bounds"; NL] ;
	    
	    let const = 
	      let lb_n = find_const_lb true cost_bounds in
	      let ub_n = find_const_lb false cost_bounds in
	      if lb_n#gt ub_n then lb_n else ub_n in
	    let const_ub = cost_bound_from_num false (const#add (mkNumerical 100)) in
	    
	    let method_name =
              (retrieve_cms caller_cmsix)#class_method_signature_string in
	    let pp =
              LBLOCK [ STR method_name; STR " @ "; INT pc;
                       STR " method call with problematic upper bounds "; NL; 
		       STR "          upper bounds ";
                       pretty_print_list
                         ubs#toList (fun b -> STR b#to_string) "{" "; " "}"; NL] in
	    chlog#add "cost loss of precision" (LBLOCK [STR (pretty_to_string pp)]) ;
            
	    pr__debug [STR "cost loss of precision "; pp] ;

	    (new cost_bounds_t
                 ~bottom:cost_bounds#isBottom
                 ~simplify:false
                 ~inflb:inf_lb
                 ~infub:inf_ub
                 ~lbounds:lbs#toList
                 ~ubounds:[const_ub],
             [],
             [])
	  end
      | (false, false) ->
         (new cost_bounds_t
              ~bottom:cost_bounds#isBottom
              ~simplify:false
              ~inflb:inf_lb
              ~infub:inf_ub
              ~lbounds:lbs#toList
              ~ubounds:ubs#toList,
          arg_lbounds,
          arg_ubounds) in

    (if !dbg then
      pr__debug [STR "after checking jterms, cost_bounds = "; NL;
                 cost_bounds#toPretty; NL]) ;


    let mk_local_var is_lb (var_jterm, bounds) =
      
      (if !dbg then
        pr__debug [STR "mk_local_var "; pp_bool is_lb; STR " ";
                   jterm_to_pretty var_jterm; NL; STR "     ";
                   (JTermCollections.set_of_list bounds)#toPretty; NL]);
      
      (var_jterm, List.map (JCHCostBound.bound_from_jterm is_lb) bounds) in
    let (arg_lbounds, arg_ubounds) =
      (List.map (mk_local_var true) arg_lbounds,
       List.map (mk_local_var false) arg_ubounds) in

    (if !dbg then
      begin
	pr__debug [STR "after mk_local_var, arg_lbounds: "; NL];
	List.iter (fun (jt, cs) ->
            pr__debug [jterm_to_pretty jt; STR ": "; pp_list cs; NL]) arg_lbounds; 
	pr__debug [STR "after mk_local_var, arg_ubounds: "; NL];
	List.iter (fun (jt, cs) ->
            pr__debug [jterm_to_pretty jt; STR ": "; pp_list cs; NL]) arg_ubounds
      end) ;

    let new_cost_bounds =
      JCHCostBounds.subst_local_vars pc cost_bounds arg_lbounds arg_ubounds in
    
    (if !dbg then
       pr__debug [ STR "changel_methodcall_cost res = ";
                   new_cost_bounds#toPretty; NL]);
    new_cost_bounds

  method private get_library_method_timecost
                   (caller:method_info_int)
                   (pc:int)
                   (callee:class_method_signature_int)
                   (summary:function_summary_int):bool * 'a * (int * int) list =
    let cost =
      if has_precanned_time_cost callee then
        get_precanned_time_cost callee
      else
        summary#get_time_cost in
    
    (if !dbg then
       pr__debug [STR "library method summary cost = "; cost#toPretty; NL]) ;
    
    let (is_top, cost) = 
      if cost#is_top then
        
        begin
	  (if !dbg then
             pr__debug [STR "summary cost is top"; NL]);
          
          timecost_diagnostics#record_missing callee ;
          (true, default_libcall_cost ("libcall_default_Top"))
        end
      else
	begin
	  timecost_diagnostics#record_jterm
            caller#get_class_method_signature pc callee cost ;
          (false, cost)
	end in
    (is_top, cost_bounds_from_jterm_range cost,[])
      
  method private get_methodcall_cost 
      (caller:class_method_signature_int)
      (pc:int)
      (callee:class_method_signature_int) : cost_bounds_t =
    
    (if !dbg then
       pr_debug [STR "get_methodcall_cost "; INT caller#index; STR " ";
                 INT pc; STR " "; INT callee#index; NL;
		 caller#toPretty; NL;
		 callee#toPretty; NL]);
    
    let res =
      let change method_cost default_map = 
        let new_cost =
          self#change_methodcall_cost method_cost caller#index pc default_map in
        
        (if !dbg then
           pr__debug [STR "change new_cost = "; new_cost#toPretty; NL]) ;
        
        if new_cost#isBottom then
          new_cost
        else if new_cost#isTop then
	  cost_bounds_from_jterm_range (default_funcall_cost "funcall_default_Top")
        else
	  begin
	    let (_, _, inf_lb, inf_ub) = get_bounds method_cost in
	    if inf_lb || inf_ub then
	      chlog#add
                "calls to possibly non-terminating methods"
	        (LBLOCK [STR "m_"; INT caller#index; STR ": ";
                         caller#toPretty; STR "@"; INT pc; NL;
		         STR "            -> m_"; INT callee#index;
                         STR ": ";callee#toPretty]);
	    new_cost
	  end in
      
      if userdata#has_methodcost callee#index then
	begin
	  let method_cost = userdata#get_methodcost callee#index in
          
	  (if !dbg then
            pr__debug [STR "get_methodcall_cost: user data method_cost ";
                       method_cost#toPretty; NL]) ;
          
	  change (cost_bounds_from_jterm_range method_cost) []
	end
      else if H.mem methodcoststore callee#index then
	begin
	  let method_cost = H.find methodcoststore callee#index in
          
	  (if !dbg then
            pr__debug [STR "get_methodcall_cost: analyzed method_cost "; NL;
                       method_cost#toPretty; NL]);
          
	  change method_cost []
	end 
      else if function_summary_library#has_method_summary callee then
	begin
	  let summary = function_summary_library#get_method_summary callee in
          let mInfo = app#get_method caller in
	  let (is_top, cost, default_map) =
            self#get_library_method_timecost mInfo pc callee summary in
          
	  let _ =
            if !dbg then
              pr__debug [STR "get_methodcall_cost: summary method_cost: "; NL;
                         cost#toPretty; NL] in
          
	  if is_top then
            cost
	  else
            change cost default_map
	end 
      else
	begin
          let cost =
            cost_bounds_from_jterm_range
              (default_funcall_cost "funcall_default_no_summary") in
          
          pr__debug [STR "get_methodcall_cost: default_functioncall_cost (no method summary) for ";
                     INT caller#index; STR " "; INT pc; STR " "; INT callee#index; NL;
		     caller#toPretty; NL;
		     callee#toPretty; NL]; 
          
          chlog#add
            "default function call cost"
            (LBLOCK [ caller#toPretty ; STR " @pc:" ; INT pc ; STR " - " ;
                      callee#toPretty ; STR ": " ; cost#toPretty ]) ;
          cost
        end in
    
    (if !dbg then
       pr__debug [STR "  get_methodcall_cost res = "; res#toPretty; NL]) ;
    
    res 


  method private get_instr_cost
                   (cmsix:int) (pc:int) (opcode:opcode_t): cost_bounds_t =
    
    (if !dbg then
      pr__debug [STR "_______________________"; NL;
                 STR "get_instr_time_cost "; INT pc; NL]) ;
    
    let res =  
      if userdata#has_instructioncost cmsix pc then
        begin
          
	  (if !dbg then
             pr_debug [STR "userdata#has_instructioncost "; NL]) ;
          
	  let cost = userdata#get_instructioncost cmsix pc in
	  cost_bounds_from_jterm_range cost
        end
      else
        begin
	  match opcode with
	  | OpInvokeVirtual _
            | OpInvokeSpecial _
            | OpInvokeStatic _
            | OpInvokeInterface _  ->
	     let cost_callee = 
	       let caller = retrieve_cms cmsix in
	       let callees =
                 match userdata#get_callees cmsix pc with
                 | [] -> callgraph_base#get_pc_callees cmsix pc
                 | l -> l in
               
	       (if !dbg then
                  pr__debug [STR "callees "; pp_list callees; NL]) ;
               
	      if (List.length callees) = 0 then
		begin
		  let cms = retrieve_cms cmsix in
                  
		  (if !dbg then
                     pr__debug [STR "no callees at pc = "; INT pc ;
                                STR " "; cms#toPretty ; STR ": " ; 
			        opcode_to_pretty opcode; NL]) ;
                  
		  chlog#add
                    "no callees"
		    (LBLOCK [ STR "pc = " ; INT pc ; STR " "; cms#toPretty ; STR ": " ; 
			      opcode_to_pretty opcode ] );
		  cost_bounds_from_jterm_range
		    (default_funcall_cost
                       ("default_funcall_no_callees_"))
   		end
	      else 
		begin
		  let sorted_inds =
                    List.sort compare (List.map (fun c -> c#index) callees) in
                  
		  (if (List.length sorted_inds)
                     > (IntCollections.set_of_list sorted_inds)#size then
                    
		    pr__debug [STR "found duplicate callees: "; NL; pp_list callees; NL]) ;
                  
		  let call_cost = 
		    begin
		      let add_cost acc callee =
                        
			(if !dbg then
                           pr__debug [NL; STR "add_cost "; callee#toPretty; NL]) ;
                        
			if acc#isTop then
                          top_cost_bounds
			else
			  begin
			    let call_cost =
                              self#get_methodcall_cost caller pc callee in
			    full_join acc call_cost
			  end in
		      let call_cost =
                        List.fold_left add_cost self#mk_bottom callees in
		      call_cost
		    end in
                  
		  let const_lb = find_const_lb true call_cost in
		  
		  (if !dbg then
                     pr__debug [STR "call_cost = "; call_cost#toPretty; NL]) ;
                  
		  if is_const_range call_cost then
                    call_cost
		  else
		    begin
		      let jterms = get_jterms call_cost in
		      if (List.exists (is_local_var true) jterms) then
			begin
			  let sym_call = make_sym_call cmsix pc const_lb in
			  add_pos_jterm pc sym_call call_cost;
			  bounds_from_jterms false [sym_call] [sym_call]
			end
		      else
			begin
			  let lb = 
			    let const_lb = find_const_lb true call_cost in
			    if const_lb#lt numerical_zero then numerical_zero
			    else const_lb in
			  let sym_cost = make_sym_cost sorted_inds lb pc in
			  let call_cost_final =
                            add_pos_jterm_final pc sym_cost call_cost in
			  coststore_final#set sorted_inds call_cost_final ;
			  bounds_from_jterms false [sym_cost] [sym_cost]
			end 
		    end
		end in
	     let cost_op =
               cost_bounds_from_jterm_range (self#get_opcode_cost opcode) in
	     add_cost_bounds cost_op cost_callee
	  | _ ->
	     cost_bounds_from_jterm_range (self#get_opcode_cost opcode) 
        end in
    
    (if !dbg then
       pr__debug [STR "get_instr_cost res = "; res#toPretty; NL]) ;
    
    res
    
  method print_cost_stores () =
    pr__debug [NL; NL; STR "final costs: "; NL; coststore_final#toPretty; NL] 
      
  method save_xml_class (cInfo:class_info_int) =
    if cInfo#is_stubbed || cInfo#is_missing then
      ()
    else
      let _ =
        pr_debug [ STR " -- " ; cInfo#get_class_name#toPretty ; NL ] in
      
      let cn = cInfo#get_class_name in
      let node = xmlElement "class" in
      begin
	self#write_xml_class_cost_results node cInfo ;
	node#setAttribute "name" cn#simple_name ;
	node#setAttribute "package" cn#package_name ;
	save_xml_cost_analysis_results cn node "class"
      end
      
  method save_xml_atlas_class (cInfo:class_info_int) =
    if cInfo#is_stubbed || cInfo#is_missing then
      ()
    else
      let cn = cInfo#get_class_name in
      let node = xmlElement "class" in
      let set = node#setAttribute in
      begin
        self#write_xml_atlas_class_cost_results node cInfo ;
        set "name" cn#simple_name ;
        set "package" cn#package_name ;
        save_xml_atlas_cost_analysis_results cn node "class"
      end
      
  method private write_xml_method_cost_results node cms =
    let mInfo = app#get_method cms in
    let cmsix = cms#index in
    begin
      (if H.mem blockcoststore cmsix then
         let pct = H.find blockcoststore cmsix in
         let pcsNode = xmlElement "blocks" in
         let blocks = ref [] in
         let _ = H.iter (fun pc cost -> blocks := (pc,cost) :: !blocks) pct in
         let blocks = List.sort (fun (pc1,_) (pc2,_) -> P.compare pc1 pc2) !blocks in
         begin
           pcsNode#appendChildren
             (List.map (fun (pc,cost) ->
                  let pcNode = xmlElement "block" in
                  begin
                    self#write_xml_cost ~tag:"ibcost" pcNode cost ;
                    pcNode#setIntAttribute "pc" pc ;
                    pcNode
                  end) blocks) ;
           node#appendChildren [ pcsNode ]
         end) ;
      (if H.mem methodcoststore cmsix then
         let mcost = H.find methodcoststore cmsix in
         self#write_xml_cost ~tag:"imcost" node mcost ) ;
      (if H.mem loopcoststore cmsix && H.mem loopstructures cmsix then
	 let mcost = H.find loopcoststore cmsix in
	 let hpcs = (H.find loopstructures cmsix)#get_loopheads in
	 if not (hpcs = []) then
	   begin
	     let lsNode = xmlElement "loops" in
	     let get_cost_one_iteration hpc = 
	       H.find mcost hpc in
	     let get_max_iterations hpc =
               if userdata#has_loopbound cmsix hpc then
                 let jtermrange = userdata#get_loopbound cmsix hpc in
                 bounds_from_jterms
                   false jtermrange#get_lowerbounds jtermrange#get_upperbounds
               else
	         let (lbs_jterms, ubs_jterms) =
                   JCHNumericAnalysis.get_iteration_bounds cmsix hpc in
	         bounds_from_jterms false lbs_jterms ubs_jterms in
	     
	     let add_loop hpc =
	       let lNode = xmlElement "loop" in
	       lNode#setIntAttribute "hpc" hpc;
	       self#write_xml_cost ~tag:"i1it" lNode (get_cost_one_iteration hpc) ;
	       self#write_xml_cost ~tag:"iitcount" lNode (get_max_iterations hpc);
	       lNode in
	     lsNode#appendChildren (List.map add_loop hpcs) ;
	     node#appendChildren [lsNode]
	   end) ;
      
      (if H.mem sidechannelchecks cmsix then
         let ssNode = xmlElement "sidechannel-checks" in
         let mchecks = H.find sidechannelchecks cmsix in
         let checks = ref [] in
         let _ = H.iter (fun _ v -> checks := v :: !checks) mchecks in
         begin
           ssNode#appendChildren
             (List.map (fun sc ->
                  let sNode = xmlElement "sc-check" in
                  begin
                    sc#write_xml sNode ;
                    sNode
                  end) !checks) ;
           node#appendChildren [ ssNode ]
         end) ;
      node#setIntAttribute "cmsix" cmsix ;
      (if mInfo#is_abstract then node#setAttribute "abstract" "yes") ;
    end
    
  method private write_xml_class_cost_results node cInfo = 
    let mmNode = xmlElement "methods" in
    begin
      mmNode#appendChildren
        (List.map (fun ms ->
	     let cms = make_cms cInfo#get_class_name ms in
             let mNode = xmlElement "method" in
             begin
               self#write_xml_method_cost_results mNode cms ;
               mNode
             end) cInfo#get_methods_defined) ;
      node#appendChildren [ mmNode ]
    end
    
  method private write_xml_atlas_cost
                   (node:xml_element_int)
                   (ms:method_signature_int)
                   (b:cost_bounds_t) =
    write_xml_atlas_bounds node ms b
    
  method private write_xml_atlas_method_cost_results
                   (node:xml_element_int) (cms:class_method_signature_int) =
    let set = node#setAttribute in
    let cmsix = cms#index in
    let sNode = xmlElement "signature" in
    begin
      cms#method_signature#write_xmlx sNode ;
      node#appendChildren [ sNode ] ;
      (if H.mem methodcoststore cmsix then
         let mcost = H.find methodcoststore cmsix in
         let cNode = xmlElement "cost" in
         let _ = self#write_xml_atlas_cost cNode cms#method_signature mcost in
         node#appendChildren [ cNode ]) ;
      set "name" cms#name ;
      set "sig" cms#method_signature#to_signature_string
    end

  method  private write_xml_atlas_class_cost_results node cInfo =
    let mmNode = xmlElement "methods" in
    let _ =
      mmNode#appendChildren
        (List.map (fun ms ->
             let cms = make_cms cInfo#get_class_name ms in
             let mNode = xmlElement "method" in
             begin
               self#write_xml_atlas_method_cost_results mNode cms ;
               mNode
             end) cInfo#get_methods_defined) in
    node#appendChildren [ mmNode ]

  method private read_xml_method_cost_results node =
    let cms = node#getIntAttribute "cmsix" in
    begin
    ( match node#hasOneTaggedChild "blocks" with
      | true -> let bbNode = (node#getTaggedChild "blocks") in
         ( match bbNode#hasTaggedChildren "block" with
           | true ->
              let bNodes = (bbNode#getTaggedChildren "block") in
              (List.iter
                 (fun bNode ->
                   let _ = pr_debug [ STR "New Node : " ; NL ] in
                   let pc = bNode#getIntAttribute "pc" in
                   let bCost = self#read_xml_cost ~tag:"ibcost" bNode in
                   let _ = (self#set_block_cost cms pc bCost) in
                   let _ = self#get_block_cost cms pc in () )
                 bNodes )
           | false -> pr_debug [ STR "No blocks" ; NL ])
      | false -> pr_debug [ STR "No blocks node" ; NL ] ) ;
    
    (if node#hasNamedAttribute "imcost" then
       let mCost = self#read_xml_cost ~tag:"imcost" node in
       (self#set_methodcost cms mCost) ) ;
    end
    
  method private read_xml_class_cost_results node (cInfo:class_info_int) =
    let mmNode = node#getTaggedChild "methods" in
    let mNodes = mmNode#getTaggedChildren "method" in
    (List.iter self#read_xml_method_cost_results mNodes)

  method read_xml_class (cInfo:class_info_int) =
    if cInfo#is_stubbed || cInfo#is_missing then () else
     let cn = (cInfo#get_class_name) in
     let node_option = (load_xml_cost_analysis_results cn) in
     match node_option with
     | None ->
        pr_debug [ STR "Warning: No cost results file found for " ;
                   cn#toPretty ; NL ]
     | Some (node) ->
        begin
          self#read_xml_class_cost_results node cInfo
        end
end
  
