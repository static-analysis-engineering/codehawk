(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
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


(* -----------------------------------------------------------------------------
 * Provides user data obtained from files:
 * - loads default cost data from chanalysis/costdata.xml, if present
 * - loads user-provided cost data from chuserdata/<package-dir>/<class-name>.xml
 *       if present
 *
 * Type of data:
 * - symbolic constants with assigned values
 * - default/user-provided loop bound expressions
 * - user-provided instruction costs
 * - (sensitive decision, sink) pairs for locations of potential side channels
 * - run methods associated with Thread.start() calls
 * 
 * user-provided bounds have priority over default bounds
 *
 * Elements within methods:
 * 
 * <bounds>
 *   <loop pc=[number] it=[number]/>    number of iterations at loop starting at pc
 *   <loop pc=[number] itc=[name]/>     number of iterations specified by named constant
 *   <loop pc=[number] itc=[name] exp=[number]/>
 *       number of iterations specified by named constant to the power exp
 * </bounds>
 * 
 * <instruction-costs>
 *   <icost pc=[number] cost=[number]/>  cost value for instruction at pc
 *   <icost pc=[number] lb=[number] ub=[number]/> cost range for instruction
 * </instruction-costs>
 * 
 * <block-costs>
 *   <bcost pc=[number] cost=[number]> cost value for basic block starting at pc
 *   <bcost pc=[number] lb=[number] ub=[number]>  cost range for basic block
 * </block-costs>
 * 
 * <method-cost cost=[number]>                    cost value for calling this method
 * <method-cost lb=[number] ub=[number]>          cost range for calling this method
 * 
 * <callees>
 *    <callee pc=[number] kind="run" class=[classname]>
 *            run method associated with a Thread.start() call at pc
 *    <callee pc=[number] kind="restrict" class=[classname]>
 *            target class for virtual or interface call with multiple targets
 *    <callee pc=[number] kind="restrict">   
 *       <cn name=[classname]/>
 *       <cn name=[classname]/>
 *       ....
 *    </callee>      set of target classes for virtual or interface call
 * </callees>
 * 
 * <nops>
 *   <nop pc=[number]/>     replace instruction at pc=number with a no-op
 * </nops>
 * 
 * <side-channel-checks>
 *   <scc observation-pc=[number] decision-pc=[number]>
 * </side-channel-checks>
 * ----------------------------------------------------------------------------- *)

(* chlib *)
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm

(* jchpre *)
open JCHApplication
open JCHMethodImplementations
open JCHPreAPI

module H = Hashtbl

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end


class userdata_t:userdata_int =
object (self)

  val bounds = H.create 3               (* cms-ix -> pc -> constrained_jterm_int *)
  val instructioncosts = H.create 3     (* cms-ix -> pc -> constrained_jterm_int *)
  val blockcosts = H.create 3           (* cms-ix -> pc -> constrained_jterm_int *)
  val methodcosts = H.create 11         (* cms-ix -> constrained_jterm_int *)
  val sidechannelchecks = H.create 3    (* cms-ix -> (decision-pc,observation-pc) *)
  val runmethods = H.create 1           (* cms-ix -> pc -> cms *)
  val callees = H.create 3              (* cms-ix -> pc -> cms list *)
  val nopreplacements = H.create 3      (* cms-ix -> pc list *)
  val constants = H.create 11           (* name -> jterm_t *)

  val edges = H.create 3                (* (cmsix,pc) -> class_name_int *)

  method add_userdata (node:xml_element_int) =
    begin
      (if node#hasOneTaggedChild "constants" then
         List.iter self#add_user_constant
                   ((node#getTaggedChild "constants")#getTaggedChildren "c")) ;
      List.iter self#add_user_class_data (node#getTaggedChildren "class")
    end

  method private add_user_constant (node:xml_element_int) =
    let get = node#getAttribute in
    let has = node#hasNamedAttribute in
    let name = get "name" in
    let lbopt = if has "lb" then Some (mkNumericalFromString (get "lb")) else None in
    let ubopt = if has "ub" then Some (mkNumericalFromString (get "ub")) else None in
    let jterm = JSymbolicConstant (TBasic Int, lbopt, ubopt, name) in
    H.add constants name jterm 

  method private add_user_class_data (node:xml_element_int) =
    let name = node#getAttribute "name" in
    let cn = make_cn name in
    List.iter (fun n ->
        self#add_user_method_data cn n) (node#getTaggedChildren "method")

  method has_edge (src:(int * int)) = H.mem edges src

  method get_edge (src:(int * int)) =
    if self#has_edge src then
      H.find edges src
    else
      raise (JCH_failure (LBLOCK [ STR "No edge found for " ;
                                   INT (fst src) ; STR " at pc = " ; INT (snd src) ]))

  method private add_user_method_data (cn:class_name_int) (node:xml_element_int) =
    let getc = node#getTaggedChild in
    let hasc = node#hasOneTaggedChild in
    let name = node#getAttribute "name" in
    let ssig = node#getAttribute "sig" in
    let msix = method_signature_implementations#get_ms_index name ssig in
    let ms = retrieve_ms msix in
    let cms = make_cms cn ms in
    let _ =
      List.iter (fun n ->
          let geti = n#getIntAttribute in
          let get = n#getAttribute in
          let has = n#hasNamedAttribute in
          let pc = geti "pc" in
          let count =
            let jterm =
              if has "kind" && n#getAttribute "kind" = "symbolic" then
                let name = get "iteration-count" in
                if H.mem constants name then
                  H.find constants name
                else
                  let lbopt = if has "lb" then Some (mkNumericalFromString (get "lb")) else None in
                  let ubopt = if has "ub" then Some (mkNumericalFromString (get "ub")) else None in
                  JSymbolicConstant (TBasic Int, lbopt, ubopt, name) 
              else
                JConstant (mkNumerical (geti "iteration-count")) in
            mk_jterm_jterm_range jterm in
          self#add_bound cms#index pc count) (node#getTaggedChildren "loop") in
    let _ =
      if hasc "edges" then
        let xedges = getc "edges" in
        List.iter (fun n ->
            let geti = n#getIntAttribute in
            let get = n#getAttribute in
            let pc = geti "pc" in
            let tgt = get "tgt" in
            let cn = make_cn tgt in
            H.add edges (cms#index, pc) cn) (xedges#getTaggedChildren "edge") in
    if hasc "side-channel-checks" then
      let xscs =
        List.map (fun n ->
            let geti = n#getIntAttribute in
            let has = n#hasNamedAttribute in
            let decisionpc = if has "decision-pc" then geti "decision-pc" else 0 in
            let observationpc = geti "observation-pc" in
            (decisionpc,observationpc))
                 ((getc "side-channel-checks")#getTaggedChildren "scc") in
      H.add sidechannelchecks cms#index xscs
      

  method register_constants (node:xml_element_int) =
    List.iter (fun n ->
        let has = n#hasNamedAttribute in
        let geti = n#getIntAttribute in
        let name = n#getAttribute "name" in
        if has "value" then
          H.add constants name (JConstant (mkNumerical (geti "value")))
        else
          let lb = if has "lb" then Some (mkNumerical (geti "lb")) else None in
          let ub = if has "ub" then Some (mkNumerical (geti "ub")) else None in
          H.add constants name (JSymbolicConstant (TBasic Int,lb,ub,name)))          
      (node#getTaggedChildren "constant")

  method private get_constant_value (name:string) =
    if H.mem constants name then H.find constants name else
      raise (JCH_failure
	       (LBLOCK [ STR "No constant found for name " ; STR name ]))

  method add_class_data (node:xml_element_int) = 
    let cname = node#getAttribute "name" in
    let package = node#getAttribute "package" in
    let cname = if package = "" then cname else package ^ "." ^ cname in
    let cn = make_cn cname in
    begin
      (if node#hasOneTaggedChild "methods" then
         List.iter (self#add_method_data cn) 
	           ((node#getTaggedChild "methods")#getTaggedChildren "method")) ;
      (if node#hasOneTaggedChild "constructors" then
         List.iter (self#add_constructor_data cn)
	           ((node#getTaggedChild "constructors")#getTaggedChildren "constructor"))
    end

  method add_default_costdata (node:xml_element_int) =
    List.iter (fun mnode ->
      let cmsix = mnode#getIntAttribute "cms-ix" in
      List.iter (fun lnode ->
	let geti = lnode#getIntAttribute in
	let pc = geti "pc" in
	let bound = geti "bound" in
	self#add_bound cmsix pc (mk_intconstant_jterm_range (mkNumerical bound)))
	((mnode#getTaggedChild "loops")#getTaggedChildren "loop"))
              (node#getTaggedChildren "method")

  method private get_constructor_sig_signature (node:xml_element_int) (cn:class_name_int) =
    let ssig = node#getAttribute "sig" in
    let name = "<init>" in
    let msix = method_signature_implementations#get_ms_index name ssig in
    let ms = retrieve_ms msix in
    make_cms cn ms

  method private get_sig_signature (node:xml_element_int) (cn:class_name_int) =
    let ssig = node#getAttribute "sig" in
    let name = node#getAttribute "name" in
    let msix = method_signature_implementations#get_ms_index name ssig in
    let ms = retrieve_ms msix in
    make_cms cn ms
    
  method private add_constructor_data (cn:class_name_int) (node:xml_element_int) =
    (* let cms = read_xmlx_constructor_signature node cn in *)
    let cms = self#get_constructor_sig_signature node cn in
    self#add_user_data cms node 

  method private add_method_data (cn:class_name_int) (node:xml_element_int) =
    (* let cms = read_xmlx_class_method_signature node cn in *)
    let cms = self#get_sig_signature node cn in
    self#add_user_data cms node

  method private add_bound (cmsix:int) (pc:int) (v:jterm_range_int) =
    let _ = if H.mem bounds cmsix then () else H.add bounds cmsix (H.create 3) in
    let _ = chlog#add "user loop bound"
                      (LBLOCK [ (retrieve_cms cmsix)#toPretty ; STR " @pc " ; INT pc ;
                                STR ": " ; v#toPretty ]) in
    H.replace (H.find bounds cmsix) pc v

  method private add_bounds (cmsix:int) (node:xml_element_int) =
    List.iter (fun bnode ->
      let get = bnode#getAttribute in
      let geti = bnode#getIntAttribute in
      let has = bnode#hasNamedAttribute in
      let pc = geti "pc" in
      let iterations = if has "it" then
	  JConstant (mkNumerical (geti "it"))
	else if has "itc" then
	  self#get_constant_value (get "itc")
	else 
	  let cms = retrieve_cms cmsix in
	  raise (JCH_failure
		   (LBLOCK [ STR "Specification of iterations missing in " ;
			     cms#toPretty ; STR " at pc = " ; INT pc ])) in
      let iterations =
        if has "exp" then
	  let exp = geti "exp" in   (* exponent *)
	  match exp with
	  | 0 -> JConstant numerical_one
	  | 1 -> iterations
	  | _ -> 
	    (match iterations with
	    | JConstant n ->
	      (match exp with
	      | 2 -> JConstant (n#mult n)
	      | 3 -> JConstant ((n#mult n)#mult n)
	      | 4 -> JConstant (((n#mult n)#mult n)#mult n)
	      | _ -> 
		let cms = retrieve_cms cmsix in
		raise (JCH_failure
			 (LBLOCK [ STR "Unusually high value for exponent: " ; INT exp ;
				   STR " in " ; cms#toPretty ; STR " at pc = " ;
				   INT pc ])))
	    | _ -> 
	      let cms = retrieve_cms cmsix in
	      begin
		chlog#add "ignore exponent"
		  (LBLOCK [ cms#toPretty ; STR " at pc = " ; INT pc ]) ;
		iterations
	      end)
	else
	  iterations in
      self#add_bound cmsix pc (mk_jterm_jterm_range iterations))
    (node#getTaggedChildren "loop")

  method private add_instruction_cost 
    (cmsix:int) 
    (pc:int) 
    (v:jterm_range_int) =
    let _ = if H.mem instructioncosts cmsix then () else
	H.add instructioncosts cmsix (H.create 3) in
    H.replace (H.find instructioncosts cmsix) pc v

  method private add_instruction_costs (cmsix:int) (node:xml_element_int) =
    let cms = retrieve_cms cmsix in
    List.iter (fun inode ->
      let pc = inode#getIntAttribute "pc" in
      let cost = read_xmlx_jterm_range inode cms in
      self#add_instruction_cost cmsix pc cost) (node#getTaggedChildren "icost")

  method private add_block_cost
    (cmsix:int) 
    (pc:int) 
    (v:jterm_range_int) =
    let _ = if H.mem blockcosts cmsix then () else
	H.add blockcosts cmsix (H.create 3) in
    H.replace (H.find blockcosts cmsix) pc v

  method private add_block_costs (cmsix:int) (node:xml_element_int) =
    let cms = retrieve_cms cmsix in
    List.iter (fun bnode ->
      let pc = bnode#getIntAttribute "pc" in
      let cost = read_xmlx_jterm_range bnode cms in
      self#add_block_cost cmsix pc cost) (node#getTaggedChildren "bcost")

  method private add_method_cost (cmsix:int) (node:xml_element_int) =
    let cms = retrieve_cms cmsix in
    let cost = read_xmlx_jterm_range node cms in
    H.replace methodcosts cmsix cost

  method private add_instruction_run_class (cmsix:int) (pc:int) (cname:string) =
    let cn = make_cn cname in
    let ms = make_ms false "run" (make_method_descriptor ~arguments:[] ()) in
    let cms = make_cms cn ms in
    let _ = if H.mem runmethods cmsix then () else H.add runmethods cmsix (H.create 1) in
    H.replace (H.find runmethods cmsix) pc cms

  method private add_callee_restriction (cmsix:int) (pc:int) (cnames:string list) =
    let mInfo = app#get_method (retrieve_cms cmsix) in
    let opcode =
      try
        mInfo#get_opcode pc
      with
      | JCH_failure p ->
         raise (JCH_failure
                  (LBLOCK [ STR "Error in callee restriction in " ;
                            (retrieve_cms cmsix)#toPretty ; STR ": " ; p ])) in
    let ms = match opcode with
      | OpInvokeStatic (_,ms) 
      | OpInvokeSpecial (_, ms)
      | OpInvokeInterface (_,ms)
      | OpInvokeVirtual (_,ms) -> ms
      | _ ->
	raise (JCH_failure 
		 (LBLOCK [ STR "Non-call instruction with callees: " ; 
			   mInfo#get_class_method_signature#toPretty ; 
			   STR " at pc = " ; INT pc ])) in
    let cmss = List.map (fun name -> make_cms (make_cn name) ms) cnames in
    let _ = if H.mem callees cmsix then () else H.add callees cmsix (H.create 1) in
    let _ = chlog#add "user callee restriction"
                      (LBLOCK [ (retrieve_cms cmsix)#toPretty ; STR " @pc " ; INT pc ;
                                STR ": " ; STR (String.concat "," cnames) ]) in
    H.replace (H.find callees cmsix) pc cmss

  method private add_callees (cmsix:int) (node:xml_element_int) =
    List.iter (fun cnode ->
      let get = cnode#getAttribute in
      let geti = cnode#getIntAttribute in
      let getcc = cnode#getTaggedChildren in
      let has = cnode#hasNamedAttribute in
      let pc = geti "pc" in
      match (get "kind") with 
      | "run" -> self#add_instruction_run_class cmsix pc (get "class")
      | "restrict" ->
	if has "class" then
	  self#add_callee_restriction cmsix pc [ get "class" ]
	else
	  self#add_callee_restriction cmsix pc 
	    (List.map (fun clnode -> clnode#getAttribute "name") (getcc "class"))
      | s -> 
	raise_xml_error node
	  (LBLOCK [ STR "callee kind " ; STR s ; STR " not recognized" ]))
      (node#getTaggedChildren "callee")

  method private add_user_data 
    (cms:class_method_signature_int) 
    (node:xml_element_int) =
    let getc = node#getTaggedChild in
    let hasc = node#hasOneTaggedChild in
    let cmsix = cms#index in
    begin
      (if hasc "bounds" then 
	  self#add_bounds cmsix (getc "bounds")) ;
      (if hasc "instruction-costs" then 
	  self#add_instruction_costs cmsix (getc "instruction-costs")) ;
      (if hasc "block-costs" then 
	  self#add_block_costs cmsix (getc "block-costs")) ;
      (if hasc "method-cost" then
	  self#add_method_cost cmsix (getc "method-cost")) ;
      (if hasc "callees" then
	  self#add_callees cmsix (getc "callees")) ;
      (if hasc "nops" then
	  let nops = List.map (fun nnode -> 
	    nnode#getIntAttribute "pc") ((getc "nops")#getTaggedChildren "nop") in
	  H.add nopreplacements cms#index nops) ;
      (if hasc "side-channel-checks" then
	  let xscs = List.map (fun x -> 
	    let has = x#hasNamedAttribute in
	    let geti = x#getIntAttribute in
	    let decisionpc = if has "decision-pc" then geti "decision-pc" else 0 in
	    let observationpc = geti "observation-pc" in
	    (decisionpc,observationpc)) ((getc "side-channel-checks")#getTaggedChildren "scc") in
	  H.add sidechannelchecks cms#index xscs) ;
    end

  method private getnamedconstant (name:string):jterm_t =
    if H.mem constants name then
      H.find constants name
    else
      raise (JCH_failure
	       (LBLOCK [ STR "no constant found for " ; STR name ]))

  method get_loopbound (cmsix:int) (pc:int):jterm_range_int = 
    if H.mem bounds cmsix then 
      if H.mem (H.find bounds cmsix) pc then
	H.find (H.find bounds cmsix) pc 
      else
	let cms = retrieve_cms cmsix in
	raise (JCH_failure
		 (LBLOCK [ STR "No loop bounds found for " ; cms#toPretty ; 
			   STR " at pc = " ; INT pc ]))
    else
      let cms = retrieve_cms cmsix in
      raise (JCH_failure
	       (LBLOCK [ STR "No loop bounds found for " ; cms#toPretty ]))

  method has_loopbound (cmsix:int) (pc:int) =
    (H.mem bounds cmsix) && (H.mem (H.find bounds cmsix) pc)

  method get_method_sidechannelchecks (cmsix:int) =
    if H.mem sidechannelchecks cmsix then H.find sidechannelchecks cmsix else []

  method get_sidechannelchecks =
    let scclist = ref [] in
    let _ = H.iter (fun cmsix lst -> scclist := (cmsix,lst) :: !scclist) sidechannelchecks in
    !scclist
                

  method has_instructioncost (cmsix:int) (pc:int) =
    (H.mem instructioncosts cmsix) && (H.mem (H.find instructioncosts cmsix) pc)

  method get_instructioncost (cmsix:int) (pc:int) =
    if self#has_instructioncost cmsix pc then
      H.find (H.find instructioncosts cmsix) pc 
    else
      let cms = retrieve_cms cmsix in
      raise (JCH_failure
	       (LBLOCK [ STR "no instruction cost found for pc = " ; INT pc ;
			 STR " for method " ; cms#toPretty ]))

  method has_blockcost (cmsix:int) (pc:int) =
    (H.mem blockcosts cmsix) && (H.mem (H.find blockcosts cmsix) pc)

  method get_blockcost (cmsix:int) (pc:int) =
    if self#has_blockcost cmsix pc then
      H.find (H.find blockcosts cmsix) pc 
    else
      let cms = retrieve_cms cmsix in
      raise (JCH_failure
	       (LBLOCK [ STR "no block cost found for pc = " ; INT pc ;
			 STR " for method " ; cms#toPretty ]))

  method has_run_method (cmsix:int) (pc:int) =
    (H.mem runmethods cmsix) && (H.mem (H.find runmethods cmsix) pc)

  method get_run_method (cmsix:int) (pc:int) =
    if self#has_run_method cmsix pc then
      H.find (H.find runmethods cmsix) pc 
    else
      let cms = retrieve_cms cmsix in
      raise (JCH_failure
	       (LBLOCK [ STR "no run method class found for pc = " ; INT pc ;
			 STR " for method " ; cms#toPretty ]))

  method has_methodcost (cmsix:int) = H.mem methodcosts cmsix

  method get_methodcost (cmsix:int) =
    if self#has_methodcost cmsix then H.find methodcosts cmsix else
      let cms = retrieve_cms cmsix in
      raise (JCH_failure
	       (LBLOCK [ STR "no method cost found for " ; cms#toPretty ]))

  method get_callees (cmsix:int) (pc:int) =
    if H.mem callees cmsix then
      if H.mem (H.find callees cmsix) pc then
	H.find (H.find callees cmsix) pc 
      else
	[]
    else
      []

  method get_nopreplacements (cmsix:int) =
    if H.mem nopreplacements cmsix then
      H.find nopreplacements cmsix
    else
      []

  method private cmsix_bounds_to_pretty (cmsix,cmsixbounds) =
    let pcbounds = H.fold (fun k v a -> (k,v) :: a) cmsixbounds [] in
    let pcbounds_to_pretty (pc,jtermrange) =
      LBLOCK [ INDENT(3, LBLOCK [ INT pc ; STR ": " ; jtermrange#toPretty ; NL ]) ] in
    let cms = retrieve_cms cmsix in
    LBLOCK [ cms#toPretty ; NL ;
             LBLOCK (List.map pcbounds_to_pretty pcbounds) ; NL ]

  method private bounds_to_pretty =
    let cmsixbounds = H.fold (fun k v a -> (k,v) :: a) bounds [] in
    LBLOCK (List.map self#cmsix_bounds_to_pretty cmsixbounds)

  method toPretty = self#bounds_to_pretty
    
	
end

let userdata = new userdata_t
