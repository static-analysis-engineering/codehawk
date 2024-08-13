(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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

(* chutil *)
open CHLogger
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBcDictionary
open JCHDictionary
open JCHJTDictionary

(* jchpre *)
open JCHAnnotationsPre
open JCHApplication
open JCHBCFunction
open JCHBytecodeData
open JCHBytecodeLocation
open JCHPreAPI
open JCHPreFileIO
open JCHTaintOrigin
open JCHXmlUtil

module H = Hashtbl


let cd = JCHDictionary.common_dictionary


class method_invariants_t (cmsId:int) =
object

  val pctable = H.create 3
  (* val invtable = new method_invariant_table_t *)
  val cms = retrieve_cms cmsId

  method add_invariants invs =
    List.iter (fun (pc,xl) -> H.add pctable pc xl) invs

  method get_invariants (pc:int) =
    if H.mem pctable pc then H.find pctable pc else []

  method write_xml (node:xml_element_int) =
    let invs = H.fold (fun pc xl acc -> (pc,xl) :: acc) pctable [] in
    let invs = List.sort (fun (pc1,_) (pc2,_) -> Stdlib.compare pc1 pc2) invs in
    node#appendChildren (List.map (fun (pc,xl) ->
        let pcnode = xmlElement "pc-invs" in
        begin
          jtdictionary#write_xml_relational_expr_list pcnode xl;
          pcnode#setIntAttribute "pc" pc;
          pcnode
        end) invs)

  method read_xml (node:xml_element_int) =
    List.iter (fun n ->
        let pc = n#getIntAttribute "pc" in
        let xl = jtdictionary#read_xml_relational_expr_list n in
        H.add pctable pc xl) (node#getTaggedChildren "pc-invs")

end


class method_taints_t (_cmsId: int):method_taints_int =
object (self)

  val pctable = H.create 3    (* pc -> tainted_variable_ids index *)

  method add_taints (taints:(int * (variable_t * taint_origin_set_int) list) list) =
    List.iter (fun (pc,tl) ->
      let pctaints = ref [] in
      begin
	List.iter (fun (var,t1) ->
            let tdata = { tvar = var; untrusted = t1#get_origins } in
            let vindex = taint_dictionary#index_tainted_variable tdata in
            let tvar = get_tainted_variable vindex in
	    pctaints := tvar#index :: !pctaints) tl;
	(match !pctaints with
         | [] -> ()
         | _ ->  H.add pctable pc !pctaints)
      end) taints

 method get_taint (pc:int) =
    if H.mem pctable pc then
      let tvarindices = H.find pctable pc in
      List.map get_tainted_variable tvarindices
    else
      []

  (* return the number of tainted loop counter variables at this pc *)
  method get_loopcounter_taint_level (pc:int) =
    List.length (List.filter (fun (tv) ->
      let vname = tv#getvariable#getName#getBaseName in
      String.length vname > 2
      && vname.[0] == 'l'
      && vname.[1] = 'c'
      && tv#may_be_tainted) (self#get_taint pc))

  method write_xml (node:xml_element_int) =
    let pctaints = H.fold (fun k v acc -> (k,v) :: acc) pctable [] in
    let pctaints =
      List.sort (fun (pc1,_) (pc2,_) -> Stdlib.compare pc1 pc2) pctaints in
    node#appendChildren
      (List.map (fun (pc, ids) ->
           let pcnode = xmlElement "pcn" in
           begin
             taint_dictionary#write_xml_tainted_variable_ids pcnode ids;
             pcnode#setIntAttribute "pc" pc;
             pcnode
           end) pctaints)

  method private read_xml (node:xml_element_int) =
    try
      List.iter (fun n ->
          let pc = n#getIntAttribute "pc" in
          let ids = taint_dictionary#read_xml_tainted_variable_ids n in
          H.add pctable pc ids) (node#getTaggedChildren "pcn")
    with
    | JCH_failure p ->
       begin
         pr_debug [STR "Error in method_taints#read_xml: "; p; NL];
         raise (JCH_failure p)
       end

  method pc_to_pretty (pc:int) =
    LBLOCK (List.map (fun tv -> LBLOCK [tv#toPretty; NL]) (self#get_taint pc))

end


let rec write_xml_summary_value_type (node:xml_element_int) (v:value_type_t) =
  match v with
  | TBasic bt -> node#appendChildren [xmlElement (java_basic_type_to_string bt)]
  | TObject ot -> write_xml_summary_object_type node ot

and write_xml_summary_object_type (node:xml_element_int) (v:object_type_t) =
  let append = node#appendChildren in
  match v with
  | TClass cn -> append [xml_string "object" cn#name]
  | TArray vt ->
    let aNode = xmlElement "array" in
    begin write_xml_summary_value_type aNode vt; append [aNode] end


let write_xml_summary_constant_value (node:xml_element_int) (v:constant_value_t) =
  let append = node#appendChildren in
  let appendstr tag key v = append [xml_attr_string tag key v] in
  match v with
  | ConstString s ->
    let snode = xmlElement "string" in
    JCHXmlUtil.write_xml_constant_string snode "value" s
    (* appendstr "string" "value" s  *)
  | ConstInt i   -> appendstr "int" "value" (Int32.to_string i)
  | ConstFloat f -> appendstr "float" "value" (Printf.sprintf "%f" f)
  | ConstLong l  -> appendstr "long" "value" (Int64.to_string l)
  | ConstDouble d -> appendstr "double" "value" (Printf.sprintf "%f" d)
  | ConstClass ot -> write_xml_summary_object_type node ot


let write_xml_loop_calls (node:xml_element_int) cms calls =
  begin
    node#appendChildren (List.map (fun (cnIx,msIx,pc) ->
      let cNode = xmlElement "call" in
      let seti = cNode#setIntAttribute in
      let set = cNode#setAttribute in
      let loc = get_bytecode_location cms#index pc in
      let iInfo = app#get_instruction loc in
      let targets = if iInfo#has_method_target then
	  let mtargets = (iInfo#get_method_target ())#get_all_targets in
	  List.map (fun m -> m#get_index) mtargets
	else
	  [] in
      let tNode = xmlElement "targets" in
      begin
	cNode#appendChildren [tNode];
	tNode#appendChildren (List.map (fun t ->
	  let mNode = xmlElement "tgt" in
	  begin mNode#setIntAttribute "cms-ix" t; mNode end) targets);
	seti "cn-ix" cnIx;
	seti "ms-ix" msIx;
	seti "pc" pc;
	set "name" (retrieve_ms msIx)#name;
	cNode
      end) calls);
    node#setIntAttribute "count" (List.length calls)
  end


let write_xml_loopinfo
      (node:xml_element_int) (linfo:loop_info_t) (mInfo:method_info_int) =
  let iinode = xmlElement "inner-loops" in
  let oonode = xmlElement "outer-loops" in
  let jjnode = xmlElement "jump-conditions" in
  let ccnode = xmlElement "calls" in
  let seti = node#setIntAttribute in
  let exitconditions = List.map (fun pc ->
    let offset = get_offset mInfo pc in
    (pc,offset,fst (get_cfg_tf_annotations mInfo pc))) linfo.li_cond_pcs in
  begin
    iinode#appendChildren (List.map (fun (s,e) ->
      let iNode = xmlElement "inner-loop" in
      let seti = iNode#setIntAttribute in
      begin seti "first-pc" s; seti "last-pc" e; iNode end) linfo.li_inner_loops);
    oonode#appendChildren (List.map (fun (s,e) ->
      let oNode = xmlElement "outer-loop" in
      let seti = oNode#setIntAttribute in
      begin seti "first-pc" s; seti "last-pc" e; oNode end) linfo.li_outer_loops);
    jjnode#appendChildren (List.map (fun (pc,offset,c) ->
      let jNode = xmlElement "jump-cond" in
      begin
	jNode#setIntAttribute "pc" pc;
	jNode#setIntAttribute "offset" offset;
	jNode#setAttribute "cond" c;
	jNode
      end) exitconditions);
    write_xml_loop_calls ccnode mInfo#get_class_method_signature linfo.li_calls;
    node#appendChildren [iinode; oonode; jjnode; ccnode];
    iinode#setIntAttribute "size" (List.length linfo.li_inner_loops);
    oonode#setIntAttribute "size" (List.length linfo.li_outer_loops);
    seti "first-pc" linfo.li_first_pc;
    seti "entry-pc" linfo.li_entry_pc;
    seti "last-pc" linfo.li_last_pc;
    seti "instrs" linfo.li_instr_count;
    seti "exits" (List.length linfo.li_cond_pcs);
    seti "depth" (List.length linfo.li_inner_loops);
    (match linfo.li_max_iterations with
    | [] -> ()
    | l ->
      let mNode = xmlElement "max-iterations" in
      begin
	mNode#appendChildren (List.map (fun j ->
	  let jNode = xmlElement("max-it") in
	  begin
	    jtdictionary#write_xml_jterm jNode j;
	    jNode
	  end) l);
	node#appendChildren [mNode];
      end);
  end


let write_xml_variable_table (node:xml_element_int) (mInfo:method_info_int) =
  if mInfo#has_local_variable_table then
    let vtable = mInfo#get_local_variable_table in
    let vtable =
      List.sort (fun (_,_,_,_,l1) (_,_,_,_,l2) -> Stdlib.compare l1 l2) vtable in
    node#appendChildren (List.map (fun (startpc,length,name,ty,index) ->
      let sNode = xmlElement "slot" in
      let seti = sNode#setIntAttribute in
      begin
	seti "spc" startpc;
	cd#write_xml_string ~tag:"iname" sNode name;
        cd#write_xml_value_type sNode ty;
	seti "epc" (startpc + length);
	seti "vix" index;
	sNode
      end) vtable)
  else
    ()


let write_xml_method_cfg (node:xml_element_int) (mInfo:method_info_int) =
  let (blocks,succ) = get_bc_function_basic_blocks mInfo in
  let cfglooplevels = get_cfg_loop_levels mInfo blocks succ in
  let getcond pc =
    if is_conditional_jump mInfo pc then
      Some (get_cfg_tf_annotations mInfo pc)
    else
      None in
  let bbNode = xmlElement "blocks" in
  let eeNode = xmlElement "edges" in
  begin
    bbNode#appendChildren (List.map (fun b ->
      let bNode = xmlElement "bblock" in
      let set = bNode#setAttribute in
      let seti = bNode#setIntAttribute in
      begin

	(if H.mem cfglooplevels b#get_firstpc then
	    let levels = H.find cfglooplevels b#get_firstpc in
	    let llNode = xmlElement "loop-levels" in
	    begin
	      llNode#appendChildren (List.map (fun l ->
		let lNode = xmlElement "level" in
		let seqnr = l#getSeqNumber in
		begin
		  lNode#setIntAttribute "pc" seqnr;
		  lNode
		end) levels);
	      bNode#appendChildren [llNode]
	    end);
	(match getcond b#get_lastpc with
	 | Some (tc,fc) ->
            begin
              set "tcond" (replace_control_characters tc);
              set "fcond" (replace_control_characters fc)
            end
	| _ -> ());
	seti "first-pc" b#get_firstpc;
	seti "last-pc" b#get_lastpc;
	bNode
      end) blocks);
    eeNode#appendChildren (List.map (fun (src,tgt) ->
      let eNode = xmlElement "edge" in
      let seti = eNode#setIntAttribute in
      begin
	seti "src" src;
	seti "tgt" tgt;
	eNode
      end) succ);
    node#appendChildren [bbNode; eeNode]
  end


let write_xml_exception_handlers (node:xml_element_int) (mInfo:method_info_int) =
  let etable = mInfo#get_exception_table in
  node#appendChildren (List.map (fun h ->
    let hNode = xmlElement "handler" in
    let seti = hNode#setIntAttribute in
    begin
      (match h#catch_type with
      | Some cn -> seti "cnix" cn#index
      | _ -> ());
      seti "start" h#h_start;
      seti "end" h#h_end;
      seti "pc" h#handler;
      hNode
    end) etable)


let save_xml_method_bc (d:bcdictionary_int) mInfo =
  let cms = mInfo#get_class_method_signature in
  let node = xmlElement "method" in
  let iiNode = xmlElement "instructions" in
  let vtNode = xmlElement "variable-table" in
  let eeNode = xmlElement "exception-handlers" in
  let cNode = xmlElement "cfg" in
  begin
    write_xml_bc_instructions d iiNode mInfo;
    write_xml_variable_table vtNode mInfo;
    write_xml_method_cfg cNode mInfo;
    write_xml_exception_handlers eeNode mInfo;
    node#appendChildren [vtNode; cNode; eeNode; iiNode];
    save_method_xml_file cms node "bc"
  end


let write_xml_method_analysis_results
      (node:xml_element_int)
      (cms:class_method_signature_int)
      (loops:loop_info_t list) =
  let mInfo = app#get_method cms in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let llNode = xmlElement "loops" in
  begin
    llNode#appendChildren (List.map (fun linfo ->
      let lnode = xmlElement "loop" in
      begin write_xml_loopinfo lnode linfo mInfo; lnode end) loops);
    llNode#setIntAttribute "count" (List.length loops);
    append [llNode];
    (if (List.length loops) > 0 then seti "max-depth" (get_max_loop_levels mInfo));
    seti "cmsix" cms#index;
    sety "final" mInfo#is_final;
    sety "abstract" mInfo#is_abstract;
    sety "native" mInfo#is_native;
    sety "synchronized" mInfo#is_synchronized;
    sety "static" mInfo#is_static;
    sety "bridge" mInfo#is_bridge;
    set "access" (access_to_string mInfo#get_visibility);
  end


let write_xml_summary_field (node:xml_element_int) (cfs:class_field_signature_int) =
  let fInfo =
    try
      app#get_field cfs
    with
    | JCH_failure p ->
       begin
         ch_error_log#add
           "missing field in analysis-results"
           (LBLOCK [cfs#toPretty; STR ": "; p]);
         raise (JCH_failure (LBLOCK [STR "analysis-results: "; p]))
       end in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let sety key v = if v then set key "yes" else () in
  begin
    (if fInfo#has_value then
	let vNode = xmlElement "value" in
	begin
          write_xml_summary_constant_value vNode fInfo#get_value;
          append [vNode]
        end);
    sety "static" fInfo#is_static;
    sety "final" fInfo#is_final;
    sety "not-null" fInfo#is_not_null;
    set "access" (access_to_string fInfo#get_visibility);
    seti "cfsix" cfs#index
  end


class class_analysis_results_t (cInfo:class_info_int):class_analysis_results_int =
object (self)

  val invariants = H.create 3     (* cmsId -> method_invariants_int *)
  val taintorigins = H.create 3   (* cmsId -> method_taints_int *)
  val returntaints = H.create 3   (* cmsId -> (taint_origin_set_int * taint_origin_set_int) option *)
  val loops = H.create 3          (* cmsId -> loop_info_t list *)

  method set_method_invariants (cmsId:int) (invs:(int * relational_expr_t list) list) =
    let minvs = new method_invariants_t cmsId in
    begin
      minvs#add_invariants invs;
      H.add invariants cmsId minvs
    end

  method set_method_taint_origins
    (cmsId:int)
    (taints:(int * (variable_t * taint_origin_set_int) list) list) =
    let mtaints = new method_taints_t cmsId in
    begin
      mtaints#add_taints taints;
      H.add taintorigins cmsId mtaints
    end

  method set_method_return_origins
    (cmsId:int) (origins:taint_origin_set_int option) =
    H.add returntaints cmsId origins

  method set_method_loops (cmsId:int) (loopinfos: loop_info_t list) =
    H.add loops cmsId loopinfos

  method private write_xml_class_analysis_results
    (node:xml_element_int) (cInfo:class_info_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let sety tag v = if v then set tag "yes" else () in
    let cn = cInfo#get_class_name in
    let mmNode = xmlElement "methods" in
    let ffNode = xmlElement "fields" in
    let bbNode = xmlElement "bootstrap-methods" in
    let cfss = List.map (fun fs -> make_cfs cn fs) cInfo#get_fields_defined in
    let cfss =
      List.sort (fun cfs1 cfs2 -> Stdlib.compare cfs1#name cfs2#name) cfss in
    let interfaces = app#get_all_interfaces cn in
    let cmss = List.map (fun ms -> make_cms cn ms) cInfo#get_methods_defined in
    let bootstrapmethods = cInfo#get_bootstrap_methods in
    begin
      bbNode#appendChildren (
          List.map (fun bm ->
              let bNode = xmlElement "bsm" in
              begin
                common_dictionary#write_xml_bootstrap_method_data bNode bm#get_data;
                bNode
              end) bootstrapmethods);
      mmNode#appendChildren
        (List.map (fun cms ->
	     let cmsId = cms#index in
	     let mNode = xmlElement "method" in
	     let loops = if H.mem loops cmsId then H.find loops cmsId else [] in
	     begin
	       write_xml_method_analysis_results mNode cms loops ;
	       mNode
	     end)
           (List.sort (fun cms1 cms2 -> Stdlib.compare cms1#name cms2#name) cmss));
      ffNode#appendChildren (List.map (fun cfs ->
	let fNode = xmlElement "field" in
	begin write_xml_summary_field fNode cfs; fNode end) cfss);
      (match interfaces with [] -> () | _ ->
	let iiNode = xmlElement "interfaces" in
	begin
	  iiNode#appendChildren (List.map (fun i ->
	    xml_string "implements" i#name) interfaces);
	  append [iiNode]
	end);
      append [ffNode; bbNode; mmNode];
      (if cInfo#has_super_class then
	  seti "super-ix" cInfo#get_super_class#index);
      sety "final" cInfo#is_final;
      sety "abstract" cInfo#is_abstract;
      sety "immutable" cInfo#is_immutable;
      seti "ix" cn#index
    end

  method private save_xml_method_invariants (cms:class_method_signature_int) =
    let node = xmlElement "method" in
    if H.mem invariants cms#index then
    begin
      (H.find invariants cms#index)#write_xml node;
      save_method_xml_file cms node "invs"
    end

  method private save_xml_method_taints (cms:class_method_signature_int) =
    let node = xmlElement "method" in
    if H.mem taintorigins cms#index then
    begin
      (H.find taintorigins cms#index)#write_xml node;
      save_method_xml_file cms node "taint"
    end

  method private save_xml_method_loops (cms:class_method_signature_int) =
    let node = xmlElement "method" in
    let mInfo = app#get_method cms in
    let llnode = xmlElement "loops" in
    if H.mem loops cms#index then
      begin
	llnode#appendChildren (List.map (fun linfo ->
	  let lnode = xmlElement "loop" in
	  begin
            write_xml_loopinfo lnode linfo mInfo;
            lnode
          end) (H.find loops cms#index));
	node#appendChildren [llnode];
      save_method_xml_file cms node "loops"
    end

  method save_xml_class =
    if cInfo#is_stubbed || cInfo#is_missing then () else
      let _ = pr_debug [STR "  - "; cInfo#get_class_name#toPretty; NL] in
      let d = mk_bcdictionary () in
      let cn = cInfo#get_class_name in
      let node = xmlElement "class" in
      let dnode = xmlElement "bcdictionary" in
      let appdir = get_stac_analysis_app_dir () in
      begin
	self#write_xml_class_analysis_results node cInfo;
	List.iter (fun ms ->
            let cms = make_cms cn ms in
	    try
	      let mInfo = app#get_method cms in
	      if mInfo#has_bytecode then
	        begin
	          self#save_xml_method_invariants cms;
	          self#save_xml_method_taints cms;
	          self#save_xml_method_loops cms;
	          save_xml_method_bc d mInfo;
	        end
	    with JCH_failure p ->
              pr_debug [
                  STR "Failure when saving method ";
                  cms#toPretty;
                  STR ": ";
                  p;
                  NL]
          ) cInfo#get_methods_defined;
        d#write_xml dnode;
        node#appendChildren [dnode];
        save_class_xml_file appdir cInfo#get_class_name node "class";
      end

end


class application_analysis_results_t:application_analysis_results_int =
object (self)

  val invariants = H.create 3     (* cmsId -> method_invariants_int *)
  val taintorigins = H.create 3   (* cmsId -> method_taints_int *)
  val returntaints = H.create 3   (* cmsId -> (taint_origin_set_int * taint_origin_set_int) option *)
  val loops = H.create 3          (* cmsId -> loop_info_t list *)

  method private load_taints (cmsId:int) =
    if self#has_taints cmsId then () else
    let mtaints = new method_taints_t cmsId in
    try
      begin
	(match load_method_xml_file (retrieve_cms cmsId) "taint" with
	| Some node -> (mtaints#read_xml node)
	| _ ->
	  chlog#add "taint results not found" (retrieve_cms cmsId)#toPretty);
	H.add taintorigins cmsId mtaints
      end
    with
    | XmlDocumentError (line,col,p) ->
      begin
	pr_debug [STR "Xml error in taints for "; (retrieve_cms cmsId)#toPretty;
		   STR ": "; p; NL];
	raise (XmlDocumentError (line,col,p))
      end

  method get_taints (cmsId:int) =
    begin self#load_taints cmsId; H.find taintorigins cmsId end

  method private load_invariants (cmsId:int) =
    let cms = retrieve_cms cmsId in
    if self#has_invariants cmsId then () else
      try
	let minvs = new method_invariants_t cmsId in
	begin
	  (match load_method_xml_file cms "invs" with
	  | Some node -> minvs#read_xml node
	  | _ ->
	    chlog#add "invariant results not found" cms#toPretty);
	  H.add invariants cmsId minvs
	end
      with
      | XmlDocumentError (line,col,p) ->
	begin
	  pr_debug [STR "Xml error in invariants "; cms#toPretty;
		     STR ": "; p; NL];
	  raise (XmlDocumentError (line,col,p))
	end

  method get_invariants (cmsId:int) =
    begin self#load_invariants cmsId; H.find invariants cmsId end

  method has_taints (cmsId:int) = H.mem taintorigins cmsId

  method has_invariants (cmsId:int) = H.mem invariants cmsId

end


let init_class_analysis_results = new class_analysis_results_t

let application_analysis_results = new application_analysis_results_t
