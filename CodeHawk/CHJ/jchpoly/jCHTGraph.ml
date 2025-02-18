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
open CHUtils
open CHPretty
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecodeLocation
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI
open JCHTaintOrigin

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

(* jchpoly *)
open JCHTNode

let dbg = ref false

let call_index = ref (-1) (* index for the CALL nodes *)

let get_call_args args =
  let return_opt = ref None in
  let other_vars = ref [] in
  let get_vars (s, v, _m) =
    match s with
    | "return" -> return_opt := Some v
    | "throw" -> ()
    | _ -> other_vars := v :: !other_vars in
  List.iter get_vars args ;
  (!return_opt, exception_var, List.rev !other_vars)


class collect_taint_var_graph_t
    (_var_to_loops: IntCollections.set_t VariableCollections.table_t)
    (bound_to_loops: IntCollections.set_t VariableCollections.table_t)
    (proc_info: JCHProcInfo.jproc_info_t) =
  object (self:_)
    inherit code_walker_t as super

    val jvar_infos =   proc_info#get_jvar_infos
    val proc_name = proc_info#get_name
    val proc = proc_info#get_procedure
    val current_state = ref state_name_sym

    (* read var -> write var *)
    val rwedges = new TaintNodeCollections.table_t

    (* same edges, in reverse order *)
    val wredges = new TaintNodeCollections.table_t

    (* set of all fields referenced *)
    val fields = new TaintNodeCollections.set_t

    (* set of all variables in invocations *)
    val call_nodes = new TaintNodeCollections.set_t

    (* set of all call nodes *)
    val calls = new TaintNodeCollections.set_t

    (* set of all variable nodes *)
    val var_nodes = new TaintNodeCollections.set_t

    (* vars in an eq node -> eq node *)
    val var_to_eq_nodes = new VariableCollections.table_t

    (* var1 -> var2 -> states where var1 = var2 *)
    val var_to_var_to_eqs = proc_info#get_var_to_var_to_eqs

    (* var1 -> var2 -> states where var1 < var2 or var1 <= var2 *)
    val var_to_var_to_ineqs = proc_info#get_var_to_var_to_ineqs

    (* var -> state -> nodes that depend on var in state *)
    val var_to_state_to_nodes = new VariableCollections.table_t

    method get_edges = rwedges
    method get_rev_edges = wredges
    method get_fields = fields
    method get_call_nodes = call_nodes
    method get_calls = calls
    method get_var_nodes = var_nodes

    method private mk_vnode v =
      let node = mk_var_node proc_name v in
      var_nodes#add node;
      node

    (* Adds a node from rn to wn *)
    method private add_edge_to_tables wn rn =
      let add_to_table table n1 n2 =
	match table#get n1 with
	| Some set -> set#add n2
	| _ -> table#set n1 (TaintNodeCollections.set_of_list [n2]) in
      add_to_table rwedges rn wn;
      add_to_table wredges wn rn

    method private addE wnode rnode =
      self#add_edge_to_tables wnode rnode;
      let add_eq_nodes enode =
	match enode#get_node_type with
	| TN_VAR_EQ (_, _, _, statelist) ->
           let states = new SymbolCollections.set_t in
           let _ = states#addList statelist in
	   if states#has !current_state then
             self#add_edge_to_tables wnode enode
	   else
             ()
	| _ -> () in
      match rnode#get_node_type with
	| TN_VAR (_, v, _) ->
	    begin
	      let table =
		match var_to_state_to_nodes#get v with
		| Some table -> table
		| _ ->
		    let t = new SymbolCollections.table_t in
		    var_to_state_to_nodes#set v t;
		    t in
	      (match table#get !current_state with
	      | Some set -> set#add wnode
	      | _ ->
                 table#set
                   !current_state (TaintNodeCollections.set_of_list [wnode]));
	      (match var_to_eq_nodes#get v with
	      |	Some set -> set#iter add_eq_nodes
	      |	None -> ());
	    end
	| _ -> ()

    method private is_unreachable n =
      match n#get_node_type with
      | TN_VAR (cmsix, v, _) ->
         let proc_name = make_procname cmsix in
         JCHNumericAnalysis.is_unreachable proc_name v
      | _ -> false

    method private add_edge wn rn =
      if self#is_unreachable wn || self#is_unreachable rn then
        begin
	  if !dbg then
            pr__debug[STR "no edge added because it is unreachable "; NL];
        end
      else if rn#is_const_var then
        ()
      else
        self#addE wn rn

    method private add_cedge no_back_edge wn rn =
      if self#is_unreachable wn || self#is_unreachable rn then
        ()
      else if no_back_edge then
        self#add_edge wn rn
      else
	begin
	  self#add_edge wn rn;
	  self#add_edge rn wn
	end

    method private add_var_edge w r =
      self#add_edge (self#mk_vnode w) (self#mk_vnode r)

    method private add_var_edges ws rs =
      List.iter (fun w -> List.iter (self#add_var_edge w) rs) ws

    method private add_eq_nodes =
      let add_var_eq var enode =
	match var_to_eq_nodes#get var with
	| Some set -> set#add enode
	| None ->
           var_to_eq_nodes#set var (TaintNodeCollections.set_of_list [enode]) in
      let add_eq var1 var2 (states:SymbolCollections.set_t) =
	if var1#getIndex > var2#getIndex then
          ()  (* add an equation only once *)
	else
	  let enode = mk_eq_node proc_name var1 var2 states in
	  self#add_edge enode (self#mk_vnode var1);
	  self#add_edge enode (self#mk_vnode var2);
	  add_var_eq var1 enode;
	  add_var_eq var2 enode;
	  match var_to_state_to_nodes#get var1 with
	  | Some table ->
	      let add_state_to_nodes state nodes =
		if states#has state then
		  nodes#iter (fun nd -> self#add_edge_to_tables nd enode)
	      in
	      table#iter add_state_to_nodes
	  | _ -> () in
      let add_eqs var table =
	table#iter (add_eq var) in
      var_to_var_to_eqs#iter add_eqs

    (* is_meta_meth is an argument needed for the stonesoup unit tests to work *)

    method private add_call_edges pc msig (iInfo:instruction_info_int) args =
      let meth_name = msig#name in
      let cinfo = app#get_method proc_info#get_method#get_class_method_signature in
      let (return_opt, _throw, call_args) = get_call_args args in
      let mk_return_edge call_node =
	match return_opt with
	| Some v ->
	    let v_node = self#mk_vnode v in
	    self#add_cedge (self#is_immutable v) v_node call_node
	| _ ->
	    () in
      let mk_edge call_node v =
	let v_node = self#mk_vnode v in
	call_nodes#add v_node;
	if meth_name = "<init>" then self#add_cedge false call_node v_node
	else self#add_cedge (self#is_immutable v) call_node v_node in

      let add_invoc_edges tinfo =
	if JCHSystem.jsystem#not_analyzed_bad tinfo#get_procname#getSeqNumber then
	  begin
	    let add_origin v =
	      let origs =
                mk_taint_origin_set
                  [mk_call_origin tinfo "not_analyzed" proc_name pc] in
	      let _ = (self#mk_vnode v)#add_untrusted_origins origs in
	      () in
	    List.iter add_origin call_args
	  end
	else
	  begin
	    let index =
	      incr call_index;
	      !call_index in
	    let call_node =
              mk_call_node index pc cinfo tinfo return_opt call_args in
	    calls#add call_node;
	    mk_return_edge call_node;
	    List.iter (mk_edge call_node) call_args
	  end in

      let target = iInfo#get_method_target () in
      if target#is_top then
	begin
	  let index =
	    incr call_index;
	    !call_index in
	  let unknown_call_node =
            mk_unknown_call_node index pc cinfo return_opt call_args in
	  mk_return_edge unknown_call_node;
	  List.iter (mk_edge unknown_call_node) call_args;
	  let add_origin v =
	    if not (self#is_immutable v) then
	      begin
		let origs =
                  mk_taint_origin_set
                    [mk_top_target_origin target proc_name pc] in
		let _ = (self#mk_vnode v)#add_untrusted_origins origs in
		()
	      end in
	  List.iter add_origin call_args;
	  match return_opt with
	  | Some return ->
	     let origs = mk_taint_origin_set
                           [mk_top_target_origin target proc_name pc] in
	      let _ = (self#mk_vnode return)#add_untrusted_origins origs in
	      ()
	  | _ -> ()
	end;
      List.iter add_invoc_edges target#get_valid_targets

    method private is_immutable v =
      let vtypes = (proc_info#get_jvar_info v)#get_types in
      let res = JCHTypeUtils.is_immutable_type vtypes in
      res

    method private taint_field
                     fnode (fInfo:field_info_int) (pc:int) =
      let is_not_analyzed cms =
	JCHSystem.jsystem#not_analyzed_bad cms#index in
      if List.exists is_not_analyzed (fInfo#get_writing_methods) then
	begin
	  let origs =
            mk_taint_origin_set
              [mk_field_origin
                 fInfo "writing method not analyzed" proc_name pc] in
	  fnode#set_untrusted_origins origs
	end
      else if fInfo#is_accessible_to_stubbed_methods then
	begin
	  let origs =
            mk_taint_origin_set
              [mk_field_origin
                 fInfo "accessible to stubbed methods" proc_name pc] in
	  fnode#set_untrusted_origins origs
	end
      else
	begin
	  let cn = fInfo#get_class_name in
	  let fs = fInfo#get_class_signature#field_signature in
	  match fs#descriptor with
	  | TObject TClass cn1 ->
	     if fs#name = "in"
                && cn1#name = "java.io.InputStream"
                && cn#name = "java.lang.System" then
		begin
		  let origs =
                    mk_taint_origin_set
                      [mk_field_origin
                         fInfo "untrusted field" proc_name pc] in
		  fnode#set_untrusted_origins origs
		end
	  | _ -> ()
	end

    method walkOperation {op_name = opname; op_args = args} =
      match opname#getBaseName with
      |	"i"
      | "ii" ->
	    begin
	      let pc = opname#getSeqNumber in
	      let cms = retrieve_cms proc_name#getSeqNumber in
	      let bcloc = get_bytecode_location cms#index pc in
	      let iInfo = app#get_instruction bcloc in
	      match iInfo#get_opcode with
	      | OpIfNull _
	      | OpIfCmpAEq _
	      | OpIfCmpANe _ -> ()
	      | OpCheckCast _ ->
		  let ref = JCHSystemUtils.get_arg_var "src1" args in
		  let ref_new_type = JCHSystemUtils.get_arg_var "dst1" args in
		  let rnode = self#mk_vnode ref in
		  let rntnode = self#mk_vnode ref_new_type in
                  begin
		    self#add_edge rntnode rnode;
		    self#add_edge rnode rntnode
                  end
	      | OpNewArray _ ->
		  let array = JCHSystemUtils.get_arg_var "ref" args in
		  let length = JCHSystemUtils.get_arg_var "length" args in
		  let anode = self#mk_vnode array in
		  let lnode = self#mk_vnode length in
		  let size_node = mk_size_node proc_name array pc in
                  begin
		    self#add_edge size_node lnode;
		    self#add_edge anode size_node
                  end
	      | OpAMultiNewArray _ ->
		  let array = JCHSystemUtils.get_arg_var "ref" args in
		  let dims = JCHSystemUtils.get_read_vars args in
		  let anode = self#mk_vnode array in
		  let dnodes = List.map self#mk_vnode dims in
		  let size_node = mk_size_node proc_name array pc in
                  begin
		    List.iter (self#add_edge size_node) dnodes;
		    self#add_edge anode size_node
                  end
	      | OpArrayLength ->
		  let array = JCHSystemUtils.get_arg_var "ref" args in
		  let length = JCHSystemUtils.get_arg_var "val" args in
		  let anode = self#mk_vnode array in
		  let lnode = self#mk_vnode length in
		  let size_node = mk_size_node proc_name array pc in
                  begin
		    self#add_edge size_node anode;
		    self#add_edge lnode size_node
                  end
	      | OpNew _
	      | OpStringConst _
	      |	OpClassConst _
	      |	OpAConstNull -> ()
	      | OpFloatConst _
	      | OpDoubleConst _ -> ()
	      | OpArrayStore _ ->
		  let array = JCHSystemUtils.get_arg_var "array" args in
		  let element = JCHSystemUtils.get_arg_var "val" args in
		  let anode = self#mk_vnode array in
		  let enode = self#mk_vnode element in
                  begin
		    self#add_edge anode enode;
		    if self#is_immutable element then
                      ()
		    else
		      self#add_edge enode anode
                  end
	      | OpArrayLoad _ ->
		  let array = JCHSystemUtils.get_arg_var "array" args in
		  let element = JCHSystemUtils.get_arg_var "val" args in
		  let index = JCHSystemUtils.get_arg_var "index" args in
		  let anode = self#mk_vnode array in
		  let enode = self#mk_vnode element in
		  let inode = self#mk_vnode index in
                  begin
		    self#add_edge enode anode;
		    self#add_edge enode inode;
		    if self#is_immutable element then
                      ()
		    else
                      self#add_edge anode enode
                  end
	      | OpPutStatic (cn, fs) ->
		let fInfo = iInfo#get_field_target in
		if JCHFields.int_field_manager#is_const_field fInfo &&
		  not (JCHFields.int_field_manager#is_dt_field cn fs)
		then
                  ()
		else
		  let fnode = mk_field_node fInfo in
		  self#taint_field fnode fInfo pc;
		  let var = JCHSystemUtils.get_arg_var "val" args in
		  let vnode = self#mk_vnode var in
                  begin
		    fields#add fnode;
		    self#add_edge fnode vnode;
		    if self#is_immutable var then
                      ()
		    else
                      self#add_edge vnode fnode;
		  end
	      | OpPutField (_cn, fsig) ->
		  let var = JCHSystemUtils.get_arg_var "val" args in
		  let ref = JCHSystemUtils.get_arg_var "ref" args in
		  let vnode = self#mk_vnode var in
		  let ref_node = self#mk_vnode ref in
		  let fnode = mk_obj_field_node proc_name ref fsig#index pc in
		  self#add_edge ref_node fnode;
		  self#add_edge fnode vnode;
		  if not (self#is_immutable var) then
		    begin
		      self#add_edge vnode fnode;
		      self#add_edge fnode ref_node;
		    end
	      | OpGetStatic (cn, fs) ->
		  let fInfo = iInfo#get_field_target in
		  let var = JCHSystemUtils.get_arg_var "val" args in
		  let vnode = self#mk_vnode var in
		  if JCHFields.int_field_manager#is_const_field fInfo
		    && not (JCHFields.int_field_manager#is_dt_field cn fs)
		  then
                    ()
		  else
		    let fnode = mk_field_node fInfo in
                    begin
		      self#taint_field fnode fInfo pc;
		      fields#add fnode;
		      self#add_edge vnode fnode;
		      if self#is_immutable var then
                        ()
		      else
                        self#add_edge fnode vnode;
		    end
	      | OpGetField (_cn, fs) ->
		  let var = JCHSystemUtils.get_arg_var "val" args in
		  let ref = JCHSystemUtils.get_arg_var "ref" args in

		  pr__debug [
                      STR "OpGetField ";
                      proc_name#toPretty;
                      STR " ";
                      ref#toPretty;
                      NL];

		  let vnode = self#mk_vnode var in
		  let ref_node = self#mk_vnode ref in
		  let fnode = mk_obj_field_node proc_name ref fs#index pc in
		  self#add_edge vnode fnode;
		  self#add_edge fnode ref_node;
		  if not (self#is_immutable var) then
		    begin
		      self#add_edge ref_node fnode;
		      self#add_edge fnode vnode;
		    end
	      | OpInvokeStatic (_, ms)
	      | OpInvokeVirtual (_, ms)
	      | OpInvokeSpecial (_, ms)
	      | OpInvokeInterface (_, ms) ->
		  self#add_call_edges pc ms iInfo args
	      | OpInvokeDynamic (_, _ms) ->
		  begin
		    let (return_opt, _, call_args) = get_call_args args in
		    match return_opt with
		    | Some return ->
			begin
			  let return_node = self#mk_vnode return in
			  let arg_nodes = List.map self#mk_vnode call_args in
			  List.iter (fun n -> self#addE return_node n) arg_nodes
			end
		    | _ -> ()
		  end
	      | OpCmpL
	      | OpCmpFL
	      | OpCmpFG
	      | OpCmpDL
	      | OpCmpDG ->
		  let src1 = JCHSystemUtils.get_arg_var "src1" args in
		  let src2 = JCHSystemUtils.get_arg_var "src2" args in
		  let dst = JCHSystemUtils.get_arg_var "dst1" args in
		  self#add_var_edges [dst] [src1; src2]
	      | OpIfEq _
	      | OpIfNe _
	      | OpIfLt _
	      | OpIfGe _
	      | OpIfGt _
	      | OpIfLe _
	      | OpIfCmpEq _
	      | OpIfCmpNe _
	      | OpIfCmpLt _
	      | OpIfCmpGe _
	      | OpIfCmpGt _
	      | OpIfCmpLe _ ->
		  let rvars = JCHSystemUtils.get_read_vars args in
		  let rnodes = List.map self#mk_vnode rvars in
		  let cond_node = mk_cond_node proc_name pc in
		  List.iter (self#add_edge cond_node) rnodes
	      | _ ->
		  let wvars =
		    List.filter
                      JCHSystemUtils.is_not_exception
                      (JCHSystemUtils.get_write_vars args) in
		  let rvars = JCHSystemUtils.get_read_vars args in
		  self#add_var_edges wvars rvars
	    end
      |	_ ->
	  ()

    method !walkCmd cmd =
      match cmd with
      |	CFG (_, cfg) ->
	  let states = cfg#getStates in
	  let walkState state_name =
	    current_state := state_name;
	    let state = cfg#getState state_name in
	    self#walkCode state#getCode in
	  List.iter walkState states
      |	ASSIGN_NUM (_x, NUM _)
      |	ASSIGN_SYM (_x, SYM _) -> ()
      |	ASSIGN_NUM (x, NUM_VAR y) ->
	  self#add_var_edge x y;  (* phi assignments *)
      |	ASSIGN_NUM (x, PLUS (y, z))
      |	ASSIGN_NUM (x, MINUS (y, z))
      |	ASSIGN_NUM (x, MULT (y, z))
      |	ASSIGN_NUM (x, DIV (y, z)) ->
	  self#add_var_edge x y;
	  self#add_var_edge x z;
      |	ASSIGN_ARRAY (x, y)
      |	ASSIGN_STRUCT (x, y)
      |	ASSIGN_SYM (x, SYM_VAR y) -> (* phi assignment ? *)
	  self#add_var_edge x y;
	  if x#getName#getBaseName = y#getName#getBaseName then
            ()
	  else if (self#is_immutable x || self#is_immutable y) then
            ()
	  else
            self#add_var_edge y x
      |	ASSIGN_NUM_ELT (a, _i, v) ->
	  self#add_var_edge a v
      |	READ_NUM_ELT (v, a, _i) ->
	  self#add_var_edge v a
      |	SHIFT_ARRAY (tgt, src, _) ->     (* only for int arrays *)
	  self#add_var_edge tgt src
      |	BLIT_ARRAYS (tgt, _tgt_o, src, _src_o, _n) ->  (* only for int arrays *)
	  self#add_var_edge tgt src
      |	SET_ARRAY_ELTS (a, _s, _n, v) ->     (*  only for int arrays *)
	  self#add_var_edge a v
      |	OPERATION op ->
	  self#walkOperation op
      |	_ -> super#walkCmd cmd

    (* tainted loop does not transfer taint to the variables
     * changes inside the loop *)
    method add_loop_edges =
      let index_to_loopn = new IntCollections.table_t in
      let var_to_node:taint_node_int VariableCollections.table_t =
        new VariableCollections.table_t in
      let get_loopn index =
	match index_to_loopn#get index with
	| Some loopn ->
	    loopn
	| None ->
	    let loop_var_name = new symbol_t ~seqnr:index "lc" in
	    let loop_var = new variable_t loop_var_name NUM_VAR_TYPE in
	    let loopn = self#mk_vnode loop_var in
	    var_to_node#set loop_var loopn;
	    index_to_loopn#set index loopn;
	    loopn in

      let add_bedge bn index =
	let loopn = get_loopn index in
	self#add_edge loopn bn in
      let add_bedges b set =
	let bn = self#mk_vnode b in
	set#iter (add_bedge bn) in
      bound_to_loops#iter add_bedges

    method private add_init_this =
      let minfo = proc_info#get_method_info in
      if minfo#is_constructor && not minfo#is_static then
	()

    method private remove_cmp_var_edges =
      let remove_from_table table node1 node2 =
	match table#get node1 with
	| Some set -> set#remove node2
	| _ -> () in
      let remove_edge rnode wnode =
	remove_from_table rwedges rnode wnode;
	remove_from_table wredges wnode rnode in
      let remove node (wnodes: TaintNodeCollections.set_t) =
	match node#get_node_type with
	| TN_VAR_EQ (_, v1, v2, _) ->
	    let vnode1 = mk_var_node proc_name v1 in
	    let vnode2 = mk_var_node proc_name v2 in
	    wnodes#iter (fun wn -> remove_edge vnode1 wn; remove_edge vnode2 wn)
	| _ -> () in
      rwedges#iter remove

    method walkProcedure (proc: procedure_int) =
      self#add_init_this;
      self#add_eq_nodes;
      super#walkCode proc#getBody;
      self#add_loop_edges

  end

class taint_graph_t
    ~(proc_name:symbol_t)
    ~(sig_nodes:taint_node_int list)
    ~(fields:TaintNodeCollections.set_t)
    ~(call_nodes:TaintNodeCollections.set_t)
    ~(calls:TaintNodeCollections.set_t)
    ~(var_nodes:TaintNodeCollections.set_t)
    ~(edges:TaintNodeCollections.set_t TaintNodeCollections.table_t)
    ~(rev_edges:TaintNodeCollections.set_t TaintNodeCollections.table_t)
    ~(sources:TaintNodeCollections.set_t) =
  object (self: 'a)

    val return_node_opt =
      let is_return tnode =
	match tnode#get_node_type with
	| TN_VAR (_, v, _) ->
	    let index = v#getIndex in
	    index = num_return_var_index || index = sym_return_var_index
	| _ -> false in
      match List.filter is_return sig_nodes  with
      |	n :: _ns -> Some n
      |	_ -> None

    val exception_node_opt =
      let is_exc tnode =
	match tnode#get_node_type with
	| TN_VAR (_, v, _) -> JCHSystemUtils.is_exception v
	| _ -> false in
      match List.filter is_exc sig_nodes  with
      |	n :: _ns -> Some n
      |	_ -> None

    val arg_nodes =
      let is_arg tnode =
	match tnode#get_node_type with
	| TN_VAR (_, v, _) ->
	    not (JCHSystemUtils.is_return v || JCHSystemUtils.is_exception v)
	| _ -> false in
      List.filter is_arg sig_nodes

    method get_proc_name = proc_name

    method get_sig_nodes =
      match (return_node_opt, exception_node_opt) with
      |	(Some return, Some exc) ->
	  exc :: return :: arg_nodes
      |	(None, Some exc) ->
	  exc :: arg_nodes
      |	(Some return, None) ->
	  return :: arg_nodes
      |	_ ->
	  arg_nodes

    method get_ret_and_arg_nodes =
      match return_node_opt with
      |	Some return ->
	  return :: arg_nodes
      |	_ ->
	  arg_nodes

    method get_return_node = return_node_opt

    method get_arg_nodes = arg_nodes

    method get_fields = fields

    method get_call_nodes = call_nodes

    method get_calls = calls

    method get_var_nodes = var_nodes

    method get_edges = edges

    method get_rev_edges = rev_edges

    method get_sources = sources

    method private add_table_edge table n1 n2 =
      match table#get n1 with
      |	Some set ->
	  set#add n2
      |	None ->
	  let set = TaintNodeCollections.set_of_list [n2] in
	  table#set n1 set

    method add_edge rn wn =
      self#add_table_edge edges rn wn;
      self#add_table_edge rev_edges wn rn;
      let _ = wn#add_untrusted_origins (rn#get_untrusted_origins) in
      ()

    method leq (a: 'a) =
      let aedges = a#get_edges in
      if edges#size > aedges#size then false
      else
	begin
	  let leq_set k =
	    let set1 = Option.get (edges#get k) in
	    match aedges#get k with
	    | Some set2 -> set1#subset set2
	    | _ -> false in
	  List.for_all leq_set edges#listOfKeys
	end

    method equal (a: 'a) =
      let aedges = a#get_edges in
      if edges#size <> aedges#size then false
      else
	begin
	  let eq_set k =
	    let set1 = Option.get (edges#get k) in
	    match aedges#get k with
	    | Some set2 -> set1#equal set2
	    | _ -> false in
	  List.for_all eq_set edges#listOfKeys
	end

    method toPretty =
      let pp_edges =
	let pp = ref [] in
	let pp_edge n (set: TaintNodeCollections.set_t) =
	  pp :=
            (LBLOCK [n#toPretty; NL;
		     INDENT
                       (5,
                        LBLOCK (List.map (fun m ->
                                    LBLOCK [m#toPretty; NL]) set#toList))])
            :: !pp in
	edges#iter pp_edge;
	!pp in
      LBLOCK [proc_name#toPretty; NL;
	       STR "signature: "; pp_list sig_nodes; NL;
	       STR "edges: "; NL; INDENT (5, LBLOCK pp_edges); NL;
	       STR "variable_nodes: "; NL;
	       INDENT
                 (5, LBLOCK(List.map (fun n ->
                                LBLOCK [n#toPretty; NL]) var_nodes#toList)); NL;
	       STR "calls: "; NL; calls#toPretty; NL]

  end

(* for investigation *)

let make_tgraph proc_info =
  let proc = proc_info#get_procedure in
  let proc_name = proc_info#get_name in
  let (var_to_loops, bound_to_loops) =
    JCHTaintLoopUtils.get_taint_loop_info proc_info in
  let collector =
    new collect_taint_var_graph_t var_to_loops bound_to_loops proc_info in
  let _ = collector#walkProcedure proc in
  let sig_nodes =
    List.map
      (mk_var_node proc_name)
      (JCHSystemUtils.get_signature_vars proc) in
  let fields = collector#get_fields in
  let call_nodes = collector#get_call_nodes in
  let calls = collector#get_calls in
  let var_nodes = collector#get_var_nodes in
  let _ = var_nodes#addList sig_nodes in
  let edges = collector#get_edges in
  let rev_edges = collector#get_rev_edges in
  let sources =  new TaintNodeCollections.set_t in
  let tgraph =
    new taint_graph_t
        ~proc_name
        ~sig_nodes
        ~fields
        ~call_nodes
        ~calls
        ~var_nodes
        ~edges
        ~rev_edges
        ~sources in
  tgraph

let mk_empty_tgraph proc_name =
  new taint_graph_t
      ~proc_name
      ~sig_nodes:[]
      ~fields:(new TaintNodeCollections.set_t)
      ~call_nodes:(new TaintNodeCollections.set_t)
      ~calls:(new TaintNodeCollections.set_t)
      ~var_nodes:(new TaintNodeCollections.set_t)
      ~edges:(new TaintNodeCollections.table_t)
      ~rev_edges:(new TaintNodeCollections.table_t)
      ~sources:(new TaintNodeCollections.set_t)


(* Graph with edges between scc's with nodes given by one representative
 * of an scc
 * It includes the transitive edges *)
class scc_taint_graph_t =
  object (self: 'a)
    val node_to_rep = new TaintNodeCollections.table_t
    val rep_to_nodes = new TaintNodeCollections.table_t
    val node_edges = new TaintNodeCollections.table_t
    val node_rev_edges = new TaintNodeCollections.table_t
    val rep_edges = new TaintNodeCollections.table_t
    val rep_rev_edges = new TaintNodeCollections.table_t
    val tainted_nodes = new TaintNodeCollections.set_t
    val dt_tainted_nodes = new TaintNodeCollections.set_t

    method private get_rep node =
      let path_nodes = new TaintNodeCollections.set_t in
      let rec go_up n =
	path_nodes#add n;
	let up_n = Option.get (node_to_rep#get n) in
	if up_n#get_index = n#get_index then n
	else go_up up_n in
      let rep = go_up node in
      if node#get_index = rep#get_index then
	path_nodes#iter (fun n -> node_to_rep#set n rep);
      rep

    method add_node_edge n1 n2 =
      node_to_rep#set n1 n1;
      node_to_rep#set n2 n2;
      if n1#get_index = n2#get_index then ()
      else
	begin
	  (match node_edges#get n1 with
	  | Some set -> set#add n2
	  | _ -> node_edges#set n1 (TaintNodeCollections.set_of_list [n2]));
	  (match node_rev_edges#get n2 with
	  | Some set -> set#add n1
	  | _ -> node_rev_edges#set n2 (TaintNodeCollections.set_of_list [n1]))
	end

    method add_node_edges (n: taint_node_int) (set: TaintNodeCollections.set_t) =
      set#iter (self#add_node_edge n)

    method private find_node_sccs visited start_node =
      let on_path = new TaintNodeCollections.set_t in
      let path = Stack.create () in
      Stack.push (start_node, None) path;
      while not (Stack.is_empty path) do
	match Stack.pop path with
	| (node, None) ->
	    begin
	      let rep = self#get_rep node in
	      if on_path#has rep then
		begin
		  let all_nexts = new TaintNodeCollections.set_t in
		  let rec unroll () =
		    let (n, next_opts) = Stack.top path in
		    let nexts = Option.get next_opts in
		    on_path#remove n;
		    if n#get_index <> rep#get_index then
		      begin
			let _ = Stack.pop path in
			all_nexts#addSet nexts;
			node_to_rep#set node rep;
			unroll ()
		      end
		    else
		      begin
			nexts#addSet all_nexts
		      end in
		  unroll ()
		end
	      else if not (visited#has node) then
		begin
		  visited#add node;
		  match node_edges#get node with
		  | Some nexts -> Stack.push (node, Some nexts#clone) path
		  | _ ->
                     Stack.push (node, Some (new TaintNodeCollections.set_t)) path
		end
	    end
	| (node, Some nexts) ->
	    if nexts#isEmpty then
	      begin
		on_path#remove node;
		if Stack.is_empty path then ()
		else let (parent, _) = Stack.top path in on_path#remove parent
	      end
	    else
	      begin
		let node' = Option.get nexts#choose in
		nexts#remove node';
		Stack.push (node, Some nexts) path;
		on_path#add node;
		Stack.push (node', None) path
	      end
      done

    method find_sccs =
      let visited = new TaintNodeCollections.set_t in
      let find_from_node node _next_nodes =
	if visited#has node then self#find_node_sccs visited node in
      node_edges#iter find_from_node

    method private make_rep_to_nodes =
      let process node rep =
	match rep_to_nodes#get rep with
	| Some set -> set#add node
	| _ ->
           rep_to_nodes#set rep (TaintNodeCollections.set_of_list [node]) in
      node_to_rep#iter process

    method get_nodes rep =
      match rep_to_nodes#get rep with
      |	Some set -> set
      |	_ -> TaintNodeCollections.set_of_list [rep]

    method private make_rep_graph_ =
      let add_edge node next_nodes =
	let rep = Option.get (node_to_rep#get node) in
	let next_reps =
	  match rep_edges#get rep with
	  | Some set -> set
	  | _ ->
	      let set = new TaintNodeCollections.set_t in
	      rep_edges#set rep set;
	      set in
	let add n =
	  let r = Option.get (node_to_rep#get n) in
	  if r#get_index <> rep#get_index then
	    begin
	      next_reps#add r;
	      match rep_rev_edges#get r with
	      |	Some set -> set#add rep
	      |	_ ->
                 rep_rev_edges#set r (TaintNodeCollections.set_of_list [rep])
	    end in
	next_nodes#iter add in
      node_edges#iter add_edge


    method get_terminals =
      let terminals = new TaintNodeCollections.set_t in
      let add rep _prevs =
	match rep_edges#get rep with
	| Some set -> if set#isEmpty then terminals#add rep
	| _ -> terminals#add rep in
      rep_rev_edges#iter add;
      terminals

    method add_transitive_edges =
      let work_list = self#get_terminals in
      let consumable_edges = new TaintNodeCollections.table_t in
      let add_edges rep nexts =
	consumable_edges#set rep nexts#clone in
      rep_edges#iter add_edges;
      while not work_list#isEmpty do
	let rep = Option.get work_list#choose in
	work_list#remove rep;
	match rep_rev_edges#get rep with
	| Some prevs ->
	    let add_to_work_list r =
	      let nexts = Option.get (consumable_edges#get r) in
	      nexts#remove rep;
	      if nexts#isEmpty then work_list#add r in
	    prevs#iter add_to_work_list
	| _ -> ()
      done

    method make_rep_graph =
      self#make_rep_to_nodes;
      self#make_rep_graph_;
      self#add_transitive_edges

    method private is_untrusted_field (fInfo:field_info_int) =
      let cn = fInfo#get_class_name in
      let fs = fInfo#get_class_signature#field_signature in
      match fs#descriptor with
      |	TObject TClass cn1 ->
	 fs#name = "in"
         && cn1#name = "java.io.InputStream"
         && cn#name = "java.lang.System"
      |	_ -> false

    method private is_untrusted node =
      match node#get_taint with
      |	Some t -> t = 1
      | _ -> false

    method private taint_scc rep =
      let nodes = Option.get (rep_to_nodes#get rep) in
      let untrusted_origs = ref (mk_taint_origin_set []) in
      let add_taint n =
	untrusted_origs :=
          join_taint_origin_sets !untrusted_origs n#get_untrusted_origins in
      (match rep_rev_edges#get rep with
      | Some reps -> reps#iter add_taint
      | _ -> ());
      nodes#iter add_taint;
      let set_taint (n : taint_node_int) =
	let _ = n#add_untrusted_origins !untrusted_origs in
	() in
      nodes#iter set_taint

    method taint =
      let reps = rep_to_nodes#listOfKeys in
      let reps_with_edges = rep_rev_edges#listOfKeys in
      let leaf_reps =
        List.filter (fun r -> not (List.mem r reps_with_edges)) reps in

      let processed = new TaintNodeCollections.set_t in
      let rec work (reps : taint_node_int list) =
	match reps with
	| rep :: rest_reps->
	    let has_all_prevs_processed rep =
	      match rep_rev_edges#get rep with
	      | Some prev_reps -> List.for_all processed#has prev_reps#toList
	      |	_ -> true in
	    processed#add rep;
	    self#taint_scc rep;
	    let next_reps =
	      match rep_edges#get rep with
	      | Some set -> List.filter has_all_prevs_processed set#toList
	      | _ -> [] in
	    work (rest_reps @ next_reps)
	| _ -> () in
      work leaf_reps

    method restrict_to_proc (proc_name: symbol_t) =
      let is_from_proc node =
	match node#get_node_type with
	| TN_VAR (cmsix, _, _) -> cmsix = proc_name#getIndex
	| TN_FIELD _ -> true
	| _ -> false in
      let rep_to_proc_nodes = new TaintNodeCollections.table_t in
      let proc_reps = new TaintNodeCollections.set_t in
      let add rep nodes =
	let proc_nodes = nodes#filter is_from_proc in
	if proc_nodes#isEmpty then
	  begin
	    rep_to_proc_nodes#set rep proc_nodes;
	    proc_reps#add rep
	  end in
      rep_to_nodes#iter add;
      let new_rep_edges = new TaintNodeCollections.table_t in
      let add rep set =
	if proc_reps#has rep then
	  begin
	    let proc_set = set#filter proc_reps#has in
	    if not proc_set#isEmpty then
	      new_rep_edges#set rep proc_set
	  end in
      rep_edges#iter add;
      let proc_edges = new TaintNodeCollections.table_t in
      let add_proc_edge n1 n2 =
	match proc_edges#get n1 with
	| Some set -> set#add n2
	| _ -> proc_edges#set n1 (TaintNodeCollections.set_of_list [n2]) in
      let add_proc_edges n1 set =
	set#iter (add_proc_edge n1) in
      new_rep_edges#iter add_proc_edges;
      proc_edges

    method toPretty =
      LBLOCK [
          STR "scc_taint_graph: "; NL;
	  INDENT
            (5,
             LBLOCK [
                 STR "node_to_rep: "; NL; node_to_rep#toPretty; NL;
		 STR "rep_to_nodes: "; NL; rep_to_nodes#toPretty; NL;
		 STR "rep_edges: "; NL; rep_edges#toPretty; NL])]

  end


let big_graph = new scc_taint_graph_t

let add_edges_to_big_graph edges =
  List.iter (fun (n1, n2) -> big_graph#add_node_edge n1 n2) edges

let connect_to_big_graph (g: taint_graph_t) =
  let add_edge (n1: taint_node_int) (n2:taint_node_int) =
    match (n1#get_node_type, n2#get_node_type) with
    | (TN_VAR (_, _v, _), _n) ->
	big_graph#add_node_edge n1 n2
    | (_, TN_VAR (_, v, _)) ->
       if JCHSystemUtils.is_exception v then
         ()
       else
         big_graph#add_node_edge n1 n2
    | _ ->
       big_graph#add_node_edge n1 n2 in

  let add_edges (n: taint_node_int) (nexts: TaintNodeCollections.set_t) =
    nexts#iter (add_edge n) in
  g#get_edges#iter add_edges

let taint_big_graph _untrusted_nodes _unknown_nodes =
  big_graph#make_rep_graph;
  big_graph#taint

(* Returns true if the edges in graph g1 are included in graph g2
 * considering equivalent any two nodes that have the same
 * representative in big_graph *)

let restrict_big_graph_to_proc proc_name =
  big_graph#restrict_to_proc proc_name
