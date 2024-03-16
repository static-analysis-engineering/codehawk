(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode

(* jchpre *)
open JCHApplication
open JCHIFSystem
open JCHLoops
open JCHPreAPI
open JCHSystemSettings

(* jchfeatures *)
open JCHFeaturesAPI
open JCHSubgraph

module H = Hashtbl


let blockSize = 10000   (* maximum size of a block when saving in xml *)


let libcall_package_prefixes4 = ["java"; "sun."]


let libcall_package_prefixes7 =
  ["org.w3c"; "org.xml"; "com.sun"; "io.nett"; "org.jso"; ]


let libcall_package_prefixes10 =
  ["org.apache"; "gnu.trove."; "org.eclips";
    "com.google"; "fi.iki.elo"; "org.mapdb.";
    "org.slf4j."; "org.spring"]


let islibcallpkg pkgname =
  if (String.length pkgname) > 4 then
    if List.mem (String.sub pkgname 0 4) libcall_package_prefixes4 then
      true
    else if (String.length pkgname) > 7 then
      if List.mem (String.sub pkgname 0 7) libcall_package_prefixes7 then
        true
      else if (String.length pkgname) > 10 then
        List.mem (String.sub pkgname 0 10) libcall_package_prefixes10
      else
        false
    else
      false
  else
    false


let scale_table table =
  let newTable = H.create (H.length table) in
  let total = float (H.fold (fun _ v acc -> v + acc) table 0) in
  let _ =
    H.iter (fun k v ->
        H.add newTable k (FloatFeature (v,(float v) /. total))) table in
  newTable


let int_table table =
  let newTable = H.create (H.length table) in
  let _ = H.iter (fun k v -> H.add newTable k (IntFeature v)) table in
  newTable


let opcode_to_category (opc:opcode_t) =
  match opc with
  | OpIInc _ -> "ao"
  | OpAdd _ | OpSub _ | OpMult _ | OpDiv _ | OpRem _ | OpNeg _ -> "ao"
  | OpIShl | OpLShl | OpIShr | OpIUShr | OpLUShr
  | OpIAnd | OpLAnd | OpIOr | OpLOr
  | OpIXor | OpLXor -> "lo"
  | OpIntConst _ | OpLongConst _ | OpFloatConst _
  | OpDoubleConst _ | OpByteConst _ | OpShortConst _ -> "nc"
  | OpAConstNull | OpStringConst _ | OpClassConst _ -> "oc"
  | OpCmpL | OpCmpFL | OpCmpFG | OpCmpDL | OpCmpDG -> "cp"
  | OpIfEq _ | OpIfNe _ | OpIfLt _ | OpIfGe _ | OpIfGt _ | OpIfLe _
  | OpIfNull _ | OpIfNonNull _
  | OpIfCmpEq _ | OpIfCmpNe _ | OpIfCmpLt _ | OpIfCmpGe _
  | OpIfCmpGt _ | OpIfCmpLe _ -> "cj"
  | OpGoto _ | OpRet _ | OpReturn _ -> "cf"
  | OpLookupSwitch _ | OpTableSwitch _ -> "sw"
  | OpNew _ | OpNewArray _ | OpAMultiNewArray _-> "nw"
  | OpArrayLength | OpArrayLoad _ | OpArrayStore _ -> "ro"
  | OpInvokeVirtual _
  | OpInvokeSpecial _
  | OpInvokeStatic _
  | OpInvokeInterface _ -> "cl"
  | OpGetStatic _
  | OpPutStatic _
  | OpGetField _
  | OpPutField _ -> "fa"
  | OpThrow -> "ex"
  | OpMonitorEnter | OpMonitorExit -> "th"
  | _ -> "xx"


let basic_type_to_category (t:java_basic_type_t) =
  match t with
  | Int | Short | Char | Byte | Bool | Long | Int2Bool | ByteBool -> "integral"
  | Float | Double -> "float"
  | Object -> "object"
  | Void -> "void"


let feature_value_to_string (fv:feature_value_t) =
  match fv with
  | IntFeature i -> string_of_int i
  | FloatFeature (_,f) -> Printf.sprintf "%.4f" f


let split_list lst count =
  let rec aux l n result =
    if n <= 0 then (List.rev result, l) else
      match l with
      | [] -> (List.rev result, [])
      | hd::tl -> aux tl (n-1) (hd::result) in
  aux lst count []


let list_divide (lst:'a list) (len:int):'a list list =
  let rec aux l result =
    match l with
    | [] -> List.rev result
    | _ -> let (lstpre,lstsuf) = split_list l len in
	   aux lstsuf (lstpre :: result) in
  aux lst []


let write_xml_feature_set (node:xml_element_int) (l:key_value_pair_t list) =
  let seti = node#setIntAttribute in
  let lsts = list_divide l blockSize in
  begin
    node#appendChildren (List.map (fun sublist ->
      let sNode = xmlElement "block" in
      begin
	sNode#appendChildren (List.map (fun (k, v) ->
	  let eNode = xmlElement "kv" in
	  begin
	    eNode#setAttribute "k" k;
	    eNode#setAttribute "v" (feature_value_to_string v);
	    eNode
	  end) sublist);
	sNode
      end) lsts);
    seti "keys" (List.length l)
  end


let write_xml_feature_sets (node:xml_element_int) (l:feature_values_set_t list) =
  node#appendChildren (List.map (fun (fname,fset) ->
    let fNode = xmlElement "feature-set" in
    begin
      write_xml_feature_set fNode fset;
      fNode#setAttribute "name" fname;
      fNode
    end) l)


let add_to_table (t:(string,int) H.t) (tag:string) (v:int) =
  let e = if H.mem t tag then H.find t tag else 0 in H.replace t tag (v + e)


class loop_features_t
  (mInfo:method_info_int)
  (lInfo:loop_info_t)
  (feature_sets:string list):loop_features_int =
object (self)

  val table = H.create 3

  method private add_features
                   (tag:string) (kvtable:(string, feature_value_t) H.t) =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) kvtable in
    let l = List.sort (fun (_,v1) (_,v2) -> Stdlib.compare v2 v1) !l in
    H.add table tag l

  method count_key_value_pairs =
    H.fold (fun _ v a -> a + (List.length v)) table 0

  method get_size = H.length table

  method private get_code = mInfo#get_bytecode#get_code

  method private get_loop_pcs =
    let fstPc = lInfo.li_first_pc in
    let lstPc = lInfo.li_last_pc in
    let in_loop pc = fstPc <= pc && pc <= lstPc in
    let loopPcs = ref [] in
    let _ =
      mInfo#bytecode_iteri (fun pc opc ->
          if in_loop pc then loopPcs := (pc,opc) :: !loopPcs) in
    !loopPcs

  method private generate_bc_features =
    let t = H.create 7 in
    let loopPcs = self#get_loop_pcs in
    let condPcs = lInfo.li_cond_pcs in
    let _ =
      List.iter (fun (pc,opc) ->
          let hex = opcode_to_opcode_index_string opc in
          let hex = if List.mem pc condPcs then hex ^ "#x" else hex in
          add_to_table t hex 1) loopPcs in
    scale_table t

  method private generate_cat_features =
    let t = H.create 7 in
    let loopPcs = self#get_loop_pcs in
    let _ = List.iter (fun (_,opc) ->
      let cat = opcode_to_category opc in
      add_to_table t cat 1) loopPcs in
    scale_table t

  method private generate_libcall_features =
    let t = H.create 3 in
    let loopPcs = self#get_loop_pcs in
    let add_call cn ms =
      let name = cn#name ^ "." ^ ms#name in
      if islibcallpkg cn#package_name then add_to_table t name 1 in
    let _ = List.iter (fun (_,opc) ->
      match opc with
      | OpInvokeStatic (cn,ms)
      | OpInvokeVirtual (TClass cn,ms)
      | OpInvokeSpecial (cn,ms)
      | OpInvokeInterface (cn,ms) -> add_call cn ms
      | _ -> ()) loopPcs in
    int_table t

  method private generate_size_features =
    let t = H.create 7 in
    let add key v = if v > 0 then H.add t key v else () in
    begin
      add "instrs" (List.length self#get_loop_pcs);
      add "depth" (List.length lInfo.li_inner_loops);
      add "exits" (List.length lInfo.li_cond_pcs);
      int_table t
    end

  method generate_features =
    let generate_feature (feature_set:string) =
      match feature_set
      with "loop_bc" ->
            self#add_features "bc" self#generate_bc_features
         | "loop_bc-cat" ->
            self#add_features "bc-cat" self#generate_cat_features
         | "loop_libcalls" ->
            self#add_features "libcalls" self#generate_libcall_features
         | "loop_sizes" ->
            self#add_features "sizes" self#generate_size_features
      | _ -> ()
    in List.iter generate_feature feature_sets

  method private get_table =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) table in
    !l

  method write_xml (node:xml_element_int) =
    let seti = node#setIntAttribute in
    begin
      write_xml_feature_sets node self#get_table;
      seti "entry-pc" lInfo.li_entry_pc;
      seti "last-pc" lInfo.li_last_pc
    end

end


class method_features_t
  (mInfo:method_info_int)
  (feature_sets:string list):method_features_int =
object (self)

  val table = H.create 5
  val mutable loops = []
  val mutable max_depth = 0
  val mutable loop_count = 0
  val mutable subgraph_count = 0
  val mutable state_count = 0
  val mutable edge_count = 0
  val mutable complexity = 0
  val mutable translation_failure = false
  val jmethod = mInfo#get_method
  val concrete = mInfo#get_method#is_concrete
  val class_names_recorded_table = H.create 13
  val native =
    mInfo#get_method#is_concrete &&
      (match mInfo#get_method#get_implementation with Native -> true | _ -> false)

  method is_native = native

  method failed_to_translate = translation_failure

  method get_feature (name:string) =
    if H.mem table name then H.find table name else []

  method get_method_info = mInfo

  method get_name = mInfo#get_class_method_signature#name

  method get_byte_count = mInfo#get_byte_count

  method get_instruction_count = mInfo#get_instruction_count

  method get_subgraph_count = subgraph_count

  method get_state_count = state_count

  method get_edge_count = edge_count

  method get_complexity = complexity

  method get_interface_call_count =
    match self#get_code with
    | Some code ->
      let n = ref 0 in
      let _ = code#iteri (fun _ opc ->
	match opc with OpInvokeInterface _ -> n := !n + 1 | _ -> ()) in
      !n
    | _ -> 0

  method get_virtual_call_count =
    match self#get_code with
    | Some code ->
      let n = ref 0 in
      let _ = code#iteri (fun _ opc ->
	match opc with OpInvokeVirtual _ -> n := !n + 1 | _ -> ()) in
      !n
    | _ -> 0

  method get_loop_count = loop_count

  method get_max_depth = max_depth

  method get_size = H.fold (fun _ l acc -> acc + (List.length l)) table 0

  method count_key_value_pairs =
    let methodKv = H.fold (fun _ v a -> a + (List.length v)) table 0 in
    let loopKv =
      List.fold_left (fun a l -> a + l#count_key_value_pairs) 0 loops in
    methodKv + loopKv

  method private get_table =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) table in
    !l

  method private add_features
                   (tag:string) (kvtable:(string, feature_value_t) H.t) =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) kvtable in
    let l = List.sort (fun (_,v1) (_,v2) -> Stdlib.compare v2 v1) !l in
    H.add table tag l

  method private get_code =
    if concrete then
      match jmethod#get_implementation with
      | Bytecode bc -> Some bc#get_code
      | Native -> None
    else
      None

  method private generate_size_features =
    let t = H.create 7 in
    let add key v = if v > 0 then H.add t key v else () in
    begin
      add "instrs" self#get_instruction_count;
      add "i-calls" self#get_interface_call_count;
      add "v-calls" self#get_virtual_call_count;
      add "loops" self#get_loop_count;
      add "args"
	(List.length
           mInfo#get_class_method_signature#method_signature#descriptor#arguments);
      add "max-depth" self#get_max_depth;
      add "exn-handlers" (List.length mInfo#get_exception_table);
      add "checked-exns" (List.length mInfo#get_exceptions);
      add "subgraphs" subgraph_count;
      add "cfg-edges" edge_count;
      add "cfg-nodes" state_count;
      add "complexity" complexity;
      int_table t
    end

  method private generate_attr_features =
    let t = H.create 7 in
    let add key c = if c then H.add t key 1 else () in
    begin
      add "static" mInfo#is_static;
      add "final" mInfo#is_final;
      add "native" mInfo#is_native;
      add "public" mInfo#is_public;
      add "private" mInfo#is_private;
      add "synch" mInfo#is_synchronized;
      add "constructor" mInfo#is_constructor;
      add "class-constructor" mInfo#is_class_constructor;
      add "translation-failure" translation_failure;
      int_table t
    end

  method private  get_arraystore_count =
    match self#get_code with
    | Some code ->
      let n = ref 0 in
      let _ = code#iteri (fun _ opc ->
	match opc with OpArrayStore _ -> n := !n + 1 | _ -> ()) in
      !n
    | _ -> 0

  method private can_translate_to_chif =
    let instrcount = mInfo#get_instruction_count in
    let arraystorecount = self#get_arraystore_count  in
    not (instrcount > 4000 && arraystorecount > 1000)

  method generate_features =
    (* loop features are available only for methods with chif translations *)
    let cms = mInfo#get_class_method_signature in
    let _ =
      if self#can_translate_to_chif then
        chif_system#create_method_stack_layout mInfo
      else
        pr_debug [
            STR "Skip translation of ";
            mInfo#get_class_method_signature#toPretty;
            NL] in
    let _ =
      if chif_system#has_procedure_by_cms base_system cms then
	self#add_loop_features
      else
	pr_debug [STR "  -- No loop features added for "; cms#toPretty; NL] in
    let generate_feature (feature_set:string) =
      match feature_set with
      | "method_bc" -> self#add_features "bc" self#generate_bc_features
      | "method_bc2" -> self#add_features "bc2" self#generate_bc2_features
      | "method_bc3" -> self#add_features "bc3" self#generate_bc3_features
      | "method_libcalls" ->
         self#add_features "libcalls" self#generate_libcall_features
      | "method_libcalls_sig" ->
         self#add_features "libcalls-sig" self#generate_libcall_sig_features
      | "method_api-types" ->
         self#add_features "api-types" self#generate_api_type_features
      | "method_op-types" ->
         self#add_features "op-types" self#generate_op_type_features
      | "method_literals" ->
         self#add_features "literals" self#generate_literal_features
      | "method_attrs" -> self#add_features "attrs" self#generate_attr_features
      | "method_sizes" -> self#add_features "sizes" self#generate_size_features
      | _ -> ()
    in List.iter generate_feature feature_sets

  method private generate_bc_features =
    let t = H.create 11 in
    let _ = match self#get_code with
      | Some code -> code#iteri (fun _ opc ->
	add_to_table t (opcode_to_opcode_index_string opc) 1)
      | None -> () in
    scale_table t

  method private generate_bc2_features =
    let hex = opcode_to_opcode_index_string in
    let t = H.create 11 in
    let _ = match self#get_code with
      | Some code when code#instr_count > 1 ->
	let p_opc = ref (code#at 0) in
	code#iteri (fun i opc ->
	  if i = 0 then () else
	    begin
              add_to_table t ((hex !p_opc) ^ (hex opc)) 1;
              p_opc := opc
            end)
      | _ -> () in
    scale_table t

  method private generate_bc3_features =
    let hex = opcode_to_opcode_index_string in
    let t = H.create 11 in
    let _ = match self#get_code with
      | Some code when code#instr_count > 2 ->
	let p_opc1 = ref (code#at 0) in
	let i2 = Option.get (code#next 0) in
	let p_opc2 = ref (code#at i2) in
	let nexti = ref (code#next i2) in
	while (match !nexti with Some _ -> true | _ -> false) do
	  let nxt = Option.get !nexti in
	  let opc = code#at nxt in
	  begin
	    add_to_table t ((hex !p_opc1) ^ (hex !p_opc2) ^ (hex opc)) 1;
	    p_opc1 := !p_opc2;
	    p_opc2 := opc;
	    nexti := code#next nxt
	  end
	done
      | _ -> () in
    scale_table t

  method private generate_libcall_features =
    let t = H.create 11 in
    let add_call cn ms =
      let name = cn#name ^ "." ^ ms#name in
      if islibcallpkg cn#package_name then
	add_to_table t name 1
      else if ms#equal mInfo#get_class_method_signature#method_signature then
	let key = "self-ms-" ^ ms#to_signature_string in
	add_to_table t key 1 in
    let _ = match self#get_code with
      | Some code ->
	code#iteri (fun _ opc ->
	  match opc with
	  | OpInvokeStatic (cn,ms)
	  | OpInvokeVirtual (TClass cn,ms)
	  | OpInvokeSpecial (cn,ms)
	  | OpInvokeInterface (cn,ms) -> add_call cn ms
	  | _ -> ())
      | _ -> () in
    int_table t

  method private generate_libcall_sig_features =
    let t = H.create 11 in
    let add_call cn ms =
      let name = cn#name ^ "." ^ ms#name ^ ms#to_signature_string in
      if islibcallpkg cn#package_name then
	add_to_table t name 1
      else if ms#equal mInfo#get_class_method_signature#method_signature then
	let key = "self-ms-" ^ ms#to_signature_string in
	add_to_table t key 1 in
    let _ = match self#get_code with
      | Some code ->
	code#iteri (fun _ opc ->
	  match opc with
	  | OpInvokeStatic (cn,ms)
	  | OpInvokeVirtual (TClass cn,ms)
	  | OpInvokeSpecial (cn,ms)
	  | OpInvokeInterface (cn,ms) -> add_call cn ms
	  | _ -> ())
      | _ -> () in
    int_table t

  method private generate_literal_features =
    let t = H.create 11 in
    let add key = add_to_table t key 1 in
    let _ = match self#get_code with
      | Some code ->
	code#iteri (fun _ opc ->
	  match opc with
	  | OpIntConst i32 -> add ("I_" ^ (Int32.to_string i32))
	  | OpLongConst i64 -> add ("L_" ^ (Int64.to_string i64))
	  | OpFloatConst f -> add ("F_" ^ (Printf.sprintf "%f" f))
	  | OpDoubleConst d -> add ("D_" ^ (Printf.sprintf "%f" d))
	  | OpByteConst b -> add ("B_" ^ (string_of_int b))
	  | OpShortConst s -> add ("S_" ^ (string_of_int s))
	  | OpStringConst _ -> add "string"
	  | OpClassConst _ -> add "class"
	  | _ -> ())
      | _ -> () in
    int_table t

  method private generate_api_type_features =
    let t = H.create 3 in
    let desc = jmethod#get_signature#descriptor in
    let add prefix s = add_to_table t (prefix ^ s) 1 in
    let add_class_type prefix cn  =
      if H.mem class_names_recorded_table cn#name then
	add prefix (H.find class_names_recorded_table cn#name)
      else
	add prefix "obj" in
    let rec add_type prefix (vt:value_type_t) =
      match vt with
      | TBasic bt -> add prefix (basic_type_to_category bt)
      | TObject (TArray att) ->
         begin add prefix "array"; add_type prefix att end
      | TObject (TClass cn) -> add_class_type prefix cn in
    let _ = List.iter (add_type "#a") desc#arguments in
    let _ = match desc#return_value with
      | Some vt -> add_type "#r" vt
      | _ -> () in
    int_table t

  method private generate_subgraph_features (proc:procedure_int) =
    let t = H.create 3 in
    let (features,nStates,nEdges) = get_cfg_4subgraphs proc in
    let _ = List.iter (fun s -> add_to_table t s 1) features in
    begin
      self#add_features "ksubgraph" (scale_table t);
      subgraph_count <- List.length features;
      state_count <- nStates;
      edge_count <- nEdges;
      complexity <- (nEdges - nStates) + 2
    end

  method private generate_op_type_features =
    let t = H.create 11 in
    let add s = add_to_table t s 1 in
    let add_class_type cn  =
      if H.mem class_names_recorded_table cn#name then
	add_to_table t (H.find class_names_recorded_table cn#name) 1
      else
	add "obj" in
    let rec add_type (vt:value_type_t) =
      match vt with
      | TBasic bt -> add (basic_type_to_category bt)
      | TObject (TArray att) -> begin add "array"; add_type att end
      | TObject (TClass cn) -> add_class_type cn in
    let _ = match self#get_code with
      | Some code ->
         code#iteri (fun _ opc -> List.iter add_type (opcode_arg_types opc))
      | _ -> () in
    scale_table t

  method private add_loop_features =
    let get_max_depth lInfos =
      List.fold_left (fun mx lInfo ->
	let le = List.length in
	let d = (le lInfo.li_inner_loops) + (le lInfo.li_outer_loops) + 1 in
	if d > mx then d else mx) 0 lInfos in
    if native then () else
      try
	let proc = get_chif mInfo#get_class_method_signature in
	let lInfos = get_loop_infos mInfo in
	begin
	  (if (List.exists (fun x -> x = "method_ksubgraph") feature_sets) then
	      self#generate_subgraph_features proc
	   else
	      ());
	  loop_count <- List.length lInfos;
	  max_depth <- get_max_depth lInfos;
	  loops <-
            List.map (fun lInfo ->
	        let loop = new loop_features_t mInfo lInfo feature_sets in
	        begin
                  loop#generate_features;
                  loop
                end) lInfos
	end
      with
      | JCH_failure p ->
	begin
	  system_settings#log_error
	    (LBLOCK [
                 STR "No loop features for ";
		 mInfo#get_class_method_signature#toPretty;
		 STR ": ";
                 p;
                 NL]);
	  translation_failure <- true
	end

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let llNode = xmlElement "loops" in
    let mNode = xmlElement "method-features" in
    begin
      write_xml_feature_sets mNode self#get_table;
      llNode#appendChildren (List.map (fun loop ->
	let lNode = xmlElement "loop" in
	begin loop#write_xml lNode; lNode end) loops);
      append [llNode; mNode]
    end

end


class class_features_t
  (cInfo:class_info_int)
  (feature_sets:string list):class_features_int =
object (self)

  val methodtable =
    let msLst = cInfo#get_methods_defined in
    let mLst = List.fold_left (fun acc ms ->
      try
	let jm = cInfo#get_method ms in if jm#is_concrete then jm::acc else acc
      with
	JCH_failure _ -> acc) [] msLst in
    let mLst =
      List.map (fun m -> app#get_method m#get_class_method_signature) mLst in
    let t = H.create 3 in
    let _ =
      List.iter (fun mInfo ->
          let cms = mInfo#get_class_method_signature in
          let mFeatures = new method_features_t mInfo feature_sets in
          let _ = mFeatures#generate_features in
          H.add t cms#index mFeatures) mLst in
    t

  val table = H.create 13

  method count_key_value_pairs =
    let classKv = H.fold (fun _ v a -> a + (List.length v)) table 0 in
    let methodKv =
      H.fold (fun _ v a -> a + v#count_key_value_pairs) methodtable 0 in
    classKv + methodKv

  method private add_features
                   (tag:string) (kvtable:(string, feature_value_t) H.t) =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) kvtable in
    let l = List.sort (fun (_,v1) (_,v2) -> Stdlib.compare v2 v1) !l in
    H.add table tag l

  method private get_table =
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) table in
    !l

  method get_class_info = cInfo

  method get_method_features =
    let l = ref [] in
    let _ = H.iter (fun _ v -> l := v :: !l)  methodtable in
    let l =
      List.sort (fun m1 m2 ->
          Stdlib.compare
            m1#get_method_info#get_method_name
            m2#get_method_info#get_method_name) !l in
    l

  method private accumulate_method_frequency (name:string) =
    let t = H.create 3 in
    let _ = H.iter (fun _ m ->
      List.iter (fun (k,v) ->
	let c = match v with IntFeature i | FloatFeature (i,_) -> i in
	add_to_table t k c ) (m#get_feature name)) methodtable in
    scale_table t

  method private accumulate_method_count (name:string) =
    let t = H.create 3 in
    let _ = H.iter (fun _ m ->
      List.iter (fun (k,v) ->
	let c = match v with IntFeature i | FloatFeature (i,_) -> i in
	add_to_table t k c ) (m#get_feature name)) methodtable in
    int_table t

  method get_bc_method_count =
    H.fold (fun _ m acc -> if m#is_native then acc else acc+1) methodtable 0

  method private get_native_method_count =
    H.fold (fun _ m acc -> if m#is_native then acc+1 else acc) methodtable 0

  method private get_translation_failures =
    H.fold
      (fun _ m acc ->
        if m#failed_to_translate then acc+1 else acc) methodtable 0

  method get_native_methods =
    H.fold (fun _ m acc ->
      if m#is_native then
	let mInfo = m#get_method_info in
	let name = mInfo#get_method_name in
	let access = access_to_string mInfo#get_visibility in
	let sigStr = mInfo#get_signature_string in
	(name,sigStr,access) :: acc
      else
	acc) methodtable []

  method private generate_size_features =
    let t = H.create 7 in
    let add key v = if v > 0 then H.add t key v else  () in
    begin
      add "methods" self#get_bc_method_count;
      add "native-methods" self#get_native_method_count;
      add "fields" cInfo#get_field_count;
      add "max-depth" self#get_max_depth;
      add "loops" self#get_loop_count;
      add "instrs" cInfo#get_instruction_count;
      add "subgraphs" self#get_subgraph_count;
      add "max-complexity" self#get_max_complexity;
      add "translation-failures" self#get_translation_failures;
      int_table t
    end

  method private generate_attr_features =
    let t = H.create 7 in
    let add key c = if c then H.add t key 1 else () in
    begin
      add "interface" cInfo#is_interface;
      add "final" cInfo#is_final;
      add "immutable" cInfo#is_immutable;
      add "dispatch" cInfo#is_dispatch;
      add "collection" cInfo#is_collection_class;
      add "map" cInfo#is_map_class;
      add "wrapper" cInfo#is_wrapper_class;
      int_table t
    end

  method get_loop_count =
    H.fold (fun _ v acc -> acc + v#get_loop_count) methodtable 0

  method get_size =
    H.fold (fun _ v acc -> acc + v#get_size) methodtable 0

  method private get_subgraph_count =
    H.fold (fun _ v acc -> acc + v#get_subgraph_count) methodtable 0

  method get_max_depth =
    H.fold (fun _ v acc ->
      let d = v#get_max_depth in if d > acc then d else acc) methodtable 0

  method get_max_complexity =
    H.fold (fun _ v acc ->
      let d = v#get_complexity in if d > acc then d else acc) methodtable 0

  method generate_features =
    let generate_feature (feature_set:string) =
      match feature_set
      with
      | "class_bc" ->
         self#add_features "bc" (self#accumulate_method_frequency "bc");
      | "class_bc2" ->
         self#add_features "bc2" (self#accumulate_method_frequency "bc2");
      | "class_bc3" ->
         self#add_features "bc3" (self#accumulate_method_frequency "bc3");
      | "class_libcalls" ->
	 self#add_features "libcalls" (self#accumulate_method_count "libcalls");
      | "class_api-types" ->
	 self#add_features "api-types" (self#accumulate_method_count "api-types");
      | "class_op-types" ->
	 self#add_features "op-types" (self#accumulate_method_frequency "op-types");
      | "class_ksubgraph" ->
	 self#add_features
           "ksubgraph" (self#accumulate_method_frequency "ksubgraph");
      | "class_literals" ->
	 self#add_features "literals" (self#accumulate_method_count "literals");
      | "class_sizes" -> self#add_features "sizes" self#generate_size_features;
      | "class_attrs" -> self#add_features "attrs" self#generate_attr_features;
      | _ -> ()
    in List.iter generate_feature feature_sets

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let mmNode = xmlElement "methods" in
    let cNode = xmlElement "class-features" in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    begin
      mmNode#appendChildren (List.map (fun m ->
	let mNode = xmlElement "method" in
	begin
	  m#write_xml mNode;
	  mNode#setAttribute "name" m#get_method_info#get_method_name;
	  mNode#setAttribute "sig" m#get_method_info#get_signature_string;
	  mNode
	end) self#get_method_features);
      write_xml_feature_sets cNode self#get_table;
      append [cNode; mmNode];
      set "name" cInfo#get_class_name#simple_name;
      set "package" cInfo#get_class_name#package_name;
      set "md5" cInfo#get_md5_digest;
      seti "key-value-pairs" self#count_key_value_pairs
    end

end


let get_class_features
    (cInfo:class_info_int)
    (feature_sets:string list) =
  let c = new class_features_t cInfo feature_sets in
  let _ = c#generate_features in
  c
