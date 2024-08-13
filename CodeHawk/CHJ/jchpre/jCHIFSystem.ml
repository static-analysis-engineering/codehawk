(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
open CHNumerical
open CHPretty
open CHUtils
open CHLanguage
open CHOnlineCodeSet

(* chutil *)
open CHDot
open CHLogger
open CHUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHTranslateToCHIF


(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHPreAPI
open JCHSystemSettings

module H = Hashtbl

module F = CHOnlineCodeSet.LanguageFactory

module NumericalCollections = CHCollections.Make
  (struct
    type t = numerical_t
    let compare x y = x#compare y
    let toPretty n = n#toPretty
   end)


let command_pretty_printer = fun cms_index cmd ->
  match cmd with
    OPERATION { op_name = op_name; op_args = op_args } ->
      let tag = op_name#getBaseName in
      let procname = new symbol_t ~seqnr:cms_index "procname"  in
      begin
	match tag with
	| "i" | "ii" | "v" ->
	   let bcloc =
             get_bytecode_location procname#getSeqNumber op_name#getSeqNumber in
	    let instruction = app#get_instruction bcloc in
	    begin
	      match tag with
	      | "i" | "ii" ->
		 let args = match op_args with
		   | [] -> STR ""
		   | _ ->
		      let p =
                        pretty_print_list op_args
			  (fun (name, arg, mode) ->
			    LBLOCK [
                                STR name;
                                STR ":";
				arg_mode_to_pretty mode;
                                STR " => ";
                                arg#toPretty])
			  "(" ", " ")" in
		      LBLOCK [NL; STR " with args "; p] in
		 LBLOCK [
                     instruction#toPretty;
                     (if tag = "ii" then STR " (inverted)" else STR "");
		     args]
	      | "v" -> LBLOCK [STR "pc = "; INT instruction#get_location#get_pc]
	      | _ -> command_to_pretty 0 cmd
	    end
	| _ -> command_to_pretty 0 cmd
      end
  | _ -> command_to_pretty 0 cmd


let _ = JCHTranslateToCHIF.set_command_pretty_printer command_pretty_printer


let count_states_and_edges (proc: procedure_int) =
  let body = proc#getBody in
  match body#getCmdAt 0 with
    CFG (_,cfg) ->
      let states = cfg#getStates in
      let edges =
        List.fold_left (fun a s ->
	    a + (List.length s#getOutgoingEdges))
          0 (List.map cfg#getState states) in
      (List.length states, edges)
  | _ ->
    begin
      ch_info_log#add
        "cfg" (LBLOCK [STR "No cfg found in "; proc#getName#toPretty]);
      (0, 0)
    end


let cfg_to_dot_exn (cfg: cfg_int) =
  let g = mk_dot_graph "cfg" in
  let is_exn_exit s = List.mem "exceptional" (string_nsplit '-' s#getBaseName) in
  let is_handler s = List.mem "handler" (string_nsplit '-' s#getBaseName) in
  let has_exn_exit s =
    match (cfg#getState s)#getOutgoingEdges with
    | [] -> false
    | l -> List.for_all is_exn_exit l in
  let states = cfg#getStates in
  let add_node s =
    if is_exn_exit s || is_handler s || has_exn_exit s then
      ()
    else
      let name = s#getBaseName in g#addNode ~label:name name in
  let add_edge s t =
    if (is_exn_exit s) || (is_exn_exit t) then
      ()
    else
      g#addEdge s#getBaseName t#getBaseName in
  begin
    List.iter add_node states;
    List.iter (fun s ->
      List.iter (fun t -> add_edge s t) (cfg#getState s)#getOutgoingEdges) states;
    g#setRankdir "TB";
    g
  end


let chifbasesystem = "chif_base"


class chif_system_t:chif_system_int =
object (self)

  val chif_systems =
    let t = new StringCollections.table_t in
    let s = new system_t (new symbol_t chifbasesystem) in
    let _ = t#set chifbasesystem s in
    t
  val mutable method_translation_failures = []
  val stacklayouts = H.create 3

  val mutable current_cms_index = 0

  method make_code cms cmds =
    if cms#index = current_cms_index then
      F.mkCode cmds
    else
      begin
	current_cms_index <- cms#index;
	F.set_command_pretty_printer (command_pretty_printer cms#index);
	F.mkCode cmds
      end

  method new_system name =
    let s = new system_t (new symbol_t name) in chif_systems#set name s

  method get_systems = chif_systems#listOfValues

  method get_system_names = chif_systems#listOfKeys

  method get_system name =
    match chif_systems#get name with
    | Some s -> s
    | _ ->
       raise (JCH_failure (LBLOCK [STR "No system found with name "; STR name]))

  method get_procedure (system_name:string) (procname:symbol_t) =
    let s = self#get_system system_name in
    if s#hasProcedure procname then s#getProcedure procname else
      raise
        (JCH_failure
           (LBLOCK [STR "No procedure "; procname#toPretty; STR " found"]))

  method get_procedure_by_cms (system_name:string) (cms:class_method_signature_int) =
    self#get_procedure system_name (get_procname_symbol cms)

  method get_method_translation_failures = method_translation_failures

  method has_method_translation_failed (cms:class_method_signature_int) =
    List.mem cms#index (List.map (fun c -> c#index) method_translation_failures)

  method translate ?(default_exn=true) (system_name:string) =
    let methods = List.filter (fun m -> m#has_bytecode) app#get_methods in
    let system = self#get_system system_name in
    let _ =
      if not default_exn then
        pr_debug [STR "Warning: default_exn=false not recognized in translate"] in
    begin
      List.iter
	(fun mInfo ->
	  let cms = mInfo#get_class_method_signature in
	  let procname = make_procname cms#index in
	  let java_method = mInfo#get_method in
	  let exnInfoFn = defaultExnInfoFn mInfo#get_method in
	  try
	    translate_method
	      ~proc_filter:(fun _ -> true)
	      ~simplify:false
	      ~transform:false
	      ~java_method:java_method
	      ~code_set:system
	      ~exn_infos_fn:exnInfoFn
	      ();
	    mInfo#set_num_variables
	      (List.length (system#getProcedure procname)#getScope#getVariables)
	  with
	    JCH_failure p ->
	      let cms = java_method#get_class_method_signature in
	      begin
		method_translation_failures <- cms :: method_translation_failures;
		system_settings#log_error
		  (LBLOCK [
                       STR "Translation of ";
                       cms#toPretty;
		       STR " failed due to ";
                       p]);
                pr_debug [
                    STR "Translation of ";
                    cms#toPretty;
                    STR " failed due to ";
                    p;
                    NL];
		(app#get_method cms)#set_translation_failure
	      end) methods;
      pr_debug [
          NL;
          STR "Methods with bytecode : ";
	  INT (List.length methods);
          NL;
	  STR "Methods translated    : ";
	  INT (List.length system#getProcedures);
          NL; NL];
      let (states,edges) =
        List.fold_left (fun (sa, ea) p ->
	    let (s, e) = count_states_and_edges (system#getProcedure p) in
            (sa+s, ea+e)) (0, 0) system#getProcedures in
      chlog#add
        "system-size"
        (LBLOCK [STR "states: "; INT states; STR "; edges: "; INT edges])
    end

  method translate_method
    (system_name:string)
    ?(assert_types=false)
    (mInfo:method_info_int) =
    let system = self#get_system system_name in
    let _ =
      if assert_types then
        pr_debug [
            STR "Warning: assert_types not recognized in translate_method"] in
    if mInfo#has_bytecode then
      try
	begin
	  translate_method
	    ~proc_filter:(fun _ -> true)
	    ~simplify:false
	    ~transform:false
	    ~java_method:mInfo#get_method
	    ~code_set:system
	    ~exn_infos_fn:(fun _ -> [])
	    (* ~initialization_cmd *)
	    ()
	end
      with
      | JCH_failure p ->
	  let cms = mInfo#get_class_method_signature in
	  begin
	    method_translation_failures <- cms :: method_translation_failures;
	    system_settings#log_error
	      (LBLOCK [
                   STR "Translation of "; cms#toPretty; STR " failed due to "; p])
	  end
    else
      pr_debug [STR "No bytecode found"; NL]

  method create_method_stack_layout (mInfo: method_info_int) =
    let cms = mInfo#get_class_method_signature in
    if List.exists (fun c -> cms#index = c#index) method_translation_failures then
      ()
    else if system_settings#has_instruction_limit
            && mInfo#get_instruction_count > system_settings#get_max_instructions then
      begin
	system_settings#log_error
	  (LBLOCK [
               STR "skip chif translations for ";
	       cms#toPretty;
               STR " (";
               INT mInfo#get_instruction_count;
	       STR " instrs)"]);
	pr_debug [
            STR "Skip translation of ";
            cms#toPretty;
	    STR " (";
            INT mInfo#get_instruction_count;
            STR " instrs)";
            NL]
      end
    else
      try
	let s =
          get_method_stack_layout
            (self#get_system chifbasesystem) mInfo#get_method in
	H.add stacklayouts cms#index s
      with
      | JCH_failure p ->
	  let cms = mInfo#get_class_method_signature in
	  begin
	    pr_debug [cms#toPretty; STR " -- failed: "; p; NL];
	    method_translation_failures <- cms :: method_translation_failures;
	    system_settings#log_error
	      (LBLOCK [
                   STR "Translation of "; cms#toPretty; STR " failed due to "; p])
	  end

  method get_method_stack_layout (mInfo: method_info_int) =
    if H.mem stacklayouts mInfo#get_index then
      H.find stacklayouts mInfo#get_index
    else
      let cms = mInfo#get_class_method_signature in
      raise
        (JCH_failure
           (LBLOCK [STR "No method stack layout found for "; cms#toPretty]))

  method has_system (system_name:string) = chif_systems#has system_name

  method has_method_stack_layout (cms:class_method_signature_int) =
    H.mem stacklayouts cms#index

  method has_procedure (system_name:string) (name:symbol_t) =
    (self#get_system system_name)#hasProcedure name

  method has_procedure_by_cms
           (system_name: string) (cms: class_method_signature_int) =
    self#has_procedure system_name (get_procname_symbol cms)

  method procedure_to_pretty (system_name:string) (name:symbol_t) =
    let system = self#get_system system_name in
    if system#hasProcedure name then
      let proc = system#getProcedure name in
      let cms = retrieve_cms name#getSeqNumber in
      LBLOCK [
	STR "PROCEDURE "; cms#toPretty; STR " ";
	signature_to_pretty proc#getSignature; NL;
	INDENT (tab,
		LBLOCK [
		  STR "BINDINGS: "; bindings_to_pretty proc#getBindings; NL;
		  STR "SCOPE"; NL; proc#getScope#toPretty;
		  proc#getBody#toPretty; NL
		])]
    else
      LBLOCK [STR "Procedure "; name#toPretty; STR " not found"; NL]

  method procedure_to_dot (system_name:string) (name:symbol_t) =
    let system = self#get_system system_name in
    if system#hasProcedure name then
      let proc = system#getProcedure name in
      match proc#getBody#getCmdAt 0 with
	CFG (_, cfg) -> Some (cfg_to_dot_exn cfg)
      | _ -> None
    else
      None

  method stack_layout_to_pretty (m:method_info_int) =
    if m#has_bytecode then
      let stackLayout = self#get_method_stack_layout m in
      let opcodes = m#get_bytecode#get_code in
      let p = ref [] in
      let _ = for i = opcodes#length - 1 downto 0  do
	  match opcodes#at i with
	  | OpInvalid -> ()
	  | opc ->
	     p :=
               (LBLOCK [
                    NL;
		    INDENT (3, (stackLayout#get_stack_layout i)#toPretty); NL;
		    STR "pc = ";
                    INT i;
                    STR "  ";
		    opcode_to_pretty opc;
                    NL]) :: !p
	done in
      LBLOCK [m#get_class_method_signature#toPretty; NL; LBLOCK !p]
    else
      LBLOCK [
          m#get_class_method_signature#toPretty; STR " does not have bytecode"; NL]

  method toPretty (system_name:string) =
    let system = self#get_system system_name in
    pretty_print_list system#getProcedures
      (fun p -> self#procedure_to_pretty system_name p) "" "" ""

end


let chif_system = new chif_system_t

let base_system = chifbasesystem


let translate_base_system
    ?(default_exn=true)
    ?(method_info=None)
    () =
  let system_name = chifbasesystem in
  begin
    match method_info with
	Some m -> chif_system#translate_method  system_name m; system_name
      | _ -> chif_system#translate ~default_exn  system_name;
    system_name
  end


let get_chif (cms:class_method_signature_int) =
  let system_name = chifbasesystem in
  let procname = get_procname_symbol cms in
  if chif_system#has_method_translation_failed cms then
    raise (JCH_failure (LBLOCK [STR "Unable to translate "; cms#toPretty]))
  else
    let _ = if chif_system#has_system system_name then
	()
      else
	chif_system#new_system system_name in
    let _ = if chif_system#has_procedure system_name procname then
	()
      else
	chif_system#translate_method system_name (app#get_method cms) in
    if chif_system#has_method_translation_failed cms then
      raise (JCH_failure (LBLOCK [STR "Unable to translate "; cms#toPretty]))
    else
      try
	chif_system#get_procedure system_name procname
      with
	JCH_failure p ->
	  begin
	    ch_error_log#add
              "translation failure"
	      (LBLOCK [STR "Unable to translate "; cms#toPretty]);
	    raise
              (JCH_failure
                 (LBLOCK [
                      STR "Translation failure: Unable to translate ";
		      cms#toPretty;
                      STR ": ";
                      p]))
	  end


let get_chif_pretty (cms:class_method_signature_int) =
  let system_name = "chif_base" in
  let procname = get_procname_symbol cms in
  let _ =
    if chif_system#has_system "chif_base" then
      ()
    else
      chif_system#new_system system_name in
  let _ =
    if chif_system#has_procedure system_name procname then
      ()
    else
      chif_system#translate_method system_name (app#get_method cms) in
  try
    Some (chif_system#procedure_to_pretty system_name procname)
  with
  | Not_found ->
      begin
	ch_info_log#add
          "translation failure"
          (LBLOCK [cms#toPretty; STR " could not be translated"]);
	None
      end


let get_cfg_dot (cms: class_method_signature_int):dot_graph_int option =
  let system_name = "chif_base" in
  let procname = get_procname_symbol cms in
  let _ =
    if chif_system#has_system "chif_base" then
      ()
    else
      chif_system#new_system system_name in
  let _ =
    if chif_system#has_procedure system_name procname then
      ()
    else
      chif_system#translate_method system_name (app#get_method cms) in
  try
    chif_system#procedure_to_dot system_name procname
  with
  | Not_found ->
     begin
       ch_error_log#add
         "dot failure" (LBLOCK [cms#toPretty; STR " not found in CHIF system "]);
       None
     end


let pc_label (pc: int) = "pc=" ^ (string_of_int pc)

let handler_pc_label (pc: int) = new symbol_t ((pc_label pc) ^ "-handler")


let get_catch_blocks (cms: class_method_signature_int) =
  let system_name = "chif_base" in
  let m = app#get_method cms in
  let exceptionTable = m#get_exception_table in
  let procname = get_procname_symbol cms in
  if chif_system#has_procedure system_name procname then
    try
      let body = (chif_system#get_procedure system_name procname)#getBody in
      let cfg = match body#getCmdAt 0 with
	  CFG (_, cfg) -> cfg
	| _ ->
	  begin
	    pr_debug [cms#toPretty; STR " does not have a cfg"; NL];
	    raise (JCH_failure (LBLOCK [STR "No cfg found for "; cms#toPretty]))
	  end in
	  let entry = cfg#getEntry in
	  let regularNodes = new SymbolCollections.set_t in
	  let workList = new SymbolCollections.set_t in
	  let _ = workList#add entry#getLabel in
	  let _ = while not workList#isEmpty do
	      let nodeLabel = Option.get workList#choose in
	      let _ = workList#remove nodeLabel in
	      if regularNodes#has nodeLabel then () else
		begin
		  regularNodes#add nodeLabel;
		  workList#addList (cfg#getState nodeLabel)#getOutgoingEdges
		end
	    done in
	  let handlerPcs = new SymbolCollections.set_t in
	  let _ =
            handlerPcs#addList
              (List.map (fun h -> handler_pc_label h#handler) exceptionTable) in
	  let handler_code_to_pretty h =
	    let state = cfg#getState h in
	    let code = state#getCode in
	    let p = ref [] in
	    let _ =
              for i = 0 to code#length - 1 do
	        match code#getCmdAt i with
		| CODE (l, _) -> p := (LBLOCK [l#toPretty; STR "; "]) :: !p
	        | _ -> ()
	      done in
	    LBLOCK !p in
	  handlerPcs#iter
	    (fun handlerPc ->
	      let handlerState = cfg#getState handlerPc in
	      let handlerBlock = new SymbolCollections.set_t in
	      let _ = handlerBlock#add handlerState#getLabel in
	      let workList = new SymbolCollections.set_t in
	      let _ = workList#addList handlerState#getOutgoingEdges in
	      let _ = while not workList#isEmpty do
		  let nodeLabel = Option.get workList#choose in
		  let _ = workList#remove nodeLabel in
		  if handlerBlock#has nodeLabel then
                    ()
		  else if regularNodes#has nodeLabel then
                    ()
		  else if handlerPcs#has nodeLabel then
                    ()
		  else
		    begin
		      handlerBlock#add nodeLabel;
		      workList#addList (cfg#getState nodeLabel)#getOutgoingEdges
		    end
		done in
	      pr_debug [
                  STR "Handler ";
                  handlerPc#toPretty; NL;
		  pretty_print_list
                    handlerBlock#toList handler_code_to_pretty "[" ";" "]";
                  NL; NL])
    with
    | JCH_failure _ -> ()
  else
    pr_debug [STR "No bytecode found for "; cms#toPretty]
