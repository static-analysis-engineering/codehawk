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

open Big_int_Z

(* chlib *)
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHPreAPI

(* jchsys *)
open JCHPrintUtils
open JCHGlobals

module F = CHOnlineCodeSet.LanguageFactory


(* Makes a new state with all the fields of oldState but with new_cmds *)
let mk_state (oldState:state_int) (new_cmds:code_int):state_int =
  let new_state = F.mkState oldState#getLabel new_cmds in
  let preds = oldState#getIncomingEdges in
  let succs = oldState#getOutgoingEdges in
  List.iter new_state#addIncomingEdge preds;
  List.iter new_state#addOutgoingEdge succs;
  new_state

class proc_checker_t proc_name proc =
  object (self: _)

    inherit code_walker_t as super

    val mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber)

    method private check_invoke
                     (cn:class_name_int)
                     (ms:method_signature_int)
                     (iInfo:instruction_info_int) =
      match cn#name with
      |	"java.lang.Integer"
      | "java.lang.Short"
      | "java.lang.Character"
      | "java.lang.Byte"
      | "java.lang.Long"
      | "java.lang.Float"
      | "java.lang.Double"
      | "java.math.BigInteger"
      | "java.math.BigDecimal"

      (* found the last one in com.ibm.icu.impl.data.LocaleElements_fa *)
      |	"com.ibm.icu.impl.ICUListResourceBundle$ResourceBinary"

      (* found in com.ibm.icu.impl.data.LocaleElements *)
      |	"com.ibm.icu.impl.ICUListResourceBundle$ResourceString"

      (* found in com.ibm.icu.impl.data.LocaleElements_sr <clinit> *)
      |	"com.ibm.icu.impl.ICUListResourceBundle$Alias"

      (* found in com.google.javascript.jscomp.regex.CaseCanonicalize.<clinit> *)
      |	"com.google.javascript.jscomp.regex.CaseCanonicalize$DeltaSet"

      (* found in xmlbeans-2.6.0/build/lib/saxon.jar *)
      |	"net.sf.saxon.charcode.GB2312CharacterSet"

      |	"java.util.HashMap"

      (* found in fop *)
      |	"org.apache.batik.gvt.text.GVTAttributedCharacterIterator$TextAttribute" ->
	 if ms#name <> "<init>" then
	   raise
             (JCH_failure
                (LBLOCK [ STR "JCHTransformUtils:check_invoke: complicated";
                          STR "not safe at: "; iInfo#toPretty ]))

      (* found in com.google.javascript.jscomp.regex.CaseCanonicalize.<clinit> *)
      |	"com.google.javascript.jscomp.regex.CharRanges" ->
	 let name = ms#name in
	 if name <> "withRanges" && name <> "inclusive" && name <> "withMembers"then
	   raise
             (JCH_failure
                (LBLOCK [ STR "JCHTransformUtils:check_invoke: complicated";
                          STR "not safe at: "; iInfo#toPretty ]))

      (* found in com.google.common.net.TldPatterns.<clinit> *)
      |	"com.google.common.collect.ImmutableList"

        (* found in com.google.javascript.jscomp.regex.CaseCanonicalize.<clinit> *)
        | "com.google.common.collect.ImmutableSet" ->
	  if ms#name <> "of" then
	   raise
             (JCH_failure
                (LBLOCK [ STR "JCHTransformUtils:check_invoke: complicated";
                          STR "not safe at: "; iInfo#toPretty ]))

      |	"java.util.Collections" -> (* found in fop *)
	 if ms#name <> "synchronizedMap" then
	   raise
             (JCH_failure
                (LBLOCK [ STR "JCHTransformUtils:check_invoke: complicated";
                          STR "not safe at: "; iInfo#toPretty ]))

      |	_ ->
	  let cms = make_cms cn ms in
	  let mInfo = app#get_method cms in
	  if mInfo#get_analysis_exclusions = [] then
	   raise
             (JCH_failure
                (LBLOCK [ STR "JCHTransformUtils:check_invoke: complicated";
                          STR "not safe at: "; iInfo#toPretty ]))

    method !walkCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | OPERATION op ->

	begin
	  match op.op_name#getBaseName with
	  | "i"
	  | "ii" ->
	     let bcloc = get_bytecode_location
                           proc_name#getSeqNumber op.op_name#getSeqNumber in
	    let iInfo = app#get_instruction bcloc in
	    begin
	      match mInfo#get_opcode op.op_name#getSeqNumber with
	      | OpInvokeStatic (cn, ms)
	      | OpInvokeSpecial (cn, ms)
	      | OpInvokeInterface (cn, ms) ->
		 self#check_invoke cn ms iInfo

	      | OpInvokeVirtual _
	      | OpGetStatic _
	      | OpGetField _ ->
	         raise
                   (JCH_failure
                      (LBLOCK [ STR "JCHTransformUtils:proc_checker:walkCmd: complicated";
                          STR "not safe at: "; iInfo#toPretty ]))
	      | _ -> ()
	    end
	  | _ -> super#walkCmd cmd
	end
    | _ -> super#walkCmd cmd

    method does_not_need_to_be_analyzed =
      let args = JCHSystemUtils.get_signature_read_vars proc in
      let ret_opt = JCHSystemUtils.get_return_var proc in
      match args with
      | [] ->
	 begin
	   try
	     self#walkCode proc#getBody;
	     Option.is_none ret_opt
	   with
           | _ ->
	      if mInfo#get_instruction_count > 100 then
	        pr__debug [STR "possible large safe method: ";
                           proc_name#toPretty; STR " ";
                           proc_name_pp proc_name; NL];
	      false
	 end
      | _ -> false
  end

(* Note: this function is not called anywhere *)
let does_not_need_to_be_analyzed proc_name proc =
  let proc_checker = new proc_checker_t proc_name proc in
  proc_checker#does_not_need_to_be_analyzed


(* A var collector of variables modified when running the program.
 * Some variables are writes in ASSERTs and flow control ops
 *  but they are not modifed when running the program *)
class read_write_var_collector_t (_proc_name:symbol_t) =
  object (self: _)

    inherit var_collector_t

    val read_vars = new VariableCollections.set_t
    val write_vars = new VariableCollections.set_t
    val read_write_vars = new VariableCollections.set_t

    method getReadVars = read_vars
    method getWriteVars = write_vars
    method getReadWriteVars = read_write_vars


    method !walkCmd  (cmd: (code_int, cfg_int) command_t) =
      match cmd with
      | CODE (_, code) ->
	  self#walkCode code
      | CFG (_, cfg) ->
	  let states = cfg#getStates in
	    List.iter (fun s -> self#walkCode (cfg#getState s)#getCode) states
      | RELATION code ->
	  self#walkCode code
      | TRANSACTION (_, code, post_code) ->
	  begin
	    self#walkCode code;
	    match post_code with
	      | None -> ()
	      | Some code -> self#walkCode code
	  end
      | ABSTRACT_VARS l ->
	  write_vars#addList l
      |	ASSIGN_SYM (v, SYM _)
      | ASSIGN_NUM (v, NUM _) ->
	  write_vars#add v
      |	ASSIGN_NUM (v, PLUS (y,z))
      |	ASSIGN_NUM (v, MINUS (y,z))
      |	ASSIGN_NUM (v, MULT (y,z))
      |	ASSIGN_NUM (v, DIV (y,z)) ->
	  write_vars#add v;
	  read_vars#addList [y; z]
      | INCREMENT (v, _) ->
	  read_write_vars#add v;
      | ASSIGN_NUM (v, NUM_VAR w)
      | ASSIGN_STRUCT (v, w)
      |	ASSIGN_ARRAY (v, w)
      | ASSIGN_SYM (v, SYM_VAR w) ->
	  write_vars#add v;
	  read_vars#add w;
      | READ_NUM_ELT (v, a, i) ->
         (* Arrays are introduced only for arrays of numbers *)
	  write_vars#add v;
	  read_vars#addList [a; i]
      |	ASSIGN_NUM_ELT (a, i, v) ->
	  read_write_vars#add a;
	  read_vars#addList [i; v]
      |	SHIFT_ARRAY (tgt, src, _n) ->
         (* Only for arrays of numbers *)
	  write_vars#add tgt;
	  read_vars#add src
      |	BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
         (* Only for arrays of numbers *)
	  write_vars#add tgt;
	  read_vars#addList [tgt; tgt_o; src; src_o; n]
      |	SET_ARRAY_ELTS (a, s, n, v) ->
         (* Only for arrays of numbers *)
	  write_vars#add a;
	  read_vars#addList [a; s; n; v]
      |	OPERATION {op_name = opname; op_args = args} ->
	 if opname#getBaseName = "phi"
            || opname#getBaseName = "final_phi" then
           ()
	  else
	    let addArg (_s, v, mode) =
	      match mode with
	      | READ ->
		  read_vars#add v
	      | WRITE ->
		  write_vars#add v
	      |	_ ->
		  read_write_vars#add v in
	    List.iter  addArg args
      |	DOMAIN_OPERATION (_, {op_name = _opnm; op_args = args}) ->
	  let addArg (_, v, mode) =
	    match mode with
	    | READ ->
		read_vars#add v
	    | WRITE ->
		write_vars#add v
	    | _ ->
		read_write_vars#add v in
	  List.iter addArg args
      |	_ -> ()

    method get_vars_in_code code =
      self#walkCode code;
      (read_vars, write_vars, read_write_vars)

    method get_vars_in_cmd cmd =
      self#walkCmd cmd;
      (read_vars, write_vars, read_write_vars)


  end

let get_vars_in_code proc_name code =
  let collector = new read_write_var_collector_t proc_name in
  collector#get_vars_in_code code

let get_vars_in_cmd proc_name cmd =
  let collector = new read_write_var_collector_t proc_name in
  collector#get_vars_in_cmd cmd

(* A stack with a toPretty method *)
class ['a] pretty_stack_t =
  object

    inherit ['a] CHStack.stack_t

    method toPretty =
      pretty_print_list stack (fun s -> s#toPretty) "{" ", " "}"
  end

(* A class to manage stacks of versions of variables *)
class vv_stacks_t =
  object (self:_)

    val stacks : variable_t pretty_stack_t VariableCollections.table_t =
      new VariableCollections.table_t

    val number_assignments : pretty_int_t VariableCollections.table_t ref =
      ref (new VariableCollections.table_t)

    method get_tops =
      let table = new VariableCollections.table_t in
      let add_top var stack =
	try table#set var stack#top with _ -> () in
      stacks#iter add_top;
      table


    method increase_assignments (var:variable_t) =
      match !number_assignments#get var with
      |	Some num_p ->
	  let num = num_p#int in
	  !number_assignments#set var (new pretty_int_t (num + 1))
      |	None ->
	  !number_assignments#set var (new pretty_int_t (1))

    method push (var:variable_t) (new_var:variable_t) =
      let _ =
	match stacks#get var with
	| Some stack ->
	    stack#push new_var
	| None ->
	    let new_stack = new pretty_stack_t in
	    let _ = new_stack#push new_var in
	    stacks#set var new_stack in
      self#increase_assignments var

    method pop (num_assignments: pretty_int_t VariableCollections.table_t) =
      let pop_stack_var var =
	let stack = Option.get (stacks#get var) in
	let num = (Option.get (num_assignments#get var))#int in
	for _i = 0 to num - 1 do
	  let _ = stack#pop in
	  ()
	done in
      let vars = num_assignments#listOfKeys in
      List.iter pop_stack_var vars

    method get (var:variable_t) = stacks#get var

    method get_top (var:variable_t) =
      (Option.get (stacks#get var))#top

    method reset_num_assignments =
      number_assignments := new VariableCollections.table_t

    method num_assignments =
      !number_assignments

    method toPretty =
      LBLOCK [STR "stacks:"; NL; stacks#toPretty; NL;
	       STR "num_assignments:"; NL; !number_assignments#toPretty; NL]
  end

(* A class for equivalence classes of variables *)
class alias_sets_t =
  object (self:_)

    val representative : variable_t VariableCollections.table_t =
      new VariableCollections.table_t

    val constants : numerical_t VariableCollections.table_t =
      new VariableCollections.table_t

    method private change_rep (old_rep:variable_t) (new_rep:variable_t) =
      let change (var:variable_t) (rep:variable_t) =
	if rep#getIndex = old_rep#getIndex then
	  representative#set var new_rep in
      representative#iter change

    method add (var1: variable_t) (var2: variable_t) =
      let get_rep var =
	match representative#get var with
	| Some rep -> rep
	| None ->
	    begin
	      representative#set var var;
	      var
	    end in
      let rep1 = get_rep var1 in
      let rep2 = get_rep var2 in
      if self#better rep1 rep2 then
	self#change_rep rep2 rep1
      else self#change_rep rep1 rep2

    method add_const (var: variable_t) (c: numerical_t) =
      let first =  var#getName#getBaseName.[0] in
      if first = 's' || first = 't' then
	let const_var =
	  make_variable ("cN" ^ (string_of_big_int c#getNum)) NUM_VAR_TYPE in
	constants#set const_var c;
	self#add var const_var
      else ()

    method private isRegister (v:variable_t) =
      let str = v#getName#getBaseName in
      str.[0] = 'r' && str.[1] <> 'e'

    method private better (var1: variable_t) (var2: variable_t) =
      let isConstVar (v:variable_t) =
	v#getName#getBaseName.[0] = 'c' in
      let var1_index = var1#getIndex in
      let var2_index = var2#getIndex in
      if self#isRegister var1 then
        true
      else if self#isRegister var2 then
        false
      else if isConstVar var1 then
        true
      else if isConstVar var2 then
        false
      else if var1_index = exception_var_index then
        true
      else if var2_index = exception_var_index then
        false
      else if var2#isTmp then
        true
      else if var1#isTmp then
        false
      else if var1_index = num_return_var_index
              || var1_index = sym_return_var_index then
        true
      else if var2_index = num_return_var_index
              || var2_index = sym_return_var_index then
        false
      else
        var1#getName#getSeqNumber <= var2#getName#getSeqNumber

    (* set1 and set2 are singleton sets. They are used here to as a
     * reference to one variable *)
    method private set_to_better
                     (set1: VariableCollections.set_t)
                     (set2: VariableCollections.set_t) =
      let var1 = Option.get set1#choose in
      let var2 = Option.get set2#choose in
      if self#better var1 var2 then
	begin
	  set2#remove var2;
	  set2#add var1
	end
      else
	begin
	  set1#remove var1;
	  set1#add var2
	end

    method change_representative
             (subst: variable_t VariableCollections.table_t) =
      let change_rep (var:variable_t) (rep:variable_t) =
	match subst#get rep with
	| Some new_rep ->
	    representative#set var new_rep
	| _ -> () in
      representative#iter change_rep;
      let add_new (old_rep:variable_t) (rep:variable_t) =
	representative#set old_rep rep;
	representative#set rep rep in
      subst#iter add_new

    method get_representative (var:variable_t) =
      representative#get var

    method get_representatives =
      representative

    method find_aliased_locals =
      let aliased = ref [] in
      let add_alias (var:variable_t) (rep:variable_t) =
	if var#getIndex != rep#getIndex
           && self#isRegister var
           && self#isRegister rep then
	  aliased := (var, rep) :: !aliased
	else
          () in
      representative#iter add_alias;
      !aliased

    method toPretty =
      LBLOCK[ STR "representative: "; NL; representative#toPretty;
	      STR "constants: "; NL; constants#toPretty; NL]

  end


(* A class to manage versions of variables as well as
 * temporary variables needed when transforming a CHIF to
 * SSA form for cmds such as INCREMENT or any operations with
 * READ_WRITE variables *)
class ssa_variable_t =
  object

    val versions : pretty_int_t VariableCollections.table_t =
      new VariableCollections.table_t

    val stacks = ref (new vv_stacks_t)
    val scope = ref (F.mkScope ())

    method set_stacks (sts: vv_stacks_t) =
      stacks := sts

    method set_scope (sc:scope_int) =
      scope := sc

    method get_scope:scope_int = !scope

    method make_new_variable var =
      let increase_version num =
	versions#set var (new pretty_int_t num)  in
      let vname = var#getName in
      let new_name =
	match versions#get var with
	| Some num_p ->
	    let num = num_p#int in
	    increase_version (num + 1);
	    new symbol_t
	      ~atts: vname#getAttributes
	      ~seqnr: num
	      vname#getBaseName
	| None ->
	    begin
	      versions#set var (new pretty_int_t 1);
	      new symbol_t
		~atts: vname#getAttributes
		~seqnr: 0
		vname#getBaseName
	    end in
      let new_var =
	new variable_t
	  new_name
	  ~suffix:var#getSuffix
	  ~register:var#isRegister
	  ~path:var#getPath
	  var#getType in
      (!stacks)#push var new_var;
      (!scope)#removeVariable var;
      (!scope)#addVariable new_var;
      new_var

    val temp_counter = ref (-1)

    method make_new_temp (var: variable_t) =
      let temp_name =
	incr temp_counter;
	new symbol_t ("$temp" ^ (string_of_int !temp_counter)) in
      new variable_t temp_name var#getType

  end
