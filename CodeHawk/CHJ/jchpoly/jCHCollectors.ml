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

(* jchlib *)
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation


class loop_var_collector_t proc_name =
  object (self: _)

    inherit code_walker_t as super

    val vars = new VariableCollections.set_t
    val mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber)

    (* variables that are changed in a loop in a way that could make them
     * potentially unsafe bounds even if they are in a finite range *)
    method getVars = vars#toList

    method !walkVar _var = ()

    method addOpVars args =
      let addWrite (_s, v, m) =
	match (v#getType, m) with
	| (NUM_LOOP_COUNTER_TYPE, READ)
	| (NUM_TMP_VAR_TYPE, READ)
	| (NUM_VAR_TYPE, READ) ->
	    ()
	| _ ->
	    vars#add v in
      List.iter addWrite args

    method !walkCmd  (cmd: (code_int, cfg_int) command_t) =
    match cmd with
      |	ASSIGN_NUM (_, NUM _)
      |	ASSIGN_SYM (_, SYM _) ->
	  ()
      |	READ_SYM_ELT (x, _, _)
      |	READ_NUM_ELT (x, _, _)
      |	ASSIGN_SYM (x, _)
      |	ASSIGN_NUM (x, _)
      |	ASSIGN_ARRAY (x, _)
      |	ASSIGN_STRUCT (x, _)
      |	ASSIGN_NUM_ELT (x, _, _)
      |	ASSIGN_SYM_ELT (x, _, _) ->
	  vars#add x
      |	OPERATION op ->
	  begin
	    match op.op_name#getBaseName with
	    | "i"
	    | "ii" ->
	      let pc = op.op_name#getSeqNumber in
		begin
		  match mInfo#get_opcode pc with
		    | OpIfNull _
		    | OpIfCmpAEq _
		    | OpIfCmpANe _ -> () (* Have READ_WRITE variables which do not change *)
		    | OpArrayStore _ ->
			vars#add (JCHSystemUtils.get_arg_var "array" op.op_args)
		    | _ ->
			self#addOpVars op.op_args
		end
	    | "init_param" ->
		self#addOpVars (List.tl op.op_args)
	    | _ ->
		self#addOpVars op.op_args
	  end
      |	DOMAIN_OPERATION (_, op) ->
	  self#addOpVars (List.tl op.op_args)
      |	_ -> super#walkCmd cmd

  end

let collect_loop_vars (proc_name:symbol_t) (code:code_int) =
  let collector = new loop_var_collector_t proc_name in
  begin
    collector#walkCode code;
    collector#getVars
  end

class bound_var_collector_t (proc_name:symbol_t) =
object (self: _)

    inherit code_walker_t as super

    val vars = new VariableCollections.set_t
    val mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber)

    (* variables that appear in an ASSERT or a branching op *)
    method getVars = vars#toList
    method !walkVar _var = ()

    method walkOp pc args =
      match mInfo#get_opcode pc with
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
      | OpIfCmpLe _
      | OpIfNull _
      | OpIfNonNull _
      | OpIfCmpAEq _
      | OpIfCmpANe _ ->
	  let vs = List.map (fun (_,v,_) -> v) args in
	  vars#addList vs
      |	_ -> ()

    method !walkCmd  (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | OPERATION {op_name = opname; op_args = args} ->
	begin
	  match opname#getBaseName with
	  | "i"
	  | "ii" -> let pc = opname#getSeqNumber in self#walkOp pc args
	  | _ -> super#walkCmd cmd
	end
    | _ -> super#walkCmd cmd
end

let collect_bound_vars (proc_name:symbol_t) (code:code_int) =
  let collector = new bound_var_collector_t proc_name in
  begin
    collector#walkCode code;
    collector#getVars
  end

(* Collects information used in JCHLinEqsIntDomainNoArrays to project
 * out variables that are not used any more *)
class lin_eqs_info_collector_t
        (proc_name:symbol_t) (jproc_info:JCHProcInfo.jproc_info_t) =
object (self: _)

    inherit code_walker_t as super

    val cms = retrieve_cms proc_name#getSeqNumber
    val mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber)

    (* pc -> variables that are not used afterwards *)
    val pc_to_last_read = new IntCollections.table_t

    val state_name = ref (new symbol_t "state_name")

    (* last read in the current state *)
    val var_to_last_read = ref (new VariableCollections.table_t)

    (* the result of an operation *)
    val operation_results = ref (new VariableCollections.set_t)

    (* pcs of casts for the result of an operation *)
    val op_casts = new IntCollections.set_t

    val divisor_to_dividend_to_quotient = new VariableCollections.table_t

    method get_all_info =
      (pc_to_last_read, op_casts, divisor_to_dividend_to_quotient)

    method private get_instruction_info (pc:int) =
      let bcloc = get_bytecode_location cms#index pc in
      app#get_instruction bcloc

    method walkState (cfg:cfg_int) (state:symbol_t) =
      let add_last var pc_set =
	let pc = Option.get pc_set#choose in
	match pc_to_last_read#get pc with
	| Some set -> set#add var
	| _ -> pc_to_last_read#set pc (VariableCollections.set_of_list [var]) in
      begin
        !var_to_last_read#iter add_last;
        state_name := state;
        var_to_last_read := new VariableCollections.table_t;
        operation_results := new VariableCollections.set_t;
        self#walkCode (cfg#getState state)#getCode
      end

    method !walkCmd (cmd: (code_int, cfg_int) command_t) =
      match cmd with
      |	CFG (_, cfg) ->
	  List.iter (self#walkState cfg) cfg#getStates
      | OPERATION  {op_name = opname; op_args = args} ->
	  begin
	    match opname#getBaseName with
	    | "i"
	    | "ii" ->
	      let pc = opname#getSeqNumber in
	      begin
		let is_last_state jvar_info =
                  List.exists !state_name#equal jvar_info#get_last_states in
		let check var =
		  let jvar_info = jproc_info#get_jvar_info var in
		  if not jvar_info#is_parameter
                     && not jvar_info#is_local_var
                     && not jvar_info#is_return
                     && not (JCHSystemUtils.is_constant var)
                     && is_last_state jvar_info then
		    if List.for_all
                         (fun pc' -> pc' <> pc) jvar_info#get_origins then
                      (* We record only the last read in the state *)
		      !var_to_last_read#set var (IntCollections.set_of_list [pc]) in
		List.iter check (vars_in_cmd cmd);

		match mInfo#get_opcode pc with
		| OpAdd Int2Bool
		| OpSub Int2Bool
		| OpMult Int2Bool
		| OpNeg Int2Bool ->
		  let dst1 = JCHSystemUtils.get_arg_var "dst1" args in
		  !operation_results#add dst1
		| OpDiv Int2Bool
		| OpRem Int2Bool ->
		  let dst1 = JCHSystemUtils.get_arg_var "dst1" args in
		  !operation_results#add dst1
		| OpIInc _ ->
		  let src_dst = JCHSystemUtils.get_arg_var "src_dst" args in
		  if JCHSystemUtils.is_loop_counter src_dst then
                    ()
		  else
                    !operation_results#add src_dst
		| OpI2B
		| OpI2C
		| OpI2S ->
		  let src1 = JCHSystemUtils.get_arg_var "src1" args in
		  if !operation_results#has src1 then
		    op_casts#add pc
		| _ -> ()

	      end
	    | _ -> super#walkCmd cmd
	  end
      |	ASSIGN_NUM (v, DIV (x, y)) ->
	  let dividend_to_quotient =
	    match divisor_to_dividend_to_quotient#get y with
	    | Some table -> table
	    | None ->
	       let table = new VariableCollections.table_t in
               begin
		 divisor_to_dividend_to_quotient#set y table;
		 table
               end in
	  dividend_to_quotient#set x v
      |	_ -> super#walkCmd cmd
  end

let collect_lin_eqs_info
      (proc_name:symbol_t) (jproc_info: JCHProcInfo.jproc_info_t) =
  let collector = new lin_eqs_info_collector_t proc_name jproc_info in
  let proc = jproc_info#get_procedure in
  begin
    collector#walkCode proc#getBody;
    collector#get_all_info
  end


(* Collects information used in JCHLinEqsIntDomainNoArrays to project
 * out variables that are not used any more *)
class state_pcs_collector_t =
object (self: _)

    inherit code_walker_t as super

    (* state -> pcs in state *)
    val state_to_pcs = new SymbolCollections.table_t

    val state_name_opt = ref None
    val pcs = ref (new IntCollections.set_t)

    method get_state_to_pcs = state_to_pcs

    method walkState (cfg:cfg_int) (state:symbol_t) =
      begin
        (match !state_name_opt with
         | Some state_name ->
	    state_to_pcs#set state_name !pcs
         | _ -> ());
        state_name_opt := Some state;
        pcs := new IntCollections.set_t;
        self#walkCode (cfg#getState state)#getCode
      end

    method !walkCmd (cmd: (code_int, cfg_int) command_t) =
      match cmd with
      |	CFG (_, cfg) ->
	  List.iter (self#walkState cfg) cfg#getStates
      | OPERATION  {op_name = opname; op_args = _args} ->
	  begin
	    match opname#getBaseName with
	    | "i"
	    | "ii" ->
	      !pcs#add opname#getSeqNumber
	    | _ -> ()
	  end
      |	_ -> super#walkCmd cmd
  end

let collect_state_pcs  (jproc_info: JCHProcInfo.jproc_info_t) =
  let collector = new state_pcs_collector_t in
  let proc = jproc_info#get_procedure in
  begin
    collector#walkCode proc#getBody;
    collector#get_state_to_pcs
  end
