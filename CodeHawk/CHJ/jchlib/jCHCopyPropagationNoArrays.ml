(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
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
open CHAtlas
open CHCommon
open CHConstants
open CHIterator
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues
open CHNumericalConstantsDomainNoArrays
open CHPretty
open CHSymbolicConstantsDomainNoArrays
open CHUtils

(* jchlib *)
open JCHBasicTypes

[@@@warning "-27"]


class copy_propagation_domain_no_arrays_t =
object (self: 'a)

  inherit non_relational_domain_t

  val reverse_map: VariableCollections.set_t VariableCollections.table_t =
    new VariableCollections.table_t

  method private getValue' v =
    match (self#getValue v)#getValue with
      | SYM_CONSTANT_VAL s -> s
      | TOP_VAL -> topSymbolicConstant
      | _ -> raise (CHFailure (STR "Symbolic constant expected"))

  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (SYM_CONSTANT_VAL x))

  method special _cmd _args = {< >}

  method private importValue v =
    new non_relational_domain_value_t (SYM_CONSTANT_VAL (v#toSymbolicConstant))

  method private reconstruct_reverse_map table' =
    let reverse_map' = new VariableCollections.table_t in
    let add_pair src copy =
      let copies = match reverse_map'#get src with
	| None ->
           let c = new VariableCollections.set_t in
	   let _ = reverse_map'#set src c in
	   c
	| Some c -> c
      in
      copies#add copy
    in
    let _ = table'#iter (fun x c -> match c#getValue with
      | SYM_CONSTANT_VAL s ->
	begin
	  match s#getCst with
	    | SYM_CST s -> add_pair (unmarshalVariable s) x
	    | _ -> ()
	end
      | TOP_VAL -> ()
      | _ ->
         raise (CHFailure (STR "Symbolic constant expected"))
    )
    in
    reverse_map'

  method! meet ?variables (dom: 'a) =
    if bottom then
      self#mkBottom
    else if dom#isBottom then
      self#mkBottom
    else
      try
	let table' = self#meet_tables ?variables dom in
	let reverse_map' = self#reconstruct_reverse_map table' in
	{< bottom = false; table = table'; reverse_map = reverse_map' >}
      with Found -> self#mkBottom

  method! join ?variables (dom: 'a) =
    if bottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      let table' = self#join_tables ?variables dom in
      let reverse_map' = self#reconstruct_reverse_map table' in
      {< bottom = false; table = table'; reverse_map = reverse_map' >}

  method! widening ?kind ?variables (dom: 'a) =
    if bottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      let table' = self#widening_tables ?variables dom in
      let reverse_map' = self#reconstruct_reverse_map table' in
      {< bottom = false; table = table'; reverse_map = reverse_map' >}

  method! narrowing ?variables (dom: 'a) =
    if bottom then
      self#mkBottom
    else if dom#isBottom then
      self#mkBottom
    else
      try
	let table' = self#narrowing_tables ?variables dom in
	let reverse_map' = self#reconstruct_reverse_map table' in
	{< bottom = false; table = table'; reverse_map = reverse_map' >}
      with Found -> self#mkBottom

  method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let reverse_map' = reverse_map#clone in
      let default () =
	{< table = table'; reverse_map = reverse_map' >}
      in
      let set_copy src tgt =
	begin
	  table'#set tgt (mkSymbolicConstantValue (mkSymbolicConstant src#marshalToSymbol));
	  let copies' = match reverse_map#get src with
	    | Some copies -> copies#clone
	    | None -> new VariableCollections.set_t
	  in
	  copies'#add tgt;
	  reverse_map'#set src copies'
	end
      in
      let abstract_var v =
	begin
	  table'#remove v;
	  match reverse_map#get v with
	    | Some copies ->
	      begin
		copies#iter table'#remove;
		reverse_map'#remove v
	      end
	    | None -> ()
	end
      in
      match cmd with
	| ABSTRACT_VARS l ->
	  begin
	    List.iter abstract_var l;
	    default ()
	  end
	| ASSIGN_SYM (x, SYM_VAR y)
	| ASSIGN_NUM (x, NUM_VAR y) ->
	  let src = match (self#getValue' y)#getCst with
	    | SYM_CST s -> unmarshalVariable s
	    | _ -> y
	  in
	  begin
	    abstract_var x;
	    set_copy src x;
	    default ()
	  end
	| READ_SYM_ELT (x, _, _)
	| READ_NUM_ELT (x, _, _ )
	| INCREMENT (x, _)
	| ASSIGN_SYM (x, _)
	| ASSIGN_NUM (x, _) ->
	  begin
	    abstract_var x;
	    default ()
	  end
	| SELECT {selected = selected; _} ->
	  begin
	    List.iter (fun (_, v) -> abstract_var v) selected;
	    default ()
	  end
	| ASSERT FALSE ->
	  self#mkBottom
	| _ ->
	  default ()

  method private analyzeBwd' (_cmd: (code_int, cfg_int) command_t) =
    raise (JCH_failure (STR "No backward analysis for copy propogation"))

end


class copy_propagation_no_arrays_t system =
  let simplifier ~invariant ~context ~cmd =
    if invariant#isBottom then
      match cmd with
	| OPERATION _ -> cmd (* We do not remove operations *)
	| _ -> ASSERT FALSE
    else
      let copies =
        (invariant#getDomain "copy-prop")#observer#getNonRelationalVariableObserver in
      let simplify_var v =
	match (copies v)#getValue with
	  | SYM_CONSTANT_VAL s ->
	    begin
	      match s#getCst with
		| SYM_CST s -> unmarshalVariable s
		| _ -> v
	    end
	  | _ -> v
      in
      let simplify_num_exp e =
	match e with
	  | NUM n -> NUM n
	  | NUM_VAR v -> NUM_VAR (simplify_var v)
	  | PLUS (v1, v2) -> PLUS (simplify_var v1, simplify_var v2)
	  | MINUS (v1, v2) -> MINUS (simplify_var v1, simplify_var v2)
	  | MULT (v1, v2) -> MULT (simplify_var v1, simplify_var v2)
	  | DIV (v1, v2) -> DIV (simplify_var v1, simplify_var v2)
      in
      let simplify_sym_exp e =
	match e with
	  | SYM s -> SYM s
	  | SYM_VAR v -> SYM_VAR (simplify_var v)
      in
      let simplify_bool_exp e =
	match e with
	  | LEQ (v1, v2) -> LEQ (simplify_var v1, simplify_var v2)
	  | GEQ (v1, v2) -> GEQ (simplify_var v1, simplify_var v2)
	  | EQ (v1, v2) -> EQ (simplify_var v1, simplify_var v2)
	  | NEQ (v1, v2) -> NEQ (simplify_var v1, simplify_var v2)
	  | LT (v1, v2) -> LT (simplify_var v1, simplify_var v2)
	  | GT (v1, v2) -> GT (simplify_var v1, simplify_var v2)
	  | SUBSET (v, l) -> SUBSET (simplify_var v, l)
	  | DISJOINT (v, l) -> DISJOINT (simplify_var v, l)
	  | _ -> e
      in
      match cmd with
	| ASSIGN_NUM (x, e) -> ASSIGN_NUM (x, simplify_num_exp e)
	| ASSIGN_SYM (x, e) -> ASSIGN_SYM (x, simplify_sym_exp e)
	| ASSIGN_NUM_ELT (a, i, x) -> ASSIGN_NUM_ELT (a, simplify_var i, simplify_var x)
	| ASSIGN_SYM_ELT (a, i, x) -> ASSIGN_SYM_ELT (a, simplify_var i, simplify_var x)
	| READ_NUM_ELT (x, a, i) -> READ_NUM_ELT (x, a, simplify_var i)
	| READ_SYM_ELT (x, a, i) -> READ_SYM_ELT (x, a, simplify_var i)
	| SHIFT_ARRAY (tgt, src, shift) -> SHIFT_ARRAY (tgt, simplify_var src, shift)
	| ASSERT e -> ASSERT (simplify_bool_exp e)
	| OPERATION {op_name = op_name; op_args = op_args} ->
	   OPERATION {
               op_name = op_name;
               op_args = List.map (fun (a, v, m) -> (a, simplify_var v, m)) op_args}
	| CALL (f, args) -> CALL (f, List.map (fun (a, v) -> (a, simplify_var v)) args)
	| DOMAIN_CMD (dom, cmd, args) -> DOMAIN_CMD (dom, cmd, List.map (fun a ->
	  match a with
	    | NUM_DOM_ARG n -> NUM_DOM_ARG n
	    | VAR_DOM_ARG v -> VAR_DOM_ARG (simplify_var v)
	) args)
	| MOVE_VALUES (l, src, tgt) ->
           MOVE_VALUES (List.map simplify_var l, src, tgt)
	| MOVE_RELATIONS (l, src, tgt) ->
           MOVE_RELATIONS (List.map simplify_var l, src, tgt)
	| SELECT {selected = selected; from = from; where = where} ->
	   SELECT {
               selected = selected;
               from = simplify_var from;
               where = List.map (fun (s, v) -> (s, simplify_var v)) where}
	| INSERT {into = into; values = values} ->
	   INSERT {
               into = into;
               values = List.map (fun (s, v) -> (s, simplify_var v)) values}
	| DELETE {rows_from = rows_from; rows_where = rows_where} ->
	   DELETE {
               rows_from = rows_from;
               rows_where = List.map (fun (s, v) -> (s, simplify_var v)) rows_where}
	| _ ->
           cmd
  in
object
  val iterator =
    let strategy =
      {widening = (fun _ -> (true, ""));
       narrowing = (fun _ -> true);
      }
    in
    new iterator_t
      ~strategy:strategy ~do_narrowing:false ~cmd_processor:simplifier system

  method simplify_code code =
    let atlas =
      new atlas_t [
          ("num", new numerical_constants_domain_no_arrays_t);
	  ("sym", new symbolic_constants_domain_no_arrays_t);
	  ("copy-prop", new copy_propagation_domain_no_arrays_t)
	] ~db_num:"num" ~db_sym:"sym"
    in
    let sym = new symbol_t "proc" in
    let _ =
      iterator#runFwd
        ~iterate_on_transactions:false
        ~iterate_on_relations:false
        ~domains:["num"; "sym"; "copy-prop"]
        ~atlas:atlas (CODE (sym, code))
    in
    ()

end
