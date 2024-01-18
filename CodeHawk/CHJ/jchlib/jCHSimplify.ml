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
open CHLanguage
open CHUtils

module CstProp = CHConstantPropagationNoArrays
module CopyProp = JCHCopyPropagationNoArrays


class cmd_filter_t used_vars =
object (self)

  inherit code_transformer_t as super

  method! transformCode code =
    begin
      for i = 0 to code#length - 1 do
	code#setCmdAt i (self#transformCmd (code#getCmdAt i))
      done;
      code#removeSkips
    end

  method! transformCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
      | ASSIGN_NUM (x, _)
      | ASSIGN_SYM (x, _)
      | ABSTRACT_ELTS (x, _, _)
      | ASSIGN_ARRAY (x, _)
      | INCREMENT (x, _)
      | ASSIGN_NUM_ELT (x, _, _)
      | ASSIGN_SYM_ELT (x, _, _)
      | READ_NUM_ELT (x, _, _)
      | READ_SYM_ELT (x, _, _)
      | SHIFT_ARRAY (x, _, _)
      | INSERT {into = x; _}
      | DELETE {rows_from = x; _}
      | ASSIGN_TABLE (x, _) ->
	if used_vars#has x then
	  cmd
	else
	  SKIP
      | ABSTRACT_VARS l ->
         ABSTRACT_VARS (List.filter (fun v -> used_vars#has v) l)
      | MOVE_VALUES (l, src, tgt) ->
	let l' = List.filter (fun v -> used_vars#has v) l in
	begin
	  match l' with
	    | [] -> SKIP
	    | _ -> MOVE_VALUES (l', src, tgt)
	end
      | MOVE_RELATIONS (l, src, tgt) ->
	let l' = List.filter (fun v -> used_vars#has v) l in
	begin
	  match l' with
	    | [] -> SKIP
	    | _ -> MOVE_RELATIONS (l', src, tgt)
	end
      | SELECT {selected = selected; from = from; where = where} ->
	let selected' = List.filter (fun (_, v) -> used_vars#has v) selected in
	begin
	  match selected' with
	    | [] -> SKIP
	    | _ -> SELECT {selected = selected'; from = from; where = where}
	end
      | CODE (_, code) ->
	  let _ = self#transformCode code in
(*	  if code#length = 0 then
	    SKIP
	  else if code#length = 1 then
	    code#getCmdAt 0
	  else
	    cmd *)
	  cmd
      | _ ->
	super#transformCmd cmd
end


class skip_remover_t =
object

  inherit code_walker_t as super

  method! walkCode code =
    code#removeSkips;
    super#walkCode code

end


class simplifier_t (code_set: system_int) =
object (self: _)

  method cst_propagation = new CstProp.constant_propagation_no_arrays_t code_set

  method copy_propagation = new CopyProp.copy_propagation_no_arrays_t code_set

  method remove_useless_commands proc =
    let code = proc#getBody in
    let used_vars = new VariableCollections.set_t in
    let _ = used_vars#addList (read_vars_in_code code code_set) in
    let _ = used_vars#addList (List.map snd proc#getBindings) in
    let filter = new cmd_filter_t used_vars in
    filter#transformCode code

  method remove_unused_vars (proc: procedure_int) =
    let all_vars = new VariableCollections.set_t in
    let _ = all_vars#addList proc#getScope#getVariables in
    let used_vars = new VariableCollections.set_t in
    let _ =
      used_vars#addList
        (List.filter (fun v -> not(v#isTmp)) (vars_in_code proc#getBody)) in
    let unused_vars = all_vars#diff used_vars in
    proc#getScope#removeVariables unused_vars#toList

  method remove_skips code =
    let skip_remover = new skip_remover_t in
    skip_remover#walkCode code

  method simplify_procedure (proc: procedure_int) =
    self#cst_propagation#simplify_code proc#getBody;
    self#remove_useless_commands proc;
    self#remove_unused_vars proc;
    self#copy_propagation#simplify_code proc#getBody;
    self#remove_useless_commands proc;
    self#remove_unused_vars proc;
    self#remove_skips proc#getBody

end
