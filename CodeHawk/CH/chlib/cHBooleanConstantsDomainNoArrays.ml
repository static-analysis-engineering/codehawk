(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet and Henny Sipma
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
  ============================================================================== *)

(* chlib *)
open CHCommon
open CHConstants
open CHLanguage   
open CHNonRelationalDomainNoArrays   
open CHNonRelationalDomainValues   
open CHNumericalConstraints   
open CHPretty


class boolean_constants_domain_no_arrays_t =
object (self: 'a)
     
  inherit non_relational_domain_t
        
  method private getValue' v =
    match (self#getValue v)#getValue with
    | BOOL_CONSTANT_VAL b -> b
    | TOP_VAL -> topBooleanConstant
    | _ -> raise (CHFailure (STR "Boolean constant expected"))

  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (BOOL_CONSTANT_VAL x))

  method special _cmd _args = {< >}

  method private importValue v =
    new non_relational_domain_value_t (NUM_CONSTANT_VAL (v#toNumericalConstant))

  method! importNumericalConstraints (_csts: numerical_constraint_t list) = {< >}

  method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
	{< table = table' >}
      in
      match cmd with
      | ABSTRACT_VARS l ->
	  begin
	    self#abstractVariables table' l;
	    default ()
	  end
      | ASSIGN_NUM (x, NUM_VAR y)
      | ASSIGN_SYM (x, SYM_VAR y) ->
	  self#setValue' table' x (self#getValue' y);
	  default ()
      | ASSIGN_NUM (x, PLUS (y, z))
      | ASSIGN_NUM (x, MINUS (y, z))
      | ASSIGN_NUM (x, MULT (y, z))
      | ASSIGN_NUM (x, DIV (y, z)) ->
	  let yv = self#getValue' y in
	  let zv = self#getValue' z in
	  begin
	    self#setValue' table' x (yv#join zv) ;
	    default ()
	  end
      | READ_SYM_ELT (x, _, _) 
      | READ_NUM_ELT (x, _, _) ->
	  table'#remove x;
	  default()
      | ASSERT FALSE ->
	  self#mkBottom
      | _ ->
	  default ()


  method private analyzeBwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
	{< table = table' >}
      in
      match cmd with
      | ABSTRACT_VARS l ->
	  begin
	    self#abstractVariables table' l;
	    default ()
	  end
      | ASSIGN_SYM (x, SYM_VAR y)
      | ASSIGN_NUM (x, NUM_VAR y) ->
	  let xv = self#getValue' x in
	  let yv = self#getValue' y in
	  let yv' = yv#meet xv in
	  if yv'#isBottom then
	    self#mkBottom
	  else
	    begin
	      table'#remove x;
	      self#setValue' table' y yv';
	      default ()
	    end
      | READ_NUM_ELT (x, _, _)
      | READ_SYM_ELT (x, _, _) ->
	  table'#remove x ;
	  default ()
      | ASSERT _ ->
	  self#analyzeFwd' cmd
      | _ -> 
	  default ()

end
