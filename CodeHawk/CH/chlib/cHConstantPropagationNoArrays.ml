(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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
open CHAtlas
open CHConstants   
open CHIterator   
open CHLanguage
open CHNonRelationalDomainValues   
open CHNumericalConstantsDomainNoArrays   
open CHSymbolicConstantsDomainNoArrays

[@@@warning "-27"]

class constant_propagation_no_arrays_t system =
  let simplifier ~invariant ~context ~cmd =
    if invariant#isBottom then
      match cmd with
      | OPERATION _ | DOMAIN_OPERATION _ -> cmd (* We do not remove operations *)
      | _ -> ASSERT FALSE
    else
      let num_inv = (invariant#getDomain "num")#observer#getNonRelationalVariableObserver in
      let sym_inv = (invariant#getDomain "sym")#observer#getNonRelationalVariableObserver in
      let getNumConst v =
	match (num_inv v)#getValue with
	| NUM_CONSTANT_VAL c -> 
	   begin
	     match c#getCst with
	     | NUM_CST n -> Some n
	     | _ -> None
	   end
	| INTERVAL_VAL i -> i#singleton
        | STRIDED_INTERVAL_VAL i -> i#singleton
	| _ -> None
      in
      let getSymConst v =
	match (sym_inv v)#getValue with
	| SYM_CONSTANT_VAL c -> 
	   begin
	     match c#getCst with
	     | SYM_CST s -> Some s
	     | _ -> None
	   end
	| SYM_SET_VAL s -> s#singleton
	| _ -> None
      in
      match cmd with
      | ASSIGN_NUM (v, NUM_VAR x) ->
	 begin
	   match getNumConst x with
	   | None -> cmd
	   | Some c -> ASSIGN_NUM (v, NUM c)
	 end
      | ASSIGN_NUM (v, PLUS (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> ASSIGN_NUM (v, NUM (c1#add c2))
	   | _ -> cmd
	 end
      | ASSIGN_NUM (v, MINUS (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> ASSIGN_NUM (v, NUM (c1#sub c2))
	   | _ -> cmd
	 end
      | ASSIGN_NUM (v, MULT (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> ASSIGN_NUM (v, NUM (c1#mult c2))
	   | _ -> cmd
	 end
      | ASSIGN_NUM (v, DIV (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> ASSIGN_NUM (v, NUM (c1#div c2))
	   | _ -> cmd
	 end
      | ASSIGN_SYM (v, SYM_VAR x) ->
	 begin
	   match getSymConst x with
	   | Some s -> ASSIGN_SYM (v, SYM s)
	   | None -> cmd
	 end
      | ASSERT (LEQ (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) ->  if c1#leq c2 then SKIP else ASSERT FALSE
	   | _ -> cmd
	 end
      | ASSERT (GEQ (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> if c1#geq c2 then SKIP else ASSERT FALSE
	   | _ -> cmd
	 end
      | ASSERT (LT (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> if c1#lt c2 then SKIP else ASSERT FALSE
	   | _ -> cmd
	 end
      | ASSERT (GT (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> if c1#gt c2 then SKIP else ASSERT FALSE
	   | _ -> cmd
	 end
      | ASSERT (EQ (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> if c1#equal c2 then SKIP else ASSERT FALSE
	   | _ -> cmd
	 end
      | ASSERT (NEQ (x, y)) ->
	 begin
	   match (getNumConst x, getNumConst y) with
	   | (Some c1, Some c2) -> if c1#equal c2 then ASSERT FALSE else SKIP
	   | _ -> cmd
	 end
      | ASSERT (SUBSET (x, syms)) ->
	 begin
	   match getSymConst x with
	   | Some s ->  if List.exists (fun s' -> s#equal s') syms then SKIP else ASSERT FALSE
	   | None -> cmd
	 end	      
      | ASSERT (DISJOINT (x, syms)) ->
	 begin
	   match getSymConst x with
	   | Some s ->  if List.exists (fun s' -> s#equal s') syms then ASSERT FALSE else SKIP
	   | None -> cmd
	 end	      
      | _ -> cmd
  in
  object (self: _)
       
    val iterator = 
      let strategy = {widening = (fun _ -> (true, ""));
		      narrowing = (fun _ -> true);
		     }
      in
      new iterator_t ~strategy:strategy ~do_narrowing:false ~cmd_processor:simplifier system
      
    method simplify_code code =
      let atlas = new atlas_t [("num", new numerical_constants_domain_no_arrays_t);
			       ("sym", new symbolic_constants_domain_no_arrays_t)]
                      ~db_num:"num" ~db_sym:"sym"
      in
      let sym = new symbol_t "proc" in
      let _ = iterator#runFwd ~domains:["num"; "sym"] ~atlas:atlas (CODE (sym, code)) in
      ()
      
    method simplify proc =
      self#simplify_code (system#getProcedure proc)#getBody
      
  end
  
  
