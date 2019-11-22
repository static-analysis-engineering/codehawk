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
open CHCommon
open CHConstants   
open CHDomain   
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues   
open CHNumerical   
open CHPretty
open CHUtils


class numerical_constants_domain_no_arrays_t =
object (self: 'a)
     
  inherit non_relational_domain_t
        
  method private getValue' v =
    match (self#getValue v)#getValue with
    | NUM_CONSTANT_VAL n -> n
    | TOP_VAL -> topNumericalConstant
    | _ -> raise (CHFailure (STR "Numerical constant expected"))
         
  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (NUM_CONSTANT_VAL x))
    
  method special cmd args = {< >}
                          
  method private importValue v =
    new non_relational_domain_value_t (NUM_CONSTANT_VAL (v#toNumericalConstant))
      
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
      | ASSIGN_NUM (v, NUM n) ->
	 begin
	   self#setValue' table' v (mkNumericalConstant n);
	   default ()
	 end
      | ASSIGN_NUM (v, NUM_VAR w) ->
	 begin
	   self#setValue' table' v (self#getValue' w);
	   default ()
	 end
      | ASSIGN_NUM (v, PLUS (x, y)) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 self#setValue' table' v (x_c#add y_c);
	 default ()
      | ASSIGN_NUM (v, MINUS (x, y)) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 self#setValue' table' v (x_c#sub y_c);
	 default ()
      | ASSIGN_NUM (v, MULT (x, y)) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 self#setValue' table' v (x_c#mult y_c);
	 default ()
      | ASSIGN_NUM (v, DIV (x, y)) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 self#setValue' table' v (x_c#div y_c);
	 default ()
      | INCREMENT (x, n) ->
	 let x_c = self#getValue' x in
	 self#setValue' table' x (x_c#add (mkNumericalConstant n));
	 default ()
      | READ_NUM_ELT (x, _, _) ->
	 table'#remove x;
	 default ()
      | ASSERT TRUE ->
	 default ()
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (LEQ (x, y)) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 begin
	   match (x_c#getCst, y_c#getCst) with
	   | (NUM_CST c1, NUM_CST c2) -> 
	      if c1#leq c2 then
		default ()
	      else
		self#mkBottom
	   | (_, _) -> default ()
	 end
      | ASSERT (GEQ (x, y)) ->
	 self#analyzeFwd' (ASSERT (LEQ (y, x)))
      | ASSERT (LT (x, y)) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 begin
	   match (x_c#getCst, y_c#getCst) with
	   | (NUM_CST c1, NUM_CST c2) -> 
	      if c1#lt c2 then
		default ()
	      else
		self#mkBottom
	   | (_, _) -> default ()
	 end
      | ASSERT (GT (x, y)) ->
	 self#analyzeFwd' (ASSERT (LT (y, x)))
      | ASSERT (EQ (x, y)) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 begin
	   match (x_c#getCst, y_c#getCst) with
	   | (NUM_CST c1, NUM_CST c2) -> 
	      if c1#equal c2 then
		default ()
	      else
		self#mkBottom
	   | (_, _) -> default ()
	 end
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
	   List.iter (fun v -> table'#remove v) l;
	   default ()
	 end
      | ASSIGN_NUM (x, NUM n) ->
	 let x_c = self#getValue' x in
	 let x_c' = x_c#meet (mkNumericalConstant n) in
	 if x_c'#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     default ()
	   end
      | ASSIGN_NUM (x, NUM_VAR y) ->
	 let x_c = self#getValue' x in
	 let y_c = self#getValue' y in
	 let y_c' = y_c#meet x_c in
	 if y_c'#isBottom then
	   self#mkBottom
	 else
	   begin	      
	     table'#remove x;
	     self#setValue' table' y y_c';
	     default ()
	   end
      | ASSIGN_NUM (x, PLUS (y, z)) ->
	 let x_c' = self#getValue' x in
	 let y_c' = self#getValue' y in
	 let z_c' = self#getValue' z in
	 let y_c = if x#equal y then topNumericalConstant else y_c' in
	 let z_c = if x#equal z then topNumericalConstant else z_c' in
	 let y_c'' = y_c#meet (x_c'#sub z_c) in
	 let z_c'' = z_c#meet (x_c'#sub y_c) in
	 if y_c''#isBottom || z_c''#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_c'';
	     self#setValue' table' z z_c'';
	     default()
	   end
      | ASSIGN_NUM (x, MINUS (y, z)) ->
	 let x_c' = self#getValue' x in
	 let y_c' = self#getValue' y in
	 let z_c' = self#getValue' z in
	 let y_c = if x#equal y then topNumericalConstant else y_c' in
	 let z_c = if x#equal z then topNumericalConstant else z_c' in
	 let y_c'' = y_c#meet (x_c'#add z_c) in
	 let z_c'' = z_c#meet (y_c#sub x_c') in
	 if y_c''#isBottom || z_c''#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_c'';
	     self#setValue' table' z z_c'';
	     default()
	   end	    
      | ASSIGN_NUM (v, MULT (x, y)) ->
	 begin
	   table'#remove v;
	   default ()
	 end
      | ASSIGN_NUM (v, DIV (x, y)) ->
	 begin
	   table'#remove v;
	   default ()
	 end
      | INCREMENT (x, n) ->
	 let x_c = self#getValue' x in
	 self#setValue' table' x (x_c#sub (mkNumericalConstant n));
	 default ()
      | READ_NUM_ELT (x, _, _) ->
	 table'#remove x;
	 default ()
      | ASSERT _ ->
	 let pre = self#analyzeFwd' cmd in
	 pre
      | _ ->
	 default ()    
	
end
  
