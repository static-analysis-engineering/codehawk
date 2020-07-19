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
open CHBounds
open CHCommon
open CHConstants   
open CHDomain
open CHIntervals   
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues   
open CHNumerical   
open CHPretty
open CHUtils

  
class intervals_domain_no_arrays_t =
object (self: 'a)
     
  inherit non_relational_domain_t
        
  method private getValue' v =
    match (self#getValue v)#getValue with
    | INTERVAL_VAL i -> i
    | TOP_VAL -> topInterval
    | _ -> raise (CHFailure (STR "Interval expected"))
	 
  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (INTERVAL_VAL x))
    
  method special cmd args = {< >}
                          
  method private importValue v =
    new non_relational_domain_value_t (INTERVAL_VAL (v#toInterval))
    
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
	   self#setValue' table' v (mkSingletonInterval n);
	   default ()
	 end
      | ASSIGN_NUM (v, NUM_VAR w) ->
	 begin
	   self#setValue' table' v (self#getValue' w);
	   default ()
	 end
      | ASSIGN_NUM (v, PLUS (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 self#setValue' table' v (x_i#add y_i);
	 default ()
      | ASSIGN_NUM (v, MINUS (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 self#setValue' table' v (x_i#sub y_i);
	 default ()
      | ASSIGN_NUM (v, MULT (x, y)) when x#equal y  ->
         let x_i = self#getValue' x in
         self#setValue' table' v x_i#square;
         default ()
      | ASSIGN_NUM (v, MULT (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 self#setValue' table' v (x_i#mult y_i);
	 default ()
      | ASSIGN_NUM (v, DIV (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 self#setValue' table' v (x_i#div y_i);
	 default ()
      | INCREMENT (x, n) ->
	 let x_i = self#getValue' x in
	 self#setValue' table' x (x_i#add (mkSingletonInterval n));
	 default ()
      | READ_NUM_ELT (x, _, _) ->
	 table'#remove x;
	 default ()
      | ASSERT TRUE ->
	 default ()
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (LEQ (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 let x_i' = x_i#upperBound y_i#getMax in
	 let y_i' = y_i#lowerBound x_i#getMin in
	 if x_i'#isBottom || y_i'#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' x x_i';
	     self#setValue' table' y y_i';
	     default ()
	   end
      | ASSERT (GEQ (x, y)) ->
	 self#analyzeFwd' (ASSERT (LEQ (y, x)))
      | ASSERT (LT (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 let x_i' = x_i#strictUpperBound y_i#getMax in
	 let y_i' = y_i#strictLowerBound x_i#getMin in
	 if x_i'#isBottom || y_i'#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' x x_i';
	     self#setValue' table' y y_i';
	     default ()
	   end
      | ASSERT (GT (x, y)) ->
	 self#analyzeFwd' (ASSERT (LT (y, x)))
      | ASSERT (EQ (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 let new_i = x_i#meet y_i in
	 if new_i#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' x new_i;
	     self#setValue' table' y new_i;
	     default ()
	   end		    
      | ASSERT (NEQ (x, y)) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 begin
	   match (x_i#singleton, y_i#singleton) with
	   | (Some x_c, Some y_c) ->
	      if x_c#equal y_c then
		self#mkBottom
	      else
		default ()
	   | (Some x_c, _) ->
	      begin
		match y_i#getMax#getBound with
		  NUMBER max when max#equal x_c ->
		  self#analyzeFwd' (ASSERT (LT (y, x)))
		| _ ->
		   match y_i#getMin#getBound with
		     NUMBER min  when min#equal x_c ->
		     self#analyzeFwd' (ASSERT (LT (x, y)))
		   | _ -> default ()
	      end
	   | (_, Some y_c) ->
	      begin
		match x_i#getMax#getBound with
		  NUMBER max when max#equal y_c ->
		  self#analyzeFwd' (ASSERT (LT (x, y)))
		| _ ->
		   match x_i#getMin#getBound with
		     NUMBER min when min#equal y_c ->
		     self#analyzeFwd' (ASSERT (LT (y, x)))
		   | _ ->
		      default ()
	      end
	   | _ ->
	      default ()
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
	   self#abstractVariables table' l;
	   default ()
	 end
      | ASSIGN_NUM (x, NUM n) ->
	 let x_i = self#getValue' x in
	 let x_i' = x_i#meet (mkSingletonInterval n) in
	 if x_i'#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     default ()
	   end
      | ASSIGN_NUM (x, NUM_VAR y) ->
	 let x_i = self#getValue' x in
	 let y_i = self#getValue' y in
	 let y_i' = y_i#meet x_i in
	 if y_i'#isBottom then
	   self#mkBottom
	 else
	   begin	      
	     table'#remove x;
	     self#setValue' table' y y_i';
	     default ()
	   end
      | ASSIGN_NUM (x, PLUS (y, z)) ->
	 let x_i' = self#getValue' x in
	 let y_i' = self#getValue' y in
	 let z_i' = self#getValue' z in
	 let y_i = if x#equal y then topInterval else y_i' in
	 let z_i = if x#equal z then topInterval else z_i' in
	 let y_i'' = y_i#meet (x_i'#sub z_i) in
	 let z_i'' = z_i#meet (x_i'#sub y_i) in
	 if y_i''#isBottom || z_i''#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_i'';
	     self#setValue' table' z z_i'';		    
	     default()
	   end
      | ASSIGN_NUM (x, MINUS (y, z)) ->
	 let x_i' = self#getValue' x in
	 let y_i' = self#getValue' y in
	 let z_i' = self#getValue' z in
	 let y_i = if x#equal y then topInterval else y_i' in
	 let z_i = if x#equal z then topInterval else z_i' in
	 let y_i'' = y_i#meet (x_i'#add z_i) in
	 let z_i'' = z_i#meet (y_i#sub x_i') in
	 if y_i''#isBottom || z_i''#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_i'';
	     self#setValue' table' z z_i'';
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
	 let x_i = self#getValue' x in
	 self#setValue' table' x (x_i#sub (mkSingletonInterval n));
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
  
