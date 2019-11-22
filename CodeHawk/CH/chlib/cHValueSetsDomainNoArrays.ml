(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
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

(* chlib  *)
open CHCommon
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues   
open CHNumerical   
open CHPretty
open CHValueSets


let pr_debug_vs p = ()
let command_to_pretty = CHLanguage.command_to_pretty 0
                      
class valueset_domain_no_arrays_t =
object (self: 'a)
     
  inherit non_relational_domain_t
        
  method private getValue' v =
    match (self#getValue v)#getValue with
    | VALUESET_VAL v -> v
    | TOP_VAL -> topValueSet
    | _ -> 
       begin
	 pr_debug_vs [ STR "Failure: " ; v#toPretty ; STR " is " ;
		       (new non_relational_domain_value_t
                            (self#getValue v)#getValue)#toPretty ] ;
	 
	 raise (CHFailure 
		  (LBLOCK [ STR "Value set expected: " ; v#toPretty ; STR " is " ; 
			    (new non_relational_domain_value_t
                                 (self#getValue v)#getValue)#toPretty ]))
       end

  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (VALUESET_VAL x))

  method special cmd args = {< >}

  method private importValue v = 
    new non_relational_domain_value_t (VALUESET_VAL (v#toValueSet))

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
	   pr_debug_vs [ command_to_pretty cmd ; NL ;
			 INDENT (3, LBLOCK [ v#toPretty ; STR " := " ; 
					     (mkZeroOffsetSingletonInterval n)#toPretty ; NL ]) ] ;
	   self#setValue' table' v (mkZeroOffsetSingletonInterval n);
	   default ()
	 end
      | ASSIGN_NUM (v, NUM_VAR w) ->
	 begin
	   self#setValue' table' v (self#getValue' w) ;
	   default ()
	 end
      | ASSIGN_NUM (v, PLUS (x,y)) ->
	 let x_v = self#getValue' x in
	 let y_v = self#getValue' y in
	 let sum = x_v#add y_v in
	 let _ = pr_debug_vs [ command_to_pretty cmd ; NL ;
			       INDENT (3, LBLOCK [ x_v#toPretty ; STR " + " ;
                                                   y_v#toPretty ; STR " = " ; 
						   sum#toPretty ; NL ]) ] in
	 if sum#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' v sum;
	     default ()
	   end
      | ASSIGN_NUM (v, MINUS (x,y)) ->
	 let x_v = self#getValue' x in
	 let y_v = self#getValue' y in
	 let diff = x_v#sub y_v in
	 let _ = pr_debug_vs [ command_to_pretty cmd ; NL ;
			       INDENT (3, LBLOCK [ x_v#toPretty ;
                                                   STR " - " ; y_v#toPretty ; STR " = " ; 
						   diff#toPretty ; NL ]) ] in
	 if diff#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' v diff;
	     default ()
	   end
      | ASSIGN_NUM (v, MULT (x,y)) ->
	 let x_v = self#getValue' x in
	 let y_v = self#getValue' y in
	 let prod = x_v#mult y_v in
	 if prod#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' v prod;
	     default ()
	   end
      | ASSIGN_NUM (v, DIV(x,y)) ->
	 let x_v = self#getValue' x in
	 let y_v = self#getValue' y in
	 let quot = x_v#div y_v in
	 if quot#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' v quot ;
	     default ()
	   end
      | INCREMENT (x,n) ->
	 let x_v = self#getValue' x in
	 begin
	   self#setValue' table' x (x_v#add (mkZeroOffsetSingletonInterval n));
	   default ()
	 end
      | READ_NUM_ELT (x, _, _) ->
	 begin
	   table'#remove x;
	   default ()
	 end
      | ASSERT TRUE ->
	 default ()
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (LEQ (x,y)) ->
	 let _ = pr_debug_vs [ command_to_pretty cmd ; NL ] in
	 let x_v = self#getValue' x in
	 let y_v = self#getValue' y in
	 let x_v' = x_v#upperBound y_v in
	 let y_v' = y_v#lowerBound x_v in
	 let _ = pr_debug_vs [ INDENT (3, LBLOCK [STR "x_v  = " ; x_v#toPretty ; NL ;
						  STR "y_v  = " ; y_v#toPretty ; NL ;
						  STR "x_v' = " ; x_v'#toPretty ; NL ;
						  STR "y_v' = " ; y_v'#toPretty ; NL ]) ] in
	 if x_v'#isBottom || y_v'#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' x x_v' ;
	     self#setValue' table' y y_v' ;
	     default ()
	   end
      | ASSERT (LT (x,y)) ->
	 let _ = pr_debug_vs [ command_to_pretty cmd ; NL ] in
	 let x_v = self#getValue' x in
	 let y_v = self#getValue' y in
	 let x_v' = x_v#strictUpperBound y_v in
	 let y_v' = y_v#strictLowerBound x_v in
	 let _ = pr_debug_vs [ INDENT (3, LBLOCK [STR "x_v  = " ; x_v#toPretty ; NL ;
						  STR "y_v  = " ; y_v#toPretty ; NL ;
						  STR "x_v' = " ; x_v'#toPretty ; NL ;
						  STR "y_v' = " ; y_v'#toPretty ; NL ]) ] in
	 if x_v'#isBottom || y_v'#isBottom then
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' x x_v' ;
	     self#setValue' table' y y_v' ;
	     default ()
	   end	 
      | ASSERT (GEQ (x,y)) ->
	 self#analyzeFwd' (ASSERT (LEQ (y,x)))
      | ASSERT (GT (x,y)) ->
	 self#analyzeFwd' (ASSERT (LT (y,x)))
      | ASSERT (EQ (x,y)) ->
	 let _ = pr_debug_vs [ command_to_pretty cmd ; NL ] in
	 begin
	   let x_v = self#getValue' x in
	   let y_v = self#getValue' y in
	   let new_v = x_v#meet y_v in
	   if new_v#isBottom then
	     self#mkBottom
	   else
	     let _ = pr_debug_vs [ INDENT (3, LBLOCK [ STR "x_v = "   ; x_v#toPretty ; NL ; 
						       STR "y_v = "   ; y_v#toPretty ; NL ;
						       STR "new_v = " ; new_v#toPretty ; NL] ) ] in 
	     begin
	       self#setValue' table' x new_v ;
	       self#setValue' table' y new_v ;
	       default ()
	     end
	 end
      | ASSERT (NEQ (x,y)) ->
	 let _ = pr_debug_vs [ command_to_pretty cmd ; NL ] in
	 begin
	   let x_v = self#getValue' x in
	   let y_v = self#getValue' y in
	   if y_v#isNull then
	     let new_v = x_v#removeNull in
	     if new_v#isBottom then
	       self#mkBottom
	     else
	       let _ = pr_debug_vs [ INDENT (3, LBLOCK [ STR "x_v = "   ; x_v#toPretty ; NL ; 
							 STR "y_v = "   ; y_v#toPretty ; NL ;
							 STR "new_v = " ; new_v#toPretty ; NL] ) ] in 
	       begin
		 self#setValue' table' x new_v ;
		 default ()
	       end
	   else if x_v#isNull then
	     let new_v = y_v#removeNull in
	     if new_v#isBottom then
	       self#mkBottom
	     else
	       let _ = pr_debug_vs [ INDENT (3, LBLOCK [ STR "x_v = "   ; x_v#toPretty ; NL ; 
							 STR "y_v = "   ; y_v#toPretty ; NL ;
							 STR "new_v = " ; new_v#toPretty ; NL] ) ] in 
	       begin
		 self#setValue' table' y new_v ;
		 default ()
	       end
	   else
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
	 let x_v = self#getValue' x in
	 let x_v' = x_v#meet (mkZeroOffsetSingletonInterval n) in
	 let _ = pr_debug_vs [ STR "(bw) " ; command_to_pretty cmd ; NL ;
			       INDENT (3, LBLOCK [x_v#toPretty ; STR " -> "  ;
                                                  x_v'#toPretty ; NL ])] in
	 if x_v'#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     default ()
	   end
      | ASSIGN_NUM (x, NUM_VAR y) ->
	 let x_v = self#getValue' x in
	 let y_v = self#getValue' y in
	 let y_v' = y_v#meet x_v in
	 let _ = pr_debug_vs [ STR "(bw) " ; command_to_pretty cmd ; NL ] in
	 let _ = pr_debug_vs [ INDENT (3, LBLOCK [ y_v#toPretty ; 
						   STR " meet " ; 
						   x_v#toPretty ; STR " -> "  ;
                                                   y_v'#toPretty ; NL ])] in
	 if y_v'#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_v';
	     default ()
	   end
      | ASSIGN_NUM (x, PLUS (y, z))  ->
	 let x_v' = self#getValue' x in
	 let y_v' = self#getValue' y in
	 let z_v' = self#getValue' z in
	 let y_v = if x#equal y then topValueSet else y_v' in
	 let z_v = if x#equal z then topValueSet else z_v' in
	 let y_v'' = y_v#meet (x_v'#sub z_v) in
	 let z_v'' = z_v#meet (x_v'#sub y_v) in
	 let _ = pr_debug_vs [ STR "(bw)" ; command_to_pretty cmd ; NL ;
			       INDENT (3,
				       LBLOCK [ y_v'#toPretty ; STR " -> " ;
                                                y_v''#toPretty ; NL ;
						z_v'#toPretty ; STR " -> " ;
                                                z_v''#toPretty ; NL ]) ] in
	 if y_v''#isBottom || z_v''#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_v'' ;
	     self#setValue' table' z z_v'' ;
	     default ()
	   end
      | ASSIGN_NUM (x, MINUS (y, z)) ->
	 let x_v' = self#getValue' x in
	 let y_v' = self#getValue' y in
	 let z_v' = self#getValue' z in
	 let y_v = if x#equal y then topValueSet else y_v' in
	 let z_v = if x#equal z then topValueSet else z_v' in
	 let y_v'' = y_v#meet (x_v'#add z_v) in
	 let z_v'' = z_v#meet (y_v#sub x_v') in
	 let _ = pr_debug_vs [ STR "(bw)" ; command_to_pretty cmd ; NL ;
			       INDENT (3,
				       LBLOCK [ y_v'#toPretty ; STR " -> " ;
                                                y_v''#toPretty ; NL ;
						z_v'#toPretty ; STR " -> " ;
                                                z_v''#toPretty ; NL ]) ] in
	 if y_v''#isBottom || z_v''#isBottom then
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_v'' ;
	     self#setValue' table' z z_v'' ;
	     default ()
	   end
      | ASSIGN_NUM (v, MULT (_, _))
        | ASSIGN_NUM (v, DIV (_, _)) ->
	 begin
	   table'#remove v;
	   default ()
	 end
      | INCREMENT (x, n) ->
	 let x_v' = self#getValue' x in
	 begin
	   self#setValue' table' x (x_v'#sub (mkZeroOffsetSingletonInterval n));
	   default ()
	 end
      | READ_NUM_ELT (v, _, _) ->
	 begin
	   table'#remove v;
	   default ()
	 end
      | ASSERT _ ->
	 begin
	   pr_debug_vs [ STR "analyze ASSERT bw" ; NL ];
	   self#analyzeFwd' cmd
	 end
      | _ ->
	 default ()
	
  method analyzeOperation ~(domain_name:string) ~(fwd_direction:bool) 
                          ~(operation:operation_t):'a =
    let name = operation.op_name#getBaseName in
    let table' = table#clone in
    let default () = {< table = table' >} in
    match name with
      "initialize" ->
      begin
	List.iter (fun (s,v,_) ->
	    begin
	      self#setValue' table' v 
		             (mkBaseOffsetSingletonInterval v#getName numerical_zero)
	    end) operation.op_args;
	default ()
      end
    | "initialize_with_null" ->
       begin
	 List.iter (fun (s,v,_) ->
	     begin
               let _ = pr_debug_vs [ STR "Initialize with null" ; NL ] in
	       self#setValue' table' v
		              (mkBaseOffsetNullSingletonInterval v#getName numerical_zero)
	     end) operation.op_args;
	 default ()
       end
    | "set_unknown_scalar" ->
       begin
	 List.iter (fun (_,v,_) -> self#setValue' table' v topZeroOffset)
	           operation.op_args ;
	 default ()
       end
    | _ ->
       default ()
      


end
