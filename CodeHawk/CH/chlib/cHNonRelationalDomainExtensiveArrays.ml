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
open CHCommunications   
open CHConstants   
open CHDomain
open CHDomainObserver   
open CHIntervals   
open CHLanguage
open CHNonRelationalDomainBase      
open CHNonRelationalDomainValues
open CHNumerical   
open CHPretty
open CHStridedIntervals
open CHUtils


class virtual non_relational_domain_extensive_arrays_t
                (do_precise_read_write: bool)
                (index_domain: string) =
object (self: 'a)
     
  inherit ['a] domain_downlink_int
  inherit non_relational_domain_base_int
        
  val indexDomain = index_domain
                  
  val precise_read_write_enabled = do_precise_read_write
                                 
  val expansions: interval_t VariableCollections.table_t =
    new VariableCollections.table_t
                                                         
  val arrays: ('v NumericalCollections.table_t) VariableCollections.table_t =
    new VariableCollections.table_t

  val expand_all_arrays: interval_t option = None
    
  method private setElement table a i v =
    match table#get a with
    | None ->
       if v#isTop then
	 ()
       else
	 let elts = new NumericalCollections.table_t in	    
	 let _ = elts#set i v in
	 table#set a elts
    | Some elts ->
       let elts' = elts#clone in
       let _ = if v#isTop then
	         elts'#remove i
	       else
	         elts'#set i v 
       in
       table#set a elts'
       
  method private getElements a =
    match arrays#get a with
    | None -> new NumericalCollections.table_t
    | Some t -> t
              
  method private getElement a i =
    match arrays#get a with
    | None -> topNonRelationalDomainValue
    | Some t ->
       begin
	 match t#get i with
	 | None -> topNonRelationalDomainValue
	 | Some v -> v
       end
      
  method private mkBottom' =
    {< arrays = new VariableCollections.table_t;
       expansions = new VariableCollections.table_t >}#mkBottom
    
  method private getExpansion v =
    match expand_all_arrays with
    | Some r -> r
    | none ->
       begin
	 match expansions#get v with
	 | None -> bottomInterval
	 | Some range -> range
       end
      
  method private setExpansion exp v r =
    if r#isBottom then
      exp#remove v
    else
      exp#set v r
    
  method private getIndex v =
    match ((self#getDownlink indexDomain)#observer#getNonRelationalVariableObserver v)#getValue with
    | INTERVAL_VAL i -> i
    | STRIDED_INTERVAL_VAL i -> stridedIntervalToInterval i
    | NUM_CONSTANT_VAL c ->
       begin
	 match c#getCst with
	 | NUM_CST n -> mkSingletonInterval n
	 | _ -> topInterval
       end
    | _ ->
       topInterval
      
  method observer =
    let observer' = self#observer' in
    object
      inherit domain_observer_t
            
      method getObservedVariables = observer'#getObservedVariables
                                  
      method getObservedArrays = arrays#listOfKeys
                               
      method getObservedArrayIndices a =
        match arrays#get a with
	| None -> []
	| Some elts -> elts#listOfKeys
                     
      method getNonRelationalVariableObserver = observer'#getNonRelationalVariableObserver
                                              
      method getNonRelationalExtensiveArrayObserver a i =
        match arrays#get a with
	| None ->
	   topNonRelationalDomainValue
	| Some elts ->
	   begin
	     match elts#get i with
	     | None -> topNonRelationalDomainValue
	     | Some v -> v
	   end
	  
    end
    
  method special (cmd: string) (args: domain_cmd_arg_t list) =
    match (cmd, args) with
    | ("expand array", [VAR_DOM_ARG a; NUM_DOM_ARG min; NUM_DOM_ARG max]) when a#isArray ->
       let expansions' = expansions#clone in	    
       let _ = self#setExpansion expansions' a (mkInterval min max) in
       {< expansions = expansions' >}
    | ("expand all arrays", [NUM_DOM_ARG min; NUM_DOM_ARG max]) ->
       {< expand_all_arrays = Some (mkInterval min max) >}
    | ("expand no arrays", []) ->
       {< expand_all_arrays = None >}
    | ("dismiss array", [VAR_DOM_ARG a]) when a#isArray ->
       let expansions' = expansions#clone in
       let arrays' = arrays#clone in
       let _ = expansions'#remove a in
       let _ = arrays'#remove a in
       {< expansions = expansions'; arrays = arrays' >}
    | _ ->
       {< >}
      
  method private abstractElements arrays' a abstract_r =
    if (self#getExpansion a)#leq abstract_r then
      arrays'#remove a
    else
      match arrays#get a with
      | Some elts ->
	 let elts' = elts#clone in
	 let _ = elts#iter (fun i _ -> if abstract_r#contains i then elts'#remove i) in
	 if elts'#size = 0 then
	   arrays'#remove a
	 else
	   arrays'#set a elts'
      | None -> ()
              
  method private abstractVariables' table' arrays' expansions' vars =
    List.iter (fun v ->
        if v#isArray 
	then
	  begin 
	    arrays'#remove v;
	    if v#isRegister || v#isTmp then expansions'#remove v else ()
	  end
	else
	  table'#remove v) vars
    
  method private assign_array_elt table' arrays' a i x =
    let expansion_r = self#getExpansion a in
    if expansion_r#isBottom then
      ()
    else
      let v = self#getValue x in
      let i_r = (self#getIndex i)#meet expansion_r in
      if i_r#isBottom then
	()
      else if v#isTop then
	self#abstractElements arrays' a i_r
      else		    
	match i_r#singleton with
	| Some index ->
	   let elts = (self#getElements a)#clone in
	   begin
	     elts#set index v;
	     arrays'#set a elts
	   end
	| None ->
	   if precise_read_write_enabled then
	     let elts = self#getElements a in
	     let elts' = elts#clone in
	     let _ =
               List.iter (fun i ->
		   match elts#get i with
		   | None -> 
		      ()
		   | Some e -> 
		      if i_r#contains i then
			let e' = v#join e in
			if e'#isTop then
			  elts'#remove i
			else
			  elts'#set i e'
		      else
			())
		         elts#listOfKeys
	     in
	     if elts'#size = 0 then
	       arrays'#remove a
	     else
	       arrays'#set a elts'
	   else
	     self#abstractElements arrays' a i_r
	  
  method private read_array_elt table' arrays' x a i =
    let expansion_r = self#getExpansion a in
    if expansion_r#isBottom then
      table'#remove x
    else
      let i_r = (self#getIndex i)#meet expansion_r in
      if i_r#isBottom then
	()
      else		    
	match i_r#singleton with
	| Some index ->
	   begin
	     match (self#getElements a)#get index with
	     | None -> table'#remove x
	     | Some e -> self#setValue table' x e
	   end
	| None ->
	   if precise_read_write_enabled then
	     let acc = ref None in
	     let elts = self#getElements a in
	     let _ = try 
		 i_r#iter (fun i ->
                     match elts#get i with
		     | None -> raise Found
		     | Some e ->
			begin
			  match !acc with
			  | None -> acc := Some e
			  | Some v -> acc := Some (v#join e)
			end)
	       with Found -> acc := None
	     in
	     match !acc with
	     | None -> table'#remove x
	     | Some e -> self#setValue table' x e				      
               
  method private abstract_elts arrays' expansions' a min max =
    let expansion_r = self#getExpansion a in
    if expansion_r#isBottom then
      ()
    else
      let min_i = self#getIndex min in
      let max_i = self#getIndex max in
      let min_i = min_i#upperBound max_i#getMax in
      let max_i = max_i#lowerBound min_i#getMin in
      if min_i#isBottom || max_i#isBottom then
	()
      else
	let r = min_i#join max_i in
	let abstract_r = expansion_r#meet r in
	if abstract_r#isBottom then
	  ()
	else if expansion_r#leq abstract_r then
	  arrays'#remove a
	else
	  self#abstractElements arrays' a abstract_r
	
  method analyzeFwd (cmd: (code_int, cfg_int) command_t) =
    if self#isBottom then
      self#mkBottom'
    else
      let table' = table#clone in
      let arrays' = arrays#clone in
      let expansions' = expansions#clone in
      let default () =
        {< table = table'; arrays = arrays'; expansions = expansions' >} in
      match cmd with
      | ABSTRACT_VARS l ->
	 self#abstractVariables' table' arrays' expansions' l;
	 default ()
      | ABSTRACT_ELTS (a, min, max) ->
	 self#abstract_elts arrays' expansions' a min max;
	 default ()
      | ASSIGN_ARRAY (a1, a2) ->
	 let _ = match arrays#get a2 with
	   | Some elts ->
	      if a1#isRegister || a1#isTmp then 
		begin
		  expansions'#set a1 (self#getExpansion a2);
		  arrays'#set a1 elts
		end
	      else
		let r1 = self#getExpansion a1 in
		let r2 = self#getExpansion a2 in
		if r1#isBottom then
		  ()
		else if r2#leq r1 then
		  arrays'#set a1 elts
		else
		  let r = r1#meet r2 in
		  let elts' = new NumericalCollections.table_t in
		  let _ =
                    elts#iter (fun i e ->
			if r#contains i then
			  elts'#set i e 
			else
			  ()) in
		  arrays'#set a1 elts'
	   | None ->
	      arrays'#remove a1
	 in
	 default ()
      | (ASSIGN_NUM_ELT (a, i, x) | ASSIGN_SYM_ELT (a, i, x)) ->
	 self#assign_array_elt table' arrays' a i x;
	 default ()
      | (READ_NUM_ELT (x, a, i) | READ_SYM_ELT (x, a, i)) ->
	 self#read_array_elt table' arrays' x a i;
	 default ()
      | BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
	 let _ =
           match ((self#getIndex tgt_o)#singleton,
                  (self#getIndex src_o)#singleton,
                  (self#getIndex n)#singleton) with
	   | (Some tgt_s, Some src_s, Some span) ->
	      (* We only consider the case when all array positions and the span are constant *)
	      let _ = match arrays#get src with
		| Some elts ->
		   let r = self#getExpansion tgt in
		   let elts' = match arrays#get tgt with
		     | Some tgt_elts -> tgt_elts#clone
		     | _ -> new NumericalCollections.table_t
		   in
		   let src_s_max = src_s#add (span#sub numerical_one) in
		   let _ =
                     elts#iter (fun i e ->
		         if src_s#leq i && i#leq src_s_max then
			   let i' = (i#sub src_s)#add tgt_s in
			   if r#contains i' then
			     elts'#set i' e
			   else
			     ()
		         else
			   ()
		       )
		   in
		   if elts'#size = 0 then
		     arrays'#remove tgt
		   else
		     arrays'#set tgt elts'
		| _ ->
		   arrays'#remove tgt
	      in
	      ()
	   | _ ->
	      arrays'#remove tgt
	 in
	 default ()
      | SET_ARRAY_ELTS (a, s, n, v) ->
	 let _ = match ((self#getIndex s)#singleton, (self#getIndex n)#singleton) with
	   | (Some start_i, Some span) ->
	      (* We only consider the case when the start index and the span are constant *)
	      let expansion_r = self#getExpansion a in
	      let elts' = match arrays#get a with
		| Some elts -> elts#clone 
		| _ -> new NumericalCollections.table_t
	      in
	      let i = ref start_i in
	      while (!i)#lt(start_i#add span) do
		if expansion_r#contains (!i) then
		  elts'#set (!i) (self#getValue v)
		else
		  ();
		i := (!i)#add numerical_one
	      done;
	      arrays'#set a elts'
	   | _ ->
	      arrays'#remove a
	 in
	 default ()
      | SHIFT_ARRAY (tgt, src, n) ->
	 let _ = match arrays#get src with
	   | Some elts ->
	      let r = self#getExpansion tgt in
	      let elts' = new NumericalCollections.table_t in
	      let _ =
                elts#iter (fun i e -> 
		    let i' = i#sub n in
		    if r#contains i' then
		      elts'#set i' e
		    else
		      ()) 
	      in
	      if elts'#size = 0 then
		arrays'#remove tgt
	      else
		arrays'#set tgt elts'
	   | None ->
	      arrays'#remove tgt
	 in
	 default ()
      | _ ->
	 self#analyzeFwd' cmd
        
  method analyzeBwd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | ABSTRACT_VARS _
      | ABSTRACT_ELTS _ ->
       self#analyzeFwd' cmd
    | ASSIGN_ARRAY (a1, a2) ->
       self#analyzeFwd' (ASSIGN_ARRAY (a2, a1))
    | ASSIGN_NUM_ELT (a, i, x)
      | ASSIGN_SYM_ELT (a, i, x) ->	  
       let table' = table#clone in
       let arrays' = arrays#clone in
       let expansions' = expansions#clone in
       let _ = self#read_array_elt table' arrays' x a i in
       let _ = self#abstract_elts arrays' expansions' a i i in
       {< table = table'; arrays = arrays'; expansions = expansions' >}
    | READ_NUM_ELT (x, a, i)	  
      | READ_SYM_ELT (x, a, i) ->
       let table' = table#clone in
       let arrays' = arrays#clone in
       let _ = self#assign_array_elt table' arrays' a i x in
       let _ = table'#remove x in
       {< table = table'; arrays = arrays' >}
    | BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
       (self#analyzeFwd (BLIT_ARRAYS (src, src_o, tgt, tgt_o, n)))#analyzeFwd (ABSTRACT_VARS [tgt])
    | SET_ARRAY_ELTS (a, s, n, _) ->
       (* The backward semantics of this operation can be modeled more precisely *)
       self#analyzeFwd (ABSTRACT_VARS [a])
    | SHIFT_ARRAY (tgt, src, n) ->
       (self#analyzeFwd (SHIFT_ARRAY (src, tgt, n#neg)))#analyzeFwd (ABSTRACT_VARS [tgt])
    | _ ->
       self#analyzeBwd' cmd
      
  method private leq ?(variables: (variable_t list) option) (dom: 'a) =
    if self#isBottom then
      true
    else if dom#isBottom then
      false
    else
      self#leq' dom && 
	let observer = dom#observer in
	let array_variables = new VariableCollections.set_t in
	let _ = match variables with
	  | Some vars ->
	     array_variables#addList (List.filter (fun v -> v#isArray) vars)
	  | None ->
	     array_variables#addList arrays#listOfKeys;
	     array_variables#addList observer#getObservedArrays
	in	
	try
	  let arrays' = observer#getNonRelationalExtensiveArrayObserver in	    
	  let _ =
            array_variables#iter
	      (fun a ->
		let indices = new NumericalCollections.set_t in
		let _ = match arrays#get a with
		  | Some elts -> indices#addList elts#listOfKeys
		  | None -> ()
		in
		let _ = indices#addList (observer#getObservedArrayIndices a) in
		indices#iter (fun i -> 
		    let e = self#getElement a i in
		    let e' = arrays' a i in
		    if e#leq e' then 
		      ()
		    else
		      raise Found)
	      )
	  in
	  true
	with Found -> false
	            
  method private meet_like operation ?variables (dom: 'a) =
    let observer = dom#observer in
    let array_variables = new VariableCollections.set_t in
    let _ = match variables with
      | Some vars ->
	 array_variables#addList (List.filter (fun v -> v#isArray) vars)
      | None ->
	 array_variables#addList arrays#listOfKeys;
	 array_variables#addList observer#getObservedArrays
    in	
    let arrays_res = new VariableCollections.table_t in
    let arrays' = observer#getNonRelationalExtensiveArrayObserver in	    
    let _ =
      array_variables#iter
        (fun a ->
	  let expansion_r = self#getExpansion a in
	  if expansion_r#isBottom then
	    ()
	  else 
	    let indices = new NumericalCollections.set_t in
	    let _ = match arrays#get a with
	      | Some elts -> indices#addList elts#listOfKeys
	      | None -> ()
	    in
	    let _ = indices#addList (observer#getObservedArrayIndices a) in
	    indices#iter (fun i ->
		if expansion_r#contains i then
		  let e = self#getElement a i in
		  let e' = arrays' a i in
		  let e'' = operation e e' in
		  if e''#isBottom then
		    raise Found
		  else
		    self#setElement arrays_res a i e''
		else
		  ())
        )
    in
    arrays_res
    
  method meet ?variables (dom: 'a) =
    if self#isBottom then
      self#mkBottom
    else if dom#isBottom then
      self#mkBottom
    else
      try
	{< table = self#meet_tables ?variables dom;
	   arrays = self#meet_like (fun e e' -> e#meet e') ?variables dom >}
      with Found -> self#mkBottom
	          
  method narrowing ?variables (dom: 'a) =
    if self#isBottom then
      self#mkBottom
    else if dom#isBottom then
      self#mkBottom
    else
      try
	{< table = self#narrowing_tables ?variables dom;
	   arrays = self#meet_like (fun e e' -> e#narrowing e') ?variables dom >}
      with Found -> self#mkBottom
	          
  method private join_like operation ?variables (dom: 'a) =
    let _ = pr_debug [STR "JOIN LIKE: "; NL;
		      STR "A = "; self#toPretty; NL;
		      STR "B = "; dom#toPretty; NL;
		     ]
    in
    let observer = dom#observer in
    let array_variables = new VariableCollections.set_t in
    let _ = match variables with
      | Some vars ->
	 array_variables#addList (List.filter (fun v -> v#isArray) vars)
      | None ->
	 array_variables#addList arrays#listOfKeys
    in	
    let arrays_res = new VariableCollections.table_t in
    let arrays' = observer#getNonRelationalExtensiveArrayObserver in	    
    let _ =
      array_variables#iter
        (fun a ->
	  let expansion_r = self#getExpansion a in
	  if expansion_r#isBottom then
	    ()
	  else 
	    let indices = new NumericalCollections.set_t in
	    let _ = match arrays#get a with
	      | Some elts -> indices#addList elts#listOfKeys
	      | None -> ()
	    in
	    indices#iter (fun i ->
		if expansion_r#contains i then
		  let e = self#getElement a i in
		  let e' = arrays' a i in
		  let e'' = operation e e' in
		  self#setElement arrays_res a i e''
	      )
        )
    in
    let _ = pr_debug [STR "RESULT= "; NL; arrays_res#toPretty; NL] in
    arrays_res
    
  method join ?variables (dom: 'a) =
    if self#isBottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      {< table = self#join_tables ?variables dom;
	 arrays = self#join_like (fun e e' -> e#join e') ?variables dom >}
    
  method widening ?(kind = "default") ?variables (dom: 'a) =
    if self#isBottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      let table' = self#widening_tables ?variables dom in
      match kind with
      | "default" ->
	 {< table = table';
	    arrays = self#join_like (fun e e' -> e#widening e') ?variables dom 
	 >}
      | "delayed" ->
	 {< table = table';
	    arrays = self#join_like (fun e e' -> e#join e') ?variables dom 
	 >}
      | _ ->
	 raise (CHFailure (LBLOCK [STR "Domain does not implement widening "; STR kind]))
	
  method toPretty =
    if self#isBottom then
      STR "_|_"
    else
      LBLOCK [STR "{"; NL; INDENT (tab, LBLOCK [STR "VARIABLES: "; table#toPretty; NL; 
						STR "ARRAYS: "; arrays#toPretty; NL]); STR "}"]
    
  method analyzeOperation
           ~(domain_name: string)
           ~(fwd_direction: bool)
           ~(operation: operation_t): 'a =
    raise (CHFailure (LBLOCK [STR "Domain "; STR domain_name;
                              STR " does not implement operation ";
                              operation.op_name#toPretty]))
    
end
        
