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

(* chlib *)
open CHCommon
open CHIntervals
open CHLanguage   
open CHNumerical   
open CHPretty

let pr_debug_vs (_p:pretty_t list) = ()

type base_offset_t = symbol_t * interval_t
type base_offset_null_t = symbol_t * interval_t * bool
type zero_offset_t = interval_t

let add_zero_offset_to_base_offsets (z:zero_offset_t) (b:base_offset_t list) =
  List.map (fun (s,i) -> (s, i#add z)) b 

let subtract_zero_offset_from_base_offsets (z:zero_offset_t) (b:base_offset_t list) =
  List.map (fun (s,i) -> (s,i#sub z)) b

let base_offsets_to_top (b:base_offset_t list) =
  List.map (fun (s,_) -> (s,topInterval)) b

let subtract_base_offsets (b1:base_offset_t list) (b2:base_offset_t list) =
  let rec merge l1 l2 r =
    match (l1, l2) with 
    | ([],_)
      | (_,[]) -> r
    | ((s1,i1)::t1,(s2,i2)::t2) ->
       match s1#compare s2 with
	 -1 -> merge t1 l2 r
       | 0  -> merge t1 t2 ((i1#sub i2)#join r)
       |  1 -> merge l1 t2 r 
       | _ -> raise (CHFailure (STR "Internal error in subtract_base_offsets")) in
  merge b1 b2 bottomInterval
  
let join_base_offsets (b1:base_offset_t list) (b2:base_offset_t list) =
  let rec merge l1 l2 r =
    match (l1, l2) with
    | ([],[]) -> (List.rev r)
    | (l,[])
      | ([],l) -> (List.rev ((List.rev l) @ r))
    | ((s1,i1)::t1,(s2,i2)::t2) ->
       match s1#compare s2 with
       | -1 -> merge t1 l2 ((s1,i1)::r)
       |  0 -> merge t1 t2 ((s1,i1#join i2)::r)
       |  1 -> merge l1 t2 ((s2,i2)::r)
       | _ -> raise (CHFailure (STR "Internal error in join_base_offsets")) in
  merge b1 b2 []
  
let interval_upper_bound (i1:interval_t) (i2:interval_t) = i1#upperBound i2#getMax
                                                         
let interval_lower_bound (i1:interval_t) (i2:interval_t) = i1#lowerBound i2#getMin
                                                         
let interval_strict_upper_bound (i1:interval_t) (i2:interval_t) = i1#strictUpperBound i2#getMax
                                                                
let interval_strict_lower_bound (i1:interval_t) (i2:interval_t) = i1#strictLowerBound i2#getMin
                                                                
let interval_widening (i1:interval_t) (i2:interval_t) =	if i1#isBottom then i2 else i1#widening i2
                                                      
class valueset_t (z_offset: interval_t) (b_offsets:(symbol_t * interval_t) list) (i_top:bool) =
object (self: 'a)
     
  (* Canonical representation:
   To          p: {< TopInterval, [], true >}
   Bottom : {< BottomInterval, [], false >}
   other  : {< z, [(s_k,i_k) ] , false >}
               where (s_k,i_k) is in ascending order wrt s_k ordering

   Intended semantics:
     zero_offset is a value that is constructed entirely from arithmetic operations
     on numerals;
     base_offsets (s_k,i_k) denote values that are offsets from a symbolic base s_k

   Specific values:
     {< TopInterval, [], false >} denotes an undetermined value that is not an offset
     to any symbolic base value

     {< BottomInterval, [ (s_1,BottomInterval) ; ... ; (s_k,BottomInterval) ], false >} is
     equivalent to Bottom
     {< z, [ (s_1,i_1), .., (s_j,i_j), (s_j+1, BottomInterval), (s_j+2,i_j+2) ...], false >} is
     equivalent to {< z, [ (s_1,i_1), .., (s_j,i_j), (s_j+2,i_j+2) ...], false >} 

   *)
     
  val zero_offset = z_offset
                  
  val top = i_top
          
  val base_offsets =
    if i_top then
      []
    else 
      List.sort (fun (s1,_) (s2,_) -> s1#compare s2) 
		(List.filter (fun (_, i) -> not i#isBottom) b_offsets)
    
  method length = List.length base_offsets
                
  method zeroOffset = zero_offset
                    
  method baseOffsets = base_offsets
                     
  method isBottom = zero_offset#isBottom && (self#length = 0)
                  
  method isTop = top
               
  method getValue = (self#zeroOffset, self#baseOffsets)
                  
  method zeroOffsetSingleton =
    if self#isTop || self#isBottom then
      None
    else
      match self#baseOffsets with
      | [] -> self#zeroOffset#singleton
      | _ -> None
           
  method isZeroOffset =
    if self#isTop || self#isBottom then
      false
    else
      match self#baseOffsets with
      | [] -> true
      | _ -> false
           
  method getZeroOffset =
    if self#isZeroOffset then
      self#zeroOffset
    else
      raise (CHFailure 
	       (LBLOCK [ STR "value set is not a zero-offset: " ; self#toPretty ]))
    
  method includesZero =
    not (self#zeroOffset#meet (mkSingletonInterval numerical_zero))#isBottom
    
  method isNull = self#isZeroOffset && self#hasNull
                
  method private hasNull =
    match zero_offset#singleton with
    | Some n -> n#equal numerical_zero
    | _ -> false
         
  method isSingleBase =
    if self#isTop || self#isBottom then
      false
    else
      match (self#zeroOffset#isBottom, self#baseOffsets) with
      | (true, [ (_,_) ]) -> true
      | _ -> false
	   
  method getSingleBase =
    if self#isSingleBase then
      List.hd self#baseOffsets
    else
      raise (CHFailure
	       (LBLOCK [ STR "value set is not a single base-offset: " ; self#toPretty]))
    
  method isSingleBaseNull =
    if self#isTop || self#isBottom then
      false
    else
      match (self#zeroOffset#isBottom, self#baseOffsets) with
      | (true, [ (_,_) ]) -> true
      | (_ , [ (_,_) ]) -> self#hasNull   
      | _ -> false

  method getSingleBaseNull =
    if self#isSingleBaseNull then
      let (s,i) = List.hd self#baseOffsets in
      (s,i,self#hasNull)
    else
      raise (CHFailure
	       (LBLOCK [ STR "value set is not a single base-offset: " ; self#toPretty]))
    
  method hasSingleBase (base:symbol_t) =
    if self#isSingleBase then
      let (s,_) = self#getSingleBase in
      s#equal base
    else
      false
    
  method getOffsetFromBase (base:symbol_t) =
    if self#hasSingleBase base then
      let (_,i) = self#getSingleBase in
      i
    else
      raise (CHFailure
	       (LBLOCK [ STR "value set is not a single base-offset with base " ; base#toPretty ;
			 STR ": value is " ; self#toPretty ]))
    
  method isMultipleBase =
    if self#isTop || self#isBottom then
      false
    else
      self#isBottom && self#length > 1
    
  method getMultipleBase =
    if self#isMultipleBase then
      self#baseOffsets
    else
      raise (CHFailure
	       (LBLOCK [ STR "value set is not a multiple base-offset: " ; self#toPretty]))
    
    
  method toPretty =
    if self#isTop then 
      STR "T" 
    else
      LBLOCK [ STR "[ " ; self#zeroOffset#toPretty ; STR ", " ; 
	       pretty_print_list self#baseOffsets 
		                 (fun (s,i) -> 
		                   LBLOCK [ STR "(" ; s#toPretty ; STR ": " ; i#toPretty ] )
		                 "[" ";" "]" ; STR "]" ]
    
  method mkBottom = {< zero_offset = bottomInterval ; base_offsets = [] ; top = false >}
                  
  method mkTop = {< zero_offset = topInterval ; base_offsets = [] ; top = true >}
               
  method clone = {< >}
               
  method removeNull =
    if self#hasNull then
      let _ = pr_debug_vs [ STR "Remove null" ; NL ] in
      {< zero_offset = bottomInterval >}
    else
      self#clone
    
  method removeZeroOffset = {< zero_offset = bottomInterval >}
                          
  method mkValueSet (z_offset:interval_t) (b_offsets:(symbol_t * interval_t) list) =
    if z_offset#isBottom &&
         List.for_all (fun (_,i) -> i#isBottom) b_offsets then
      self#mkBottom
    else
      let b_offsets' = List.sort (fun (s1,_) (s2,_) -> s1#compare s2) 
				 (List.filter (fun (_,i) -> not i#isBottom) b_offsets) in
      {< zero_offset = z_offset ; base_offsets = b_offsets' ; top = false >}
      
  method equal (a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, true) -> true
    | _ ->
       match (self#isBottom, a#isBottom) with
       | (true, true) -> true
       | (false, false) ->
	  (self#zeroOffset#equal a#zeroOffset) &&
	    (self#length = a#length) &&
	      List.for_all2 (fun (s1,i1) (s2,i2) -> s1#equal s2 && i1#equal i2)
			    self#baseOffsets a#baseOffsets
       | _ -> false
            
  method leq (a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, true) -> true
    | _ ->
       match (self#isBottom, a#isBottom) with
       | (true, _) -> true
       | (_, true) -> false
       | (false, false) ->
	  (self#zeroOffset#leq a#zeroOffset) &&
	    (self#length <= a#length) &&
	      List.for_all (fun (s,i) ->
		  List.exists (fun (s',i') -> s#equal s' && i#leq i') a#baseOffsets)
			   self#baseOffsets
	 
  method meet (a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, true) -> self#mkTop
    | (true, _) -> a#clone
    | (_, true) -> self#clone
    | _ ->
       match (self#isBottom, a#isBottom) with 
       | (true, _)
	 | (_, true) -> self#mkBottom 
       | (false, false) -> 
	  let z_offset = 
	    if a#includesZero && self#zeroOffset#isBottom then 
	      a#zeroOffset 
	    else 
	      self#zeroOffset#meet a#zeroOffset in
	  let b_offsets = 
	    List.fold_left 
	      (fun acc (s,i) -> 
		try let (s',i') =
		      List.find (fun (ss,_) -> ss#equal s) a#baseOffsets in 
		    (s', i'#meet i) :: acc 
		with 
		  Not_found -> acc) [] self#baseOffsets in 
	  self#mkValueSet z_offset (List.rev b_offsets) 
          
  (* note: join never results in top *)
  method join (a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, _)
      | (_, true) -> self#mkTop
    | _ ->
       match (self#isBottom, a#isBottom) with
       | (true, _) -> a#clone
       | (_, true) -> self#clone
       | (false, false) ->
	  let z_offset = self#zeroOffset#join a#zeroOffset in
	  let b_offsets = join_base_offsets self#baseOffsets a#baseOffsets in
	  self#mkValueSet z_offset b_offsets

  method widening (a: 'a) =
    let _ = pr_debug_vs [ STR "widen " ; self#toPretty ; STR " with " ; a#toPretty ; NL ] in
    match (self#isTop, a#isTop) with
    | (true, _)
      | (_, true) -> self#mkTop
    | _ ->
       match (self#isBottom, a#isBottom) with
       | (true, _) -> self#mkBottom
       | (_, true) -> self#clone
       | (false, false) ->
	  let z_offset = interval_widening self#zeroOffset a#zeroOffset in
	  let b_offsets =
	    let rec merge l1 l2 r =
	      match (l1, l2) with
	      | ([],[]) -> List.rev r
	      | ([],l)
		| (l,[]) -> List.rev ((List.rev l) @ r)
	      | ((s1,i1)::t1, (s2,i2)::t2) ->
		 match s1#compare s2 with
		 | -1 -> merge t1 l2 ((s1,i1)::r)
		 | 0  -> merge t1 t2 ((s1,interval_widening i1 i2)::r)
		 | 1  -> merge l1 t2 ((s2,i2)::r)
		 | _ ->
		    raise (CHFailure (STR "internal error in CHValueSets.widening")) in
	    merge self#baseOffsets a#baseOffsets [] in
	  let result = self#mkValueSet z_offset b_offsets in
	  let _ = pr_debug_vs [ INDENT (3, LBLOCK [ result#toPretty ; NL ]) ] in
	  result
	  
  method narrowing (a: 'a) =
    let _ = pr_debug_vs [ STR "narrow " ; self#toPretty ; STR " with " ; a#toPretty ; NL ] in
    match (self#isTop, a#isTop) with
    | (true, true) -> self#mkTop
    | _ ->
       match (self#isBottom, a#isBottom) with
       | (true, _)
	 | (_, true) -> self#mkBottom
       | (false, false) ->
	  let z_offset = self#zeroOffset#narrowing a#zeroOffset in
	  let b_offsets =
	    List.fold_left
	      (fun acc (s,i) ->
		try
		  let (s',i') = List.find (fun (ss,_) -> ss#equal s) a#baseOffsets in
		  (s',i#narrowing i') :: acc
		with
		  Not_found -> acc) [] self#baseOffsets in
	  let result = self#mkValueSet z_offset (List.rev b_offsets) in
	  let _ = pr_debug_vs [ INDENT (3, LBLOCK [ result#toPretty ; NL ]) ] in
	  result
	  
          
          
  method add (a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, true) ->  self#mkTop
    | (true, _) ->
       begin
	 if a#zeroOffset#isBottom then
	   self#mkValueSet bottomInterval (base_offsets_to_top a#baseOffsets)
	 else
	   self#mkTop
       end
    | (_, true) ->
       begin
	 if self#zeroOffset#isBottom then
	   self#mkValueSet bottomInterval (base_offsets_to_top self#baseOffsets)
	 else
	   self#mkTop
       end
    | _ ->
       match (self#isBottom, a#isBottom) with
       | (true, _) | (_, true) -> self#mkBottom
       | (false, false) ->
	  let zsum = self#zeroOffset#add a#zeroOffset in
	  let b1z2sum = List.map (fun (s,i) -> (s,i#add a#zeroOffset)) self#baseOffsets in
	  let b2z1sum = List.map (fun (s,i) -> (s,i#add self#zeroOffset)) a#baseOffsets in
	  let bsum = join_base_offsets b1z2sum b2z1sum in
	  self#mkValueSet zsum bsum
	  
  method sub (a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, _) -> self#mkTop
    | (_, true) ->
       self#mkValueSet topInterval (base_offsets_to_top self#baseOffsets)
    | (false, false) ->
       let zdiff = self#zeroOffset#sub a#zeroOffset in
       let bdiff = subtract_base_offsets self#baseOffsets a#baseOffsets in
       let zero_offset = zdiff#join bdiff in
       let b1z2diff = subtract_zero_offset_from_base_offsets a#zeroOffset self#baseOffsets in
       let b2z1diff = subtract_zero_offset_from_base_offsets self#zeroOffset a#baseOffsets in
       let base_offsets = join_base_offsets b1z2diff b2z1diff in
       self#mkValueSet zero_offset base_offsets
       
  method mult(a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, _) | (_, true) -> self#mkTop
    | _ ->
       self#mkValueSet (self#zeroOffset#mult a#zeroOffset) []
      
  method div(a: 'a) =
    match (self#isTop, a#isTop) with
    | (true, _) | (_, true) -> self#mkTop
    | _ ->
       self#mkValueSet (self#zeroOffset#div a#zeroOffset) []
      
  method upperBound (a: 'a) =
    match (self#isBottom, a#isBottom) with
    | (true, _) | (_, true) -> self#mkBottom
    | (false, false) ->
       if a#isTop || self#isTop then
	 {< >}
       else
	 let z = interval_upper_bound self#zeroOffset a#zeroOffset in
	 let b =
	   let rec merge l1 l2 r =
	     match (l1,l2) with
	     | ([],_) | (_,[]) -> List.rev r
	     | ((s1,i1)::t1,(s2,i2)::t2) ->
		match s1#compare s2 with
		| -1 -> merge t1 l2 r
		|  0 -> merge t1 t2 ((s1, interval_upper_bound i1 i2)::r)
		|  1 -> merge l1 t2 r 
		| _ -> raise (CHFailure (STR "Internal error in CHValueSets.upperBound")) in
	   merge self#baseOffsets a#baseOffsets [] in
	 self#mkValueSet z b
	 
  method lowerBound (a: 'a) =
    match (self#isBottom, a#isBottom) with
    | (true, _) | (_, true) -> self#mkBottom
    | (false, false) ->
       let _ = pr_debug_vs [ STR "lower bound with " ; a#toPretty ; NL ] in
       if a#isTop then
	 {< >}
       else if self#isTop && a#isZeroOffset then
	 let z = interval_lower_bound topInterval a#zeroOffset in
	 self#mkValueSet z []
       else if self#isTop then
	 {< >}
       else
	 let z = interval_lower_bound self#zeroOffset a#zeroOffset in
	 let b =
           if a#includesZero then 
	     self#baseOffsets
	   else
	     let rec merge l1 l2 r =
	       match (l1,l2) with
	       | ([],_) | (_,[]) -> List.rev r
	       | ((s1,i1)::t1,(s2,i2)::t2) ->
		  match s1#compare s2 with
		  | -1 -> merge t1 l2 r
		  |  0 -> merge t1 t2 ((s1, interval_lower_bound i1 i2)::r)
		  |  1 -> merge l1 t2 r 
		  | _ -> raise (CHFailure (STR "Internal error in CHValueSets.lowerBound")) in
	     merge self#baseOffsets a#baseOffsets [] in
	 self#mkValueSet z b
         
  method strictUpperBound (a: 'a) =
    match (self#isBottom, a#isBottom) with
    | (true, _) | (_, true) -> self#mkBottom
    | (false, false) ->
       if a#isTop || self#isTop then
	 {< >}
       else
	 let z = interval_strict_upper_bound self#zeroOffset a#zeroOffset in
	 let b =
	   let rec merge l1 l2 r =
	     match (l1,l2) with
	     | ([],_) | (_,[]) -> List.rev r
	     | ((s1,i1)::t1,(s2,i2)::t2) ->
		match s1#compare s2 with
		| -1 -> merge t1 l2 r
		|  0 -> merge t1 t2 ((s1, interval_strict_upper_bound i1 i2)::r)
		|  1 -> merge l1 t2 r 
		| _ -> raise (CHFailure (STR "Internal error in CHValueSets.strictUpperBound")) in
	   merge self#baseOffsets a#baseOffsets [] in
	 self#mkValueSet z b
         
  method strictLowerBound (a: 'a) =
    match (self#isBottom, a#isBottom) with
    | (true, _) | (_, true) -> self#mkBottom
    | (false, false) ->
       if a#isTop then
	 {< >}
       else if self#isTop && a#isZeroOffset then
	 let z = interval_strict_lower_bound topInterval a#zeroOffset in
	 self#mkValueSet z []
       else if self#isTop then
	 {< >}
       else
	 let _ = pr_debug_vs [ STR "strict lower bound with " ; a#toPretty ; NL ] in
	 let z = interval_strict_lower_bound self#zeroOffset a#zeroOffset in
	 let b =
           if a#includesZero then 
	     self#baseOffsets
	   else
	     let rec merge l1 l2 r =
	       match (l1,l2) with
	       | ([],_) | (_,[]) -> List.rev r
	       | ((s1,i1)::t1,(s2,i2)::t2) ->
		  match s1#compare s2 with
		  | -1 -> merge t1 l2 r
		  |  0 -> merge t1 t2 ((s1, interval_strict_lower_bound i1 i2)::r)
		  |  1 -> merge l1 t2 r 
		  | _ -> raise (CHFailure (STR "Internal error in CHValueSets.lowerBound")) in
	     merge self#baseOffsets a#baseOffsets [] in
	 self#mkValueSet z b
	 
end
  
  
let topValueSet = new valueset_t topInterval [] true
                
let bottomValueSet = new valueset_t bottomInterval [] false
                   
let topZeroOffset = new valueset_t topInterval [] false
                  
let mkZeroOffsetSingletonInterval n =
  new valueset_t (mkSingletonInterval n) [] false
  
let mkBaseOffsetSingletonInterval s n =
  new valueset_t bottomInterval [ (s, mkSingletonInterval n)] false
  
let mkBaseOffsetNullSingletonInterval s n =
  new valueset_t
      (mkSingletonInterval numerical_zero) [ (s, mkSingletonInterval n) ] false
  
