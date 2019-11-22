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
open CHBitstring
open CHCommon
open CHMatrix   
open CHNumerical
open CHPolyhedraGlobalData
open CHPretty
open CHSaturationMatrix   
open CHVector

module Cherni = CHChernikova

type tsign_t =
  | Tsign_bottom
  | Tsign_gt
  | Tsign_eq
  | Tsign_lt
  | Tsign_geq
  | Tsign_leq
  | Tsign_top

let tsign_is_leq x y =
  if x = y || y = Tsign_top then
    true
  else
    match x with
    | Tsign_bottom -> true
    | Tsign_gt -> y = Tsign_geq
    | Tsign_eq -> y = Tsign_geq || y = Tsign_leq
    | Tsign_lt -> y = Tsign_leq
    | _ -> false
	 
let tsign_union x y =
  if x = y || x = Tsign_top || y = Tsign_bottom then
    x
  else if y = Tsign_top || x = Tsign_bottom then
    y
  else
    match x with
    | Tsign_gt ->
       if y = Tsign_eq || y = Tsign_geq then
	 Tsign_geq
       else
	 Tsign_top
    | Tsign_eq ->
       if y = Tsign_gt || y = Tsign_geq then
	 Tsign_geq
       else if y = Tsign_lt || y = Tsign_leq then
	 Tsign_leq
       else
	 Tsign_top
    | Tsign_lt ->
       if y = Tsign_eq || y = Tsign_leq then
	 Tsign_leq
       else
	 Tsign_top
    | Tsign_geq ->
       if y = Tsign_eq || y = Tsign_gt then
	 Tsign_geq
       else
	 Tsign_top
    | Tsign_leq ->
       if y = Tsign_eq || y = Tsign_lt then
	 Tsign_leq
       else
	 Tsign_top
    | _ ->
       raise (CHFailure (STR "Polyhedra #7: Internal error in tsign_union")) 
      
class polyhedron_t dim =
object (self: 'a)
     
  val _c: matrix_t option ref = ref None
                              
  val _f: matrix_t option ref = ref None
                              
  val _satC: satmat_t option ref = ref None
                                 
  val _satF: satmat_t option ref = ref None
                                 
  val _dim: int = dim
                
  val _nbeq: int ref = ref 0
                     
  val _nbline: int ref = ref 0
                       
                       
  method mkNew dim =
    {< _c = ref None;
       _f = ref None;
       _satC = ref None;
       _satF = ref None;
       _dim = dim;
       _nbeq = ref 0;
       _nbline = ref 0
    >}
    
  method toPretty =
    LBLOCK [STR "{"; NL;
	    INDENT (2,
		    LBLOCK [STR "C= "; NL; (match !_c with
                                            | Some c -> c#toPretty
                                            | None -> STR "empty"); NL;
			    STR "F= "; NL; (match !_f with
                                            | Some f -> f#toPretty
                                            | None -> STR "empty"); NL;
			    STR "dim= "; INT _dim; NL;
			    STR "nbeq= "; INT !_nbeq; NL;
			    STR "nbline= "; INT !_nbline; NL
			   ]
		   );
	    STR "}"
	   ]
    
  method set_c (c: matrix_t) = _c := Some c
                             
  method set_f (f: matrix_t) = _f := Some f
                             
  method reset_c = _c := None
                 
  method reset_f = _f := None
                 
  method set_satC (satC: satmat_t) = _satC := Some satC
                                   
  method set_satF (satF: satmat_t) = _satF := Some satF
                                   
  method reset_satC = _satC := None
                    
  method reset_satF = _satF := None
                    
  method set_nbeq (nbeq: int) = _nbeq := nbeq
                              
  method set_nbline (nbline: int) = _nbline := nbline
                                  
  method c = _c
           
  method f = _f
           
  method satC = _satC
              
  method satF = _satF
              
  method dim = _dim
             
  method nbeq = !_nbeq
              
  method nbline = !_nbline
                
  method nbeq_ref = _nbeq
                  
  method nbline_ref = _nbline
                    
  method mkUniverse (dim: int) =
    let gd = !(pGD) in
    if dim < 0 || dim > gd#maxcolumns - gd#dec then
      raise (CHFailure (LBLOCK [ STR "Polyhedra: Cannot create polyhedron with ";
                                 INT dim; STR " dimensions in mkUniverse"]))
    else
      ();
    let po = self#mkNew dim in
    let po_c = new matrix_t (gd#dec - 1) (gd#dec + dim) true in
    let po_f = new matrix_t (gd#dec + dim - 1) (gd#dec + dim) true in
    let po_satC = new satmat_t (gd#dec + dim - 1) (gd#dec - 1) in
    let _ = 
      begin
	po#set_c po_c;
	po#set_f po_f;
	po#set_satC po_satC;
	po#reset_satF;
	po#set_nbeq 0;
	po#set_nbline dim;
	
	(* lines x_i *)
	for i = 0 to dim - 1 do
	  po_f#set i (gd#dec + dim - 1 - i) numerical_one
	done;
	if (gd#strict) then
	  (* Not implemented *)
	  ()
	else
	  begin
	    (* Ray x_i *)
	    po_f#set dim 0 numerical_one;
	    po_f#set dim gd#cst numerical_one;
	    (* Constraint x_i >= 0 *)
	    po_c#set 0 0 numerical_one;
	    po_c#set 0 gd#cst numerical_one;
	    (* Saturation matrix *)
	    po_satC#set_p dim 0 bitstring_msb
	  end	
      end
    in
    po
    
  method minimize =
    match (!_c, !_f) with
    | (Some _, Some _) -> ()
    | (None, None) -> ()
    | (Some _, None) ->
       Cherni.minimize true _c _f _satF _nbeq _nbline
    | (None, Some _) ->
       Cherni.minimize false _f _c _satC _nbline _nbeq
      
  method is_empty =
    match !_f with
    | Some _ -> false
    | None ->
       begin
	 match !_c with
	 | Some _ ->
	    begin
	      self#minimize;
	      match (!_c, !_f) with
	      | (None, None) -> true
	      | _ -> false
	    end
	 | None -> true		  
       end
      
  method is_universe =
    if (is_none !_c) && (is_none !_f) then
      false
    else
      try
	if (is_none !_c) || (is_none !_f) then
	  begin
	    self#minimize;
	    if is_none !_c then
	      raise Found
	    else
	      ()
	  end
	else
	  ();
	match !_c with
	| None -> raise (CHFailure (STR "Polyhedra #8: Inconsistency in is_universe"))
	| Some c -> c#nbrows = (!pGD)#dec - 1
      with Found -> false
                  
  method is_minimal =
    match (!_c, !_f) with
    | (Some _, Some _) -> true
    | (None, None) -> true
    | _ -> false
         
  method copy =
    let npo_c = match !_c with
      | Some m -> Some m#copy
      | None -> None
    in
    let npo_f = match !_f with
      | Some m -> Some m#copy
      | None -> None
    in
    let npo_satC = match !_satC with
      | Some m -> Some m#copy
      | None -> None
    in
    let npo_satF = match !_satF with
      | Some m -> Some m#copy
      | None -> None
    in
    {< _c = ref npo_c; 
       _f = ref npo_f;
       _satC = ref npo_satC;
       _satF = ref npo_satF;
       _nbeq = ref !_nbeq;
       _nbline = ref !_nbline
    >}
    
  method check =
    let res =
      match (!_c, !_f) with
      | (None, _) 
	| (_, None) ->
	 !_nbeq = 0
         && !_nbline = 0
         && (match (!_satC, !_satF) with 
	     | (None, None) -> true 
	     | _ -> false)
      | (Some c, Some f) ->
	 (match (!_satC, !_satF) with
	  | (Some satC, Some satF) ->
	     (Cherni.checksatmat true c f satC)
	     && (Cherni.checksatmat false f c satF)
	     && (Cherni.checksat true c !_nbeq f !_nbline satC)
	  | (Some satC, None) ->
	     (Cherni.checksatmat true c f satC)
	     && (Cherni.checksat true c !_nbeq f !_nbline satC)
	  | (None, Some satF) ->
	     (Cherni.checksatmat false f c satF)
	     && (Cherni.checksat false f !_nbline c !_nbeq satF)
	  | (None, None) ->
	     false
	 )
    in
    if res then
      ()
    else
      raise (CHFailure (STR "Polyhedra #4: polyhedron failed consistency check"))
    
  method check_dims (pa: 'a) (pb: 'a) (msg: string) =
    if pa#dim != pb#dim then
      raise (CHFailure (LBLOCK [STR "Polyhedra #5: incompatible dimensions in function: ";
                                STR msg]))
    else
      ()
    
  method frames_versus_constraint (f: matrix_t) (tab: vector_t) =
    if (tab#get 0)#is_zero then
      (* The constraint is an equality *)
      try
	for i = 0 to f#nbrows - 1 do
	  let prod = (f#p i)#product_strict tab in
	  if not(prod#is_zero) then
	    raise Found
	  else
	    ()
	done;
	Tbool_top
      with Found -> Tbool_bottom
    else
      (* The constraint is an inequality *)
      (* is_strict: Strict inequalities not implemented *)
      let tsign = ref Tsign_bottom in
      let tsign_all = ref Tsign_bottom in
      let tsign_xi = ref Tsign_bottom in
      try
	begin
	  for i = 0 to f#nbrows - 1 do
	    let prod = (f#p i)#product_strict tab in
	    let sign = prod#compare numerical_zero in
	    if (f#get i 0)#is_zero then
	      (* Lines *)
	      if sign != 0 then
		raise Found
	      else
		()
	    else
	      begin
		tsign := 
		  if sign = 0 then
		    Tsign_eq
		  else if sign > 0 then
		    Tsign_gt
		  else
		    Tsign_lt;
		if (f#get i (!pGD)#cst)#gt numerical_zero then
		  tsign_xi := tsign_union !tsign_xi !tsign
		else
		  ();
		(* if is_strict ...: not implemented *)
		tsign_all := tsign_union !tsign_all !tsign;
		if !tsign_all = Tsign_top then
		  raise Found
		else
		  ()
	      end
	  done;
	  (* if is_strict: not implemented *)
	  if !tsign_all = Tsign_eq then
	    Tbool_top
	  else if !tsign_all = Tsign_geq || !tsign_all = Tsign_gt then
	    Tbool_true
	  else if !tsign_all = Tsign_lt || 
	            (!tsign_all = Tsign_leq
		     && !tsign_xi = Tsign_lt (* tsign_eps == Tsign_bottom *)) then
	    Tbool_false
	  else
	    Tbool_bottom
	end
      with Found -> Tbool_bottom
                  
  method is_included_in (pb: 'a) =
    let pa = self in
    let res = ref false in
    let _ = 
      begin
	self#check_dims pa pb "is_included_in";
	if (is_none !(pa#c)) && (is_none !(pa#f)) then
	  res := true
	else
	  ();
	if is_none !(pa#f) then
	  pa#minimize
	else
	  ();
	if is_none !(pa#f) then
	  res := true
	else
	  ();
	if (is_none !(pb#c)) && (is_none !(pb#f)) then
	  res := false
	else
	  ();
	if is_none !(pb#c) then
	  pb#minimize
	else
	  ();
	if (is_some !(pa#c))
           && (is_some !(pa#f))
           && (is_some !(pb#c))
           && (is_some !(pb#f))
	   && (pa#nbeq < pb#nbeq || pa#nbline > pb#nbline) then
	  res := false
	else
	  begin
	    res := true;
	    match (!(pa#f), !(pb#c)) with
	    | (Some paf, Some pbc) ->
	       (try
		  for i = 0 to pbc#nbrows - 1 do
		    let tres = self#frames_versus_constraint paf (pbc#p i) in
		    if tres == Tbool_false || tres = Tbool_bottom then
		      begin
			res := false;
			raise Found
		      end
		    else
		      ()
		  done
		with Found -> ())
	    | _ ->
	       raise (CHFailure (STR "Polyhedra #6: inconsistent polyhedra in is_included_in"))
	  end
      end
    in
    !res
    
  method is_equal (pb: 'a) =
    let pa = self in
    let _ = 
      begin
	self#check_dims pa pb "is_equal";
	pa#minimize;
	pb#minimize
      end
    in
    if pa#nbeq = pb#nbeq && pa#nbline = pb#nbline then
      pa#is_included_in pb && pb#is_included_in pa
    else
      false
    
  method obtain_sorted_F_with_satF =
    match (!_f, !_c) with
    | (Some f, Some c) ->
       begin
	 if f#is_sorted then
	   if is_none !_satF then
	     match !_satC with
	     | Some satC ->
		_satF := Some (satC#transpose c#nbrows)
	     | None ->
		raise (CHFailure (STR "Polyhedra: Inconsistency #1 in obtain_sorted_F_with_satF"))
	   else
	     ()
	 else
	   match (!_satC, !_satF) with
	   | (Some satC, _) ->
	      begin
		if is_some !_satF then
		  _satF := None
		else
		  ();
		f#sort_rows_with_sat satC;
		_satF := Some (satC#transpose c#nbrows)
	      end
	   | (None, Some satF) ->
	      let satC = satF#transpose f#nbrows in
	      begin
		_satC := Some satC;
		_satF := None;
		f#sort_rows_with_sat satC;
		_satF := Some (satC#transpose c#nbrows)
	      end
	   | _ ->
	      raise (CHFailure (STR "Polyhedra: Inconsistency #3 in obtain_sorted_F_with_satF"))
       end
    | _ ->
       raise (CHFailure (STR "Polyhedra: Inconsistency #2 in obtain_sorted_F_with_satF"))
      
  method obtain_sorted_C_with_satC =
    match (!_f, !_c) with
    | (Some f, Some c) ->
       begin
	 if c#is_sorted then
	   if is_none !_satC then
	     match !_satF with
	     | Some satF ->
		_satC := Some (satF#transpose f#nbrows)
	     | None ->
		raise (CHFailure (STR "Polyhedra: Inconsistency #1 in obtain_sorted_C_with_satC"))
	   else
	     ()
	 else
	   match (!_satF, !_satC) with
	   | (Some satF, _) ->
	      begin
		if is_some !_satC then
		  _satC := None
		else
		  ();
		c#sort_rows_with_sat satF;
		_satC := Some (satF#transpose f#nbrows)
	      end
	   | (None, Some satC) ->
	      let satF = satC#transpose c#nbrows in
	      begin
		_satF := Some satF;
		_satC := None;
		c#sort_rows_with_sat satF;
		_satC := Some (satF#transpose f#nbrows)
	      end
	   | _ ->
	      raise (CHFailure (STR "Polyhedra: Inconsistency #3 in obtain_sorted_C_with_satC"))
       end
    | _ ->
       raise (CHFailure (STR "Polyhedra: Inconsistency #2 in obtain_sorted_C_with_satC"))
      
  method obtain_sorted_F =
    match !_f with
    | Some f ->
       if not(f#is_sorted) then
	 match !_satC with
	 | Some satC ->
	    begin
	      if is_some !_satF then
		_satF := None
	      else
		();
	      f#sort_rows_with_sat satC
	    end
	 | None ->
	    (match !_satF with
	     | Some satF ->
		let satC = satF#transpose f#nbrows in
		begin			     
		  _satC := Some satC;
		  _satF := None;
		  f#sort_rows_with_sat satC
		end
	     | None -> f#sort_rows
	    )
       else
	 ()
    | None -> 
       raise (CHFailure (STR "Polyhedra: Inconsistency in obtain_sorted_F"))
      
  method obtain_sorted_C =
    match !_c with
    | Some c ->
       if not(c#is_sorted) then
	 match !_satF with
	 | Some satF ->
	    begin
	      if is_some !_satC then
		_satC := None
	      else
		();
	      c#sort_rows_with_sat satF
	    end
	 | None ->
	    (match !_satC with
	     | Some satC ->
		let satF = satC#transpose c#nbrows in
		begin			     
		  _satF := Some satF;
		  _satC := None;
		  c#sort_rows_with_sat satF
		end
	     | None -> c#sort_rows
	    )
       else
	 ()
    | None -> 
       raise (CHFailure (STR "Polyhedra: Inconsistency in obtain_sorted_C"))
      
  method obtain_satF =
    if is_none !_satF then
      match (!_c, !_satC) with
      | (Some c, Some satC) -> _satF := Some (satC#transpose c#nbrows)
      | _ -> raise (CHFailure (STR "Polyhedra: Inconsistency in obtain_satF"))
           
  method reduce_polyhedra (pa: 'a) (pb: 'a) =
    match (!(pa#c), !(pb#c)) with
    | (Some pa_c, Some pb_c) ->
       let lin_pa = pa_c#get_linear_constraints in
       let lin_pb = pb_c#get_linear_constraints in
       let common_lin = lin_pa#intersect_constraints lin_pb in
       let ma = pa_c#copy in
       let mb = pb_c#copy in
       let _ = ma#reduce_constraints common_lin in
       let _ = mb#reduce_constraints common_lin in
       let pol_a = (self#mkUniverse pa#dim)#add_constraints ma in
       let pol_b = (self#mkUniverse pb#dim)#add_constraints mb in
       (pol_a, pol_b, common_lin)
    | _ ->
       raise (CHFailure (STR "Polyhedra: Inconsistency in reduce_polyhedra"))
      
  method convex_hull (pb: 'a) =
    let pa = self in
    begin
      self#check_dims pa pb "convex_hull";
      if pa#is_empty || pb#is_universe then
	pb#copy
      else if pb#is_empty || pa#is_universe then
	pa#copy
      else
	let npoly = self#mkNew _dim in
	let (pa, pb, common_lin) = self#reduce_polyhedra pa pb in
	let _ =
	  match (!(pa#c), !(pa#f), !(pb#c), !(pb#f)) with
	  | (Some pa_c, Some pa_f, Some pb_c, Some pb_f) ->
	     begin
	       if pa#nbline > pb#nbline ||
		    (pa#nbline = pb#nbline && pa_f#nbrows >= pb_f#nbrows) then
		 begin
		   pa#obtain_sorted_F_with_satF;
		   pb#obtain_sorted_F;
		   let pa_satF = match !(pa#satF) with
		     | Some m -> m
		     | None ->
			raise (CHFailure (STR "Polyhedra: Inconsistency #1 in convex hull"))
		   in
		   try
		     Cherni.add_and_minimize
                       false
		       pa_f pa_c pa_satF pa#nbeq 
		       pb_f
		       npoly#f npoly#c npoly#satC
		       npoly#nbline_ref npoly#nbeq_ref
		   with
		     CHFailure p ->
		     raise (CHFailure (LBLOCK [ p ; NL ;
						STR "; called by CHPolyhedra.convex hull" ]))
		 end
	       else
		 begin
		   pb#obtain_sorted_F_with_satF;
		   pa#obtain_sorted_F;
		   let pb_satF = match !(pb#satF) with
		     | Some m -> m
		     | None ->
			raise (CHFailure (STR "Polyhedra: Inconsistency #2 in convex hull"))
		   in
		   Cherni.add_and_minimize
                     false
		     pb_f pb_c pb_satF pb#nbeq
		     pa_f
		     npoly#f npoly#c npoly#satC
		     npoly#nbline_ref npoly#nbeq_ref
		 end;
	       npoly#check
	     end
	  | _ ->
	     raise (CHFailure (STR "Polyhedra: inconsistency in convex_hull"))
	in
	npoly#add_constraints common_lin
    end
    
  method intersection (pb: 'a) =
    let pa = self in
    begin
      self#check_dims pa pb "intersection";
      if pa#is_empty || pb#is_universe then
	pa#copy
      else if pb#is_empty || pa#is_universe then
	pb#copy
      else
	let npoly = self#mkNew _dim in
	let _ =
	  match (!_c, !_f, !(pb#c), !(pb#f)) with
	  | (Some pa_c, Some pa_f, Some pb_c, Some pb_f) ->
	     begin
	       if pa#nbeq > pb#nbeq ||
		    (pa#nbeq = pb#nbeq && pa_c#nbrows >= pb_c#nbrows) then
		 begin
		   pa#obtain_sorted_C_with_satC;
		   pb#obtain_sorted_C;
		   let pa_satC = match !_satC with
		     | Some m -> m
		     | None ->
			raise (CHFailure (STR "Polyhedra: Inconsistency #1 in intersection"))
		   in
		   Cherni.add_and_minimize
                     true
		     pa_c pa_f pa_satC pa#nbline 
		     pb_c
		     npoly#c npoly#f npoly#satF
		     npoly#nbeq_ref npoly#nbline_ref
		 end
	       else
		 begin
		   pb#obtain_sorted_C_with_satC;
		   pa#obtain_sorted_C;
		   let pb_satC = match !(pb#satC) with
		     | Some m -> m
		     | None ->
			raise (CHFailure (STR "Polyhedra: Inconsistency #2 in intersection"))
		   in
		   Cherni.add_and_minimize
                     true
		     pb_c pb_f pb_satC pb#nbline
		     pa_c
		     npoly#c npoly#f npoly#satF
		     npoly#nbeq_ref npoly#nbline_ref
		 end;
	       npoly#check
	     end
	  | _ ->
	     raise (CHFailure (STR "Polyhedra: inconsistency in intersection"))
	in
	npoly
    end
    
  method widening (pb: 'a) =
    let pa = self in
    begin
      self#check_dims pa pb "widening";
      pa#minimize;
      pb#minimize;
      if is_none !(pa#c) && is_none !(pa#f) then
	(* pa is empty *)
	pb#copy
      else
	let npoly = self#mkNew _dim in
	let (pa, pb, common_lin) = self#reduce_polyhedra pa pb in
	let _ = pa#obtain_satF in
	let sat = match !(pa#satF) with
	  | Some satF -> satF#copy
	  | None -> raise (CHFailure (STR "Polyhedra: inconsistency #1 in widening"))
	in
	let _ = sat#sort_rows in
	let sat_nbcols = sat#nbcolumns in
	let nbrows = ref 0 in
	let _ =
	  match (!(pa#c), !(pa#f), !(pb#c), !(pb#f)) with
	  | (Some pa_c, Some pa_f, Some pb_c, Some pb_f) ->		
	     let npoly_c = new matrix_t ((!pGD)#dec - 1 + pb_c#nbrows) pb_c#nbcolumns false in
	     let _ = npoly#set_c npoly_c in
	     begin
	       (* Strict inequalities not implemented *)
	       (* constraint xi >= 0 *)
	       npoly_c#set 0 0 numerical_one;
	       npoly_c#set 0 (!pGD)#cst numerical_one;
	       nbrows := 1;
	       
	       (* Main loop *)
	       for i = 0 to pb_c#nbrows - 1 do
		 let bitstringp = Array.make sat_nbcols zero_bitstring in
		 let _ = Cherni.buildsatline pa_f (pb_c#get_row i) bitstringp in
		 let index = sat#index_in_sorted_rows bitstringp in
		 if (index >= 0) then
		   (* The affine widening is not implemented *)
		   begin
		     for j = 0 to pb_c#nbcolumns - 1 do
		       npoly_c#set !nbrows j (pb_c#get i j)
		     done;
		     nbrows := !nbrows + 1
		   end
		 else
		   ()
	       done;
	       
	       npoly_c#set_nbrows !nbrows;
	       npoly#check
	     end
	  | _ ->
	     raise (CHFailure (STR "Polyhedra: inconsistency #2 in widening"))
	in
	npoly#add_constraints common_lin
    end
    
  method add_constraints (mat: matrix_t) =
    if _dim != mat#nbcolumns - (!pGD)#dec then
      raise (CHFailure (STR "Polyhedra: Incompatible dimensions in add_constraints"))
    else
      let npoly = self#mkNew _dim in
      let _ =
	begin
	  self#minimize;
	  if not(self#is_empty) then
	    begin
	      self#obtain_sorted_C_with_satC;
	      if not(mat#is_sorted) then
		mat#sort_rows
	      else
		();
	      match (!_c, !_f, !_satC) with
	      | (Some c, Some f, Some satC) ->
		 Cherni.add_and_minimize
                   true
		   c f satC !_nbline
		   mat
		   npoly#c npoly#f npoly#satF
		   npoly#nbeq_ref npoly#nbline_ref
	      | _ ->
		 raise (CHFailure (STR "Polyhedra: inconsistency in add_constraints"))
	    end
	  else
	    ();
	  npoly#check
	end
      in
      npoly
      
  method add_dimensions_and_embed (dimsup: int) =
    if dimsup < 0 then
      raise (CHFailure (LBLOCK [STR "Polyhedra #3: Cannot perform add_dimensions_and_embed with dimsup = "; INT dimsup]))
    else if dimsup = 0 then
      {< >}
    else
      let npoly = self#mkNew (_dim + dimsup) in
      let _ =
	begin
	  Cherni.add_dimensions !_c !_f _satC !_satF dimsup npoly#c npoly#f npoly#satC;
	  (match (!_c, !_f) with
	   | (Some _, Some _) ->
	      begin
		npoly#set_nbeq !_nbeq;
		npoly#set_nbline (!_nbline + dimsup)
	      end
	   | _ -> ());
	  npoly#check
	end
      in
      npoly
      
  method permute_remove_dimensions (dimsup: int) (permutation: int array) =
    let po = self in
    if dimsup < 0 || dimsup > po#dim then
      raise (CHFailure (LBLOCK [STR "Polyhedra: inconsistent dimensions in permute_remove_dimensions- dimsup= ";
				INT dimsup; STR ", dim= "; INT po#dim]))
    else
      let npoly = self#mkNew (po#dim - dimsup) in
      let _ = if is_some !_c || is_some !_f then
	        begin
	          if is_none !_f then
	            po#minimize
	          else
	            ();
	          match !_f with
	          | Some f -> npoly#set_f (f#permute_remove_dimensions dimsup permutation)
	          | None -> ()
	        end
	      else
	        ()
      in
      let _ = npoly#check in
      npoly
      
  method get_constraints =
    let _ = self#minimize in
    match !_c with
    | None -> empty_matrix
    | Some c -> c
	      
end
  
let universe (dim: int) =
  let gd = !(pGD) in
  if dim < 0 || dim > gd#maxcolumns - gd#dec then
    raise (CHFailure (LBLOCK [STR "Polyhedra #1: Cannot create polyhedron with ";
                              INT dim; STR " dimensions"]))
  else
    ();
  let po = new polyhedron_t dim in
  let po_c = new matrix_t (gd#dec - 1) (gd#dec + dim) true in
  let po_f = new matrix_t (gd#dec + dim - 1) (gd#dec + dim) true in
  let po_satC = new satmat_t (gd#dec + dim - 1) (gd#dec - 1) in
  let _ = 
    begin
      po#set_c po_c;
      po#set_f po_f;
      po#set_satC po_satC;
      po#reset_satF;
      po#set_nbeq 0;
      po#set_nbline dim;
      
      (* lines x_i *)
      for i = 0 to dim - 1 do
	po_f#set i (gd#dec + dim - 1 - i) numerical_one
      done;
      if (gd#strict) then
	(* Not implemented *)
	()
      else
	begin
	  (* Ray x_i *)
	  po_f#set dim 0 numerical_one;
	  po_f#set dim gd#cst numerical_one;
	  (* Constraint x_i >= 0 *)
	  po_c#set 0 0 numerical_one;
	  po_c#set 0 gd#cst numerical_one;
	  (* Saturation matrix *)
	  po_satC#set_p dim 0 bitstring_msb
	end	
    end
  in
  po
  
let empty_polyhedron (dim: int) = new polyhedron_t dim
                                
let of_constraints (mat: matrix_t) =
  if mat#nbcolumns <= 0 || mat#nbcolumns > (!pGD)#maxcolumns then
    raise (CHFailure (LBLOCK [STR "Polyhedra #2: Cannot create polyhedron with ";
                              INT mat#nbcolumns; STR " dimensions"]))
  else
    ();
  let po = new polyhedron_t (mat#nbcolumns - (!pGD)#dec) in
  let _ = po#set_c mat in
  po
