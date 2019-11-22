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


let conversion (con: matrix_t) (start: int) (ray: matrix_t) 
    (satc: satmat_t) (nbline': int) =
  let nbline = ref nbline' in
  let index_non_zero = ref 0 in
  let equal_bound = ref 0 in
  let sup_bound = ref 0 in
  let inf_bound = ref 0 in
  let bound = ref 0 in
  let nbcommonconstraints = ref 0 in
  let m = ref zero_bitstring in
  let aux = ref zero_bitstring in
  let redundant = ref false in
  let k = new bitindex_t start in
  let nbcols = con#nbcolumns in
  let satnbcols = bitindex_size con#nbrows in
  let nbrows = ref ray#nbrows in
  let bitstringp = Array.make (!pGD)#maxnbrows zero_bitstring in
  let _ = 
    while k#index < con#nbrows do
      (* Iteration over all constraints *)
      let is_inequality = not((con#get k#index 0)#is_zero) in
	begin
	  (* Scalar product and index *)
	  
	  index_non_zero := !nbrows;
	  for i = 0 to !nbrows - 1 do
	    ray#set i 0 ((ray#p i)#product (con#p k#index));
	    if !index_non_zero = !nbrows && not((ray#get i 0)#is_zero) then
	      index_non_zero := i
	    else
	      ()
	  done;
	  
	  if !index_non_zero < !nbline then
	    (* A line does not satisfy the constraint *)
	    begin
	      nbline := !nbline - 1;
	      if !index_non_zero != !nbline then
		ray#exch_rows !index_non_zero !nbline
	      else
		();
	      (* Compute new linearity space *)
	      for i = !index_non_zero to !nbline - 1 do
		if not((ray#get i 0)#is_zero) then
		  ray#combine_rows i !nbline i 0
		else
		  ()
	      done;

	      (* Orient the new ray *)
	      if (ray#get !nbline 0)#lt numerical_zero then
		for j = 0 to nbcols - 1 do
		  ray#set !nbline j (ray#get !nbline j)#neg
		done
	      else
		();
	      
	      (* Compute the new pointed cone *)
	      for i = !nbline + 1 to !nbrows - 1 do
		if not((ray#get i 0)#is_zero) then
		  ray#combine_rows i !nbline i 0
		else
		  ()
	      done;

	      if (is_inequality) then
		satc#set !nbline k
	      else
		begin
		  nbrows := !nbrows - 1;
		  ray#set_nbrows (ray#nbrows - 1);
		  satc#set_nbrows (satc#nbrows - 1);
		  ray#exch_rows !nbline !nbrows;
		  satc#exch_rows !nbline !nbrows
		end;
	      
	      k#inc
	    end
	  else
	    (* All the lines saturate the constraint *)
	    begin
	      equal_bound := !nbline;
	      sup_bound := !nbline;
	      inf_bound := !nbrows;
	      while !inf_bound > !sup_bound do
		let s = ray#get !sup_bound 0 in
		  if s#is_zero then
		    begin
		      ray#exch_rows !sup_bound !equal_bound;
		      satc#exch_rows !sup_bound !equal_bound;
		      equal_bound := !equal_bound + 1;
		      sup_bound := !sup_bound + 1
		    end
		  else if s#lt numerical_zero then
		    begin
		      inf_bound := !inf_bound - 1;
		      ray#exch_rows !sup_bound !inf_bound;
		      satc#exch_rows !sup_bound !inf_bound
		    end
		  else
		    sup_bound := !sup_bound + 1
	      done;

	      if is_inequality && !sup_bound = !nbrows then
		(* Redundancy *)
		begin
		  con#set_nbrows (con#nbrows - 1);
		  con#exch_rows k#index con#nbrows
		end
	      else
		begin
		  if !sup_bound = !nbline then
		    (* No ray satisfies the constraint *)
		    begin
		      satc#set_nbrows !nbline;
		      ray#set_nbrows !nbline;
		      nbrows := !nbline
		    end
		  else
		    (* Some rays do not satisfy the constraint *)
		    begin
		      bound := !nbrows;
		      for i = !equal_bound to !sup_bound - 1 do
			for j = !sup_bound to !bound - 1 do
			  nbcommonconstraints := 0;
			  for w = 0 to k#word - 1 do
			    aux := (satc#p i w)#logical_or (satc#p j w);
			    bitstringp.(w) <- !aux;
			    m := bitstring_msb;
			    while not((!m)#is_zero) do
			      if ((!aux)#logical_and !m)#is_zero then
				nbcommonconstraints := !nbcommonconstraints + 1
			      else
				();
			      m := (!m)#shift_right 1
			    done
			  done;
			  aux := (satc#p i k#word)#logical_or (satc#p j k#word);
			  bitstringp.(k#word) <- !aux;
			  m := bitstring_msb;
			  while not((!m)#equal k#bit) do
			    if ((!aux)#logical_and !m)#is_zero then
			      nbcommonconstraints := !nbcommonconstraints + 1
			    else
			      ();
			    m := (!m)#shift_right 1
			  done;
			  if !nbcommonconstraints + !nbline >= nbcols - 3 then
			    (* Possibly adjacent *)
			    begin
			      redundant := false;
			      (try
				 for l = !nbline to !bound - 1 do
				   if l != i && l != j then
				     let w = ref 0 in
				       (try				       
					  while !w <= k#word do
					    if not(((satc#p l !w)#logical_and (((bitstringp.(!w))#logical_not)))#is_zero) then
					      raise Found
					    else
					      ();
					    w := !w + 1
					  done
					with Found -> ());
				       if !w > k#word then
					 begin
					   redundant := true;
					   raise Found
					 end
				       else
					 ()
				   else
				     ()
				 done
			       with Found -> ());
			      if not(!redundant) then
				begin
				  if !nbrows = ray#maxrows then
				    raise (CHOutOfMemory (STR "Chernikova: too many rays"))
				  else
				    ();				  
				  (* Compute the new ray and append it to the matrix *)
				  ray#combine_rows j i !nbrows 0;
				  (* New row in saturation matrix *)
				  for w = 0 to k#word do
				    satc#set_p !nbrows w bitstringp.(w)
				  done;
				  for w = k#word + 1 to satnbcols - 1 do
				    satc#set_p !nbrows w zero_bitstring
				  done;
				  nbrows := !nbrows + 1;
				  ray#set_nbrows (ray#nbrows + 1);
				  satc#set_nbrows (satc#nbrows + 1)
				end
			      else
				()
			    end
			  else
			    ()
			done
		      done;
		      (* Remove non extremal rays *)
		      let i = ref 0 in
		      let j = ref 0 in
			begin
			  if is_inequality then
			    begin
			      j := !sup_bound;
			      for l = !equal_bound to !sup_bound - 1 do
				satc#set l k
			      done
			    end
			  else
			    j := !equal_bound;
			  i := !nbrows;
			  while !j < !bound && !i > !bound do
			    i := !i - 1;
			    ray#exch_rows !i !j;
			    satc#exch_rows !i !j;
			    j := !j + 1
			  done;
			  nbrows := if !j = !bound then !i else !j;
			  ray#set_nbrows !nbrows;
			  satc#set_nbrows !nbrows
			end
		    end;
		  k#inc
		end
	    end
	end
    done
  in
    (* status coefficient *)
  let _ =
    begin
      for i = 0 to !nbline - 1 do
	ray#set i 0 numerical_zero
      done;
 
      for i = !nbline to !nbrows - 1 do
	ray#set i 0 numerical_one
      done;
 
      satc#set_nbrows !nbrows;
      ray#set_nbrows !nbrows
    end
  in
    !nbline

let gauss (intp: int array) (con: matrix_t) (nbeq: int) =
  let rank = ref 0 in
  let s = ref 0 in
  let i = ref 0 in
  let _ =
    for j = con#nbcolumns - 1 downto 1 do
      i := !rank;
      (try
	 while !i < nbeq do
	   s := (con#get !i j)#sgn;
	   if !s != 0 then
	     raise Found
	   else
	     ();
	   i := !i + 1;
	 done
       with Found -> ());
      if !i < nbeq then
	begin
	  if !i > !rank then
	    con#exch_rows !i !rank
	  else
	    ();
	  if !s < 0 then
	    for k = 1 to con#nbcolumns - 1 do
	      con#set !rank k (con#get !rank k)#neg
	    done
	  else
	    ();
	  con#set !rank 0 numerical_zero;
	  for k = !i + 1 to nbeq - 1 do
	    if not((con#get k j)#is_zero) then
	      con#combine_rows k !rank k j
	    else
	      ()
	  done;
	  intp.(!rank) <- j;
	  rank := !rank + 1
	end
      else
	()
    done
  in
    !rank

let backsubstitute (intp: int array) (con: matrix_t) (rank: int) =
  let i = ref 0 in
  let j = ref 0 in
  let k = ref 0 in
    begin
      k := rank - 1;
      while !k >= 0 do
	j := intp.(!k);
	i := 0;
	while !i < !k do
	  if not((con#get !i !j)#is_zero) then
	    con#combine_rows !i !k !i !j
	  else
	    ();
	  i := !i + 1
	done;
	i := !k + 1;
	while !i < con#nbrows do
	  if not((con#get !i !j)#is_zero) then
	    con#combine_rows !i !k !i !j
	  else
	    ();
	  i := !i + 1
	done;
	k := !k - 1
      done
    end

let simplify (con: matrix_t) (ray: matrix_t) (satf: satmat_t) (nbline: int) =
  let i = ref 0 in
  let j = ref 0 in
  let nb = ref 0 in
  let nbj = ref 0 in
  let nbeq = ref 0 in
  let rank = ref 0 in
  let w = ref 0 in
  let m = ref zero_bitstring in
  let redundant = ref false in
  let is_equality = ref false in
  let nbcols = con#nbcolumns in
  let nbrays = new bitindex_t ray#nbrows in
  let nbcons = ref con#nbrows in
  let intp = Array.make (!pGD)#maxcolumns 0 in
  let _ =
    begin
      (* Find the first inequality *)
      nbeq := 0;
      (try
	 while !nbeq <  !nbcons do
	   if not((con#get !nbeq 0)#is_zero) then
	     raise Found
	   else
	     ();
	   nbeq := !nbeq + 1
	 done
       with Found -> ());
      
      i := !nbeq;
      while !i < !nbcons do
	is_equality := (con#get !i 0)#is_zero;
	if not(!is_equality) then
	  begin
	    is_equality := true;
	    w := 0;
	    try
	      while !w < satf#nbcolumns do
		if not((satf#p !i !w)#is_zero) then
		  begin
		    is_equality := false;
		    raise Found
		  end
		else
		  ();
		w := !w + 1;
	      done
	    with Found -> ()
	  end
	else
	  ();
	if !is_equality then
	  (* We have an equality *)
	  begin
	    con#set !i 0 numerical_zero;
	    con#exch_rows !i !nbeq;
	    satf#exch_rows !i !nbeq;
	    nbeq := !nbeq + 1
	  end
	else
	  (* We count the number of null bits *)
	  begin
	    nb := 0;
	    w := 0;
	    while !w < nbrays#word do
	      m := bitstring_msb;
	      while not((!m)#is_zero) do
		if ((satf#p !i !w)#logical_and (!m))#is_zero then
		  nb := !nb + 1
		else
		  ();
		m := (!m)#shift_right 1
	      done;
	      w := !w + 1
	    done;
	    m := bitstring_msb;
	    while not((!m)#equal nbrays#bit) do
	      if ((satf#p !i nbrays#word)#logical_and (!m))#is_zero then
		nb := !nb + 1
	      else
		();
	      m := (!m)#shift_right 1
	    done;
	    con#set !i 0 (mkNumerical !nb)
	  end;	    
	i := !i + 1
      done;
      
      (* Remove redundant equalities and update nbeq *)      
      rank := gauss intp con !nbeq;


      (* Remove redundant equations located between rank and nbeq *)
      if !rank < !nbeq then
	begin
	  i := !nbcons;
	  j := !rank;
	  while !j < !nbeq && !i > !nbeq do
	    i := !i - 1;
	    con#exch_rows !j !i;
	    satf#exch_rows !j !i;
	    j := !j + 1
	  done;
	  nbcons := !nbcons + !rank - !nbeq;
	  nbeq := !rank
	end
      else
	();
      
      (* Remove trivially redundant inequalities *)
      i := !nbeq;
      while !i < !nbcons do
	nb := (con#get !i 0)#toInt;
	if !nb < nbcols - !nbeq - 2 then
	  (* Redundant constraint *)
	  begin
	    nbcons := !nbcons - 1;
	    con#exch_rows !i !nbcons;
	    satf#exch_rows !i !nbcons
	  end
	else
	  i := !i + 1
      done;
      
      (* Remove other redundant inequalities *)
      i := !nbeq;
      while !i < !nbcons do
	nb := (con#get !i 0)#toInt;
	redundant := false;
	j := !nbeq;
	(try
	   while !j < !nbcons do
	     begin
	       nbj := (con#get !j 0)#toInt;
	       if !nbj > !nb then
		 begin
		   redundant := true;
		   w := 0;
		   (try
		      while !w < satf#nbcolumns do
			if not((((satf#p !i !w)#logical_not)#logical_and (satf#p !j !w))#is_zero) then
			  begin
			    redundant := false;
			    raise Found
			  end
			else
			  ();
			w := !w + 1
		      done
		    with Found -> ());
		   if !redundant then
		     raise Found
		   else
		     j := !j + 1
		 end
	       else if !nbj = !nb && !j != !i then
		 begin
		   (* Are i and j redundant *)
		   is_equality := true;
		   w := 0;
		   (try
		      while !w < satf#nbcolumns do
			if not((satf#p !i !w)#equal (satf#p !j !w)) then
			  begin
			    is_equality := false;
			    raise Found
			  end
			else
			  ();
			w := !w + 1
		      done
		    with Found -> ());
		   if !is_equality then
		     (* Yes: we can remove j *)
		     begin
		       nbcons := !nbcons - 1;
		       con#exch_rows !j !nbcons;
		       satf#exch_rows !j !nbcons
		     end
		   else
		     j := !j + 1
		 end
	       else
		 j := !j + 1;
	     end
	   done
	 with Found -> ());
	if !redundant then
	  begin
	    nbcons := !nbcons - 1;
	    con#exch_rows !i !nbcons;
	    satf#exch_rows !i !nbcons
	  end
	else
	  i := !i + 1
      done;
      
      (* Setting status coefficient *)
      i := !nbeq;
      while !i < !nbcons do
	con#set !i 0 numerical_one;
	i := !i + 1
      done;
      con#set_nbrows !nbcons;
      satf#set_nbrows !nbcons;
      
      (* Run back substitution over remaining constraints *)
      backsubstitute intp con !nbeq
    end
  in
    !nbeq    

let minimize (con_to_ray: bool) (p_C: matrix_t option ref) (p_F: matrix_t option ref) 
    (p_satF: satmat_t option ref) (p_nbeq: int ref) (p_nbline: int ref) =
  match !p_C with
    | Some c ->
	begin
	  if not(c#is_sorted) then c#sort_rows else ();
	  let dec = (!pGD)#dec in
	  let bigray = new matrix_t (!pGD)#maxnbrows c#nbcolumns false in
	  let bigsatc = new satmat_t (!pGD)#maxnbrows (bitindex_size c#nbrows) in
	  let special = ref true in
	    begin
	      bigray#set_nbrows (c#nbcolumns - 1);
	      bigsatc#set_nbrows (c#nbcolumns - 1);
	      (* Initialized with zero values *)
	      bigray#set_nbrows (c#nbcolumns - 1);
	      bigsatc#set_nbrows (c#nbcolumns - 1);
	      for i = 0 to c#nbcolumns - 2 do
		bigray#set i (i + 1) numerical_one
	      done;
	      
	      p_nbline := conversion c 0 bigray bigsatc (c#nbcolumns - 1);
	      
	      special := true;
	      (try 
		 for i = !p_nbline to bigray#nbrows - 1 do
		   if ((bigray#p i)#get (dec - 1))#gt numerical_zero then
		     begin
		       special := false;
		       raise Found
		     end
		   else
		     ()
		 done
	       with Found -> ());
	      
	      if !special then
		if con_to_ray then
		  begin
		    (* empty polyhedron *)
		    p_C := None;
		    p_F := None;
		    p_satF := None;
		    p_nbeq := 0;
		    p_nbline := 0
		  end
		else
		  raise (CHFailure (STR "Chernikova minimize: matrix of rays was not valid"))
	      else
		let sat = bigsatc#transpose c#nbrows in
		  begin
		    p_satF := Some sat;
		    p_nbeq := simplify c bigray sat (!p_nbline);
		    p_F := Some bigray
		  end
	    end
	end
    | None ->
	raise (CHFailure (STR "Chernikova #1"))
	  
let add_dimensions (_C: matrix_t option) (_F: matrix_t option)
    (p_satC: satmat_t option ref) (satF: satmat_t option) (dimsup: int)
    (p_Cres: matrix_t option ref) (p_Fres: matrix_t option ref)
    (p_satCres: satmat_t option ref) =
  let nC = ref None in
  let nF = ref None in
  let nsatC = ref None in
    if dimsup <= 0 then
      raise (CHFailure (LBLOCK [STR "Chernikova add_dimensions: inconsistent dimension: "; 
				INT dimsup]))
    else
      begin
	(match (_C, _F) with
	   | (Some _, _)
	   | (_, Some _) ->
	       begin
		 (match _C with
		    | Some c -> 
			let nc = c#add_dimensions dimsup in
			  nC := Some nc
		    | None -> ()
		 );
		 (match _F with
		    | Some f ->
			let nf = new matrix_t (f#nbrows + dimsup) (f#nbcolumns + dimsup) false in
			  begin
			    nF := Some nf;
			    for i = 0 to dimsup - 1 do
			      nf#set i (nf#nbcolumns - 1 - i) numerical_one
			    done;
			    for i = 0 to f#nbrows - 1 do
			      nf#set_row (dimsup + i) ((f#p i)#add_dimensions dimsup)
			    done;
			    nf#set_sorted (f#is_sorted && (nf#p (dimsup - 1))#compare (nf#p dimsup) <= 0)				
			  end
		    | None ->
			()
		 );
		 (match (!p_satC, satF) with
		    | (None, Some satf) -> 
			(match _F with
			   | Some f -> p_satC := Some (satf#transpose f#nbrows)
			   | None -> raise (CHFailure (STR "Chernikova add_dimensions: inconsistent frame matrix"))
			)
		    | _ -> ()
		 );
		 (match !p_satC with
		    | Some satC ->
			let nsatc = new satmat_t (satC#nbrows + dimsup) satC#nbcolumns in
			  begin
			    nsatC := Some nsatc;
			    for i = 0 to satC#nbrows - 1 do
			      for j = 0 to satC#nbcolumns - 1 do
				nsatc#set_p (dimsup + i) j (satC#p i j)
			      done
			    done
			  end
		    | None -> ()
		 )
	       end
	   | _ ->
	       ()
	);
	p_Cres := !nC;
	p_Fres := !nF;
	p_satCres := !nsatC
      end

let checksatmat (con_to_ray: bool) (c: matrix_t) (f: matrix_t) (satC: satmat_t) =
  try
    for i = 0 to f#nbrows - 1 do
      let j = new bitindex_t 0 in
	while j#index < c#nbrows do
	  let prod = (f#get_row i)#product (c#get_row j#index) in
	  let s1 = prod#sgn in
	  let s2 = satC#get i j in
	    begin
	      if s1 < 0 || (s1 != 0 && s2#is_zero) || (s1 = 0 && not(s2#is_zero)) then
		raise Found
	      else
		();
	      j#inc
	    end
	done
    done;
    true
  with Found -> false

let checksat (con_to_ray: bool) (c: matrix_t) (nbequations: int)
    (f: matrix_t) (nblines: int) (satC: satmat_t) =
  let nb = ref 0 in
  let rank = ref 0 in
  let res = ref true in
  let intp = Array.make (!pGD)#maxcolumns 0 in
  let nbcols = c#nbcolumns in
    (* Ray saturation *)
  let mat = new matrix_t c#nbrows nbcols false in
  let _ = 
    for i = 0 to f#nbrows - 1 do
      nb := 0;
      let j = new bitindex_t 0 in
	while j#index < c#nbrows do
	  if (satC#get i j)#is_zero then
	    begin
	      for k = 0 to nbcols - 1 do
		mat#set !nb k (c#get j#index k)
	      done;
	      nb := !nb + 1
	    end
	  else
	    ();
	  j#inc
	done;
	rank := gauss intp mat !nb;
	if not(((f#get i 0)#is_zero && !nb = c#nbrows)
	       || (!rank = nbcols - 2 - nblines && !nb >= !rank)) then
	  res := false
	else
	  ()
    done
  in
    (* Constraint saturation *)
  let mat = new matrix_t f#nbrows nbcols false in
  let _ = 
    let j = new bitindex_t 0 in
      while j#index < c#nbrows do
	nb := 0;
	for i = 0 to f#nbrows - 1 do
	  if (satC#get i j)#is_zero then
	    begin
	      for k = 0 to nbcols - 1 do
		mat#set !nb k (f#get i k)
	      done;
	      nb := !nb + 1
	    end
	  else
	    ()
	done;
	rank := gauss intp mat !nb;
	if not(((c#get j#index 0)#is_zero && !nb = f#nbrows)
	       || (!rank = nbcols - 2 - nbequations && !nb >= !rank)) then
	  res := false
	else
	  ();
	j#inc
      done
  in
    !res

let add_and_minimize (con_to_ray: bool)
    (cdep: matrix_t) (fdep: matrix_t)
    (satCdep: satmat_t) (nblines: int)
    (caut: matrix_t)
    (p_C: matrix_t option ref) (p_F: matrix_t option ref) (p_satF: satmat_t option ref)
    (p_nbeq: int ref) (p_nbline: int ref) =
  if cdep#nbrows + caut#nbrows + 1 >= (!pGD)#maxnbrows then
    raise (CHFailure (STR "Chernikova: too many constraints in add_and_minimize"))
  else
    let i = ref 0 in
    let kdep = ref 0 in
    let kaut = ref 0 in
    let special = ref false in
    let nbcols = cdep#nbcolumns in
    let c = new matrix_t (cdep#nbrows + caut#nbrows) nbcols false in
      begin
	(* Filling in with cdep first *)
	for i = 0 to cdep#nbrows - 1 do
	  for j = 0 to nbcols - 1 do
	    c#set i j (cdep#get i j)
	  done
	done;
	(* Filling in with constraints of caut that are not already present in cdep *)
	i := cdep#nbrows;
	while !kdep < cdep#nbrows && !kaut < caut#nbrows do
	  let s = (cdep#get_row !kdep)#compare (caut#get_row !kaut) in
	    if s = 0 then
	      begin
		kdep := !kdep + 1;
		kaut := !kaut + 1
	      end
	    else if s < 0 then
	      kdep := !kdep + 1
	    else
	      begin
		for j = 0 to nbcols - 1 do 
		  c#set !i j (caut#get !kaut j)
		done;
		i := !i + 1;
		kaut := !kaut + 1
	      end
	done;
	while !kaut < caut#nbrows do
	  for j = 0 to nbcols - 1 do
	    c#set !i j (caut#get !kaut j)
	  done;
	  i := !i + 1;
	  kaut := !kaut + 1
	done;
	c#set_nbrows !i;
	while !i < c#maxrows do
	  for j = 0 to nbcols - 1 do
	    c#set !i j numerical_zero
	  done;
	  i := !i + 1
	done;

	(* Frame and saturation matrices *)
	let bigray = new matrix_t (!pGD)#maxnbrows nbcols false in
	let bigsatc = new satmat_t (!pGD)#maxnbrows (bitindex_size c#nbrows) in
	  begin
	    bigray#set_nbrows fdep#nbrows;
	    bigsatc#set_nbrows fdep#nbrows;
	    for i = 0 to fdep#nbrows - 1 do
	      for j = 0 to nbcols - 1 do
		bigray#set i j (fdep#get i j)
	      done;
	      
	      for j = 0 to satCdep#nbcolumns - 1 do
		try
		  bigsatc#set_p i j (satCdep#p i j)
		with
		  Invalid_argument s ->
		    raise (CHFailure (LBLOCK [ STR "Chernikova add_and_minimize #2 " ; STR s ; NL ;
					       STR ";  i = " ; INT i ; STR " ; j = " ; INT j ;
					       STR "; bigsatc#nbrows = " ; INT (!pGD)#maxnbrows ;
					       STR "; bigsatc#nbcols = " ; INT (bitindex_size c#nbrows) ;
					       STR "; satCdep#nbrows = " ; INT satCdep#nbrows ;
					       STR "; satCdep#nbcolumns = " ; INT satCdep#nbcolumns ]))		  
	      done;
	      
	      for j = satCdep#nbcolumns to bigsatc#nbcolumns - 1 do
		bigsatc#set_p i j zero_bitstring
	      done
	    done;
	    (* Conversion *)

	    p_nbline := conversion c cdep#nbrows bigray bigsatc nblines;
	    
	    (* Special case? *)
	    special := true;
	    (try
	       for i = !p_nbline to bigray#nbrows - 1 do
		 if (bigray#get i ((!pGD)#dec - 1))#gt numerical_zero then
		   begin
		     special := false;
		     raise Found
		   end
		 else
		   ()
	       done
	     with Found -> ());
	    if !special then
	      if con_to_ray then
		begin
		  p_C := None;
		  p_F := None;
		  p_satF := None;
		  p_nbeq := 0;
		  p_nbline := 0
		end
	      else
		raise (CHFailure (STR "Chernikova: invalid matrix of rays in add_and_minimize"))
	    else
	      let satf = bigsatc#transpose c#nbrows in
		begin
		  p_satF := Some satf;
		  p_nbeq := simplify c bigray satf !p_nbline;
		  p_C := Some c;
		  p_F := Some bigray
		end
	  end
      end
	
let buildsatline (con: matrix_t) (tab: vector_t) (satline: bitstring_t array) =
  let jx = new bitindex_t 0 in
    while jx#index < con#nbrows do
      let prod = (con#get_row jx#index)#product tab in
	if not(prod#is_zero) then
	  satline.(jx#word) <- satline.(jx#word)#logical_or jx#bit
	else
	  ();
	jx#inc
    done
