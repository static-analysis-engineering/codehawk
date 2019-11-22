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
open CHNumerical
open CHPolyhedraGlobalData   
open CHPretty
open CHSaturationMatrix
open CHVector


class matrix_t (mr: int) (nc: int) (s: bool) =
object (self: 'a)

  val mutable _empty: bool = ((mr * nc) = 0)

  val mutable _maxrows: int = mr

  val mutable _nbrows: int = mr

  val mutable _nbcolumns: int = nc

  val mutable _p: vector_t array = Array.make mr empty_vector

  val mutable _sorted: bool = s

  initializer
    for i = 0 to mr - 1 do
      _p.(i) <- new vector_t nc
    done

      
  method mkNew mr nc s =
    let p = Array.make mr empty_vector in
    let _ = 
      for i = 0 to mr - 1 do
	p.(i) <- new vector_t nc
      done
    in
      {< _empty = ((mr * nc) = 0);
	 _maxrows = mr;
	 _nbrows = mr;
	 _nbcolumns = nc;
	 _p = p;
	 _sorted = s
      >}

  method empty = _empty
	
  method is_sorted = _sorted

  method nbrows = _nbrows

  method nbcolumns = _nbcolumns

  method maxrows = _maxrows

  method p (i: int): vector_t = _p.(i)

  method get (i: int) (j: int) = (_p.(i))#get (j)

  method get_row (i: int) = _p.(i)

  method set (i: int) (j: int) (e: numerical_t) =
    (_p.(i))#set j e

  method set_row (i: int) (r: vector_t) = _p.(i) <- r

  method set_nbrows n = _nbrows <- n

  method set_nbcolumns n = _nbcolumns <- n

  method set_sorted (s: bool) = _sorted <- s

  method set_empty (empty: bool) = _empty <- empty

  method set_p (p: vector_t array) = _p <- p

  method reset mr nc s =
    begin
      _empty <- ((mr * nc) = 0);
      _maxrows <- mr;
      _nbrows <- mr;
      _nbcolumns <- nc;
      _p <- Array.make mr empty_vector;
      for i = 0 to mr - 1 do
	_p.(i) <- new vector_t nc
      done;
      _sorted <- s
    end

  method copy = 
    let c_p = Array.make _maxrows empty_vector in
    let _ = for i = 0 to _maxrows - 1 do
      c_p.(i) <- (_p.(i))#copy
    done
    in
      {< _p = c_p >}

  method clear =
    if _empty then
      ()
    else
      for i = 0 to _nbrows - 1 do
	for j = 0 to _nbcolumns - 1 do
	  (self#p i)#set j numerical_zero
	done
      done
	
  method sort_rows =
    if self#is_sorted then
      ()
    else
      let slice = Array.sub _p 0 _nbrows in
	begin
	  _sorted <- true;
	  Array.fast_sort (fun v1 v2 -> v1#compare v2) slice;
	  Array.blit slice 0 _p 0 _nbrows
	end
	
  method exch_rows (i: int) (j: int) =
    let row = _p.(i) in
      begin
	_p.(i) <- _p.(j);
	_p.(j) <- row
      end

  method combine_rows (l1: int) (l2: int) (l3: int) (k: int) =
    (_p.(l3))#combine _p.(l1) _p.(l2) k

  method add_dimensions (dimsup: int) =
    let nmat = new matrix_t _nbrows (_nbcolumns + dimsup) _sorted in
    let _ =
      for i = 0 to _nbrows - 1 do
	nmat#set_row i (_p.(i)#add_dimensions dimsup)
      done
    in
      nmat

  method sort_rows_with_sat (sat: satmat_t) =
    (* We use insertion sort *)
    if _sorted then
      ()
    else
      let i = ref 1 in
	begin
	  while !i < _nbrows do
	    let row = _p.(!i) in
	    let rowsat = sat#get_row !i in
	    let j = ref !i in
	    let s = ref 1 in
	    let _ = try
	      while !j > 0 do
		s := _p.(!j - 1)#compare row;
		if !s = 0 then
		  raise (CHFailure (STR "Matrix: inconsistency in sort_rows_with_sat"))
		else if !s <= 0 then
		  raise Found
		else
		  begin
		    _p.(!j) <- _p.(!j - 1);
		    sat#set_row !j (sat#get_row (!j - 1));
		    j := !j - 1
		  end
	      done
	    with Found -> ()
	    in
	      begin
		_p.(!j) <- row;
		sat#set_row !j rowsat;
		i := !i + 1
	      end
	  done;
	  _sorted <- true
	end

  method row_echelon =
    let con = self in
    let rank = ref 0 in
    let s = ref 0 in
    let nbeq = _nbrows in
    let i = ref 0 in
    let _ =
      begin
	for j = con#nbcolumns - 1 downto 1 do
	  (try
	     i := !rank;
	     while !i< nbeq do
	       s := (self#get !i j)#sgn;
	       if !s != 0 then
		 raise Found
	       else
		 ();
	       i := !i + 1
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
		  self#set !rank k (self#get !rank k)#neg
		done
	      else
		();
	      self#set !rank 0 numerical_zero;
	      for k = !i + 1 to nbeq - 1 do
		if not((self#get k j)#is_zero) then
		  con#combine_rows k !rank k j
		else
		  ()
	      done;
	      rank := !rank + 1
	    end
	  else
	    ()
	done;
	
	let j = ref 0 in
	  for i = !rank - 1 downto 1 do
	    j := con#nbcolumns - 1 ;
	    (try
	       while !j >= 1 do
		 s := (self#get i !j)#sgn;
		 if !s != 0 then
		   raise Found
		 else
		   ();
		 j := !j - 1
	       done
	     with Found -> ());
	    for k = i - 1 downto 0 do
	      if not((self#get k !j)#is_zero) then
		con#combine_rows k i k !j
	      else
		()
	    done
	  done	  
      end
    in
      !rank
    
  method has_constraint (c: vector_t) =
    let m = self in
      try
	for i = 0 to m#nbrows - 1 do
	  if c#compare (m#get_row i) = 0 then
	    raise Found
	  else
	    ()
	done;
	false
      with Found -> true

  method intersect_constraints (b: 'a) =
    let a = self in
    let r = self#mkNew _nbrows _nbcolumns false in
    let row = ref 0 in
    let _ =
      begin
	for i = 0 to a#nbrows - 1 do
	  if b#has_constraint (a#get_row i) then
	    begin
	      for j = 0 to a#nbcolumns - 1 do
		r#set !row j (a#get i j)
	      done;
	      row := !row + 1
	    end
	  else
	    ()
	done;
	r#set_nbrows !row
      end
    in
      r
	
  method reduce_constraints (lins: 'a) =
    let m = self in
    let head = Array.make m#nbcolumns false in
    let eqs = self#mkNew lins#nbcolumns lins#nbcolumns false in
      begin
	for i = 0 to lins#nbrows - 1 do
	  let h = (lins#get_row i)#get_head in
	    head.(h) <- true;
	    for j = 0 to eqs#nbcolumns - 1 do
	      eqs#set h j (lins#get i j)
	    done
	done;

	for i = 0 to m#nbrows - 1 do
	  for j = (!pGD)#dec to m#nbcolumns - 1 do
	    if not((m#get i j)#is_zero) && head.(j) then
	      (m#get_row i)#combine (m#get_row i) (eqs#get_row j) j
	    else
	      ()
	  done
	done;

	let last_pos = ref 0 in
	let removed = ref 0 in
	  begin
	    for i = 0 to m#nbrows - 1 do
	      if (m#get_row i)#is_null_strict then
		removed := !removed + 1
	      else
		if i = !last_pos then
		  last_pos := !last_pos + 1
		else
		  begin
		    for j = 0 to m#nbcolumns - 1 do
		      m#set !last_pos j (m#get i j)
		    done;
		    last_pos := !last_pos + 1
		  end
	    done;
	    m#set_nbrows (m#nbrows - !removed)
	  end
      end

  method get_constraints (kind: int) =
    let kind_n = mkNumerical kind in
    let m = self in
    let cst_m = self#mkNew _nbrows _nbcolumns false in
    let row = ref 0 in
    let _ =
      begin
	for i = 0 to m#nbrows - 1 do
	  if (m#get i 0)#equal kind_n then
	    begin
	      for j = 0 to m#nbcolumns - 1 do
		cst_m#set !row j (m#get i j)
	      done;
	      row := !row + 1
	    end
	  else
	    ()
	done;
	cst_m#set_nbrows !row;
	
	if kind = 0 then
	  let _ = cst_m#row_echelon in
	    ()
	else
	  ()
      end
    in
      cst_m	
    
  method get_linear_constraints = self#get_constraints 0

  method get_inequality_constraints = self#get_constraints 1    
    
  method permute_remove_dimensions (dimsup: int) (permutation: int array) =
    let mat = self in
      if dimsup < 0 then
	raise (CHFailure (STR "Matrices: negative dimsup argument in permute_remove_dimensions"))
      else
	let nmat = self#mkNew _nbrows (_nbcolumns - dimsup) false in
	let _ = 
	  for i = 0 to _nbrows - 1 do
	    (mat#get_row i)#permute_remove_dimensions (nmat#get_row i) dimsup permutation
	  done
	in
	  nmat
	    
  method toPretty =
    INDENT (2, ABLOCK (Array.map (fun v -> LBLOCK [v#toPretty; NL]) (Array.sub _p 0 _nbrows)));
    
end

let empty_matrix = new matrix_t 0 0 true
