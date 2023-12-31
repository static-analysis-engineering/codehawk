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

class vector_t (n: int) =
object (self: 'a)

  val _size: int = n
    
  val _v: numerical_t array = Array.make n numerical_zero


  method size = _size

  method get_v = _v

  method get (i: int) = _v.(i)
    
  method set (i: int) (e: numerical_t) = _v.(i) <- e
    

  method mkVector (n: int) = {< _size = n; _v = Array.make n numerical_zero >}

  method copy = {< _v = Array.copy _v >}

  method subvector (start: int) =
    let size' = _size - start in
    let v' = self#mkVector size' in
    let _ = Array.blit _v start (v'#get_v) 0 size' in
      v'
	
  method gcd =
    if _size = 0 then
      numerical_zero
    else
      Array.fold_left (fun a x -> a#gcd x) _v.(0) _v

  method compare (v2: 'a) =
    let v1 = self in      
    let res = (v1#get 0)#compare (v2#get 0) in
      if res != 0 then
	if res > 0 then 2 else -2
      else
	let dec = (!pGD)#dec in
	let gcd1 = (v1#subvector dec)#gcd in
	let gcd2 = (v2#subvector dec)#gcd in
	let nextcompare gcd1 gcd2 =
	  let cst = (!pGD)#cst in
	    if cst < _size then
	      let a = (v1#get cst)#mult gcd2 in
	      let b = (v2#get cst)#mult gcd1 in
	      let res = a#compare b in
		(* Strict inequalities are not implemented *)
		if res != 0 then
		  if res > 0 then 1 else -1
		else
		  0
	    else
	      0
	in
	  if gcd1#is_zero && gcd2#is_zero then
	    nextcompare numerical_one numerical_one
	  else
	    let gcd1' = if gcd1#is_zero then numerical_one else gcd1 in
	    let gcd2' = if gcd2#is_zero then numerical_one else gcd2 in
	      try
		for i = dec to _size - 1 do
		  let a = (v1#get i)#div gcd1' in
		  let b = (v2#get i)#div gcd2' in
		  let res = a#compare b in
		    if res != 0 then
		      raise (Got_integer (if res > 0 then 2 else -2))
		    else
		      ()
		done;
		nextcompare gcd1' gcd2'
	      with Got_integer result -> result

  method normalize =
    let tmp1 = (self#subvector 1)#gcd in
      if tmp1#gt numerical_one then
	for i = 1 to _size - 1 do
	  _v.(i) <- (_v.(i))#div tmp1
	done
      else
	()
	  
  method clear =
    for i = 0 to _size - 1 do
      _v.(i) <- numerical_zero
    done

  method product (v: 'a) =
    let prod = ref numerical_zero in
    let _ = 
      for i = 1 to _size - 1 do
	prod := (!prod)#add ((self#get i)#mult(v#get i))
      done
    in
      !prod

  method product_strict (v: 'a) =
    let cst = (!pGD)#cst in
    let prod = ref numerical_zero in
      try
	begin
	  if cst < _size then
	    prod := _v.(cst)#mult (v#get cst)
	  else
	    raise Found;
	  for j = (!pGD)#dec to _size - 1 do
	    let tmp = _v.(j)#mult (v#get j) in
	      prod := (!prod)#add tmp
	  done
	end;
	!prod
      with Found -> numerical_zero
	
  method combine (q1: 'a) (q2: 'a) (k: int) =
    let q3 = self in
    let tmp0 = (q1#get k)#gcd (q2#get k) in
    let tmp1 = (q1#get k)#div tmp0 in
    let tmp2 = (q2#get k)#div tmp0 in
    let _ =
      for j = 1 to _size - 1 do
	if j != k then
	  let tmp3 = tmp2#mult (q1#get j) in
	  let tmp4 = tmp1#mult (q2#get j) in
	    q3#set j (tmp3#sub tmp4)
	else
	  ()
      done
    in
      begin
	q3#set k numerical_zero;
	q3#normalize
      end

  method add_dimensions (dimsup: int) =
    let q1 = self in
    let q2 = self#mkVector (_size + dimsup) in
    let _ = 
      if dimsup > 0 then
	begin
	  for j = 0 to _size - 1 do
	    q2#set j (q1#get j)
	  done;
	  for j = _size to _size + dimsup - 1 do
	    q2#set j numerical_zero
	  done
	end
      else
	for j = 0 to _size + dimsup - 1 do
	  q2#set j (q1#get j)
	done
    in
      q2

  method get_head =
    try
      for i = _size - 1 downto 1 do
	if not(_v.(i)#is_zero) then
	  raise (Got_integer i)
	else
	  ()
      done;
      0
    with Got_integer i -> i
	
  method is_null_strict =
    let q = self in
    let res = ref true in
    let _ =
      try
	if _size > (!pGD)#cst then
	  begin
	    res := (q#get (!pGD)#cst)#is_zero;
	    if !res then
	      for i = (!pGD)#dec to _size - 1 do
		if not((q#get i)#is_zero) then
		  begin
		    res := false;
		    raise Found
		  end
		else
		  ()
	      done
	    else
	      ()
	  end
	else
	  ()
      with Found -> ()
    in
      !res

  method permute_remove_dimensions (newq: vector_t) (_dimsup: int) (permut: int array) =
    let q = self in
      begin
	for j = 0 to (!pGD)#dec - 1 do
	  newq#set j (q#get j)
	done;
	for j = (!pGD)#dec to q#size - 1 do
	  let newj = permut.(j - (!pGD)#dec) + (!pGD)#dec in
	    if newj < newq#size then
	      newq#set newj (q#get j)
	    else
	      ()
	done
      end

  method toPretty = pretty_print_array _v (fun n -> n#toPretty) "[" " " "]"

end

let empty_vector = new vector_t 0
