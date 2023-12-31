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


class satmat_t nr nc =
object (self: 'a)
    
  val mutable _nbrows: int = nr

  val _nbcolumns: int = nc

  val _p: bitstring_t array array = Array.make_matrix nr nc zero_bitstring
    

  method mkNew nr nc =
    let mat = Array.make_matrix nr nc zero_bitstring in
      {< _nbrows = nr; _nbcolumns = nc; _p = mat >}
	
  method is_empty = ((_nbrows * _nbcolumns) = 0)

  method nbrows = _nbrows

  method nbcolumns = _nbcolumns

  method set_nbrows (n: int) = _nbrows <- n

  method p (i: int) (w: int) =
    _p.(i).(w)

  method get_row (i: int) = _p.(i)

  method set_row (i: int) (row: bitstring_t array) =
    _p.(i) <- row

  method set_p (i: int) (w: int) (b: bitstring_t) =
    _p.(i).(w) <- b

  method get (i: int) (jx: bitindex_t) =
    _p.(i).(jx#word)#logical_and jx#bit

  method set (i: int) (jx: bitindex_t) =
    _p.(i).(jx#word) <- _p.(i).(jx#word)#logical_or jx#bit

  method copy =
    let p' = Array.make_matrix _nbrows _nbcolumns zero_bitstring in
    let _ = 
      for i = 0 to _nbrows - 1 do
	for j = 0 to _nbcolumns - 1 do
	  p'.(i).(j) <- _p.(i).(j)
	done
      done
    in
      {< _p = p' >}
	
  method exch_rows (i: int) (j: int) =
    let row = _p.(i) in
      begin
	_p.(i) <- _p.(j);
	_p.(j) <- row
      end

  method transpose (nbcols: int) =
    let dest = self#mkNew nbcols (bitindex_size _nbrows) in
    let i = new bitindex_t 0 in
    let _ = 
      while i#index < _nbrows do
	let j = new bitindex_t 0 in
	  while j#index < nbcols do
	    if not((self#get i#index j)#is_zero) then
	      dest#set j#index i
	    else	      
	      ();
	    j#inc
	  done;
	  i#inc
      done
    in
      dest

  method index_in_sorted_rows (satline: bitstring_t array) =
    let sat = self in
    let index_satline = satline in
    let rec index2 low high =
      if high - low <= 4 then
	let res = ref (-1) in
	let _ =
	  try
	    for i = low to high - 1 do
	      let cmp = bitstring_cmp (sat#get_row i) index_satline in
		if cmp = 0 then
		  begin
		    res := i;
		    raise Found
		  end
		else if cmp > 0 then
		  raise Found
		else
		  ()
	    done
	  with Found -> ()
	in
	  !res
      else
	let mid = (high - low) / 2 in
	let cmp = bitstring_cmp (sat#get_row mid) index_satline in
	  if cmp < 0 then
	    index2 (mid + 1) high
	  else if cmp > 0 then
	    index2 low mid
	  else
	    mid
    in
      index2 0 sat#nbrows
	
  method sort_rows =
    Array.sort bitstring_cmp _p
      
end
  
let empty_satmat = new satmat_t 0 0

