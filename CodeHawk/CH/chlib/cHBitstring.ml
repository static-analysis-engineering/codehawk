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
   

let bitstring_size = 16

let bitindex_size (n: int) =
  let size = n / bitstring_size in
    if (n mod bitstring_size = 0) then size else size + 1


class bitstring_t (n: int32) =
object (_self: 'a)
  
  val _b: int32 = n
  
    
  method b = _b

  method shift_right (n: int) = {< _b = Int32.shift_right_logical _b n >}
    
  method shift_left (n: int) = {< _b = Int32.shift_left _b n >}
    
  method logical_and (bs: 'a) = {< _b = Int32.logand _b bs#b >}

  method logical_or (bs: 'a) = {< _b = Int32.logor _b bs#b >}

  method logical_not = {< _b = Int32.lognot _b >}
    
  method is_zero = ((compare _b (Int32.of_int 0)) = 0)

  method equal (bs: 'a) = (_b = bs#b)

  method gt (bs: 'a) = ((compare _b bs#b) = 1)

  method lt (bs: 'a) = ((compare _b bs#b) = -1)

end


let zero_bitstring = new bitstring_t (Int32.of_int 0)
  
let one_bitstring = new bitstring_t (Int32.of_int 1)

let bitstring_msb = one_bitstring#shift_left (bitstring_size - 1)

let bitstring_cmp (r1: bitstring_t array) (r2: bitstring_t array) =
  let res = ref 0 in
  let _ =
    try
      for i = 0 to (Array.length r1) - 1 do
	if r1.(i)#lt r2.(i) then
	  begin
	    res := -1;
	    raise Found
	  end
	else if r1.(i)#gt r2.(i) then
	  begin
	    res := 1;
	    raise Found
	  end
	else
	  ()
      done
    with Found -> ()
  in
    !res

class bitindex_t (col: int) =
object (_self: 'a)
  
  val mutable _index: int = col

  val mutable _word: int = col / bitstring_size

  val mutable _bit: bitstring_t = bitstring_msb#shift_right (col mod bitstring_size)
    

  method index = _index

  method word = _word

  method bit = _bit

  method inc =
    _index <- _index + 1;
    _bit <- _bit#shift_right 1;
    if _bit#is_zero then
      begin
	_bit <- bitstring_msb;
	_word <- _word + 1
      end
    else
      ()

  method dec =
    _index <- _index - 1;
    if not(_bit#equal bitstring_msb) then
      _bit <- _bit#shift_left 1
    else
      begin
	_bit <- one_bitstring;
	_word <- _word - 1
      end
	
end
