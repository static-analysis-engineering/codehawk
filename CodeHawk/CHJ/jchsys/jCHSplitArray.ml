(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
   ============================================================================= *)


let small_array_size = ref 50


class ['b] split_array_t (size:int) (init_entry: 'b) =
  object (self: 'a)

    val empty_small_array = Array.make 0 init_entry
    val dim1 = ref 0
    val dim2 = ref 0
    val arrays = ref (Array.make 0 (Array.make 0 init_entry))

    initializer
      let (d1, d2) = self#get_dimensions size in
      dim1 := d1;
      dim2 := d2;
      arrays := Array.make !dim1 empty_small_array;
      for i = 0 to !dim1 - 2 do
	!arrays.(i) <- (Array.make !small_array_size init_entry)
      done;
      !arrays.(pred !dim1) <- Array.make !dim2 init_entry

    method copy =
      let new_arrays = Array.copy !arrays in
      for i = 0 to pred !dim1 do
	new_arrays.(i) <- Array.copy (!arrays.(i))
      done;
      {< arrays = ref new_arrays >}

    method private get_indices index =
      let index1 = index / !small_array_size in
      let index2 = index mod !small_array_size in
      (index1, index2)

    method private get_dimensions dim =
      if dim = 0 then (0, 0)
      else
	let (index1, index2) = self#get_indices dim in
	if index2 = 0 then (index1, !small_array_size)
	else (succ index1, index2)

    method get ind : 'b =
      let (ind1, ind2) = self#get_indices ind in
      !arrays.(ind1).(ind2)

    method set ind (entry: 'b) =
      let (ind1, ind2) = self#get_indices ind in
      !arrays.(ind1).(ind2) <- entry

    method iteri (f : int -> unit) =
      let index = ref (-1) in
      for i = 0 to !dim1 - 1 do
	let ai = !arrays.(i) in
	for _j = 0 to Array.length ai do
	  incr index;
	  f (!index)
	done
      done;

  end


class split_matrix_t size1 size2 i =
  object (self: 'a)

    val empty_small_array = Array.make 0 i
    val empty_small_matrix = Array.make 0 (Array.make 0 (Array.make 0 i))
    val dim1 = ref 0
    val dim2 = ref 0
    val dim3 = ref 0
    val dim4 = ref 0
    val arrays = ref (Array.make 0 (Array.make 0 (Array.make 0 (Array.make 0 i))))

    initializer
      let (d1, d2) = self#get_dimensions size1 in
      dim1 := d1;
      dim2 := d2;
      let (d3, _d4) = self#get_dimensions size2 in
      dim3 := d3;
      dim4 := d2;
      let small_matrix = Array.make !dim3 empty_small_array in
      for i = 0 to !dim3 - 2 do
	small_matrix.(i) <- Array.make !small_array_size i
      done;
      small_matrix.(pred !dim3) <- Array.make !dim4 i;

      arrays := Array.make !dim1 empty_small_matrix;
      for i = 0 to !dim1 - 2 do
	!arrays.(i) <- Array.make !small_array_size small_matrix
      done;
      !arrays.(pred !dim1) <- Array.make !dim2 small_matrix

    method copy =
      let new_arrays = Array.copy !arrays in
      for i = 0 to pred !dim1 do
	let ai = !arrays.(i) in
	for j = 0 to pred (Array.length ai) do
	  let aj = ai.(j) in
	  for k = 0 to pred (Array.length aj) do
	    new_arrays.(i).(j).(k) <- Array.copy (aj.(k))
	  done
	done
      done;
      {< arrays = ref new_arrays >}

    method private get_indices index =
      let index1 = index / !small_array_size in
      let index2 = index mod !small_array_size in
      (index1, index2)

    method private get_dimensions dim =
      if dim = 0 then (0, 0)
      else
	let (index1, index2) = self#get_indices dim in
	if index2 = 0 then (index1, !small_array_size)
	else (succ index1, index2)

    method get ind1 ind2 : 'b =
      let (i1, i2) = self#get_indices ind1 in
      let (i3, i4) = self#get_indices ind2 in
      !arrays.(i1).(i2).(i3).(i4)

    method set ind1 ind2 (entry: 'b) =
      let (i1, i2) = self#get_indices ind1 in
      let (i3, i4) = self#get_indices ind2 in
      !arrays.(i1).(i2).(i3).(i4) <- entry


  end


class ['b] split3_array_t (size:int) (init_entry: 'b) =
  object (self: 'a)

    val empty_small_array = Array.make 0 init_entry
    val empty_medium_array = Array.make 0 (Array.make 0 init_entry)
    val dim1 = ref 0
    val dim2 = ref 0
    val dim3 = ref 0
    val arrays = ref (Array.make 0 (Array.make 0 (Array.make 0 init_entry)))

    initializer
      let (d1, d2, d3) = self#get_dimensions size in
      dim1 := d1;
      dim2 := d2;
      dim3 := d3;
      arrays := Array.make !dim1 empty_medium_array;
      for i = 0 to !dim1 - 2 do
	for j = 0 to !small_array_size do
	  !arrays.(i).(j) <- empty_small_array
	done
      done;
      let last_a = !arrays.(pred !dim1) in
      for j = 0 to !dim2 - 2 do
	last_a.(j) <- empty_small_array
      done;
      last_a.(pred !dim2) <- Array.make !dim3 init_entry

    method copy =
      let new_arrays = Array.make !dim1 empty_medium_array in
      for i = 0 to pred !dim1 do
	let ai = !arrays.(i) in
	let len = Array.length ai in
	let new_ai = Array.make len empty_small_array in
	new_arrays.(i) <- new_ai;
	for j = 0 to pred len do
	  new_ai.(j) <- Array.copy ai.(j)
	done
      done;
      {< arrays = ref new_arrays >}

    method private get_indices index =
      let d = index / !small_array_size in
      let index3 = index mod !small_array_size in
      let index1 = d / !small_array_size in
      let index2 = d mod !small_array_size in
      (index1, index2, index3)

    method private get_dimensions dim =
      if dim = 0 then (0, 0, 0)
      else
	let (index1, index2, index3) = self#get_indices dim in
	if index3 = 0 then
	  if index2 = 0 then (index1, !small_array_size, !small_array_size)
	  else (succ index1, index2, !small_array_size)
	else (succ index1, succ index2, index3)

    method get ind : 'b =
      let (ind1, ind2, ind3) = self#get_indices ind in
      !arrays.(ind1).(ind2).(ind3)

    method set ind (entry: 'b) =
      let (ind1, ind2, ind3) = self#get_indices ind in
      !arrays.(ind1).(ind2).(ind3) <- entry

    method iteri (f : int -> unit) =
      let index = ref (-1) in
      for i = 0 to !dim1 - 1 do
	let ai = !arrays.(i) in
	for j = 0 to Array.length ai do
	  let aj = ai.(j) in
	  for _k = 0 to Array.length aj do
	    incr index;
	    f (!index)
	  done
	done
      done

  end


let make size init_entry = new split_array_t size init_entry
let make_empty init_entry = make 0 init_entry


let make_matrix size1 size2 i = new split_matrix_t size1 size2 i
let make_empty_matrix i = make_matrix 0 0 i

let make3 size init_entry = new split3_array_t size init_entry
let make3_empty init_entry = make3 0 init_entry
