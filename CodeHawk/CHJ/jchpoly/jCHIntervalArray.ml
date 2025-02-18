(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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


(* chlib *)
open CHIntervals
open CHLanguage
open CHPretty

(* chutil *)
open CHPrettyUtil

(* jchsys *)
open JCHPrintUtils

let interval_array_index = ref (-1)
let get_interval_array_index () =
  begin
    incr interval_array_index;
    !interval_array_index
  end

let dbg = ref false
let empty_small_array = Array.make 0 topInterval
let array_size = JCHAnalysisUtils.numeric_params#interval_array_size

(* Wrapper around an array of intervals.
 * The bottom interval is used for a variable that is not in use,
 * such as before it is first assigned, or after is last read. *)
class interval_array_t s =
  object (self: 'a)

    val size = s
    val intervals_opt = None      (* double indexed array of intervals *)
    val type_intervals_opt = None (* double indexed array of type intervals *)
    val interval_array_ind = get_interval_array_index ()

    method private make_arrays (size:int) (interval:interval_t) =
      let (dim1, dim2) = self#get_dimensions size in
      let new_arrays = Array.make dim1 empty_small_array in
      begin
        for i = 0 to dim1 - 2 do
	  new_arrays.(i) <- (Array.make array_size interval)
        done;
        new_arrays.(pred dim1) <- Array.make dim2 interval;
        new_arrays
      end

    method make (size:int) (interval:interval_t) =
      if size = 0 then
        {< intervals_opt = None >}
      else
        {< size = size;
	   intervals_opt = Some (self#make_arrays size interval);
	   type_intervals_opt = None;
	   interval_array_ind = get_interval_array_index ()
        >}

    method set_type_intervals
             (jproc_info:JCHProcInfo.jproc_info_t) (vars:variable_t list) =
      if vars = [] then
        {< type_intervals_opt = None;
           interval_array_ind = get_interval_array_index ()
        >}
      else
	let new_arrays = self#make_arrays size topInterval in
	let set_interval i var =
	  let tinterval =
	    if JCHAnalysisUtils.numeric_params#use_types then
	      try (* var could be made-up length variable that is not in the system *)
		let num_type = (jproc_info#get_jvar_info var)#get_basic_num_type in
		JCHTypeUtils.get_var_interval_from_type var num_type
	      with _ -> JCHTypeUtils.length_interval
	    else
              topInterval in
	  let (index1, index2) = self#get_indices i in
          begin
	    new_arrays.(index1).(index2) <- tinterval;
	    succ i
          end in
	let _ = List.fold_left set_interval 0 vars in
	{< type_intervals_opt = Some new_arrays;
           interval_array_ind = get_interval_array_index ()
        >}

    (* Always uses the type interval regardles of numeric_params#use_types *)
    method set_type_intervals_and_restrict
             (jproc_info:JCHProcInfo.jproc_info_t) (vars:variable_t list) =
      if vars = [] then
        {< type_intervals_opt = None;
           interval_array_ind = get_interval_array_index ()
        >}
      else
	let new_type_arrays = self#make_arrays size topInterval in
	let new_arrays = self#make_arrays size topInterval in
	let set_intervals i var =
	  let tinterval =
	    try (* var could be made-up length variable that is not in the system *)
	      let num_type = (jproc_info#get_jvar_info var)#get_basic_num_type in
	      JCHTypeUtils.get_var_interval_from_type var num_type
	    with _ -> JCHTypeUtils.length_interval in
	  let (index1, index2) = self#get_indices i in
          begin
	    new_type_arrays.(index1).(index2) <- tinterval;
	    new_arrays.(index1).(index2) <-
              new_arrays.(index1).(index2)#meet tinterval;
	    succ i
          end in
	let _ = List.fold_left set_intervals 0 vars in
	{<intervals_opt = Some new_arrays;
	  type_intervals_opt = Some new_type_arrays;
	  interval_array_ind = get_interval_array_index ()
        >}

    method clone =
      match intervals_opt with
      |	Some arrays -> {< intervals_opt = Some (Array.copy arrays) >}
      |	None -> {< >}

    method private copy' arrays =
      let new_arrays = Array.copy arrays in
      begin
        for i = 0 to pred (Array.length arrays) do
	  new_arrays.(i) <- Array.copy (arrays.(i))
        done;
        new_arrays
      end

    method copy =
      {< intervals_opt = Some (self#copy' self#get_arrays);
         interval_array_ind = get_interval_array_index ()
      >}

    method make_bottom_intervals (size:int) =
      if size = 0 then
        {< intervals_opt = None;
           interval_array_ind = get_interval_array_index ()
        >}
      else
        {< intervals_opt = Some (self#make_arrays size bottomInterval);
           interval_array_ind = get_interval_array_index ()
        >}

    method make_top_intervals (size:int) =
      if size = 0 then
        {< intervals_opt = None;
           interval_array_ind = get_interval_array_index ()
        >}
      else
        {< size = size;
	   intervals_opt = Some (self#make_arrays size topInterval);
	   type_intervals_opt = None;
           interval_array_ind = get_interval_array_index ()
        >}

    method make_from_types (size:int) =
      if size = 0 then
        {< intervals_opt = None;
           interval_array_ind = get_interval_array_index ()
        >}
      else
        {< intervals_opt = Some (self#copy' self#get_type_arrays);
           interval_array_ind = get_interval_array_index ()
        >}

    method get_arrays =
      match intervals_opt with
      |	Some arrays -> arrays
      |	None -> Array.make 0 empty_small_array

    method private get_type_arrays =
      match type_intervals_opt with
      |	Some arrays -> arrays
      |	None -> Array.make 0 empty_small_array

    method get_type_interval (index:int) =
      let (index1, index2) = self#get_indices index in
      (self#get_type_arrays).(index1).(index2)

    method private get_indices (index:int)=
      let index1 = index / array_size in
      let index2 = index mod array_size in
      (index1, index2)

    method is_discrete (index:int) =
      let (index1, index2) = self#get_indices index in
      not (self#get_type_arrays.(index1).(index2)#equal topInterval)

    method get (index:int) =
      let (index1, index2) = self#get_indices index in
      (self#get_arrays).(index1).(index2)

    method private get_dimensions (dim:int) =
      if dim = 0 then
        (0, 0)
      else
	let (index1, index2) = self#get_indices dim in
	if index2 = 0 then
          (index1, array_size)
	else
          (succ index1, index2)

    method set (index:int) (interval:interval_t) =
      let (index1, index2) = self#get_indices index in
      (self#get_arrays).(index1).(index2) <- interval

    method copy_set (index:int) (interval:interval_t) =
      let arrays = self#get_arrays in
      let new_arrays = self#copy' arrays in
      let (index1, index2) = self#get_indices index in
      let small_array = new_arrays.(index1) in
      begin
        small_array.(index2) <- interval;
        {< intervals_opt = Some new_arrays;
           interval_array_ind = get_interval_array_index ()
        >}
      end

    method copy_set_typed (index:int) (interval:interval_t) =
      let arrays = self#get_arrays in
      let new_arrays = self#copy' arrays in
      let (index1, index2) = self#get_indices index in
      let small_array = new_arrays.(index1) in
      begin
        small_array.(index2) <- interval#meet (self#get_type_arrays).(index1).(index2);
        {< intervals_opt = Some new_arrays;
           interval_array_ind = get_interval_array_index ()
        >}
      end

    method project_out (inds:int list) =
      if inds = [] then
        {< >}
      else
	let new_intervals = self#copy' self#get_arrays in
	let type_intervals = self#get_type_arrays in
	let set_type_interval i =
	  let (index1, index2) = self#get_indices i in
	  new_intervals.(index1).(index2) <- type_intervals.(index1).(index2) in
        begin
	  List.iter set_type_interval inds;
	  {< intervals_opt = Some new_intervals;
             interval_array_ind = get_interval_array_index ()
          >}
	end

    method remove (inds:int list) =
      if inds = [] then
        {< >}
      else
	let new_intervals = self#copy' self#get_arrays in
	let set_type_interval i =
	  let (index1, index2) = self#get_indices i in
	  new_intervals.(index1).(index2) <- bottomInterval in
        begin
	  List.iter set_type_interval inds;
	  {< intervals_opt = Some new_intervals;
             interval_array_ind = get_interval_array_index ()
          >}
        end

    method restrict_to_type (inds:int list) =
      if inds = [] then
        {< >}
      else
	let intervals = self#get_arrays in
	let new_intervals = self#copy' intervals in
	let type_intervals = self#get_type_arrays in
	let set_type_interval i =
	  let (index1, index2) = self#get_indices i in
	  new_intervals.(index1).(index2) <-
            intervals.(index1).(index2)#meet type_intervals.(index1).(index2) in
        begin
	  List.iter set_type_interval inds;
	  {< intervals_opt = Some new_intervals;
             interval_array_ind = get_interval_array_index ()
          >}
        end

    method meet (a: 'a) (ignore_bottom:bool) =
      if size = 0 then
        {< >}
      else
	let new_arrays = self#make_arrays size bottomInterval in
	let arrays = self#get_arrays in
	let aarrays = a#get_arrays in
	let (dim1, dim2) = self#get_dimensions size in
        begin
	  for i = 0 to pred dim1 do
	    let small_new_array = new_arrays.(i) in
	    let small_array = arrays.(i) in
	    let small_aarray = aarrays.(i) in
	    let dim = if i = pred dim1 then dim2 else array_size in
	    for j = 0 to pred dim do
	      let interval = small_array.(j) in
	      let ainterval = small_aarray.(j) in
	      let new_interval =
	        match (interval#isBottom, ainterval#isBottom) with
	        | (true, true) -> bottomInterval
	        | (true, _) -> if ignore_bottom then ainterval else bottomInterval
	        | (_, true) -> if ignore_bottom then interval else bottomInterval
	        | _ -> interval#meet ainterval in
	      small_new_array.(j) <- new_interval
	    done
	  done;
	  {< intervals_opt = Some new_arrays;
             interval_array_ind = get_interval_array_index ()
          >}
        end

    method join' (size:int) (a: 'a) =
      if size = 0 then
        {< >}
      else
	let new_arrays = self#make_arrays size bottomInterval in
        let arrays = self#get_arrays in
	let aarrays = a#get_arrays in
	let (dim1, dim2) = self#get_dimensions size in
        begin
	  for i = 0 to pred dim1 do
	    let small_new_array = new_arrays.(i) in
	    let small_array = arrays.(i) in
	    let small_aarray = aarrays.(i) in
	    let dim = if i = pred dim1 then dim2 else array_size in
	    for j = 0 to pred dim do
	      let interval = small_array.(j) in
	      let ainterval = small_aarray.(j) in
	      small_new_array.(j) <- interval#join ainterval
	    done
	  done;
	  {< intervals_opt = Some new_arrays;
             interval_array_ind = get_interval_array_index ()
          >}
	end

    method join (a: 'a) =
      if size = 0 then
        {< >}
      else
	let new_arrays = self#make_arrays size bottomInterval in
        let arrays = self#get_arrays in
	let aarrays = a#get_arrays in
	let (dim1, dim2) = self#get_dimensions size in
        begin
	  for i = 0 to pred dim1 do
	    let small_new_array = new_arrays.(i) in
	    let small_array = arrays.(i) in
	    let small_aarray = aarrays.(i) in
	    let dim = if i = pred dim1 then dim2 else array_size in
	    for j = 0 to pred dim do
	      let interval = small_array.(j) in
	      let ainterval = small_aarray.(j) in
	      small_new_array.(j) <- interval#join ainterval
	    done
	  done;
	  {< intervals_opt = Some new_arrays;
             interval_array_ind = get_interval_array_index ()
          >}
	end

    (* It returns the variables that are singleton in one but not the
     * other or are different singletons *)
    method get_singletons_that_changed (a: 'a) :
	((int * interval_t) list * (int * interval_t) list) =
      let arrays = self#get_arrays in
      let aarrays = a#get_arrays in
      let (dim1, dim2) = self#get_dimensions size in
      let changed = ref [] in
      let achanged = ref [] in
      let index = ref 0 in
      begin
        for i = 0 to pred dim1 do
	  let small_array = arrays.(i) in
	  let small_aarray = aarrays.(i) in
	  let dim = if i = pred dim1 then dim2 else array_size in
	  for j = 0 to pred dim do
	    let interval = small_array.(j) in
	    let ainterval = small_aarray.(j) in
	    (match (interval#singleton, ainterval#singleton) with
	     | (Some n1, Some n2) ->
	        if not (n1#equal n2) then
		  begin
		    changed := (!index, interval) :: !changed;
		    achanged := (!index, ainterval) :: !achanged
		  end
	     | (Some _, _) ->
	        if not ainterval#isBottom then
		  changed := (!index, interval) :: !changed
	     | (_, Some _) ->
	        if not interval#isBottom then
		  achanged := (!index, ainterval) :: !achanged
	     | _ -> () );
	    incr index;
	  done
        done;
        (!changed, !achanged)
      end

    (* returns a list of (index, singleton value) *)
    method get_singletons =
      let (dim1, dim2) = self#get_dimensions size in
      let arrays = self#get_arrays in
      let singletons = ref [] in
      let index = ref 0 in
      begin
        for i = 0 to pred dim1 do
	  let small_array = arrays.(i) in
	  let dim = if i = pred dim1 then dim2 else array_size in
	  for j = 0 to pred dim do
	    let interval = small_array.(j) in
	    (match interval#singleton with
	     | Some n -> singletons := (!index, n#getNum) :: !singletons;
	     | _ -> () );
	    incr index;
	  done
        done;
        !singletons
      end

    method widening' (a: 'a) (* (hint_opt: 'a option) *) =
      if size = 0 then
        {< >}
      else
	let new_arrays = self#make_arrays size bottomInterval in
        let arrays = self#get_arrays in
	let aarrays = a#get_arrays in
	let (dim1, dim2) = self#get_dimensions size in
        begin
	  for i = 0 to pred dim1 do
	    let small_new_array = new_arrays.(i) in
	    let small_array = arrays.(i) in
	    let small_aarray = aarrays.(i) in
	    let dim = if i = pred dim1 then dim2 else array_size in
	    for j = 0 to pred dim do
	      let interval = small_array.(j) in
	      let ainterval = small_aarray.(j) in
	      let new_interval =
                if interval#isBottom then
                  ainterval
                else
                  interval#widening ainterval in
	      small_new_array.(j) <- new_interval
	    done
	  done;
	  {< intervals_opt = Some new_arrays;
             interval_array_ind = get_interval_array_index ()
          >}
	end

    method widening (a: 'a) (* (hint_opt: 'a option) *) =
      if size = 0 then
        {< >}
      else
	let new_arrays = self#make_arrays size bottomInterval in
        let arrays = self#get_arrays in
	let aarrays = a#get_arrays in
        let tarrays = self#get_type_arrays in
	let (dim1, dim2) = self#get_dimensions size in
        begin
	  for i = 0 to pred dim1 do
	    let small_new_array = new_arrays.(i) in
	    let small_array = arrays.(i) in
	    let small_aarray = aarrays.(i) in
	    let small_tarray = tarrays.(i) in
	    let dim = if i = pred dim1 then dim2 else array_size in
	    for j = 0 to pred dim do
	      let interval = small_array.(j) in
	      let ainterval = small_aarray.(j) in
	      let tinterval = small_tarray.(j) in
	      let new_interval =
                if interval#isBottom then
                  ainterval
                else
                  interval#widening ainterval in
	      small_new_array.(j) <- new_interval#meet tinterval
	    done
	  done;
	  {< intervals_opt = Some new_arrays;
             interval_array_ind = get_interval_array_index ()
          >}
	end

    method iteri f =
      let arrays = self#get_arrays in
      let start_index = ref 0 in
      for i = 0 to Array.length arrays - 1 do
	let small_array = arrays.(i) in
	let small_f j = f (!start_index + j) in
	Array.iteri small_f small_array;
	start_index := !start_index + array_size
      done

    method private type_iteri f =
      let arrays = self#get_type_arrays in
      let start_index = ref 0 in
      for i = 0 to Array.length arrays - 1 do
	let small_array = arrays.(i) in
        let small_f j = f (!start_index + j) in
	Array.iteri small_f small_array;
	start_index := !start_index + array_size
      done


    (* Copies the first len entries of source into dest starting at index 0 *)
    method private copy_beginning (source:'a) (dest:'a) (len:int) =
      let sarrays = source#get_arrays in
      let darrays = dest#get_arrays in
      if len = 0 then
        ()
      else
	let (len1, len2) = self#get_dimensions len in
        begin
	  for i = 0 to pred len1 do
	    let sarray = sarrays.(i) in
	    let darray = darrays.(i) in
	    let size = if i = pred len1 then len2 else array_size in
	    for j = 0 to pred size do
	      darray.(j) <- sarray.(j)
	    done
	  done
	end

    (* Unlike Array.blit, this does not work if it is the same array *)
    method private blit (a: 'a) o1 (b: 'a) o2 len =
      if len = 0 then ()
      else
	let (astart1, astart2) = self#get_indices o1 in
	let (bstart1, bstart2) = self#get_indices o2 in
	let aarrays = a#get_arrays in
	let barrays = b#get_arrays in
	let asmall_array = ref aarrays.(astart1) in
	let bsmall_array = ref barrays.(bstart1) in
	let i1 = ref astart1 in
	let j1 = ref bstart1 in
	let i2 = ref astart2 in
	let j2 = ref bstart2 in
        begin
	  for _k = 1 to len do
	    if !i2 = array_size then
	      begin
		incr i1;
		i2 := 0;
		asmall_array := aarrays.(!i1)
	      end;
	    if !j2 = array_size then
	      begin
		incr j1;
		j2 := 0;
		bsmall_array := barrays.(!j1)
	      end;
	    !bsmall_array.(!j2) <- !asmall_array.(!i2);
	    incr i2;
	    incr j2;
	  done
	end

    (* new_dim >= old_dim *)
    method augment (old_dim:int) (new_dim:int) (interval:interval_t) =
      if old_dim = new_dim then
        {< >}
      else if old_dim = 0 then
        self#make new_dim interval
      else
	let arrays = self#get_arrays in
	let (old_dim1, old_dim2) = self#get_dimensions old_dim in
	let pred_old_dim1 = pred old_dim1 in
	let (dim1, dim2) = self#get_dimensions new_dim in
	let new_arrays = Array.make dim1 empty_small_array in
        begin
	  for i = 0 to pred pred_old_dim1 do
	    new_arrays.(i) <- arrays.(i)
	  done;

	  (if old_dim2 = array_size then
	    new_arrays.(pred_old_dim1) <- arrays.(pred_old_dim1)
          else
	    begin
	      let size = if dim1 > old_dim1 then array_size else dim2 in
	      let new_small_array = Array.make size interval in
	      Array.blit arrays.(pred_old_dim1) 0 new_small_array 0 old_dim2;
	      new_arrays.(pred_old_dim1) <- new_small_array
	    end);

	  (if old_dim1 < dim1 then
	    begin
	      for i = old_dim1 to dim1 - 2 do
		new_arrays.(i) <- Array.make array_size interval
	      done;
	      new_arrays.(pred dim1) <- Array.make dim2 interval
	    end);

	  {< size = new_dim; intervals_opt = Some new_arrays;
             type_intervals_opt = None;
             interval_array_ind = get_interval_array_index ()
          >}

	end

    (* Changes the size of the array *)
    (* inds_to_remove have to be sorted from largest to smallest *)
    method remove_entries (dim:int) (inds_to_remove:int list) =
      let remove (res, dim) ind =
	let new_dim = pred dim in
	let new_array = self#make new_dim topInterval in
        begin
	  self#copy_beginning res new_array ind;
	  self#blit res (succ ind) new_array ind (new_dim - ind);
	  (new_array, new_dim)
        end in
      let (res, _new_dim) = List.fold_left remove (self, dim) inds_to_remove in
      res

    method remap (dim:int) (map:(int * int) list) =
      let new_array = self#make dim topInterval in
      begin
        for i = 0 to pred dim do
	  let new_i = List.assoc i map in
	  new_array#set new_i (self#get i)
        done;
        new_array
      end

    method to_pretty (vars:variable_t list) =
      try (* if it is top *)
	let pps = ref [] in
	let vs = ref vars in
	let add_interval _i interval =
	  let v = List.hd !vs in
          begin
	    pps :=
              (LBLOCK [v#toPretty; STR " -> "; interval#toPretty; NL]) :: !pps;
	    vs := List.tl !vs
          end in
	self#iteri add_interval;

	let pps_types = ref [] in
	let vs = ref vars in
	let add_interval _i interval =
	  let v = List.hd !vs in
          begin
	    pps_types :=
              (LBLOCK [
                   v#toPretty; STR " -> "; interval#toPretty; NL]) :: !pps_types;
	    vs := List.tl !vs
          end in
	self#type_iteri add_interval;

	LBLOCK[ STR "intervals: "; INT interval_array_ind; NL;
                LBLOCK (List.rev !pps); NL;  STR "types: "; NL;
                LBLOCK (List.rev !pps_types) ]
      with _ ->
	self#toPretty

    method toPretty =
      let pps = ref [] in
      let add_interval i interval =
	if not interval#isBottom then
	  pps := (LBLOCK [INT i; STR " -> "; interval#toPretty; NL]) :: !pps in
      self#iteri add_interval;

      let pps_types = ref [] in
      let add_interval i interval =
	pps_types :=
          (LBLOCK [INT i; STR " -> "; interval#toPretty; NL]) :: !pps_types in
      self#type_iteri add_interval;

      LBLOCK[ STR "intervals: "; INT interval_array_ind; NL;
              LBLOCK (List.rev !pps); NL;  STR "types: "; NL;
              LBLOCK (List.rev !pps_types) ]

    method pr__debug_large_interval_array
             (extra_infos:JCHNumericInfo.numeric_info_t)
             (indent:string)
             (vars:variable_t list) =
      pr__debug [STR indent; STR "intervals: "; INT interval_array_ind; NL];
      let vs = ref vars in
      let pp_interval has_excluded i interval =
	let v =
	  try
	    List.hd !vs
	  with _ ->
	    pr__debug [
                STR indent; STR "i = "; INT i; STR " -> "; interval#toPretty; NL];
	    List.hd !vs in
	vs := List.tl !vs;
	pr__debug [STR indent; v#toPretty; STR " -> "; interval#toPretty; ];
	if has_excluded then
	  let excls = extra_infos#get_excluded_vals v in
	  if excls <> [] then
	    pr__debug [STR " - "; pp_list excls; NL] else
	    pr__debug [NL]
	else pr__debug [NL] in
      self#iteri (pp_interval true);
      pr__debug [NL; STR indent; STR "types: "; NL];
      vs := vars;
      self#type_iteri (pp_interval false);
      pr__debug[NL];

  end


let make_top_intervals size = (new interval_array_t size)#make_top_intervals size

let make_from_types (jproc_info:JCHProcInfo.jproc_info_t) (vars:variable_t list) =
  let size = List.length vars in
  if size = 0 then
    (new interval_array_t 0)
  else
    let new_interval_array = make_top_intervals size in
    (new_interval_array#set_type_intervals jproc_info vars)#make_from_types size
