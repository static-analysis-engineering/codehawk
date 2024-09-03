(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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
open CHLanguage
open CHPretty
open CHUtils

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI

(* jchsys *)
open JCHPrintUtils

module H = Hashtbl


let array_size = 50

let no_temp_files = ref true

class scc_graph_t all_procs not_analyzed edges =
object (self: _)

  (* proc_name#getSeqNumber -> internal index *)
  val proc_to_index = H.create (List.length all_procs)

  (* array of index -> proc_name *)
  val procs = ref (Array.make 0 (Array.make 0 (Array.make 0 (new symbol_t "no_proc"))))

  (* proc index -> scc representative index *)
  val node_to_rep = ref (Array.make 0 (Array.make 0 (Array.make 0 (-1))))

  (* scc representative index -> indices of all the procs in the scc *)
  val rep_to_nodes =
    ref (Array.make 0 (Array.make 0 (Array.make 0 (new IntCollections.set_t))))

  (* indices of all the methods in a loop *)
  val in_loop = ref (new SymbolCollections.set_t)

  (* caller index -> callee indices of all the invocations in the caller method *)
  val node_edges =
    ref (Array.make 0 (Array.make 0 (Array.make 0 (new IntCollections.set_t))))

  (* callee index -> callers indices of all the methods that invoke it *)
  val node_rev_edges =
    ref (Array.make 0 (Array.make 0 (Array.make 0 (new IntCollections.set_t))))

  (* forward edges of scc representatives *)
  val rep_edges =
    ref (Array.make 0 (Array.make 0 (Array.make 0 (new IntCollections.set_t))))

  (* back edges of scc representatives *)
  val rep_rev_edges =
    ref (Array.make 0 (Array.make 0 (Array.make 0 (new IntCollections.set_t))))

  (* number of methods - 1 *)
  val last_index = ref 0

  (* methods that have a call to themselves *)
  val recursive_methods = new SymbolCollections.set_t

    val dim1 = ref 0
    val dim2 = ref 0
    val dim3 = ref 0

    (* Releases all the structures that are not needed after initialization *)
    method clean_up =
      in_loop := new SymbolCollections.set_t ;
      node_edges :=
        (Array.make 0 (Array.make 0 (Array.make 0 (new IntCollections.set_t)))) ;
      node_rev_edges :=
        (Array.make 0 (Array.make 0 (Array.make 0 (new IntCollections.set_t))))

    (* Makes proc_to_index *)
    method private set_proc_to_index =
      let size = List.length all_procs in
      last_index := pred size ;
      self#set_dimensions size ;
      procs := self#make_arrays_sym ;
      let count = ref (-1) in
      let index1 = ref 0 in
      let index2 = ref 0 in
      let index3 = ref (-1) in
      let set_index (proc_name:symbol_t) =
	if not (not_analyzed#has proc_name#getSeqNumber) then
	  begin
	    incr count ;
	    incr index3 ;
	    if !index3 = array_size then
	      begin
		index3 := 0 ;
		incr index2 ;
		if !index2 = array_size then
		  begin
		    index2 := 0 ;
		    incr index1
		  end
	      end ;
	    !procs.(!index1).(!index2).(!index3) <- proc_name ;
	    H.add proc_to_index proc_name#getSeqNumber !count ;
	  end  in
      List.iter set_index all_procs

    method private get_index (proc_name:symbol_t) =
      let cmsix = proc_name#getSeqNumber in
      if H.mem proc_to_index cmsix then
	H.find proc_to_index proc_name#getSeqNumber
      else
	let cms = retrieve_cms cmsix in
	if app#has_method cms then
	  let dcmsix = (app#get_method cms)#get_index in
	  if H.mem proc_to_index dcmsix then
	    H.find proc_to_index dcmsix
	  else
	    raise
              (JCH_failure
                 (LBLOCK [ STR "procname index for " ; proc_name#toPretty ;
			   STR " not found int JCHCallGraph.get_index" ]))
	else
	  raise
            (JCH_failure
               (LBLOCK [ STR "procname index for " ; proc_name#toPretty ;
			 STR " not found int JCHCallGraph.get_index" ]))


    method private get_indices (index:int) =
      let d = index / array_size in
      let index3 = index mod array_size in
      let index1 = d / array_size in
      let index2 = d mod array_size in
      (index1, index2, index3)

    method private set_dimensions (dim:int) =
      let (d1, d2, d3) =
	if dim = 0 then (0,0,0)
	else
	  let (index1, index2, index3) = self#get_indices dim in
	  if index3 = 0 then
	    if index2 = 0 then
              (index1, array_size, array_size)
	    else
              (succ index1, index2, array_size)
	  else
            (succ index1, succ index2, index3) in
      dim1 := d1 ;
      dim2 := d2 ;
      dim3 := d3

    method private make_arrays_int =
      let vl = -1 in
      let make_medium_array i =
	if i < !dim1 - 1 then
	  let make_small_array _i = Array.make array_size vl in
	  Array.init array_size make_small_array
	else
	  let make_small_array i =
	    if i < !dim2 - 1 then
              Array.make array_size vl
	    else
              Array.make !dim3 vl in
	  Array.init !dim2 make_small_array in
      let top_arrays = Array.init !dim1 make_medium_array in
      top_arrays

    method private make_arrays_sym =
      let vl = new symbol_t "no_proc" in

      let make_medium_array i =
	if i < !dim1 - 1 then
	  let make_small_array _i = Array.make array_size vl in
	  Array.init array_size make_small_array
	else
	  let make_small_array i =
	    if i < !dim2 - 1 then
              Array.make array_size vl
	    else
              Array.make !dim3 vl in
	  Array.init !dim2 make_small_array in

      let top_arrays = Array.init !dim1 make_medium_array in
      top_arrays

    method private make_arrays_set =

      let make_medium_array (i:int) =
	if i < !dim1 - 1 then
	  let make_small_array _i =
	    Array.init array_size (fun _i -> new IntCollections.set_t) in
	  Array.init array_size make_small_array
	else
	  let make_small_array (i:int) =
	    if i < !dim2 - 1 then
              Array.init array_size (fun _i -> new IntCollections.set_t)
	    else
              Array.init !dim3 (fun _i -> new IntCollections.set_t) in
	  Array.init !dim2 make_small_array in

      let top_arrays = Array.init !dim1 make_medium_array in
      top_arrays

    method private iter_on_array (f: int -> int -> int -> int -> unit) =
      let node = ref (-1) in
      for i = 0 to !dim1 - 2 do
	for j = 0 to pred array_size do
	  for k = 0 to pred array_size do
	    incr node ;
	    f i j k !node
	  done
	done
      done ;
      let pred_dim1 = pred !dim1 in
      for j = 0 to !dim2 - 2 do
	for k = 0 to pred array_size do
	  incr node ;
	  f pred_dim1 j k !node
	done
      done ;
      let pred_dim2 = pred !dim2 in
      for k = 0 to !dim3 - 1 do
	incr node ;
	f pred_dim1 pred_dim2 k !node
      done

    method private get_proc (index:int) =
      let (index1, index2, index3) = self#get_indices index in
      !procs.(index1).(index2).(index3)

    method private get_value arrays (index:int) =
      let (index1, index2, index3) = self#get_indices index in
      arrays.(index1).(index2).(index3)

    method private remove_key arrays (index:int) =
      let (index1, index2, index3) = self#get_indices index in
      arrays.(index1).(index2).(index3) <- new IntCollections.set_t

    method private get_rep_ (index:int) =
      let (index1, index2, index3) = self#get_indices index in
      !node_to_rep.(index1).(index2).(index3)

    method private get_rep (node_index:int) =
      let path_nodes = new IntCollections.set_t in
      let rec go_up (n:int) =
	path_nodes#add n ;
	let up_n = self#get_rep_ n in
	if up_n = n then n
	else go_up up_n in
      let rep_index = go_up node_index in
      if node_index <> rep_index then
        path_nodes#iter (self#change_rep rep_index);
      rep_index

    method private change_rep rep_index n_index =
      let (index1, index2, index3) = self#get_indices n_index in
      !node_to_rep.(index1).(index2).(index3) <- rep_index

    method private add_node_edge source_index target_index =
      let set = self#get_value !node_edges source_index in
      set#add target_index ;
      let set = self#get_value !node_rev_edges target_index in
      set#add source_index

    method private find_node_sccs visited (start_node: int) =
      let on_path = new IntCollections.set_t in
      let path  = Stack.create () in
      Stack.push (start_node, None) path ;
      while not (Stack.is_empty path) do
	match Stack.pop path with
	| (node, None) ->
	    begin
	      let (index1, index2, index3) = self#get_indices node in
	      let was_not_visited = visited.(index1).(index2).(index3) <> 1 in
	      let rep = self#get_rep node in
	      if on_path#has rep then
		begin
		  let all_nexts = new IntCollections.set_t in
		  let rec unroll () =
		    let (n, nexts_opt) = Stack.top path in
		    let nexts = Option.get nexts_opt in
		    on_path#remove n ;
		    if not (n = rep) then
		      begin
			let _ = Stack.pop path in
			all_nexts#addSet nexts ;
			self#change_rep rep n;
			unroll ()
		      end
		    else
		      begin
			nexts#addSet all_nexts
		      end in
		  unroll ()
		end
	      else if was_not_visited then
		begin
		  visited.(index1).(index2).(index3) <- 1 ;
		  let nexts = self#get_value !node_edges node in
		  Stack.push (node, Some nexts#clone) path
		end
	    end
	| (node, Some nexts) ->
	    if nexts#isEmpty then
	      begin
		on_path#remove node ;
		if Stack.is_empty path then
                  ()
		else
                  let (parent, _) = Stack.top path in on_path#remove parent
	      end
	    else
	      begin
		let node' = Option.get nexts#choose in
		nexts#remove node' ;
		Stack.push (node, Some nexts) path ;
		on_path#add node ;
		Stack.push (node', None) path
	      end
      done

    method private find_sccs =
      let visited = self#make_arrays_int in
      let f i j k (node: int) =
	if visited.(i).(j).(k) <> 1 then
          self#find_node_sccs visited node in
      self#iter_on_array f

    method private make_rep_to_nodes =
      let process _i _j _k node =
	let rep_index = self#get_rep node in
        let set = self#get_value !rep_to_nodes rep_index in
	set#add node in
      self#iter_on_array process

    method private make_rep_graph =
      let add_edge i j k _node =
	let rep = !node_to_rep.(i).(j).(k) in
	let next_nodes = !node_edges.(i).(j).(k) in
	let next_reps = self#get_value !rep_edges rep in
	let add_edge n =
	  let r = self#get_rep_ n in
	  if r <> rep then
	    begin
	      next_reps#add r ;
	      let prevs = self#get_value !rep_rev_edges r in
	      prevs#add rep
	    end in
	next_nodes#iter add_edge in
      self#iter_on_array add_edge

    method private find_start_reps =
      let starts = ref [] in
      let rev_edges = self#make_arrays_set in
      let find i j k node =
	if node = self#get_rep_ node then
	  begin
	    if !rep_rev_edges.(i).(j).(k)#isEmpty then
              starts := node :: !starts
	    else
              rev_edges.(i).(j).(k) <- !rep_rev_edges.(i).(j).(k)#clone
	  end in
      self#iter_on_array find ;
      (starts, rev_edges)

    method private mk_bottom_up_list =
       let (starts, rev_edges) = self#find_start_reps in

       let sorted_procs = ref [] in
       let add_to_sorted_procs rep =
	 let node_indices = self#get_value !rep_to_nodes rep in
	 let procs = List.map self#get_proc node_indices#toList in
	 if List.length procs > 1 then !in_loop#addList procs ;
	 sorted_procs := List.rev_append procs !sorted_procs in

       let rec work () =
	 match !starts with
	 | t :: rest_starts ->
	     starts := rest_starts ;
	     add_to_sorted_procs t ;
	     let nexts = self#get_value !rep_edges t in
	     let remove_from_prev n =
	       let set = self#get_value rev_edges n in
	       set#remove t ;
	       if set#isEmpty then starts := n :: !starts in
	     nexts#iter remove_from_prev ;
	     work ()
	 | _ -> () in
       work () ;
      (!sorted_procs, !in_loop)

    method initialize =

      self#set_proc_to_index ;
      node_to_rep := self#make_arrays_int ;
      rep_to_nodes := self#make_arrays_set ;
      node_edges := self#make_arrays_set ;
      node_rev_edges := self#make_arrays_set ;
      rep_edges := self#make_arrays_set ;
      rep_rev_edges := self#make_arrays_set ;

      (* Copy the call graph in node_edges in node_rev_edges *)
      let add_edge (source, target) =
	if source#equal target then
	    recursive_methods#add source
	else if not (not_analyzed#has source#getSeqNumber
                     || not_analyzed#has target#getSeqNumber) then
	  let source_index = self#get_index source in
	  let target_index = self#get_index target in
	  self#add_node_edge source_index target_index in
      List.iter add_edge edges ;

      (* Make the graph between the sccs / nodes that are not part of a loop *)
      (* Initially each node is its own representatives *)
      self#iter_on_array (fun i j k node -> !node_to_rep.(i).(j).(k) <- node) ;
      self#find_sccs ;
      self#make_rep_to_nodes ;
      self#make_rep_graph ;

      self#mk_bottom_up_list


    val reps_that_access_static_fields = new IntCollections.set_t

    method find_methods_that_access_static_fields =
      let field_infos = app#get_fields in
      let reps_that_access = new IntCollections.set_t in
      let add_field_info (fInfo:field_info_int) =
	if not fInfo#is_constant && fInfo#is_static then
	  begin
            (* A field could be read and then one of its subfields could be changed *)
	    let cmss = fInfo#get_writing_methods @ fInfo#get_reading_methods in
	    let proc_names = List.map (fun cms -> make_procname cms#index) cmss in
	    let add_rep (proc_name:symbol_t) =
	      try
		let index = self#get_index proc_name in
		reps_that_access#add (self#get_rep index)
	      with _ -> () in   (* in case the method does not need to be analyzed *)
	    List.iter add_rep proc_names ;
	  end in
      List.iter add_field_info field_infos ;
      let rec work reps =
	match reps with
	| rep_index :: rest_reps ->
	   if reps_that_access_static_fields#has rep_index then
             work rest_reps
	    else
	      begin
		reps_that_access_static_fields#add rep_index ;
		let prev_reps = self#get_value !rep_rev_edges rep_index in
		let prev_reps = prev_reps#toList in
		let new_reps =
                  List.filter (fun r ->
                      not (reps_that_access_static_fields#has r)) prev_reps in
		work (new_reps @ rest_reps)
	      end
	| _ -> () in
      work reps_that_access#toList ;

    method accesses_static_field (proc_name:symbol_t) =
      let index = self#get_index proc_name in
      let rep_index = self#get_rep_ index in
      reps_that_access_static_fields#has rep_index

    method get_descendants (proc_names:symbol_t list) =
      let reps =
        IntCollections.set_of_list
          (List.map (fun pn -> self#get_rep_ (self#get_index pn))
                    proc_names) in
      let on_the_list = reps in
      let on_the_list_now = reps#clone in
      let descendants = ref [] in
      let rec add_desc reps =
	match reps with
	| rep :: rest_reps ->
	    let next_reps = self#get_value !rep_edges rep in
	    let nexts =
              List.filter (fun r -> not (on_the_list#has r)) next_reps#toList in
	    on_the_list#addList nexts ;
	    on_the_list_now#remove rep ;
	    on_the_list_now#addList nexts ;
	    let nodes = (self#get_value !rep_to_nodes rep)#toList in
	    descendants :=
              List.rev_append (List.map self#get_proc nodes) !descendants ;
	    add_desc (List.rev_append nexts rest_reps)
	| _ -> () in
      add_desc reps#toList ;
      !descendants

    method get_unsynchronized_descendants (proc_names:symbol_t list) =
      let reps =
        IntCollections.set_of_list
          (List.map (fun pn -> self#get_rep_ (self#get_index pn)) proc_names) in
      let on_the_list = reps in
      let descendants = ref [] in
      let is_not_synch_proc (node:int) =
	let proc_name = self#get_proc node in
	let mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber) in
	not mInfo#is_synchronized in
      let is_not_synch rep =
	let nodes = (self#get_value !rep_to_nodes rep)#toList in
	List.exists is_not_synch_proc nodes in
      let rec add_desc reps =
	match reps with
	| rep :: rest_reps ->
	    let next_reps = self#get_value !rep_edges rep in
	    let nexts =
              List.filter (fun r ->
                  not (on_the_list#has r)) next_reps#toList in
	    let not_synch_nexts = List.filter is_not_synch nexts in
	    on_the_list#addList nexts ;
	    let nodes = (self#get_value !rep_to_nodes rep)#toList in
	    let not_synch_nodes = List.filter is_not_synch_proc nodes in
	    descendants :=
              List.rev_append
                (List.map self#get_proc not_synch_nodes) !descendants ;
	    add_desc (List.rev_append not_synch_nexts rest_reps)
	| _ -> () in
      add_desc reps#toList ;
      !descendants

    method get_ancestors (proc_name:symbol_t) =
      let reps =
        IntCollections.set_of_list
          [self#get_rep_ (self#get_index proc_name)] in
      let on_the_list = reps in
      let on_the_list_now = reps#clone in
      let ancestors = ref [] in
      let rec add_ancestors reps =
	match reps with
	| rep :: rest_reps ->
	    let prev_reps = self#get_value !rep_rev_edges rep in
	    let prevs =
              List.filter (fun r ->
                  not (on_the_list#has r)) prev_reps#toList in
	    on_the_list#addList prevs ;
	    on_the_list_now#remove rep ;
	    on_the_list_now#addList prevs ;
	    let nodes = (self#get_value !rep_to_nodes rep)#toList in
	    ancestors :=
              List.rev_append (List.map self#get_proc nodes) !ancestors ;
	    add_ancestors (List.rev_append prevs rest_reps)
	| _ -> () in
      add_ancestors reps#toList ;
      !ancestors

    method is_recursive proc_name =
      recursive_methods#has proc_name

    method private pr__debug_array3_int a =
      pr__debug [STR "[|"; NL] ;
      let count = ref (-1) in
      (try
	for i = 0 to !last_index do
	  for j = 0 to pred array_size do
	    for k = 0 to pred array_size do
	      incr count ;
	      pr__debug [INT !count ; STR " -> "; INT a.(i).(j).(k); NL] ;
	      if !count = !last_index then raise Exit
	    done
	  done
	done ;
      with _ -> () ) ;
      pr__debug [STR "|]"; NL]

    method private pr__debug_array3_set a =
      pr__debug [STR "[|"; NL] ;
      let count = ref (-1) in
      (try
	for i = 0 to !last_index do
	  for j = 0 to pred array_size do
	    for k = 0 to pred array_size do
	      incr count ;
	      let set = a.(i).(j).(k) in
	      if not set#isEmpty then
                pr__debug [INT !count ; STR " -> "; set#toPretty; NL] ;
	      if !count = !last_index then raise Exit
	    done
	  done
	done
      with _ -> () ) ;
      pr__debug [STR "|]"; NL]

    method private pr__debug_array3 a =
      pr__debug [STR "[|"; NL] ;
      let count = ref (-1) in
      (try
	for i = 0 to !last_index do
	  for j = 0 to pred array_size do
	    for k = 0 to pred array_size do
	      incr count ;
	      pr__debug [INT !count ; STR " -> "; a.(i).(j).(k)#toPretty; NL] ;
	      if !count = !last_index then raise Exit
	    done
	  done
	done
      with _ -> () ) ;
      pr__debug [STR "|]"; NL]

    method pr__debug : unit =
      pr__debug [STR "call graph: "; NL; STR "index_to_proc: "; NL] ;
      self#pr__debug_array3 !procs ;
      pr__debug [STR "node_to_rep: "; NL] ;
      self#pr__debug_array3_int !node_to_rep ;
      pr__debug [STR "rep_to_nodes: "; NL] ;
      self#pr__debug_array3_set !rep_to_nodes ;
      pr__debug [STR "rep_edges: "; NL] ;
      self#pr__debug_array3_set !rep_edges ;
      pr__debug [STR "in_loop: "; NL; !in_loop#toPretty; NL];
      pr__debug [STR "recursive_methods: "; NL; recursive_methods#toPretty; NL] ;

    method toPretty =
      LBLOCK [STR "call graph: "; NL;
	      INDENT (5, LBLOCK [ STR "in_loop: "; NL;
                                  !in_loop#toPretty; NL;
				  STR "recursive_methods: "; NL;
                                  recursive_methods#toPretty; NL ])]

  end

module FieldInfoCollections = CHCollections.Make (
  struct
    type t = field_info_int
    let compare f1 f2 = compare f1#get_index f2#get_index
    let toPretty f = f#toPretty
  end)

class call_graph_manager_t all_procs not_analyzed edges =
  object
    val call_graph = new scc_graph_t all_procs not_analyzed edges

    val bottom_up_file = "codehawk/temp/bottom_up"
    val top_down_file = "codehawk/temp/top_down"
    val in_loop_file = "codehawk/temp/in_loop"

    val bottom_up_list = ref []
    val top_down_list = ref []
    val in_loop_list = ref (new SymbolCollections.set_t)

    initializer

      let (list, in_loop) = call_graph#initialize in

      if !no_temp_files then
	begin
	  bottom_up_list := list ;
	  top_down_list := List.rev list ;
	  in_loop_list := in_loop
	end
      else
	begin
	  let bottom_up_channel = open_out bottom_up_file in
	  Marshal.to_channel bottom_up_channel list [Marshal.Closures] ;
	  close_out bottom_up_channel ;

	  let top_down_channel = open_out top_down_file in
	  Marshal.to_channel top_down_channel (List.rev list) [Marshal.Closures] ;
	  close_out top_down_channel ;

	  let in_loop_channel = open_out in_loop_file in
	  Marshal.to_channel in_loop_channel in_loop [Marshal.Closures] ;
	  close_out in_loop_channel ;
	end ;

      call_graph#find_methods_that_access_static_fields ;
      call_graph#clean_up

    method get_top_down_list =
      if !no_temp_files then (!top_down_list, !in_loop_list)
      else
	begin
	  let top_down_channel = open_in top_down_file in
	  let top_down_list:symbol_t list =
            Marshal.from_channel top_down_channel in
	  close_in top_down_channel ;
	  let in_loop_channel = open_in in_loop_file in
	  let in_loop:SymbolCollections.set_t =
            Marshal.from_channel in_loop_channel in
	  close_in in_loop_channel ;
	  (top_down_list, in_loop)
	end

    method get_bottom_up_list =
      if !no_temp_files then (!bottom_up_list, !in_loop_list)
      else
	begin
	  let bottom_up_channel = open_in bottom_up_file in
	  let bottom_up_list:symbol_t list =
            Marshal.from_channel bottom_up_channel in
	  close_in bottom_up_channel ;
	  let in_loop_channel = open_in in_loop_file in
	  let in_loop:SymbolCollections.set_t =
            Marshal.from_channel in_loop_channel in
	  close_in in_loop_channel ;
	  (bottom_up_list, in_loop)
	end

   (* returns a list of all the methods that are called from
    * one of the proc_names or recursively from one of the
    *  methods thus found *)
    method get_descendants proc_names =
      call_graph#get_descendants proc_names

    method get_unsynchronized_descendants proc_names =
      call_graph#get_unsynchronized_descendants proc_names

    method get_ancestors proc_name =
      call_graph#get_ancestors proc_name

    (* checks that the proc and recursively, all the methods
     * it calls do not write a static field *)
    method does_not_access_static_fields proc_name =
      not (call_graph#accesses_static_field proc_name)

    method is_recursive proc_name =
      call_graph#is_recursive proc_name

    method graph_to_pretty =
      call_graph#toPretty

    method pr__debug =
      call_graph#pr__debug

    method toPretty =
      LBLOCK [STR "Call Graph:"; NL;
		 INDENT (5, LBLOCK [call_graph#toPretty; NL])]
  end

let set_no_temp_files () =
  no_temp_files := true
