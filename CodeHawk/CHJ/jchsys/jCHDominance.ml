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

(* Mostly from Ron Cytron *)

(* chlib *)
open CHLanguage
open CHPretty
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchsys *)
open JCHGlobals

module H = Hashtbl


(* Finds the dominator graph and the dominance frontier *)
class dominance_info_t (cfg: cfg_int) =
  object (self: _)
    val nr_states = ref 0
    method get_nr_states = !nr_states

    (* The indices of the reachable states in all the arrays used *)
    val state_to_index =
      let nr_states = List.length cfg#getStates in
      (* entry state -> 0, the others get an index in reachable order *)
      H.create nr_states

    val index_to_state = ref (Array.make 1 state_name_sym)

    method get_state (st_index:int) = !index_to_state.(st_index)

    method private set_index (state_name:symbol_t) (index:int) =
      H.add state_to_index state_name#getIndex index

    (* Finds the index of a state name if it is guaranteed to be a key *)
    method get_index (state_name:symbol_t) =
      try
	H.find state_to_index state_name#getIndex
      with
	_ -> !nr_states;  (* unreachable method_exit;  *)


    method is_reachable (state_name:symbol_t) =
      H.mem state_to_index state_name#getIndex

    (* dominator_array.(i).(j) = 1 if state i is dominated by state j *)
    (* That is, any path that reaches i has to go through j *)
    val dominator_array = ref (Array.make_matrix 1 1 1)

    (* The first state is dominated by the second or it is unreachable *)
    method is_dominated_or_is_unreachable (w_state:symbol_t) (r_state:symbol_t) =
      let w_index = self#get_index w_state in
      let r_index = self#get_index r_state in
      w_index <> r_index &&
      (!dominator_array).(w_index).(r_index) == 1

    (* state_index -> set of states that it immediately dominates *)
    val dominator_tree = ref (Array.make 1 (new SymbolCollections.set_t))
    method get_immediate_dominated_children (state:symbol_t) =
      (!dominator_tree).(self#get_index state)

    val dominance_frontier = ref (Array.make 1 (new SymbolCollections.set_t))
    method get_dom_frontier (st_index:int) =
      !dominance_frontier.(st_index)

    val idominated = ref (Array.make 1 1)
    val rev_dominator_array = ref (Array.make_matrix 1 1 1)
    val rev_idominated = ref (Array.make 1 1)

    val all_states = ref ([]: symbol_t list)     (* states in reachable order *)
    val mutable states = ([]: symbol_t list)     (* states without entry *)
    val cfg = cfg

    method private getOutEdges (state:state_int) =
      let succs = state#getOutgoingEdges in
      List.filter (fun s -> s#getBaseName <> "exceptional-exit") succs

    method private getInEdges (state:state_int) =
      let preds = state#getIncomingEdges in
      List.filter (fun s -> s#getBaseName <> "exceptional-exit") preds

    (* order states form entry to exit; unreachable states are not listed *)
    initializer
      let visited = new SymbolCollections.set_t in
      let rec traverse s acc =
        let sname = s#getLabel in
        if visited#has sname then
	  acc
	else
	  let _ = visited#add sname in
	  let acc' = sname :: acc in
	  List.fold_left
	    (fun a s -> traverse (cfg#getState s) a)
	    acc'
	    (self#getOutEdges s) in
      let reachable = traverse cfg#getEntry [] in
      let _ = all_states := List.rev reachable in
      let setInd (index: int) state =
        self#set_index state index;
	index + 1 in
      nr_states := List.fold_left setInd 0 !all_states;
      index_to_state := Array.make !nr_states (new symbol_t "");
      let rec addEntry ls i =
        match ls with
        | s :: rest_ls ->
          !index_to_state.(i) <- s;
          addEntry rest_ls (i+1)
        | [] -> () in
      let _ = addEntry !all_states 0 in
      states <- List.tl !all_states


    method private inters a b =
      for i = 0 to pred !nr_states do
	a.(i) <- a.(i) * b.(i)
      done

    method private union a b =
      for i = 0 to pred !nr_states do
	if a.(i) = 0 && b.(i) = 0 then
	  a.(i) <- 0
	else
	  a.(i) <- 1
      done

    method private diff a b =
      for i = 0 to pred !nr_states do
	if a.(i) = 1 && b.(i) = 1 then
	  a.(i) <- 0
	else
	  ()
      done

    method private equal nr a b =
      if nr = -1 then
	true
      else if a.(nr) = b.(nr) then
	self#equal (nr-1) a b
      else
	false

    method private makeStateSet a =
      let set = new SymbolCollections.set_t in
      for i = 0 to pred !nr_states do
        if a.(i) = 1 then
          set#add !index_to_state.(i)
        else
          ()
      done;
      set

    method private makeStateArray a =
      let array = Array.make !nr_states (new SymbolCollections.set_t) in
      for i = 0 to pred !nr_states do
	array.(i) <- self#makeStateSet a.(i)
      done;
      array

   (* Finds the dominators *)
    method private find_dominators =
     (* initially every state dominates all the others except for the entry state *)
      let dom_array = Array.make_matrix !nr_states !nr_states 1 in
      let _ =
	for j = 1 to pred !nr_states do
	  dom_array.(0).(j) <- 0
	done in
      let changed = ref true in
      let find_dom_set_of state_name =
	let state = cfg#getState state_name in
	let preds = self#getInEdges state in
	let new_dom = Array.make !nr_states 1 in
	let intersect_dom (pred: symbol_t) =
	  if self#is_reachable pred then
            let domi = dom_array.(self#get_index pred) in
	    self#inters new_dom domi
          else
            () in (* predecessors might not be reachable *)
	let _ = List.iter intersect_dom preds in
	let statei = self#get_index state_name in
	let _ = new_dom.(statei) <- 1 in
	let old_dom = dom_array.(statei) in
	if self#equal (pred !nr_states) old_dom new_dom then
	  ()
	else
	  begin
	    dom_array.(statei) <- new_dom;
	    changed := true
	  end in
      while !changed do
	changed := false;
	List.iter find_dom_set_of states
      done;
      dom_array

    (* Makes a strict version of the matrix *)
    method private makeStrict m =
      let sm = Array.make_matrix !nr_states !nr_states 0 in
      for i = 0 to pred !nr_states do
	sm.(i) <- Array.copy m.(i);
	sm.(i).(i) <- 0
      done;
      sm


    method private mk_dom_tree sm =
      let uptree = Array.make !nr_states 0 in
      let downtree = Array.make_matrix !nr_states !nr_states 0 in
      let trimTree i =
	let doms = sm.(i) in
	let new_dom = Array.copy doms in
	let remove k =
	  if doms.(k) = 1 then
	    self#diff new_dom sm.(k)
	  else
	    () in
	let _ =
	  for i = 0 to pred !nr_states do
	    remove i
	  done in
	let im_dom =
	  let rec findImmUp k =
	    if k < 0 then
	      0  (* 0 is the entry state *)
	    else if new_dom.(k) = 1 then
	      k
	    else
	      findImmUp (pred k) in
	  findImmUp (pred !nr_states) in
	uptree.(i) <- im_dom;
	downtree.(im_dom).(i) <- 1 in
      for i = 1 to pred !nr_states do
	trimTree i
      done;
      (uptree , downtree)

   (* Find the dominance frontier *)
    method private find_dom_frontier idominated_array idominates_array =
      let find_df_loc state statei =
	let doms = idominates_array.(statei) in
	let succs = self#getOutEdges (cfg#getState state) in
	let df_loc = Array.make !nr_states 0 in
	let add_if_does_not_dominate succ =
	  let succi = self#get_index succ in
	  if doms.(succi) = 0 then
	    df_loc.(succi) <- 1
	  else
	    () in
	List.iter add_if_does_not_dominate succs;
	df_loc in
      let df_up = Array.make_matrix !nr_states !nr_states 0 in
      let dom_frontier = new SymbolCollections.table_t in
      let _ =
        dominance_frontier :=
          Array.make !nr_states (new SymbolCollections.set_t) in
      let find_df (state:symbol_t) =
	let statei = self#get_index state in
	let df =
	  let res = find_df_loc state statei in
	  let add_df_up k =
	    self#union res df_up.(k) in
	  let doms = idominates_array.(statei) in
	  for i = 0 to !nr_states - 1 do
	    if doms.(i) = 1 then
	      add_df_up i
	    else
	      ()
	  done;
	  res in
	let dfup = Array.copy df in
	let immed_dom = idominated_array.(statei) in
	let immed_doms = idominates_array.(immed_dom) in
	for i = 0 to !nr_states - 1 do
	  if immed_doms.(i) = 1 then
	    dfup.(i) <- 0
	  else ()
	done;
	df_up.(statei) <- dfup;
	dom_frontier#set state (self#makeStateSet df);
	!dominance_frontier.(statei) <- (self#makeStateSet df);
      in
      List.iter find_df (List.rev states);
      ()

    method find_dominator_tree =
      let _ = dominator_array := self#find_dominators in
      let sdominator_array = self#makeStrict !dominator_array in
      let (uptree, downtree) = self#mk_dom_tree sdominator_array in
      dominator_tree := self#makeStateArray downtree;
      idominated := uptree;
      (uptree, downtree)

    method get_dominance_frontier =
      let (uptree, downtree) = self#find_dominator_tree in
      self#find_dom_frontier uptree downtree

    method find_common_dominator states =
      let reachable_states = List.filter self#is_reachable states in
      if List.length reachable_states < 2 then
	reachable_states
      else
	let st_inds =
          List.sort (fun n m -> n - m )
                    (List.rev_map self#get_index reachable_states) in
	let st_ind = List.hd st_inds in
	let rec find_dom candidate sinds =
	  let is_not_dominated i =
	    i != candidate && !dominator_array.(i).(candidate) == 0 in
	  let not_dominated = List.filter is_not_dominated sinds in
	  if not_dominated = [] then
	    [self#get_state candidate]
	  else
	    let new_candidate = !idominated.(candidate) in
	    find_dom new_candidate not_dominated  in
	find_dom st_ind (List.tl st_inds)

    method toPretty =
      let pp_e state_name_index index pp =
        (LBLOCK [INT state_name_index; STR " -> "; INT index; NL]) :: pp in
      let pp_ht = LBLOCK (H.fold pp_e state_to_index []) in

      LBLOCK [
          STR "index_to_state: "; NL; pp_array !index_to_state; NL;
	  STR "state_to_index: "; NL; pp_ht; NL;
          STR "dominator_array: "; NL; pp_matrix_int !dominator_array; NL;
	  STR "idominated:   "; pp_array_int !idominated; NL]

  end


let find_dominance_frontier _proc_name cfg =
  let dom = new dominance_info_t cfg in
  dom#get_dominance_frontier;
  dom
