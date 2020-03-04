(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(*  chlib *)
open CHIntervals
open CHLanguage
open CHNumerical   
open CHPretty
open CHUtils
   
(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes

(* jchpre *)
open JCHPreAPI
   

class num_info_t = 
  object (self: 'a) 
    val excluded : numerical_t list = []
    val divisions : (variable_t * variable_t) list = [] 
    val empty_collection = false (* it is an empty collection *)
    val changed_sym_param = false (* it could have been changed *)

    (* fields that, at some point, had an equal value with the 
     * value of this variable
     * range of values for the var included in the range of value for each field
     * if the variable is a length of a then these are the fields for a *)
    val fields : JCHPreAPI.field_info_int list = []

    method excluded = excluded
    method divisions = divisions 
    method is_empty_collection = empty_collection 
    method is_changed_sym_param = changed_sym_param
    method fields = fields

    method is_empty = 
      excluded = []
      && divisions = []
      && not empty_collection
      && not changed_sym_param
      && fields = []

    method has_only_excluded =
      divisions = []
      && not empty_collection
      && not changed_sym_param
      && fields = []

    method remove_vars (vars: variable_t list) = 
      let is_not_in_vars var = 
	let index = var#getIndex in
	List.for_all (fun v -> v#getIndex <> index) vars in
      {< divisions =
           List.filter (fun (d,q) ->
               is_not_in_vars d && is_not_in_vars q) divisions >}

    method remove_var (var:variable_t) (interval:interval_t) = 
      {< divisions =
           List.filter (fun (d,q) ->
               not (d#equal var || q#equal var)) divisions >}

    method change_vars (vars: variable_t list) = 
      let is_in_vars var = 
	let index = var#getIndex in
	List.exists (fun v -> v#getIndex = index) vars in
      {< divisions =
           List.filter (fun (d,q) -> is_in_vars d && is_in_vars q) divisions >}

    method remove_excluded_val (vl:numerical_t) = 
      let new_excluded = List.filter (fun vl' -> not (vl'#equal vl)) excluded in
      {< excluded = new_excluded >}
	
    method remove_excluded = {< excluded = [] >}
	
    method add_excluded_val (vl:numerical_t) = 
      if List.exists (fun vl' -> vl'#equal vl) excluded then
        {< >} 
      else
        {< excluded = vl :: excluded >} 

    method add_excluded_vals (vls:numerical_t list) = 
      let vls' =
        List.filter (fun vl ->
            not (List.exists (fun vl' -> vl'#equal vl) excluded)) vls in 
      {< excluded = excluded @ vls' >} 

    method set_excluded_vals (vls:numerical_t list) = 
      {< excluded = vls >}

    method set_divisions (divisions:(variable_t * variable_t) list) = 
      {< divisions = divisions >}

    method set_empty_collection (b:bool) = 
      {< empty_collection = b >}

    method set_changed_sym_param (b:bool) = 
      {< changed_sym_param = b >}

    method add_field (fInfo:field_info_int) =
      {< fields = fInfo :: fields >}

    method remove_field (fInfo:field_info_int) =
      {< fields = List.filter (fun f -> f#compare fInfo != 0) fields >}

    method set_fields (fInfos:field_info_int list) =
      {< fields = fInfos >}

    method meet (a: 'a) = 
      let equal_vpair (v1, v2) (w1, w2) = 
	v1#getIndex = w1#getIndex && v2#getIndex = w2#getIndex in
      let aexcluded =
        List.filter (fun vl -> not (List.exists vl#equal excluded)) a#excluded in
      let adivisions =
        List.filter (fun (v1,v2) ->
            not (List.exists (equal_vpair (v1,v2)) divisions)) a#divisions in
      let afields =
        List.filter (fun f1 ->
            List.exists (fun f2 -> f1#compare f2 != 0) fields) a#fields in

      {< excluded = excluded @ aexcluded ;
	 divisions = divisions @ adivisions ;
	 empty_collection = empty_collection || a#is_empty_collection ;
	 changed_sym_param = changed_sym_param || a#is_changed_sym_param ;
	 fields = List.rev_append fields afields 
      >}
      
    method join (a: 'a) = 
      let equal_vpair (v1, v2) (w1, w2) = 
	v1#getIndex = w1#getIndex && v2#getIndex = w2#getIndex in
      let new_divisions =
        List.filter (fun (v1,v2) ->
            List.exists (equal_vpair (v1,v2)) divisions) a#divisions in

      {< excluded = List.filter (fun vl -> List.exists vl#equal excluded) a#excluded ;
	 divisions = new_divisions ;
	 empty_collection = empty_collection && a#is_empty_collection ;
	 changed_sym_param = changed_sym_param || a#is_changed_sym_param ;
	 fields =
           List.filter (fun f1 ->
               List.exists (fun f2 -> f1#compare f2 = 0) fields) a#fields 
      >}

    method replace_vars (map_v:(variable_t * variable_t) list) = 
      let changed_divisions =
        List.map (fun (d, q) -> (List.assoc d map_v, List.assoc q map_v)) divisions in
      {< divisions = changed_divisions >}

    method toPretty = 
      let excluded_pp = 
        if excluded = [] then
          STR "" 
	else
          LBLOCK [STR "excluded values: "; pp_list excluded; NL] in
      let divisions_pp = 
	if divisions = [] then
          STR ""
	else 
	  let pp_one (dividend, quotient) = 
	    LBLOCK [STR "(dividend, quotient) = (";
                    dividend#toPretty; STR ", "; quotient#toPretty; STR ")"; NL] in
	  LBLOCK [STR "divisor info: ";
                  INDENT (5, pretty_print_list divisions pp_one "" "" ""); NL] in
      let empty_collection_pp = 
	if empty_collection then
          LBLOCK [STR "empty collection"; NL]
        else
          STR "" in
      let changed_sym_param_pp = 
	if changed_sym_param then
          LBLOCK [STR "changed sym param"; NL]
        else
          STR "" in
      let fields_pp =
	if fields = [] then
          STR ""
	else
          LBLOCK [STR "fields: "; pp_list fields; NL] in
      LBLOCK [excluded_pp; divisions_pp; empty_collection_pp;
              changed_sym_param_pp; fields_pp]

    method to_pretty_no_excluded = 
      let divisions_pp = 
	if divisions = [] then
          STR ""
	else 
	  let pp_one (dividend, quotient) = 
	    LBLOCK [STR "(dividend, quotient) = ("; dividend#toPretty; STR ", ";
                    quotient#toPretty; STR ")"; NL] in
	  LBLOCK [STR "divisor info: ";
                  INDENT (5, pretty_print_list divisions pp_one "" "" ""); NL] in
      let empty_collection_pp = 
	if empty_collection then
          LBLOCK [STR "empty collection"; NL]
        else
          STR "" in
      let changed_sym_param_pp = 
	if changed_sym_param then
          LBLOCK [STR "changed sym param"; NL]
        else
          STR "" in
      let fields_pp =
	if fields = [] then
          STR ""
	else
          LBLOCK [STR "fields: "; pp_list fields; NL] in
      LBLOCK [divisions_pp; empty_collection_pp; changed_sym_param_pp;
              fields_pp]
	
  end

class numeric_info_t = 
object (self: 'a)
     
    val info_map : (int * num_info_t) list = [] 

    method initialize
             (d2div2quot: variable_t VariableCollections.table_t VariableCollections.table_t) = 
      let info_map = ref [] in
      let add_divisions divisor table = 
	let divisions = ref [] in
	let add dividend quotient = 
	  divisions := (dividend, quotient) :: !divisions in
	table#iter add ;
	let num_info = (new num_info_t)#set_divisions !divisions in
	info_map := (divisor#getIndex, num_info) :: !info_map in
      begin
        d2div2quot#iter add_divisions ;
        {< info_map = !info_map >}
      end
      
    method add_div_info
             (d2div2quot: variable_t VariableCollections.table_t VariableCollections.table_t) = 
      let imap = ref info_map in
      let add_divisions divisor table = 
	let divisions = ref [] in
	let add dividend quotient = 
	  divisions := (dividend, quotient) :: !divisions in
	table#iter add ;
	let num_info = (new num_info_t)#set_divisions !divisions in

	imap := (divisor#getIndex, num_info) :: !imap in
      begin
        d2div2quot#iter add_divisions ;
        {< info_map = !imap >}
      end

    method clone = {< >} 

    method get_info_map = info_map

    method get_num_info (var:variable_t) = 
      try
        List.assoc var#getIndex info_map
      with
      | _ -> new num_info_t 

    method private get_num_info_opt (var:variable_t) = 
      try
        Some (List.assoc var#getIndex info_map)
      with
      | _ -> None 

    method private get_num_info_opt_not_excluded (var:variable_t) = 
      try
	let num_info = List.assoc var#getIndex info_map in
	if num_info#has_only_excluded then
          None
	else
          Some num_info
      with
      | _ -> None 

    method get_num_info_ind (ind:int) = 
      try
        Some (List.assoc ind info_map)
      with
      | _ -> None 
      
    method set_num_info (var:variable_t) (num_info:num_info_t) = 
      let index = var#getIndex in
      {< info_map = (index, num_info) :: (List.remove_assoc index info_map) >}

    method replace_vars
             (map_v: (variable_t * variable_t) list)
             (map: (int * variable_t) list) = 
      let new_info_map = ref [] in
      let add_info (old_index, info) = 
	let new_var = List.assoc old_index map in
	let new_info = info#replace_vars map_v in
	new_info_map := (new_var#getIndex, new_info) :: !new_info_map in
      begin
        List.iter add_info info_map ;
        {< info_map = !new_info_map >}
      end
      
    method remove_var (var:variable_t) (interval:interval_t) = 
      let new_info_map = List.remove_assoc var#getIndex info_map in
      let rec remove_vs assocs = 
	match assocs with 
	| (ind, num_info) :: rest_assocs -> 
	    let new_num_info = num_info#remove_var var interval in
	    if new_num_info#is_empty then
              remove_vs rest_assocs 
	    else
              (ind, new_num_info) :: (remove_vs rest_assocs)
	| _ -> [] in
      {< info_map = remove_vs new_info_map >}
      

    method remove_vars (vars:variable_t list) = 
      let remove_var map var = 
	List.remove_assoc var#getIndex map in 
      let new_info_map = List.fold_left remove_var info_map vars in
      let rec remove_vs assocs = 
	match assocs with 
	| (ind, num_info) :: rest_assocs -> 
	    let new_num_info = num_info#remove_vars vars in
	    if new_num_info#is_empty then
              remove_vs rest_assocs 
	    else
              (ind, new_num_info) :: (remove_vs rest_assocs)
	| _ -> [] in
      {< info_map = remove_vs new_info_map >}

    method change_vars (vars:variable_t list) = 
      let check_assoc new_map (ind, num_info) = 
	if (List.exists (fun v -> v#getIndex = ind) vars) then 
	  (ind, num_info) :: new_map
	else
          new_map in
      let new_info_map = List.fold_left check_assoc [] info_map in
      let rec restrict_to_vs assocs = 
	match assocs with 
	| (ind, num_info) :: rest_assocs -> 
	    let new_num_info = num_info#change_vars vars in
	    if new_num_info#is_empty then
              restrict_to_vs rest_assocs 
	    else
              (ind, new_num_info) :: (restrict_to_vs rest_assocs)
	| _ -> [] in
      {< info_map = restrict_to_vs new_info_map >}

    method get_excluded_vals (var:variable_t) = 
      match self#get_num_info_opt var with 
      |	Some num_info -> num_info#excluded
      |	None -> []

    method get_excluded_vals_ind (var_ind:int) = 
      match self#get_num_info_ind var_ind with 
      |	Some num_info -> num_info#excluded 
      |	None -> [] 

    method remove_excluded_val (var:variable_t) (vl:numerical_t) = 
      match self#get_num_info_opt var with 
      |	Some num_info -> 
	  let new_num_info = num_info#remove_excluded_val vl in
	  if new_num_info#is_empty then
            self#remove_vars [var]
	  else
            self#set_num_info var new_num_info
      |	None -> {< >} 

    method remove_all_excluded (var:variable_t) = 
      match self#get_num_info_opt var with 
      |	Some num_info -> 
	  let new_num_info = num_info#remove_excluded in
	  if new_num_info#is_empty then
            self#remove_vars [var]
	  else
            self#set_num_info var new_num_info
      |	None -> {< >}

    method add_excluded_val (var:variable_t) (vl:numerical_t) = 
      let num_info = self#get_num_info var in
      let new_num_info = num_info#add_excluded_val vl in
      self#set_num_info var new_num_info 

    method add_excluded_vals (var:variable_t) (vls:numerical_t list) = 
      let num_info = self#get_num_info var in
      let new_num_info = num_info#add_excluded_vals vls in
      if new_num_info#is_empty then 
	{< info_map = List.remove_assoc var#getIndex info_map >}
      else
        self#set_num_info var new_num_info 

    method set_excluded_vals (var:variable_t) (vls:numerical_t list) = 
      let num_info = self#get_num_info var in
      let new_num_info = num_info#set_excluded_vals vls in
      if new_num_info#is_empty then 
	{< info_map = List.remove_assoc var#getIndex info_map >}
      else
        self#set_num_info var new_num_info 

    method add_empty_collection (var:variable_t) = 
      let num_info = self#get_num_info var in
      let new_num_info = num_info#set_empty_collection true in
      self#set_num_info var new_num_info 

    method is_empty_collection (var:variable_t) = 
      match self#get_num_info_opt var with 
      |	Some num_info -> num_info#is_empty_collection
      |	None -> false

    method remove_empty_collection (var:variable_t) = 
      match self#get_num_info_opt var with 
      |	Some num_info -> 
	  let new_num_info = num_info#set_empty_collection false in
	  if new_num_info#is_empty then 
	    {< info_map = List.remove_assoc var#getIndex info_map >}
	  else
            self#set_num_info var new_num_info
      |	None -> {< >} 

    method private add_changed_sym_param (a: 'a) (var: variable_t) = 
      let num_info = a#get_num_info var in
      let new_num_info = num_info#set_changed_sym_param true in
      a#set_num_info var new_num_info 

    method add_changed_sym_params (vars:variable_t list) = 
      List.fold_left self#add_changed_sym_param self vars

    method is_changed_sym_param (var:variable_t) = 
      match self#get_num_info_opt var with 
      |	Some num_info -> num_info#is_changed_sym_param
      |	None -> false

    method get_divisions (var:variable_t) = 
      match self#get_num_info_opt var with 
      |	Some num_info -> num_info#divisions
      |	None -> [] 

    method add_field (var:variable_t) (fInfo:field_info_int) =
      let num_info = self#get_num_info var in
      let new_num_info = num_info#add_field fInfo in
      if new_num_info#is_empty then 
	{< info_map = List.remove_assoc var#getIndex info_map >}
      else
        self#set_num_info var new_num_info 

    method set_fields (var:variable_t) (fInfos:field_info_int list) =
      let num_info = self#get_num_info var in
      let new_num_info = num_info#set_fields fInfos in
      if new_num_info#is_empty then 
	{< info_map = List.remove_assoc var#getIndex info_map >}
      else
        self#set_num_info var new_num_info 

    method remove_field (var:variable_t) (fInfo:field_info_int) =
      let num_info = self#get_num_info var in
      let new_num_info = num_info#remove_field fInfo in
      if new_num_info#is_empty then 
	{< info_map = List.remove_assoc var#getIndex info_map >}
      else
        self#set_num_info var new_num_info 
      
    method has_fields (var:variable_t) =
      let num_info = self#get_num_info var in
      num_info#fields != [] 

    method get_fields (var:variable_t) =
      (self#get_num_info var)#fields 

    method set_same_info (var1:variable_t) (var2:variable_t) = 
      match self#get_num_info_opt var2 with 
      |	Some num_info -> self#set_num_info var1 num_info
      |	None -> {< >}

    method meet (a: 'a) = 
      let new_info_map = ref [] in
      let inds = IntCollections.set_of_list (List.map fst info_map) in
      inds#addList (List.map fst a#get_info_map) ;
      
      let add_info ind = 
	match (self#get_num_info_ind ind, a#get_num_info_ind ind) with 
	| (Some info, Some ainfo) -> 
	    let meet_info = info#meet ainfo in
	    if not meet_info#is_empty then 
	      new_info_map := (ind, meet_info) :: !new_info_map
	| (Some info, _) -> new_info_map := (ind, info) :: !new_info_map
	| (_, Some ainfo) -> new_info_map := (ind, ainfo) :: !new_info_map
	| _ -> () in
      
      inds#iter add_info ;
      {< info_map = !new_info_map >}

    method join (a: 'a) = 
      let new_info_map = ref [] in
      let inds = IntCollections.set_of_list (List.map fst info_map) in
      inds#addList (List.map fst a#get_info_map) ;
      
      let add_info ind = 
	match (self#get_num_info_ind ind, a#get_num_info_ind ind) with 
	| (Some info, Some ainfo) -> 
	    let join_info = info#join ainfo in
	    if not join_info#is_empty then 
	      new_info_map := (ind, join_info) :: !new_info_map
	| _ -> () in
      
      inds#iter add_info ;
      {< info_map = !new_info_map >}

    method remove_out_of_interval_excluded
             (var:variable_t) (interval:interval_t) = 
      match self#get_num_info_opt var with 
      |	Some info -> 
	 if interval#isBottom then
           self#remove_vars [var]
	  else 
	    let new_excluded = List.filter interval#contains info#excluded in
	    let new_info = info#set_excluded_vals new_excluded in
	    if new_info#is_empty then 
	      {< info_map = List.remove_assoc var#getIndex info_map >}
	    else
              self#set_num_info var new_info
      |	None -> {< >} 

    method to_pretty (vars:variable_t list) = 
      let pp_info var =
	match self#get_num_info_opt var with 
	| Some num_info -> 
	    LBLOCK [var#toPretty; STR " -> "; INDENT (5, num_info#toPretty); NL]
	| _ -> STR "" in
      LBLOCK (List.map pp_info vars)

    method to_pretty_no_excluded (vars:variable_t list) =
      let pp_info var =
	match self#get_num_info_opt var with 
	| Some num_info ->
	   if num_info#has_only_excluded then
             STR ""
	   else
             LBLOCK [var#toPretty; STR " -> ";
                     INDENT (5, num_info#to_pretty_no_excluded); NL]
	| _ -> STR "" in
      LBLOCK (List.map pp_info vars)
      
    
    method toPretty = 
      let pp = ref [] in
      let pp_info (ind, info) =
	pp := LBLOCK [INT ind; STR " -> ";
                      INDENT (5, info#toPretty); NL] :: !pp in
      begin
        List.iter pp_info info_map ;
        LBLOCK (List.rev !pp)
      end

end
