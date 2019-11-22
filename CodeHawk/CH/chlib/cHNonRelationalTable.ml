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
open CHConstants   
open CHDomain   
open CHLanguage
open CHNonRelationalDomainValues   
open CHNumerical
open CHPretty
open CHSymbolicSets   
open CHUtils


class table_index_t (l: (string * symbol_t) list) =
object (self: 'a)
  
  val assoc_list = l
                 
  method getAssocList = assoc_list
                      
  method compare (i: 'a) =
    let l2 = i#getAssocList in
    let rec loop l = 
      try
	match l with
	| [] -> 0
	| (k, s) :: l' ->
	   let s' = List.assoc k l2 in
	   let c = s#compare s' in
	   if s = s' then
	     loop l'
	   else
	     c
      with Found -> raise (CHFailure (STR "Non-relational table: error #1"))
    in
    loop assoc_list 
    
  method toPretty = 
    pretty_print_list assoc_list (fun (k, s) -> LBLOCK [STR k; STR ":"; s#toPretty]) "|" "|" "|"
    
  method matching (sieve: (string * non_relational_domain_value_t) list) =
    List.fold_left (fun a (k, s) ->
        a &&
	  try
	    let v = List.assoc k sieve in
	    not((v#meet (mkSymbolicSetValue (new symbolic_set_t [s])))#isBottom)
	  with Not_found -> true) true assoc_list
    
end
  
class table_row_t (r: (string * non_relational_domain_value_t) list) =
object (self: 'a)
     
  val row = r
          
  method getRow = row
                
  method toPretty =
    pretty_print_list row (fun (k, v) -> LBLOCK [STR k; STR ":"; v#toPretty]) "|" "|" "|"
    
  method leq (r': 'a) =
    let row' = r'#getRow in
    List.fold_left (fun a (s, v) ->
	a &&
	  try
	    let v' = List.assoc s row' in
	    v#leq v'
	  with Not_found -> raise (CHFailure (STR "Non-relational table: error #9"))
      ) true row
    
  method matching (sieve: (string * non_relational_domain_value_t) list) =
    List.fold_left (fun a (k, v) ->
        a &&
	  try
	    let v' = List.assoc k sieve in
	    not((v#meet v')#isBottom)
	  with Not_found -> true) true row
    
  method addTo
           (key: string)
           (sym: symbol_t)
           (acc: non_relational_domain_value_t VariableCollections.table_t)
           (selection: (string * variable_t) list) =
    let row' = (key, mkSymbolicSetValue (new symbolic_set_t [sym])) :: row in
    List.iter (fun (s, v) ->
	try
	  let value = List.assoc s row' in
	  match acc#get v with
	  | None -> acc#set v value
	  | Some value' -> acc#set v (value#join value')
	with Not_found -> raise (CHFailure (STR "Non-relational table: error #2"))
      ) selection
    
  method join (a: 'a) =
    {< row =
         List.map (fun (s, v) ->
	     let row' = a#getRow in
	     try
	       let v' = List.assoc s row' in
	       (s, v#join v')
	     with
             | Not_found ->
                raise (CHFailure (STR "Non-relational table: error #7"))) row >}
    
  method widening (a: 'a) =
    {< row =
         List.map (fun (s, v) ->
	     let row' = a#getRow in
	     try
	       let v' = List.assoc s row' in
	       (s, v#widening v')
	     with
             | Not_found ->
                raise (CHFailure (STR "Non-relational table: error #8"))) row >}
    
end
  
module IndexCollections =
  CHCollections.Make
    (struct
      type t = table_index_t
      let compare s1 s2 = s1#compare s2
      let toPretty s = s#toPretty
    end)
  
class secondary_table_t (ks: string list) (oths: string list) =
object (self: 'a)
     
  val keys = ks
           
  val others = oths
             
  val table: table_row_t IndexCollections.table_t = new IndexCollections.table_t
                                                  
  method getTable = table
                  
  method getRows k acc =
    table#fold (fun a _ r -> (k :: r#getRow) :: a) acc
    
  method leq (t': 'a) =
    let table' = t'#getTable in
    table#fold (fun a i row ->
	a &&
	  match table'#get i with
	  | None -> false
	  | Some row' -> row#leq row') true
    
  method join (t': 'a) =
    let table' = t'#getTable in
    let keys = table#setOfKeys#union table'#setOfKeys in
    let table'' = new IndexCollections.table_t in
    let _ = keys#iter (fun i ->
		match (table#get i, table'#get i) with
		| (None, None) -> ()
		| (Some row, None) 
		  | (None, Some row) -> table''#set i row
		| (Some row, Some row') -> table''#set i (row#join row'))
    in
    {< table = table'' >}
    
  method widening (t': 'a) =
    let table' = t'#getTable in
    let keys = table#setOfKeys#union table'#setOfKeys in
    let table'' = new IndexCollections.table_t in
    let _ = keys#iter (fun i ->
		match (table#get i, table'#get i) with
		| (None, None) -> ()
		| (Some row, None) 
		  | (None, Some row) -> table''#set i row
		| (Some row, Some row') -> table''#set i (row#widening row'))
    in
    {< table = table'' >}
    
  method select
           ~(key: string)
           ~(symbol: symbol_t)
           ~(selection: (string * variable_t) list)
           ~(sieve: (string * non_relational_domain_value_t) list) 
           (acc: non_relational_domain_value_t VariableCollections.table_t) =
    table#iter (fun index row ->
	if index#matching sieve && row#matching sieve then
	  row#addTo key symbol acc selection
	else
	  ())
    
  method delete ~(sieve: (string * non_relational_domain_value_t) list) =
    let table' = new IndexCollections.table_t in
    let _ =
      table#iter (fun index row ->
	  if index#matching sieve && row#matching sieve then
	    ()
	  else
	    table'#set index row)
    in
    {< table = table' >}
    
  method private insert'
                   index
                   todo
                   (args: (string * non_relational_domain_value_t) list)
                   (table': table_row_t IndexCollections.table_t) =
    match todo  with
    | [] ->
       let keys_part = List.map (fun (k, s) ->
                           (k, mkSymbolicSetValue (new symbolic_set_t [s]))) index in
       let others_part = List.filter (fun (n, _) -> List.mem n others) args in
       let row = new table_row_t (keys_part @ others_part) in
       let table_index = new table_index_t index in
       begin
	 match table'#get table_index with
	 | None ->
	    table'#set table_index row
	 | Some row' ->
	    table'#set table_index (row'#join row)
       end 
    | k :: l ->
       try
	 let v = List.assoc k args in
	 let set = v#toSymbolicSet in
	 if set#isTop then
	   raise (CHFailure (STR "Non-relational table: error #5"))
	 else
	   set#iter (fun s -> self#insert' ((k, s) :: index) l args table')
       with Not_found -> raise (CHFailure (STR "Non-relational table: error #6"))
	               
  method insert (args: (string * non_relational_domain_value_t) list) =
    let table' = table#clone in
    let key_set = new StringCollections.set_t in
    let _ = key_set#addList keys in
    let _ = self#insert' [] key_set#toList args table' in
    {< table = table' >}
    
  method toPretty = table#toPretty
                  
end
  
class non_relational_table_t (k: string) (s: nr_table_signature_t) =
object (self: 'a)
     
  val key: string = k
                  
  val keys = List.fold_left (fun a (k, (_, i)) ->
                 match i with SECONDARY_INDEX -> k :: a | _ -> a) [] s
           
  val others = List.fold_left (fun a (k, (_, i)) ->
                   match i with NO_INDEX -> k :: a | _ -> a) [] s
             
  val table: secondary_table_t SymbolCollections.table_t = new SymbolCollections.table_t
                                                         
  method getTable = table
                  
  method getRows =
    table#fold (fun a ksym t -> 
	let kset = mkSymbolicSetValue (new symbolic_set_t [ksym]) in
	t#getRows (key, kset) a) []
    
  method leq (t': 'a) =
    let table' = t'#getTable in
    table#fold (fun a s sec_t ->
	a &&
	  match table'#get s with
	  | None -> false
	  | Some sec_t' -> sec_t#leq sec_t') true
    
  method join (t': 'a) =
    let table' = t'#getTable in
    let keys = table#setOfKeys#union table'#setOfKeys in
    let table'' = new SymbolCollections.table_t in
    let _ = keys#iter (fun s ->
		match (table#get s, table'#get s) with
		| (None, None) -> ()
		| (Some t, None) 
		  | (None, Some t) -> table''#set s t
		| (Some t, Some t') -> table''#set s (t#join t'))
    in
    {< table = table'' >}
    
  method widening (t': 'a) =
    let table' = t'#getTable in
    let keys = table#setOfKeys#union table'#setOfKeys in
    let table'' = new SymbolCollections.table_t in
    let _ = keys#iter (fun s ->
		match (table#get s, table'#get s) with
		| (None, None) -> ()
		| (Some t, None) 
		  | (None, Some t) -> table''#set s t
		| (Some t, Some t') -> table''#set s (t#widening t'))
    in
    {< table = table'' >}
    
  method select
           ~(selection: (string * variable_t) list)
           ~(sieve: (string * non_relational_domain_value_t) list) =
    let acc = new VariableCollections.table_t in
    let _ = table#iter (fun s t -> 
		let ok = 
		  try
		    let v = List.assoc key sieve in
		    not((v#meet (mkSymbolicSetValue (new symbolic_set_t [s])))#isBottom)
		  with
                  | Not_found -> true
		in
		if not(ok) then
		  ()
		else
		  t#select ~key:key ~symbol:s ~selection:selection ~sieve:sieve acc)
    in
    List.map (fun (_, v) -> 
	(v, match acc#get v with
	    | None -> bottomNonRelationalDomainValue
	    | Some value -> value)
      ) selection
    
  method delete ~(sieve: (string * non_relational_domain_value_t) list) =
    {< table =
         table#mapi (fun s t -> 
	     let ok = 
	       try
		 let v = List.assoc key sieve in
		 not((v#meet (mkSymbolicSetValue (new symbolic_set_t [s])))#isBottom)
	       with
               | Not_found -> true
	     in
	     if not(ok) then
	       t
	     else
	       t#delete ~sieve:sieve) 
    >}
    
  method insert (args: (string * non_relational_domain_value_t) list) =
    let table' = table#clone in
    let _ = 
      try
	let v = List.assoc key args in
	let set = v#toSymbolicSet in
	if set#isTop then
	  raise (CHFailure (STR "Non-relational table: error #4"))
	else
	  set#iter (fun s ->
	      match table'#get s with
	      | None ->
		 let secondary_table = new secondary_table_t keys others in
		 let secondary_table' = secondary_table#insert args in
		 table'#set s secondary_table'
	      | Some secondary_table ->
		 let secondary_table' = secondary_table#insert args in
		 table'#set s secondary_table')
      with
      | Not_found -> raise (CHFailure (STR "Non-relational table: error #3"))
    in
    {< table = table' >}
    
  method toPretty = table#toPretty
                  
end
