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
open CHDomain   
open CHLanguage
open CHNonRelationalDomainValues
open CHNonRelationalTable   
open CHPretty
open CHSymbolicSets   
open CHUtils


class non_relational_database_t =
object (self: 'a)
  
  val tables: non_relational_table_t VariableCollections.table_t = new VariableCollections.table_t
                                                                 
  method getTables = tables
                   
  method removeTables ts =
    let tables' = tables#clone in
    let _ = tables'#removeList ts in
    {< tables =  tables' >}
    
  method leq (db: 'a) =
    let tables' = db#getTables in
    tables#fold (fun a k t ->
	a &&
	  match tables'#get k with
	  | None -> false
	  | Some t' -> t#leq t') true
    
  method equal (db: 'a) =
    self#leq db && db#leq self
    
  method join (db: 'a) =
    let tables' = db#getTables in
    let vars = tables#setOfKeys#union tables'#setOfKeys in
    let tables'' = new VariableCollections.table_t in
    let _ = vars#iter (fun v ->
		match (tables#get v, tables'#get v) with
		| (None, None) -> ()
		| (Some t, None) 
		  | (None, Some t) -> tables''#set v t
		| (Some t, Some t') -> tables''#set v (t#join t'))
    in
    {< tables = tables'' >}
    
  method widening (db: 'a) =
    let tables' = db#getTables in
    let vars = tables#setOfKeys#union tables'#setOfKeys in
    let tables'' = new VariableCollections.table_t in
    let _ = vars#iter (fun v ->
		match (tables#get v, tables'#get v) with
		| (None, None) -> ()
		| (Some t, None)
		  | (None, Some t) -> tables''#set v t
		| (Some t, Some t') -> tables''#set v (t#widening t'))
    in
    {< tables = tables'' >}    
    
  method meet (db: 'a) =
    (* Databases are not subject to refinement because updates are conservative *)
    {< >}
    
  method narrowing (db: 'a) =
    (* Databases are not subject to refinement because updates are conservative *)
    {< >}
    
  method getRows (t: variable_t) =
    match tables#get t with
    | None -> []
    | Some table -> table#getRows
                  
  method analyzeQuery ~(db_num: domain_int) ~(db_sym: domain_int) ~(cmd: (code_int, cfg_int) command_t): (variable_t * non_relational_domain_value_t) list =
    match cmd with
    | SELECT {selected = selected; from = from; where = where} ->
       begin
	 match tables#get from with
	 | None ->
	    []
	 | Some table ->
	    let sieve =
              List.map (fun (s, v) -> 
		  (s, if v#isNumerical then
			db_num#getNonRelationalValue v
		      else
			db_sym#getNonRelationalValue v
		  )
		) 
		       where
	    in
	    table#select ~selection:selected ~sieve:sieve
       end
    | _ ->
       raise (CHFailure (STR "Database error #3"))
      
  method analyzeQueryNoDB
           (cmd: (code_int, cfg_int) command_t): (variable_t * non_relational_domain_value_t) list =
    match cmd with
    | SELECT {selected = selected; from = from; where = where} ->
       List.map (fun (_, v) -> (v, topNonRelationalDomainValue)) selected
    | _ ->
       raise (CHFailure (STR "Database error #5"))
      
  method analyzeUpdate
           ~(db_num: domain_int)
           ~(db_sym: domain_int)
           ~(cmd: (code_int, cfg_int) command_t): 'a =
    match cmd with
    | ASSIGN_TABLE (x, y) ->
       let tables' = tables#clone in
       let _ = match tables#get y with
	 | None -> 
	    tables'#remove x
	 | Some t ->
	    tables'#set x t
       in
       {< tables = tables' >}
    | DELETE {rows_from = from; rows_where = where} ->
       let tables' = tables#clone in
       let _ = match tables#get from with
	 | None ->
	    ()
	 | Some table ->
	    let sieve =
              List.map (fun (s, v) -> 
		  (s, if v#isNumerical then
			db_num#getNonRelationalValue v
		      else
			db_sym#getNonRelationalValue v
		  )
		) 
		       where
	    in
	    tables'#set from (table#delete ~sieve:sieve)
       in
       {< tables = tables' >}
    | INSERT {into = into; values = values} ->
       let tables' = tables#clone in
       let args =
         List.map (fun (s, v) -> 
	     (s, if v#isNumerical then
		   db_num#getNonRelationalValue v
		 else
		   db_sym#getNonRelationalValue v
	     )
	   ) 
	          values
       in
       let _ = match tables#get into with
	 | None ->
	    let table = match into#getType with
	      | NR_TABLE_TYPE s ->
		 begin
		   try
		     let (k, _) =
                       List.find (fun (k, (_, index)) ->
                           match index with
                           | PRIMARY_INDEX -> true
                           | _ -> false) s in
		     new non_relational_table_t k s
		   with
                   | Not_found -> raise (CHFailure (STR "Database error #1"))
		 end
	      | _ -> raise (CHFailure (STR "Database error #2"))
	    in
	    tables'#set into (table#insert args)
	 | Some table ->
	    tables'#set into (table#insert args)
       in	      
       {< tables = tables' >}
    | _ ->
       raise (CHFailure (STR "Database error #4"))
      
  method toPretty = tables#toPretty
	          
end
  
