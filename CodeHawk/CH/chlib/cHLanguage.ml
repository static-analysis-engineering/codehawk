(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
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
  ------------------------------------------------------------------------------ *)

(* chlib *)
open CHPretty
open CHNumerical
open CHCommon

module H = Hashtbl
module P = Pervasives

let tab = 2
        
module StringInternalization =
  CHInternalization.Make (struct
                           type t = string
                           let compare = P.compare
                           let toPretty s = STR s
                           let hash = H.hash
                         end)
  
let internal_string_table = new StringInternalization.internal_table_t ~store_ids:false 1000000
                          
class internal_symbol_t (atts: string list) (seqnr: int) (s: string) =
  let (_, s') = internal_string_table#internalize s in
  let atts' = List.map (fun s -> let (_, s') = internal_string_table#internalize s in s') atts in
  object (self: 'a)
       
    val base = s'
             
    val attributes = Array.of_list atts'
                   
    val seq_number = seqnr
                   
    method getSymbol = base :: (Array.to_list attributes)
                     
    method getSeqNumber = seq_number
                        
    method getBaseName = base
                       
    method getAttributes = Array.to_list attributes
                         
    method hash = H.hash (seq_number, base, attributes)
                
    method toPretty = (* STR base *)
      LBLOCK [pretty_print_list self#getSymbol (fun s -> STR s) "" "_" "";
	      if seq_number = -1 then STR "" else LBLOCK [STR "_"; INT seq_number; STR "_"]
	     ] 
      
    method equal (s: 'a) = self#compare s = 0
                         
    method private lexComp l1 l2 =
      match (l1, l2) with
      | ([], []) -> 0
      | ([], _) -> -1
      | (_, []) -> 1
      | (s1 :: t1, s2 :: t2) ->
	 let c = P.compare s1 s2 in
	 if c = 0 then
	   self#lexComp t1 t2
	 else
	   c
	 
    method compare (s: 'a) =
      let c = P.compare seq_number s#getSeqNumber in
      if c = 0 then
	self#lexComp self#getSymbol s#getSymbol
      else
	c
      
  end
  
module SymbolInternalization =
  CHInternalization.Make (struct
                           type t = internal_symbol_t
                           let compare s1 s2 = s1#compare s2
                           let toPretty s = s#toPretty
                           let hash s = s#hash
                         end)
  
let internal_symbol_table = new SymbolInternalization.internal_table_t 1000000
                          
class symbol_t ?(atts = []) ?(seqnr = -1) (s: string) =
  let (id, sym) = internal_symbol_table#internalize (new internal_symbol_t atts seqnr s) in
  object (self: 'a)
       
    val index = id
              
    val internal_symbol = sym
                        
    method getSymbol = internal_symbol#getSymbol
                     
    method getSeqNumber = internal_symbol#getSeqNumber
                        
    method getBaseName = internal_symbol#getBaseName
                       
    method getAttributes = internal_symbol#getAttributes
                         
    method getIndex = index
                    
    method compare (s': 'a) = P.compare index s'#getIndex
                            
    method equal (s': 'a) = index = s'#getIndex
                          
    method toPretty = internal_symbol#toPretty
                    
  end
  
type nr_table_entry_kind_t =
  | NUMERICAL_ENTRY
  | SYMBOLIC_ENTRY
  
let nr_table_entry_kind_to_pretty k =
  match k with
  | NUMERICAL_ENTRY -> STR "NUMERICAL"
  | SYMBOLIC_ENTRY -> STR "SYMBOLIC"
	            
type nr_table_index_t =
  | PRIMARY_INDEX
  | SECONDARY_INDEX
  | NO_INDEX
  
let nr_table_index_to_pretty i =
  match i with
  | PRIMARY_INDEX -> STR "[K]"
  | SECONDARY_INDEX -> STR "[k]"
  | NO_INDEX -> STR ""
              
type nr_table_signature_t = (string * (nr_table_entry_kind_t * nr_table_index_t)) list
                          
let nr_table_signature_to_pretty s =
  pretty_print_list s (fun (n, (k, i)) ->
                      LBLOCK [STR n; STR ": ";
                              nr_table_entry_kind_to_pretty k;
                              nr_table_index_to_pretty i]) "{" "; " "}"
  
let signature_included s1 s2 =
  List.fold_left (fun a (n, (k, i)) ->
      a && try
	    let (k', i') = List.assoc n s2 in
	    (k = k') && (i = i')
	  with Not_found -> false) true s1
  
type variable_type_t =
  | NUM_LOOP_COUNTER_TYPE (** Internal type reserved for use by the fixpoint iterator *)
  | NUM_TMP_VAR_TYPE
  | SYM_TMP_VAR_TYPE
  | NUM_TMP_ARRAY_TYPE
  | SYM_TMP_ARRAY_TYPE
  | NUM_VAR_TYPE
  | SYM_VAR_TYPE
  | NUM_ARRAY_TYPE
  | SYM_ARRAY_TYPE
  | STRUCT_TYPE of (symbol_t * variable_type_t) list
  | NR_TABLE_TYPE of nr_table_signature_t
                   
let rec variable_type_to_pretty vtype =
  match vtype with
  | NUM_LOOP_COUNTER_TYPE -> STR "NUM_LOOP_COUNTER"
  | NUM_TMP_VAR_TYPE -> STR "T_NUMERICAL"
  | SYM_TMP_VAR_TYPE -> STR "T_SYMBOLIC"
  | NUM_TMP_ARRAY_TYPE -> STR "T_NUMERICAL[]"
  | SYM_TMP_ARRAY_TYPE -> STR "T_SYMBOLIC[]"
  | NUM_VAR_TYPE -> STR "NUMERICAL"
  | SYM_VAR_TYPE -> STR "SYMBOLIC"
  | NUM_ARRAY_TYPE -> STR "NUMERICAL[]"
  | SYM_ARRAY_TYPE -> STR "SYMBOLIC[]"
  | STRUCT_TYPE fields -> 
     LBLOCK [
	 STR "STRUCT {"; NL;
	 INDENT (tab,
		 LBLOCK (List.map (fun (f, t) -> LBLOCK [f#toPretty; STR ": ";
                                                         variable_type_to_pretty t; NL]) fields)
	        );
	 STR "}"
       ]
  | NR_TABLE_TYPE s -> LBLOCK [STR "TABLE"; nr_table_signature_to_pretty s]
                     
let is_base_type t =
  match t with
  | NUM_LOOP_COUNTER_TYPE
    | NUM_TMP_VAR_TYPE
    | NUM_VAR_TYPE
    | SYM_TMP_VAR_TYPE
    | SYM_VAR_TYPE -> true
  | _ -> false
       
let is_numerical_type t =
  match t with
  | NUM_LOOP_COUNTER_TYPE
    | NUM_TMP_VAR_TYPE
    | NUM_TMP_ARRAY_TYPE
    | NUM_VAR_TYPE
    | NUM_ARRAY_TYPE -> true
  | _ -> false
       
let is_symbolic_type t =
  match t with
  | SYM_TMP_VAR_TYPE
    | SYM_VAR_TYPE
    | SYM_TMP_ARRAY_TYPE
    | SYM_ARRAY_TYPE -> true
  | _ -> false
       
let is_array_type t =
  match t with
  | NUM_TMP_ARRAY_TYPE
    | SYM_TMP_ARRAY_TYPE
    | NUM_ARRAY_TYPE
    | SYM_ARRAY_TYPE -> true
  | _ -> false
       
let is_table_type t =
  match t with
  | NR_TABLE_TYPE _ -> true
  | _ -> false  
       
let is_struct_type t =
  match t with
  | STRUCT_TYPE _ -> true
  | _ -> false  
       
let is_temporary_type t =
  match t with
  | NUM_TMP_VAR_TYPE 
    | SYM_TMP_VAR_TYPE 
    | NUM_TMP_ARRAY_TYPE 
    | SYM_TMP_ARRAY_TYPE -> true
  | _ -> false
       
let compatible_table_types t1 t2 =
  match (t1, t2) with
  | (NR_TABLE_TYPE s1, NR_TABLE_TYPE s2) -> (signature_included s1 s2) && (signature_included s2 s1)
  | _ -> false
       
let rec compatible_struct_types t1 t2 =
  match (t1, t2) with
  | (STRUCT_TYPE f1, STRUCT_TYPE f2) ->
     let f1s = List.sort (fun (f, _) (f', _) -> f#compare f') f1 in
     let f2s = List.sort (fun (f, _) (f', _) -> f#compare f') f2 in
     let rec scan l1 l2 =
       match (l1, l2) with
       | ([], []) -> true
       | ((f1', t1') :: l1', (f2', t2') :: l2') ->
	  f1'#equal f2' && (compatible_types t1' t2') && (scan l1' l2')
       | _ -> false
     in
     scan f1s f2s
  | _ -> false
       
and compatible_types t1 t2 =
  (
    ((is_base_type t1 && is_base_type t2) || (is_array_type t1 && is_array_type t2))
    &&
      ((is_numerical_type t1 && is_numerical_type t2) || (is_symbolic_type t1 && is_symbolic_type t2))
  )
  ||
    compatible_table_types t1 t2
  ||
    compatible_struct_types t1 t2
  
(** STRUCT_TYPE < all other types *)    
let rec compare_types t1 t2 =
  match (t1, t2) with
  | (STRUCT_TYPE f1, STRUCT_TYPE f2) ->
     let f1s = List.sort (fun (f, _) (f', _) -> f#compare f') f1 in
     let f2s = List.sort (fun (f, _) (f', _) -> f#compare f') f2 in
     (* lexicographic order over fields *)
     let rec scan l1 l2 =
       match (l1, l2) with
       | ([], []) -> 0
       | ((f1', t1') :: l1', (f2', t2') :: l2') ->
	  let c = f1'#compare f2' in
	  if c = 0 then
	    let c' = compare_types t1' t2' in
	    if c' = 0 then
	      scan l1' l2'
	    else
	      c'
	  else
	    c
       | ([], _) -> -1
       | (_, []) -> 1
     in
     scan f1s f2s      
  | (STRUCT_TYPE _, _) -> -1
  | (_, STRUCT_TYPE _) -> 1
  | _ -> P.compare t1 t2
       
let variable_index = ref (-1)
                   
class internal_variable_t
        (the_name: symbol_t)
        (the_suffix: int)
        (is_register: bool)
        (the_path: symbol_t list)
        (the_vtype: variable_type_t) =
object (self: 'a)
     
  val vtype = the_vtype
            
  val name = the_name
           
  val suffix = the_suffix
             
  val isRegister = is_register
                 
  val path = Array.of_list the_path
           
  method hash = 
    let path_ids = Array.map (fun s -> s#getIndex) path in
    H.hash (vtype, name#getIndex, suffix, isRegister, path_ids)
    
  method getType = vtype
                 
  method getName = name
                 
  method getSuffix = suffix
                   
  method getPath = Array.to_list path
                 
  method getAllComponents =
    let rec get_components v p comps =
      match v#getType with
      | STRUCT_TYPE fs ->
	 List.fold_left (fun a (f, _) -> get_components (v#field f) (p @ [f]) a) comps fs
      | _ -> p :: comps
    in
    get_components self [] []
    
  method toPretty = 
    let path = self#getPath in
    LBLOCK [
        name#toPretty;
        (if suffix = 0 then STR "" else LBLOCK [STR "_"; INT suffix]);
        (pretty_print_list path (fun s -> s#toPretty) (match path with [] -> "" | _ -> "#") "#" "");
        (if isRegister then STR "(R)" else STR "")
      ]
    
  method field (f: symbol_t) =
    match vtype with
    | STRUCT_TYPE fs ->
       let (_, vtype') = 
	 try
	   List.find (fun (a,_) -> f#equal a) fs
	 with
	   Not_found ->
           raise (CHFailure (LBLOCK [STR "Variable ";
                                     self#toPretty; STR " has no field named "; f#toPretty]))   
       in
       {< path = Array.of_list (self#getPath @ [f]); vtype = vtype' >}
    | _ ->
       raise (CHFailure (LBLOCK [STR "Variable "; self#toPretty; STR " is not a structure"]))
      
  method fields fs =
    List.fold_left (fun a f -> a#field f) self fs
    
  method private equal_paths p1 p2 =
    match (p1, p2) with
    | ([], []) -> true
    | (f :: l, f' :: l') -> (f#equal f') && (self#equal_paths l l')
    | _ -> false
         
  (** Lexicographic order *)
  method private compare_paths p1 p2 =
    match (p1, p2) with
    | (f :: p, f' :: p') ->
       let c = f#compare f' in
       if c = 0 then
	 self#compare_paths p p'
       else
	 c
    | ([], []) -> 0
    | ([], _) -> -1
    | (_, []) -> 1
               
  method equal (v: 'a) =
    (compatible_types vtype v#getType)
    && (name#equal v#getName)
    && (self#equal_paths self#getPath v#getPath)
    && (suffix = v#getSuffix)
    && (isRegister = v#isRegister)
    
  method compare (v: 'a) =
    if compatible_types vtype v#getType then
      if name#equal v#getName then
	if suffix = v#getSuffix then
	  if isRegister = v#isRegister then
	    self#compare_paths self#getPath v#getPath
	  else
	    P.compare isRegister v#isRegister
	else
	  P.compare suffix v#getSuffix
      else
	name#compare v#getName
    else
      compare_types vtype v#getType
    
  method isRegister = isRegister
                    
  method isTmp =
    match vtype with
    | NUM_TMP_VAR_TYPE | SYM_TMP_VAR_TYPE 
      | NUM_TMP_ARRAY_TYPE | SYM_TMP_ARRAY_TYPE -> true
    | _ -> false
	 
  method isNumerical = is_numerical_type vtype    
                     
  method isSymbolic = is_symbolic_type vtype
                    
  method isArray = is_array_type vtype
                 
  method isTable = is_table_type vtype
                 
  method isStruct = is_struct_type vtype
                  
  method isTemporary = is_temporary_type vtype
                     
  method isAtomic = not(self#isArray || self#isStruct || self#isTable)
                  
  method marshalToSymbol =
    match vtype with
    | NUM_VAR_TYPE | SYM_VAR_TYPE 
      | NUM_TMP_VAR_TYPE | SYM_TMP_VAR_TYPE 
      ->
       let name = self#getName#getBaseName in
       let atts = self#getName#getAttributes in
       let seqnr_str = string_of_int self#getName#getSeqNumber in
       let type_str = match vtype with
	 | NUM_VAR_TYPE -> "N"
	 | SYM_VAR_TYPE -> "S"
	 | NUM_TMP_VAR_TYPE -> "NT"
	 | SYM_TMP_VAR_TYPE -> "ST"
	 | _ -> raise (CHFailure (STR "Unreachable"))
       in
       let suffix_str = string_of_int suffix in
       let register_str = string_of_bool isRegister in
       new symbol_t ~atts:([type_str; suffix_str; register_str; seqnr_str] @ atts) name
    | _ ->
       raise (CHFailure (LBLOCK [STR "Variable "; self#toPretty; STR " cannot be marshalled"]))
      
  method transformType (t: variable_type_t) =
    {< vtype = t >}
    
end
  
module VariableInternalization =
  CHInternalization.Make (struct
                           type t = internal_variable_t
                           let compare v1 v2 = v1#compare v2
                           let toPretty v = v#toPretty
                           let hash v = v#hash
                         end)
  
let internal_variable_table = new VariableInternalization.internal_table_t 1000000
                            
class variable_t
        (name: symbol_t)
        ?(suffix = 0)
        ?(register = false)
        ?(path = [])
        (vtype: variable_type_t) =
  let (id, var) = internal_variable_table#internalize (new internal_variable_t name suffix register path vtype) in
  object (self: 'a)
       
    val internal_variable = var
                          
    val index = id
              
    method getIndex = index
                    
    method getType = internal_variable#getType
                   
    method getName = internal_variable#getName
                   
    method getSuffix = internal_variable#getSuffix
                     
    method getPath = internal_variable#getPath
                   
    method getAllComponents = internal_variable#getAllComponents
                            
    method toPretty = internal_variable#toPretty
                    
    method field (f: symbol_t) = 
      let (id', var') = internal_variable_table#internalize (internal_variable#field f) in
      {< internal_variable = var'; index = id' >}
      
    method fields (fs: symbol_t list) = 
      let (id', var') = internal_variable_table#internalize (internal_variable#fields fs) in
      {< internal_variable = var'; index = id' >}
      
    method equal (v: 'a) = index = v#getIndex
                         
    method compare (v: 'a) = P.compare index v#getIndex
                           
    method isRegister = internal_variable#isRegister
                      
    method isTmp = internal_variable#isTmp
	         
    method isNumerical = internal_variable#isNumerical
                       
    method isSymbolic = internal_variable#isSymbolic
                      
    method isArray = internal_variable#isArray
                   
    method isTable = internal_variable#isTable
                   
    method isStruct = internal_variable#isStruct
                    
    method isTemporary = internal_variable#isTemporary
                       
    method isAtomic = internal_variable#isAtomic
                    
    method marshalToSymbol = internal_variable#marshalToSymbol
                           
    method transformType (t: variable_type_t) =
      let (id', var') = internal_variable_table#internalize (internal_variable#transformType t) in
      {< internal_variable = var'; index = id' >}
      
  end
  
let unmarshalVariable (symbol: symbol_t) =
  let error () =
    raise (CHFailure (LBLOCK [STR "Cannot unmarshal symbol "; symbol#toPretty; STR " to variable"]))
  in
  match symbol#getAttributes with
  | type_str :: suffix_str :: register_str :: seqnr_str :: atts ->
     (try
	let vtype = match type_str with
	  | "N" -> NUM_VAR_TYPE
	  | "S" -> SYM_VAR_TYPE
	  | "NT" -> NUM_TMP_VAR_TYPE
	  | "ST" -> SYM_TMP_VAR_TYPE
	  | _ -> error ()
	in
	let name = new symbol_t ~seqnr:(int_of_string seqnr_str) ~atts:atts symbol#getBaseName in
	new variable_t ~suffix:(int_of_string suffix_str) ~register:(bool_of_string register_str) name vtype
      with 
	Invalid_argument _ -> error ()
      | Failure s ->
	 raise (CHFailure 
		  (LBLOCK [ STR "Cannot unmarshal symbol " ; symbol#toPretty ; STR " to variable. " ;
			    STR s ]))
     )
  | _ -> error ()
       
type arg_mode_t =
  | READ
  | WRITE
  | READ_WRITE
  
type op_arg_t = string * variable_t * arg_mode_t
              
type operation_t = {
    op_name: symbol_t;
    op_args: (string * variable_t * arg_mode_t) list;
  }
                 
type op_processor_t =
  renaming: (variable_t -> variable_t)
  -> context: (symbol_t list)
  -> operation: operation_t -> operation_t
  
type domain_cmd_arg_t =
  | NUM_DOM_ARG of numerical_t
  | VAR_DOM_ARG of variable_t
                 
type symbolic_exp_t =
  | SYM of symbol_t
  | SYM_VAR of variable_t
             
type numerical_exp_t =
  | NUM of numerical_t
  | NUM_VAR of variable_t
  | PLUS of variable_t * variable_t
  | MINUS of variable_t * variable_t
  | MULT of variable_t * variable_t
  | DIV of variable_t * variable_t
         
type boolean_exp_t =
  | RANDOM
  | TRUE
  | FALSE
  | LEQ of variable_t * variable_t
  | GEQ of variable_t * variable_t
  | LT of variable_t * variable_t
  | GT of variable_t * variable_t
  | EQ of variable_t * variable_t
  | NEQ of variable_t * variable_t
  | SUBSET of variable_t * (symbol_t list)  
  | DISJOINT of variable_t * (symbol_t list)  
              
type select_args_t = {
    selected: (string * variable_t) list; 
    from: variable_t; 
    where: (string * variable_t) list
  }
                   
type insert_args_t = {
    into: variable_t; 
    values: (string * variable_t) list
  }
                   
type delete_args_t = {
    rows_from: variable_t;
    rows_where: (string * variable_t) list
  }
                   
type ('code, 'cfg) command_t =
  | CODE of symbol_t * 'code
  (** Structured code *)
  | CFG of symbol_t * 'cfg
  (** Control-flow graph *)
  | RELATION of 'code    
  (** Iterated backward/forward analysis *)
  | TRANSACTION of symbol_t * 'code * ('code option)
  (** Atomic analysis of straight-line code involving temporary variables *)
  | BREAKOUT_BLOCK of symbol_t * 'code
  (** Catches break points in the code *) 
  | BREAK of symbol_t
  (** Break out of the specified block *)
  | GOTO_BLOCK of 'code
  (** Block of code that may contain goto's (forward branching only) *)
  | LABEL of symbol_t
  (** Defines a branching point within a GOTO_BLOCK *)
  | GOTO of symbol_t
  (** Branch to the specified label *)
  | SKIP
  (** No operation *)
  | ABSTRACT_VARS of variable_t list
  (** Abstract away variables *)
  | ASSIGN_NUM of variable_t * numerical_exp_t
  (** ASSIGN_NUM (x, e) <=> x = e *)
  | INCREMENT of variable_t * numerical_t
  (** INCREMENT (x, n) <=> x = x + n *)
  | ASSIGN_SYM of variable_t * symbolic_exp_t  
  (** ASSIGN_SYM (s, e) <=> s = e *)
  | ASSIGN_STRUCT of variable_t * variable_t
  (** ASSIGN_STRUCT (s1, s2) <=> s1 = s2 *)
  | ABSTRACT_ELTS of variable_t * variable_t * variable_t    
  (** ABSTRACT_ELTS (array, <min index>, <max index>) <=> abstract away elements in a subarray *)
  | ASSIGN_ARRAY of variable_t * variable_t
  (** ASSIGN_ARRAY (a1, a2) <=> a1 = a2 (all elements of a2 are copied into a1, no sharing) *)
  | ASSIGN_NUM_ELT of variable_t * variable_t * variable_t
  (** ASSIGN_NUM_ELT (a, i, x) <=> a[i] = x *)
  | ASSIGN_SYM_ELT of variable_t * variable_t * variable_t
  (** ASSIGN_SYM_ELT (a, i, x) <=> a[i] = x *)
  | READ_NUM_ELT of variable_t * variable_t * variable_t
  (** READ_NUM_ELT (x, a, i) <=> x = a[i] *)
  | READ_SYM_ELT of variable_t * variable_t * variable_t
  (** READ_SYM_ELT (x, a, i) <=> x = a[i] *)
  | SHIFT_ARRAY of variable_t * variable_t * numerical_t   
  (** SHIFT_ARRAY (tgt, src, shift) <=> for all i do tgt[i] = src[i + <shift>] *)
  | BLIT_ARRAYS of variable_t * variable_t * variable_t * variable_t * variable_t
  (** BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) <=> for all 0 <= i < n do tgt[tgt_o + i] = src[src_o + i] *)
  | SET_ARRAY_ELTS of variable_t * variable_t * variable_t * variable_t
  (** SET_ARRAY_ELTS (a, s, n, v) <=> for all s <= i < s + n do a[i] = v *)
  | ASSERT of boolean_exp_t
  (** Boolean assertion *)
  | BRANCH of 'code list
  (** BRANCH (<branch_1>, ..., <branch_n>) <=> non-deterministic choice among distinct branches *)
  | LOOP of 'code * 'code * 'code
  (** LOOP(<loop test true>, <loop test false>, body) <=>
      iterate \{<loop test true>; body\} exit when <loop test false> *)
  | OPERATION of operation_t
  (** User-defined operation *)
  | DOMAIN_OPERATION of (string list) * operation_t
  (** Domain-specific user-defined operation. First component is a list of domain names. *)
  | CALL of symbol_t * ((symbol_t * variable_t) list)
  (** CALL (<procedure name>, [<argument name> => <argument>; ...]) <=> procedure call *)
  | CONTEXT of symbol_t * 'code
  (** CONTEXT (`marker`, `code`) <=> push `marker` into the context stack for the analysis of `code` only *)
  | DOMAINS of (string list) * 'code
  (** DOMAINS (`domains`, `code`) <=> activate `domains` for the analysis of `code` only. *)
  | DOMAIN_CMD of string * string * (domain_cmd_arg_t list)
  (** DOMAIN_CMD (<domain>, <cmd>, <args>) <=> 
      send domain-specific command <cmd> to domain <domain> with arguments <args> *)
  | MOVE_VALUES of (variable_t list) * string * string
  (** MOVE_VALUES [var_1; ...; var_n] src_domain tgt_domain <=>
      refine tgt_domain with non-relational values for variables var_1, ..., var_n described in src_domain *)
  | MOVE_RELATIONS of (variable_t list) * string * string
  (** MOVE_VALUES [var_1; ...; var_n] src_domain tgt_domain <=>
      refine tgt_domain with relations over var_1, ..., var_n described in src_domain *)
  | SELECT of select_args_t
  (** SELECT {selected: [(e, v); ...]; from: t; where: [(k, u); ...]} <=>
      SELECT e AS v, ... FROM t WHERE k = u AND ... *)
  | INSERT of insert_args_t
  (** INSERT {into: t; values: [(e, v); ...]} <=>
      INSERT INTO t VALUES (e = v, ...) *)
  | DELETE of delete_args_t
  (** DELETE {rows_from: t; rows_where: [(k, u); ...]} <=>
      DELETE ROWS FROM t WHERE k = u AND ... *)
  | ASSIGN_TABLE of variable_t * variable_t
(** ASSIGN_TABLE (t1, t2) <=> t1 = t2 *)
                  
class type code_int =
  object ('a)
    method getId: int
    method toPretty: pretty_t
    method length: int
    method getCmdAt: int -> (code_int, cfg_int) command_t
    method setCmdAt: int -> (code_int, cfg_int) command_t -> unit
    method removeSkips: unit
    method clone:
             ?context: (symbol_t list)
             -> ?renaming: (variable_t -> variable_t)
             -> ?op_proc: op_processor_t -> unit -> 'a
  end
  
      and state_int =
        object ('a)
          method getLabel: symbol_t
          method toPretty: pretty_t
          method getIncomingEdges: symbol_t list
          method getOutgoingEdges: symbol_t list
          method getCode: code_int
          method addIncomingEdge: symbol_t -> unit
          method addOutgoingEdge: symbol_t -> unit
          method clone:
                   ?context: (symbol_t list)
                   -> ?renaming: (variable_t -> variable_t)
                   -> ?op_proc: op_processor_t -> unit -> 'a
        end
        
      (** 
       * Structural requirement: the entry state has no incoming edges and 
       * the exit state has no outgoing edges.
       *)
      and cfg_int =
        object ('a)  
          method getId: int
          method toPretty: pretty_t
          method getEntry: state_int
          method getExit: state_int
          method getState: symbol_t -> state_int
          method getStates: symbol_t list
          method getStatesFrom: symbol_t -> symbol_t list
          method addState: state_int -> unit
          method addStates: state_int list -> unit
          method addEdge: symbol_t -> symbol_t -> unit
          method clone:
                   ?context: (symbol_t list)
                   -> ?renaming: (variable_t -> variable_t)
                   -> ?op_proc: op_processor_t -> unit -> 'a
        end
	
class type scope_int =
  object ('a)
    method toPretty: pretty_t
    method getTmpBase: string
    method getRegisterBase: string
    method getVariables: variable_t list
    method getNumTmpVariables: variable_t list
    method getSymTmpVariables: variable_t list
    method getNumTmpArrays: variable_t list
    method getSymTmpArrays: variable_t list
    method addVariable: variable_t -> unit
    method addVariables: variable_t list -> unit
    method removeVariable: variable_t -> unit
    method removeVariables: variable_t list -> unit
    method transformVariables: (variable_t -> variable_t) -> unit
    method mergeWith: 'a -> (variable_t -> variable_t)
    method mkVariable: symbol_t -> variable_type_t -> variable_t
    method mkRegister: variable_type_t -> variable_t
    method startTransaction: unit
    method requestNumTmpVariable: variable_t
    method requestSymTmpVariable: variable_t
    method requestNumTmpArray: variable_t
    method requestSymTmpArray: variable_t
    method endTransaction: unit
  end
  
type signature_t = (symbol_t * variable_type_t * arg_mode_t) list
                 
type bindings_t = (symbol_t * variable_t) list
                
class type procedure_int =
  object
    method toPretty: pretty_t
    method getName: symbol_t
    method getBody: code_int
    method setBody: code_int -> unit
    method getScope: scope_int
    method getSignature: signature_t
    method getBindings: bindings_t
  end
  
class type system_int =
  object
    method toPretty: pretty_t
    method getName: symbol_t
    method getProcedure: symbol_t -> procedure_int
    method addProcedure: procedure_int -> unit
    method getProcedures: symbol_t list
    method hasProcedure: symbol_t -> bool
  end
  
module type LANGUAGE_FACTORY =
  sig
    
    val mkCode: (code_int, cfg_int) command_t list -> code_int
    val mkState: symbol_t -> code_int -> state_int
    val mkCFG: state_int -> state_int -> cfg_int
    val mkCFG_s: symbol_t -> symbol_t -> cfg_int
    val mkScope: ?tmp_base: string -> ?register_base: string -> unit -> scope_int
    val mkProcedure:
      symbol_t ->
      signature:signature_t ->
      bindings:bindings_t ->
      scope:scope_int ->
      body:code_int -> procedure_int
    val mkSystem: symbol_t -> system_int
      
  end
  
let numerical_exp_to_pretty exp =
  match exp with
  | NUM n -> n#toPretty
  | NUM_VAR v -> v#toPretty
  | PLUS (v, w) -> LBLOCK [v#toPretty; STR " + "; w#toPretty]
  | MINUS (v, w) -> LBLOCK [v#toPretty; STR " - "; w#toPretty]
  | MULT (v, w) -> LBLOCK [v#toPretty; STR " * "; w#toPretty]
  | DIV (v, w) -> LBLOCK [v#toPretty; STR " / "; w#toPretty]
                
                
let symbolic_exp_to_pretty exp =
  match exp with
  | SYM s -> LBLOCK [STR "'"; s#toPretty; STR "'"]
  | SYM_VAR v -> v#toPretty
	       
let bool_exp_to_pretty exp =
  match exp with
  | RANDOM -> STR "RANDOM"
  | TRUE -> STR "TRUE"
  | FALSE -> STR "FALSE"
  | LEQ (v, w) -> LBLOCK [v#toPretty; STR " <= "; w#toPretty]
  | GEQ (v, w) -> LBLOCK [v#toPretty; STR " >= "; w#toPretty]
  | LT (v, w) -> LBLOCK [v#toPretty; STR " < "; w#toPretty]
  | GT (v, w) -> LBLOCK [v#toPretty; STR " > "; w#toPretty]
  | EQ (v, w) -> LBLOCK [v#toPretty; STR " = "; w#toPretty]
  | NEQ (v, w) -> LBLOCK [v#toPretty; STR " != "; w#toPretty]
  | SUBSET (v, l) ->
     LBLOCK [v#toPretty; STR " IN ";
             pretty_print_list l (fun s -> s#toPretty) "{" "; " "}"]
  | DISJOINT (v, l) ->
     LBLOCK [v#toPretty; STR " NOT IN ";
             pretty_print_list l (fun s -> s#toPretty) "{" "; " "}"]
    
let arg_mode_to_pretty mode =
  match mode with
  | READ -> STR "READ"
  | WRITE -> STR "WRITE"
  | READ_WRITE -> STR "READ/WRITE"
                
let signature_to_pretty s =
  let pp (arg, arg_type, mode) =
    LBLOCK [arg_mode_to_pretty mode; STR " "; arg#toPretty;
            STR ": "; variable_type_to_pretty arg_type]
  in
  pretty_print_list s pp "(" ", " ")"
  
let bindings_to_pretty b =
  let pp (s, v) =
    LBLOCK [s#toPretty; STR " => "; v#toPretty]
  in
  pretty_print_list b pp "{" "; " "}"
  
let rec command_to_pretty (_:int) (cmd: (code_int, cfg_int) command_t) =
  match cmd with
  | CODE (s, code) ->
     LBLOCK [ STR "CODE "; STR "(" ; s#toPretty ; STR ")" ; code#toPretty ]
  | CFG (s, cfg) ->
     LBLOCK [ STR "CFG " ; STR "(" ; s#toPretty ; STR ")" ; STR "{"; NL;
	      INDENT (tab, cfg#toPretty);
	      STR "}" ]
  | RELATION code -> LBLOCK [ STR "RELATION "; code#toPretty ]
  | TRANSACTION (s, code, post_code) ->
     LBLOCK [ STR "TRANSACTION "; STR "(" ; s#toPretty ; STR ")" ; code#toPretty;
	      match post_code with
	      | None -> STR ""
	      | Some code -> LBLOCK [STR " :: "; code#toPretty] ]
  | BREAKOUT_BLOCK (s, code) ->
     LBLOCK [ STR "BREAKOUT_BLOCK "; s#toPretty; STR " "; code#toPretty ]
  | BREAK s -> LBLOCK [STR "BREAK "; s#toPretty]
  | GOTO_BLOCK code -> LBLOCK [ STR "GOTO_BLOCK "; code#toPretty ]
  | LABEL l -> LBLOCK [ STR "LABEL "; l#toPretty ]
  | GOTO l -> LBLOCK [ STR "GOTO "; l#toPretty ]
  | SKIP -> STR "SKIP"
  | ABSTRACT_VARS vars ->
     LBLOCK [ STR "ABSTRACT_VARS ";
	      pretty_print_list vars (fun v -> v#toPretty) "[" ", " "]" ]
  | ABSTRACT_ELTS (array, min, max) ->
     LBLOCK [ STR "ABSTRACT_ELTS ("; array#toPretty; STR ", ";
	      min#toPretty; STR ", "; max#toPretty; STR ")" ]
  | ASSIGN_NUM (lhs, exp) ->
     LBLOCK [ lhs#toPretty; STR " = "; numerical_exp_to_pretty exp ]
  | ASSIGN_ARRAY (lhs, rhs) ->
     LBLOCK [ lhs#toPretty; STR " = "; rhs#toPretty ]
  | INCREMENT (lhs, inc) ->
     LBLOCK [ lhs#toPretty; STR " = "; lhs#toPretty; STR " + "; inc#toPretty ]
  | ASSIGN_SYM (lhs, exp) ->
     LBLOCK [ lhs#toPretty; STR " = "; symbolic_exp_to_pretty exp ]
  | ASSIGN_STRUCT (lhs, rhs) ->
     LBLOCK [ lhs#toPretty; STR " = "; rhs#toPretty ]
  | ASSIGN_NUM_ELT (lhs, index, v) ->
     LBLOCK [ lhs#toPretty; STR "["; index#toPretty; STR "]"; STR " = ";
	      v#toPretty ]
  | ASSIGN_SYM_ELT (lhs, index, v) ->
     LBLOCK [ lhs#toPretty; STR "["; index#toPretty; STR "]"; STR " = ";
	      v#toPretty ]
  | READ_NUM_ELT (lhs, a, index) ->
     LBLOCK [ lhs#toPretty; STR " = "; a#toPretty; STR "["; index#toPretty; STR "]" ]
  | READ_SYM_ELT (lhs, a, index) ->
     LBLOCK [ lhs#toPretty; STR " = "; a#toPretty; STR "["; index#toPretty; STR "]" ]
  | SHIFT_ARRAY (tgt, src, n) ->
     LBLOCK [ tgt#toPretty; STR " = "; src#toPretty;
              (if n#geq numerical_zero then 
	         LBLOCK [STR " << "; n#toPretty]
	       else
	         LBLOCK [STR " >> "; n#neg#toPretty]) ]
  | BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
     LBLOCK [ STR "BLIT_ARRAYS ";
              pretty_print_list [tgt; tgt_o; src; src_o; n]
                                (fun v -> v#toPretty) "("", " ")" ]
  | SET_ARRAY_ELTS (a, s, n, v) ->
     LBLOCK [ STR "SET_ARRAY_ELTS ";
              pretty_print_list [a; s; n; v] (fun v -> v#toPretty) "("", " ")" ]
  | ASSERT exp ->
     LBLOCK [ STR "ASSERT ("; bool_exp_to_pretty exp; STR ")" ]
  | BRANCH branches ->
     LBLOCK [ STR "BRANCH "; 
	      pretty_print_list branches (fun c -> c#toPretty) "" " || " "" ]
  | LOOP (test_t, test_f, body) ->
     LBLOCK [ STR "LOOP WHEN "; test_t#toPretty;
	      STR " EXIT WHEN "; test_f#toPretty;
	      STR " DO "; body#toPretty ]	
  | OPERATION {op_name = op_name; op_args = op_args} ->
     LBLOCK [ STR "OPERATION ";
	      op_name#toPretty; STR " ";
	      pretty_print_list
                op_args 
	        (fun (name, arg, mode) ->
	          LBLOCK [STR name; STR ":"; arg_mode_to_pretty mode; STR " => "; arg#toPretty]
	        ) "(" ", " ")" ]
  | DOMAIN_OPERATION (domains, {op_name = op_name; op_args = op_args}) ->
     LBLOCK [ STR "OPERATION ";
	      op_name#toPretty; STR " ";
	      pretty_print_list
                op_args 
	        (fun (name, arg, mode) ->
	          LBLOCK [STR name; STR ":"; arg_mode_to_pretty mode; STR " => "; arg#toPretty]
	        ) "(" ", " ")";
	      STR " ON DOMAINS ";
	      pretty_print_list domains (fun d -> STR d) "{" "; " "}" ]
  | CALL (p, args) ->
     LBLOCK [ STR "CALL "; p#toPretty; STR " ";
	      pretty_print_list
                args
                (fun (name, arg) ->
                  LBLOCK [name#toPretty; STR " => "; arg#toPretty]) "(" ", " ")" ]
  | CONTEXT (ctxt, code) ->
     LBLOCK [ STR "CONTEXT ("; ctxt#toPretty; STR ") "; code#toPretty ]
  | DOMAINS (doms, code) ->
     LBLOCK [ STR "DOMAINS "; pretty_print_list doms (fun d -> STR d) "(" ", " ")";
              code#toPretty ]
  | DOMAIN_CMD (dom, cmd, args) ->
     LBLOCK [ STR "DOMAIN_CMD ("; STR dom; STR ", "; STR cmd; STR ", ";
	      pretty_print_list
                args
                (fun a -> 
		  match a with
		  | NUM_DOM_ARG n -> n#toPretty
		  | VAR_DOM_ARG v -> v#toPretty) "[" ", " "]";
	      STR ")" ]
  | MOVE_VALUES (l, src, tgt) ->
     LBLOCK [ STR "MOVE_VALUES OF ";
              pretty_print_list l (fun v -> v#toPretty) "{" ", " "}";
	      STR " FROM "; STR src; STR " TO "; STR tgt ]
  | MOVE_RELATIONS (l, src, tgt) ->
     LBLOCK [ STR "MOVE_RELATIONS OVER ";
              pretty_print_list l (fun v -> v#toPretty) "{" ", " "}";
	      STR " FROM "; STR src; STR " TO "; STR tgt ]
  | SELECT {selected = selected; from = from; where = where} ->
     LBLOCK [ STR "SELECT ";
	      pretty_print_list
                selected
                (fun (n, v) -> LBLOCK [STR n; STR " AS "; v#toPretty]) "" ", " "";
	      STR " FROM "; from#toPretty;
	      match where with 
	      | [] -> STR "" 
	      | _ -> 
	         LBLOCK [STR " WHERE "; 
		         pretty_print_list
                           where
                           (fun (n, v) -> LBLOCK [STR n; STR " = "; v#toPretty]) "" " AND " "" ]
            ]
  | INSERT {into = into; values = values} ->
     LBLOCK [ STR "INSERT INTO "; into#toPretty; STR " VALUES ";
	      pretty_print_list
                values
                (fun (n, v) -> LBLOCK [STR n; STR " = "; v#toPretty]) "(" ", " ")" ]
  | DELETE {rows_from = from; rows_where = where} ->
     LBLOCK [ STR "DELETE ROWS FROM "; from#toPretty;
              match where with 
	      | [] -> STR "" 
	      | _ -> 
	         LBLOCK [STR " WHERE "; 
		         pretty_print_list
                           where
                           (fun (n, v) -> LBLOCK [STR n; STR " = "; v#toPretty]) "" " AND " "" ]     
            ]
  | ASSIGN_TABLE (t1, t2) -> LBLOCK [ t1#toPretty; STR " = "; t2#toPretty ]

class code_walker_t =
object (self: _)
     
  method walkCode (code: code_int) =
    for i = 0 to code#length - 1 do
      self#walkCmd (code#getCmdAt i)
    done
    
  method walkVar v = ()
                   
  method walkNumExp e =
    match e with
    | NUM _ -> ()
    | NUM_VAR v -> self#walkVar v
    | PLUS (x, y) ->
       self#walkVar x;
       self#walkVar y
    | MINUS (x, y) ->
       self#walkVar x;
       self#walkVar y
    | MULT (x, y) ->
       self#walkVar x;
       self#walkVar y
    | DIV (x, y) ->
       self#walkVar x;
       self#walkVar y
       
  method walkSymExp e =
    match e with
    | SYM _ -> ()
    | SYM_VAR v -> self#walkVar v
	         
  method walkBoolExp e =
    match e with
    | RANDOM -> ()
    | TRUE -> ()
    | FALSE -> ()
    | LEQ (x, y) ->
       self#walkVar x;
       self#walkVar y
    | GEQ (x, y) ->
       self#walkVar x;
       self#walkVar y
    | LT (x, y) ->
       self#walkVar x;
       self#walkVar y
    | GT (x, y) ->
       self#walkVar x;
       self#walkVar y
    | EQ (x, y) ->
       self#walkVar x;
       self#walkVar y
    | NEQ (x, y) ->
       self#walkVar x;
       self#walkVar y
    | SUBSET (v, _) -> self#walkVar v
    | DISJOINT (v, _) -> self#walkVar v
                       
  method walkCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | CODE (_, code) ->
       self#walkCode code
    | CFG (_, cfg) ->
       let states = cfg#getStates in
       List.iter (fun s -> self#walkCode (cfg#getState s)#getCode) states
    | RELATION code ->
       self#walkCode code
    | TRANSACTION (_, code, post_code) ->
       begin
	 self#walkCode code;
	 match post_code with
	 | None -> ()
	 | Some code -> self#walkCode code
       end
    | BREAKOUT_BLOCK (s, code) ->
       self#walkCode code
    | GOTO_BLOCK code ->
       self#walkCode code
    | BREAK _
      | SKIP
      | GOTO _
      | LABEL _ ->
       ()
    | ABSTRACT_VARS l ->
       List.iter (fun v -> self#walkVar v) l
    | ABSTRACT_ELTS (a, min, max) ->
       self#walkVar a;
       self#walkVar min;
       self#walkVar max
    | ASSIGN_NUM (x, e) ->
       self#walkVar x;
       self#walkNumExp e
    | ASSIGN_ARRAY (x, y) ->
       self#walkVar x;
       self#walkVar y
    | INCREMENT (x, _) ->
       self#walkVar x
    | ASSIGN_SYM (x, e) ->
       self#walkVar x;
       self#walkSymExp e
    | ASSIGN_STRUCT (x, y) ->
       self#walkVar x;
       self#walkVar y
    | ASSIGN_NUM_ELT (a, i, v) ->
       self#walkVar a;
       self#walkVar i;
       self#walkVar v
    | ASSIGN_SYM_ELT (a, i, v) ->
       self#walkVar a;
       self#walkVar i;
       self#walkVar v
    | READ_NUM_ELT (v, a, i) ->
       self#walkVar v;
       self#walkVar a;
       self#walkVar i
    | READ_SYM_ELT (v, a, i) ->
       self#walkVar v;
       self#walkVar a;
       self#walkVar i
    | SHIFT_ARRAY (tgt, src, _) ->
       self#walkVar tgt;
       self#walkVar src
    | BLIT_ARRAYS (tgt, tgt_o, src, src_o, n) ->
       self#walkVar tgt;
       self#walkVar tgt_o;
       self#walkVar src;
       self#walkVar src_o;
       self#walkVar n
    | SET_ARRAY_ELTS (a, s, n, v) ->
       self#walkVar a;
       self#walkVar s;
       self#walkVar n;
       self#walkVar v
    | ASSERT e ->
       self#walkBoolExp e
    | BRANCH cl ->
       List.iter self#walkCode cl
    | LOOP (c1, c2, c3) ->
       self#walkCode c1;
       self#walkCode c2;
       self#walkCode c3
    | OPERATION {op_args = args} 
      | DOMAIN_OPERATION (_, {op_args = args}) ->
       List.iter (fun (_, v, _) -> self#walkVar v) args
    | CALL (_, params) ->
       List.iter (fun (_, v) -> self#walkVar v) params
    | CONTEXT (_, code) ->
       self#walkCode code
    | DOMAINS (_, code) ->
       self#walkCode code
    | DOMAIN_CMD (_, _, args) ->
       List.iter (fun a -> match a with
		           | VAR_DOM_ARG v -> self#walkVar v
		           | _ -> ()) args
    | MOVE_VALUES (l, _, _) ->
       List.iter self#walkVar l
    | MOVE_RELATIONS (l, _, _) ->
       List.iter self#walkVar l
    | SELECT {selected = selected; from = from; where = where} ->
       List.iter (fun (_, v) -> self#walkVar v) selected;
       self#walkVar from;
       List.iter (fun (_, v) -> self#walkVar v) where
    | INSERT {into = into; values = values} ->
       self#walkVar into;
       List.iter (fun (_, v) -> self#walkVar v) values
    | DELETE {rows_from = from; rows_where = where} ->
       self#walkVar from;
       List.iter (fun (_, v) -> self#walkVar v) where
    | ASSIGN_TABLE (t1, t2) ->
       self#walkVar t1;
       self#walkVar t2
       
end
  
class code_transformer_t =
object (self: _)
     
  method transformCode code =
    for i = 0 to code#length - 1 do
      code#setCmdAt i (self#transformCmd (code#getCmdAt i))
    done
    
  method transformCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | CODE (_, code) ->
       let _ = self#transformCode code in
       cmd
    | CFG (_, cfg) ->
       let _ = List.iter (fun s -> self#transformCode (cfg#getState s)#getCode) cfg#getStates in
       cmd
    | RELATION code ->
       let _ = self#transformCode code in
       cmd
    | TRANSACTION (_, code, post_code) ->
       let _ = self#transformCode code in
       let _ = match post_code with
	 | None -> ()
	 | Some code -> self#transformCode code
       in
       cmd
    | BREAKOUT_BLOCK (s, code) ->
       let _ = self#transformCode code in
       cmd
    | GOTO_BLOCK code ->
       let _ = self#transformCode code in
       cmd
    | BRANCH cl ->
       let _ = List.iter self#transformCode cl in
       cmd
    | LOOP (c1, c2, c3) ->
       let _ = self#transformCode c1 in
       let _ = self#transformCode c2 in
       let _ = self#transformCode c3 in
       cmd
    | CONTEXT (_, code) ->
       let _ = self#transformCode code in
       cmd
    | DOMAINS (_, code) ->
       let _ = self#transformCode code in
       cmd
    | _ ->
       cmd
      
end
  
let negate_bool_exp e =
  match e with
  | RANDOM -> RANDOM
  | TRUE -> FALSE
  | FALSE -> TRUE
  | LEQ (v, w) -> GT (v, w)
  | GEQ (v, w) -> LT (v, w)
  | LT (v, w) -> GEQ (v, w)
  | GT (v, w) -> LEQ (v, w)
  | EQ (v, w) -> NEQ (v, w)
  | NEQ (v, w) -> EQ (v, w)
  | SUBSET (v, l)-> DISJOINT (v, l)
  | DISJOINT (v, l) -> SUBSET (v, l)
	             
let modified_vars_in_cmd_fwd cmd =
  match cmd with
  | ABSTRACT_VARS l -> l
  | ABSTRACT_ELTS (x, _, _) -> [x]
  | ASSIGN_NUM (x, _) -> [x]
  | ASSIGN_ARRAY (x, _) -> [x]
  | INCREMENT (x, _) -> [x]
  | ASSIGN_SYM (x, _) -> [x]
  | ASSIGN_STRUCT (x, _) -> [x]
  | ASSIGN_NUM_ELT (x, _, _) -> [x]
  | ASSIGN_SYM_ELT (x, _, _) -> [x]
  | READ_NUM_ELT (x, _, _) -> [x]
  | READ_SYM_ELT (x, _, _) -> [x]
  | SHIFT_ARRAY (x, _, _) -> [x]
  | BLIT_ARRAYS (t, _, s, _, _) -> [t; s]
  | SET_ARRAY_ELTS (a, _, _, _) -> [a]
  | ASSERT (LEQ (x, y)) -> [x; y]
  | ASSERT (GEQ (x, y)) -> [x; y]
  | ASSERT (LT (x, y)) -> [x; y]
  | ASSERT (GT (x, y)) -> [x; y]
  | ASSERT (EQ (x, y)) -> [x; y]
  | ASSERT (NEQ (x, y)) -> [x; y]
  | ASSERT (SUBSET (x, _))-> [x]
  | ASSERT (DISJOINT (x, _)) -> [x]
  | SELECT {selected = selected} -> List.map (fun (_, v) -> v) selected
  | INSERT {into = into} -> [into]
  | DELETE {rows_from = from} -> [from]
  | ASSIGN_TABLE (t1, t2) -> [t1]
  | _ -> []
       
module VariableCollections' =
  CHCollections.Make
    (struct
      type t = variable_t
      let compare s1 s2 = s1#compare s2
      let toPretty s = s#toPretty
    end)
  
class var_collector_t =
object
  
  inherit code_walker_t as super
        
  val vars = new VariableCollections'.set_t
           
  method getVars = vars#toList
                 
  method walkVar var = vars#add var
    
end
  
let vars_in_cmd cmd =
  let collector = new var_collector_t in
  let _ = collector#walkCmd cmd in
  collector#getVars
  
let vars_in_code code =
  let collector = new var_collector_t in
  let _ = collector#walkCode code in
  collector#getVars
  
let modified_vars_in_cmd_bwd cmd =
  match cmd with
  | ABSTRACT_VARS l -> l
  | ABSTRACT_ELTS (x, _, _) -> [x]
  | ASSIGN_NUM (_, _) -> vars_in_cmd cmd
  | ASSIGN_ARRAY (_, _) -> vars_in_cmd cmd
  | INCREMENT (x, _) -> [x]
  | ASSIGN_SYM (_, _) -> vars_in_cmd cmd
  | ASSIGN_STRUCT (_, _) -> vars_in_cmd cmd
  | ASSIGN_NUM_ELT (x, _, y) -> [x; y]
  | ASSIGN_SYM_ELT (x, _, y) -> [x; y]
  | READ_NUM_ELT (x, y, _) -> [x; y]
  | READ_SYM_ELT (x, y, _) -> [x; y]
  | SHIFT_ARRAY (x, y, _) -> [x; y]
  | BLIT_ARRAYS (t, _, s, _, _) -> [t; s]
  | SET_ARRAY_ELTS (a, _, _, _) -> [a]
  | ASSERT (LEQ (x, y)) -> [x; y]
  | ASSERT (GEQ (x, y)) -> [x; y]
  | ASSERT (LT (x, y)) -> [x; y]
  | ASSERT (GT (x, y)) -> [x; y]
  | ASSERT (EQ (x, y)) -> [x; y]
  | ASSERT (NEQ (x, y)) -> [x; y]
  | ASSERT (SUBSET (x, _))-> [x]
  | ASSERT (DISJOINT (x, _)) -> [x]
  | SELECT {selected = selected} -> List.map (fun (_, v) -> v) selected
  | INSERT {into = into} -> [into]
  | DELETE {rows_from = from} -> [from]
  | ASSIGN_TABLE (t1, t2) -> [t1; t2]
  | _ -> []
       
class tmp_collector_t =
object
  
  inherit var_collector_t as super
        
  method walkVar var =
    if var#isTmp then
      super#walkVar var
    else
      ()
    
end
  
let tmp_vars_in_cmd cmd =
  let collector = new tmp_collector_t in
  let _ = collector#walkCmd cmd in
  collector#getVars
  
let tmp_vars_in_code code =
  let collector = new tmp_collector_t in
  let _ = collector#walkCode code in
  collector#getVars
  
(** Computes a *superset* of variables read in a piece of code.
    It's not possible to be more precise at this level because of calls 
    to undefined procedures, the signatures of which are unavailable. 
 *)    
class read_vars_collector_t (system: system_int) =
object (self: _)
     
  inherit var_collector_t as super
        
  method private add v = vars#add v
                       
  method private addl l = List.iter self#add l
                        
  method walkVar _ = ()
                   
  method walkNumExp e =
    match e with
    | NUM _ -> ()
    | NUM_VAR v -> self#add v
    | PLUS (x, y) 
      | MINUS (x, y) 
      | MULT (x, y) 
      | DIV (x, y) -> self#addl [x; y]
	            
  method walkSymExp e =
    match e with
    | SYM _ -> ()
    | SYM_VAR v -> self#add v
	         
  method walkBoolExp e =
    match e with
    | RANDOM -> ()
    | TRUE -> ()
    | FALSE -> ()
    | LEQ (x, y) 
      | GEQ (x, y) 
      | LT (x, y)
      | GT (x, y)
      | EQ (x, y)
      | NEQ (x, y) -> self#addl [x; y]	
    | SUBSET (v, _) 
      | DISJOINT (v, _) -> self#add v
                         
  method walkCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | ABSTRACT_ELTS (_, min, max) -> self#addl [min; max]
    | ASSIGN_STRUCT (_, y) -> self#add y
    | ASSIGN_ARRAY (_, y) -> self#add y
    | ASSIGN_NUM_ELT (_, i, v)
      | ASSIGN_SYM_ELT (_, i, v) -> self#addl [i; v]
    | READ_NUM_ELT (_, a, i)
      | READ_SYM_ELT (_, a, i) -> self#addl [a; i]
    | SHIFT_ARRAY (_, src, _) -> self#add src
    | BLIT_ARRAYS (_, tgt_o, src, src_o, n) -> self#addl [tgt_o; src; src_o; n]
    | SET_ARRAY_ELTS (_, s, n, v) -> self#addl [s; n; v]
    | OPERATION {op_args = args} 
      | DOMAIN_OPERATION (_, {op_args = args}) ->
       List.iter (fun (_, v, mode) -> match mode with WRITE -> () | _ -> self#add v) args
    | CALL (f, params) ->
       let read_params = 
	 if system#hasProcedure f then
	   let signature = (system#getProcedure f)#getSignature in
	   List.fold_left (fun a (p, _, m) -> if m = WRITE then a else p :: a) [] signature
	 else
	   (* Conservative assumption *)
	   List.map fst params
       in
       List.iter (fun (p, v) -> 
	   if List.exists (fun p' -> p#equal p') read_params then
	     self#add v
	   else
	     ()
	 ) params
    | SELECT {selected = _; from = from; where = where} ->
       self#add from;
       List.iter (fun (_, v) -> self#add v) where
    | INSERT {into = _; values = values} ->
       List.iter (fun (_, v) -> self#add v) values
    | DELETE {rows_from = _; rows_where = where} ->
       List.iter (fun (_, v) -> self#add v) where
    | ASSIGN_TABLE (_, t2) ->
       self#add t2
    | _ ->
       super#walkCmd cmd
      
end
  
let read_vars_in_code code system =
  let collector = new read_vars_collector_t system in
  let _ = collector#walkCode code in
  collector#getVars 
  
let expand_structure_assignment s1 s2 =
  let paths = s1#getAllComponents in
  let handle p =
    let v1 = s1#fields p in
    let v2 = s2#fields p in
    if v1#isNumerical then
      ASSIGN_NUM (v1, NUM_VAR v2)
    else if v1#isSymbolic then
      ASSIGN_SYM (v1, SYM_VAR v2)
    else if v1#isArray then
      ASSIGN_ARRAY (v1, v2)
    else if v1#isTable then
      ASSIGN_TABLE (v1, v2)
    else
      raise (CHFailure (LBLOCK [STR "Unexpected field type in structure assignemnt: "; v1#toPretty]))
  in
  List.map handle paths
  
let expand_struct_vars_in_list l =
  let rec expand_var v vars =
    if v#isStruct then
      let paths = v#getAllComponents in
      List.fold_left (fun a p -> expand_var (v#fields p) a) vars paths
    else
      v :: vars
  in
  List.fold_left (fun a v -> expand_var v a) [] l
  
