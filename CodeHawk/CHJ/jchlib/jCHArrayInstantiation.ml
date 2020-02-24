(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet
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

(* chlib *)
open CHAtlas
open CHCollections
open CHIterator   
open CHLanguage
open CHNonRelationalDomainValues   
open CHNumerical
open CHPretty
open CHStack
open CHSymbolicSets   
open CHSymbolicSetsDomainNoArrays   
open CHSymbolicTypeRefinement   
open CHUtils

(* jchlib *)
open JCHBasicTypes

module F = CHOnlineCodeSet.LanguageFactory

let dummy_sym = new symbol_t "_"

type type_attribute_t =
  | UNKNOWN_TYPE_ATTRIBUTE
  | NUM_ARRAY_TYPE_ATTRIBUTE

let isNumType (t: string) =
  match t with
    | "int"
    | "short"
    | "char"
    | "byte"
    | "bool"
    | "long"
    | "float"
    | "double"
    | "Int2Bool"
    | "ByteBool" -> true
    | _ -> false

let isInvokeOperation (o: operation_t) =
  match o.op_name#getBaseName with
    | "OpInvokeStatic"
    | "OpInvokeSpecial"
    | "OpInvokeInterface"
    | "OpInvokeVirtual" -> true
    | _ -> false

let isFieldOperation (o: operation_t) =
  match o.op_name#getBaseName with
    | "OpGetField"
    | "OpPutField"
    | "OpPutStatic"
    | "OpGetStatic" -> true
    | _ -> false
      
let isScalarOpNewArray (o: operation_t) =
  let s = o.op_name in
  match (s#getBaseName, s#getAttributes) with
    | ("OpNewArray", _ :: t :: _) when isNumType t -> true
    | _ -> false

let isScalarOpArrayLoadOperation (o: operation_t) =
  let s = o.op_name in
  match (s#getBaseName, s#getAttributes) with
    | ("OpArrayLoad", t :: _) when isNumType t -> true
    | _ -> false

let isScalarOpArrayStoreOperation (o: operation_t) =
  let s = o.op_name in
  match (s#getBaseName, s#getAttributes) with
    | ("OpArrayStore", t :: _) when isNumType t -> true
    | _ -> false

let isArraycopyOperation (o: operation_t) =
  let s = o.op_name in
  s#getBaseName = "OpInvokeStatic"
  && match s#getAttributes with
    | "java.lang.System" :: "arraycopy" :: _ -> true
    | _ -> false
      
let getOpNewArrayArgs (o: operation_t) =
  try
    let (_, r, _) = List.find (fun (s, _, _) -> s = "ref") o.op_args in
    let (_, l, _) = List.find (fun (s, _, _) -> s = "length") o.op_args in
    (r, l)
  with _ ->
    raise (JCH_failure
             (STR "Array instantiation: malformed operation OpNewArray"))   

let getOpArrayLength (o: operation_t) =
  try
    let (_, r, _) = List.find (fun (s, _, _) -> s = "ref") o.op_args in
    let (_, v, _) = List.find (fun (s, _, _) -> s = "val") o.op_args in
    (r, v)
  with _ ->
    raise (JCH_failure
             (STR "Array instantiation: malformed operation OpArrayLength"))

let getOpArrayAccessArgs (o: operation_t) =
  try
    let (_, a, _) = List.find (fun (s, _, _) -> s = "array") o.op_args in
    let (_, i, _) = List.find (fun (s, _, _) -> s = "index") o.op_args in
    let (_, v, _) = List.find (fun (s, _, _) -> s = "val") o.op_args in
    (a, i, v)
  with _ ->
    raise (JCH_failure
             (STR "Array instantiation: malformed array access operation"))      
    
let getSystemArraycopyArgs (o: operation_t) =
  try
    let (_, src, _) = List.find (fun (s, _, _) -> s = "arg0") o.op_args in
    let (_, src_o, _) = List.find (fun (s, _, _) -> s = "arg1") o.op_args in
    let (_, tgt, _) = List.find (fun (s, _, _) -> s = "arg2") o.op_args in
    let (_, tgt_o, _) = List.find (fun (s, _, _) -> s = "arg3") o.op_args in
    let (_, n, _) = List.find (fun (s, _, _) -> s = "arg4") o.op_args in
    (src, src_o, tgt, tgt_o, n)
  with _ ->
    raise (JCH_failure
             (STR "Array instantiation: call to System.arraycopy has incorrect signature"))      

class array_type_refinement_t (proc: procedure_int) =
  let length_field = new symbol_t "length" in
  let elements_field = new symbol_t "elements" in
  let array_type =
    STRUCT_TYPE [(length_field, NUM_VAR_TYPE); (elements_field, NUM_ARRAY_TYPE)] in
  object (self: _)
  
  inherit [type_attribute_t] symbolic_type_refinement_t
    
  val new_array_sym = new symbol_t "OpNewArray"
  val array_load_sym = new symbol_t "OpArrayLoad"
  val array_store_sym = new symbol_t "OpArrayStore"
  val array_length_sym = new symbol_t "OpArrayLength"
  val arraycopy_sym = new symbol_t "System.Arraycopy"

  method mergeAttributes a b =
    match (a, b) with
      | (UNKNOWN_TYPE_ATTRIBUTE, _) -> UNKNOWN_TYPE_ATTRIBUTE
      | (_, UNKNOWN_TYPE_ATTRIBUTE) -> UNKNOWN_TYPE_ATTRIBUTE
      | _ -> NUM_ARRAY_TYPE_ATTRIBUTE

  method abstract v = self#set v UNKNOWN_TYPE_ATTRIBUTE
    
  method analyzeOperation (o: operation_t) =
    if isScalarOpNewArray o then
      let (r, _) = getOpNewArrayArgs o in
      self#set r NUM_ARRAY_TYPE_ATTRIBUTE
    else if (isInvokeOperation o && not(isArraycopyOperation o)) || isFieldOperation o then
      List.iter (fun (_, v, _) -> 
	if v#isSymbolic then
	  self#abstract v
	else
	  ()
      ) o.op_args
    else
      ()
	
  method refineSymbolicType a =
    match a with
      | NUM_ARRAY_TYPE_ATTRIBUTE -> array_type
      | UNKNOWN_TYPE_ATTRIBUTE -> SYM_VAR_TYPE

  method op_semantics
           ~(invariant: atlas_t)
           ~(stable: bool) ~(fwd_direction: bool)
           ~(context: symbol_t stack_t)
           ~(operation: operation_t) =
    if isScalarOpNewArray operation then
      let (r, _) = getOpNewArrayArgs operation in
      let inv' = invariant#analyzeFwd (ASSIGN_SYM (r, SYM operation.op_name)) in
      inv'
    else
      invariant
	
  method getArrayRefs (v: variable_t) (invariant: atlas_t) =
    match ((invariant#getDomain "symbolic sets")#getNonRelationalValue v)#getValue with
      | SYM_SET_VAL sym_set ->
	begin
	  match sym_set#getSymbols with
	    | SET refs -> List.map (fun s -> new variable_t s array_type) refs#toList
	    | _ -> []
	end
      | _ ->
	[]

  method transformer
           ~(invariant: atlas_t)
           ~(context: symbol_t stack_t)
           ~(cmd: (code_int, cfg_int) command_t) =
    match cmd with
      | OPERATION operation ->
	begin
	  if isScalarOpNewArray operation then
	    let (r, l) = getOpNewArrayArgs operation in
	    begin
	      match self#get r with
		| Some NUM_ARRAY_TYPE_ATTRIBUTE ->
		  let scope = proc#getScope in
		  let array_variable = new variable_t operation.op_name array_type in
		  let _ = scope#addVariable array_variable in
		  let _ = scope#startTransaction in
		  let start_i = scope#requestNumTmpVariable in
		  let len = scope#requestNumTmpVariable in
		  let value = scope#requestNumTmpVariable in
		  let _ = scope#endTransaction in
		  TRANSACTION
                    (new_array_sym, 
		     F.mkCode [ASSIGN_NUM (array_variable#field length_field, NUM_VAR l);
			       ASSIGN_NUM (start_i, NUM numerical_zero);
			       ASSIGN_NUM (len, NUM_VAR l);
			       ASSIGN_NUM (value, NUM numerical_zero);
			       SET_ARRAY_ELTS (array_variable#field elements_field, start_i, len, value)
			      ],
		     None)
		| _ -> cmd
	    end
	  else if isScalarOpArrayLoadOperation operation then
	    let (a, i, v) = getOpArrayAccessArgs operation in
	    begin
	      match self#get a with
	      | Some NUM_ARRAY_TYPE_ATTRIBUTE ->
		 let array_refs = self#getArrayRefs a invariant in
		 begin
		   match array_refs with
		   | [] -> ABSTRACT_VARS [v]
		   | _ ->  
		      begin
			match List.map (fun r -> F.mkCode [READ_NUM_ELT (v, r#field elements_field, i)]) array_refs with
			| [c] -> CODE (array_load_sym, c)
			| _ as l -> BRANCH l
		      end
		 end
	      | _ -> cmd
	    end
	  else if isScalarOpArrayStoreOperation operation then
	    let (a, i, v) = getOpArrayAccessArgs operation in
	    begin
	      match self#get a with
	      | Some NUM_ARRAY_TYPE_ATTRIBUTE ->
		 let array_refs = self#getArrayRefs a invariant in
		 begin
		   match array_refs with
		   | [] -> SKIP
		   | _ ->  
		      begin
			match List.map (fun r -> F.mkCode [ASSIGN_NUM_ELT (r#field elements_field, i, v)]) array_refs with
			| [c] -> CODE (array_store_sym, c)
			| _ as l -> BRANCH l
		      end
		 end
	      | _ -> cmd
	    end
	  else if operation.op_name#getBaseName = "OpArrayLength" then
	    let (a, v) = getOpArrayLength operation in
	    begin
	      match self#get a with
	      | Some NUM_ARRAY_TYPE_ATTRIBUTE ->
		 let array_refs = self#getArrayRefs a invariant in
		 begin
		   match array_refs with
		   | [] -> ABSTRACT_VARS [v]
		   | _ ->  
		      begin
			match List.map (fun r -> F.mkCode [ASSIGN_NUM (v, NUM_VAR (r#field length_field))]) array_refs with
			| [c] -> CODE (array_length_sym, c)
			| _ as l -> BRANCH l
		      end
		 end
	      | _ -> cmd
	    end
	  else if isArraycopyOperation operation then
	    let (src, src_o, tgt, tgt_o, n) = getSystemArraycopyArgs operation in
	    match (self#get src, self#get tgt) with
	    | (Some NUM_ARRAY_TYPE_ATTRIBUTE, Some NUM_ARRAY_TYPE_ATTRIBUTE) ->
	       let src_refs = self#getArrayRefs src invariant in
	       let tgt_refs = self#getArrayRefs tgt invariant in
	       let code = List.fold_left (fun a src_r ->
		  List.fold_left (fun a' tgt_r ->
		      BLIT_ARRAYS (tgt_r#field elements_field, tgt_o, src_r#field elements_field, src_o, n) :: a'
		    ) a tgt_refs
		            ) [] src_refs
	       in
	       CODE (arraycopy_sym, F.mkCode code)
	    | _ ->
	       cmd
	  else
	    cmd
	end
      | ASSIGN_SYM (x, SYM_VAR y) ->
	 begin
	   match self#get x with
	   | Some NUM_ARRAY_TYPE_ATTRIBUTE -> SKIP
	   | _ -> cmd
	 end
      | _ -> cmd
	   
  end
  
class array_instantiator_t (code_set: system_int) =
object (self: _)
     
  method transform_procedure (proc: procedure_int) =
    let refinement = new array_type_refinement_t proc in
    let _ = refinement#analyzeProcedure proc in
    let strategy = {widening = (fun _ -> (true, "")); narrowing = (fun _ -> true)} in
    let iterator =
      new iterator_t
          ~do_loop_counters:false
          ~strategy:strategy
          ~op_semantics:refinement#op_semantics code_set
          ~cmd_processor:refinement#transformer in
    let init = new atlas_t [("symbolic sets", new symbolic_sets_domain_no_arrays_t)] in
    let _ =
      iterator#runFwd
        ~domains:["symbolic sets"]
        ~atlas:init (CODE (dummy_sym, proc#getBody)) in
    ()

end
