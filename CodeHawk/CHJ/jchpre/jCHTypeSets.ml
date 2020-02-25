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

(* chlib *)
open CHPretty
open CHCommon
open CHUtils
open CHLanguage

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypesAPI
open JCHBasicTypes

(* jchpre *)
open JCHApplication
open JCHPreAPI

let dbg = ref false 

module TypeCollections = CHCollections.Make
  (struct
     type t = value_type_t 
     let compare = compare_value_types 
     let toPretty = value_type_to_pretty
   end)

(* The numeric types are treated differently so they are distinguished in the type
 * A set of numeric types is encoded as a number while for other types a 
 * TypeCollections.set_t is used
 * The encoding seem to make some operations easier but it is an experiment *)
type t_set_t =
  | SYM_TYPE_SET of TypeCollections.set_t
  | NUM_TYPE_SET of int
  | TOP 
  | BOTTOM
     
(* Encoding for numeric types *) 
let encode_type t = 
  match t with 
  | TBasic Bool -> 1
  | TBasic Byte -> 2
  | TBasic Short -> 4
  | TBasic Char -> 8
  | TBasic Int -> 16
  | TBasic Long -> 32
  | TBasic Float -> 64
  | TBasic Double -> 128
  | _ -> 0

(* A set of numeric types is encoded as a sum of the encodings of each type *)
let encode_num_list list = 
  let add res t = res + (encode_type t) in
  List.fold_left add 0 list 
    
(* Makes a t_set_t from a list of value_type_t list *)
let t_set_from_list list = 
  if list = [] then BOTTOM
  else 
    begin
      match List.hd list with 
      | TBasic Bool 
      | TBasic Byte 
      | TBasic Short
      | TBasic Char 
      | TBasic Int 
      | TBasic Long
      | TBasic Float
      | TBasic Double -> NUM_TYPE_SET (encode_num_list list)
      |	_ -> SYM_TYPE_SET (TypeCollections.set_of_list list) 
    end

(* Decodes from a number to a set of numeric types *)
let decode n = 
  let set = new TypeCollections.set_t in
  if n land 1 <> 0 then set#add (TBasic Bool) ;
  if n land 2 <> 0 then set#add (TBasic Byte) ;
  if n land 4 <> 0 then set#add (TBasic Short) ;
  if n land 8 <> 0 then set#add (TBasic Char) ;
  if n land 16 <> 0 then set#add (TBasic Int) ;
  if n land 32 <> 0 then set#add (TBasic Long) ;
  if n land 64 <> 0 then set#add (TBasic Float) ;
  if n land 128 <> 0 then set#add (TBasic Double) ;
  set

let decode_compact n =
  let set = new TypeCollections.set_t in
  let is_bool = n land 1 <> 0 in
  let is_byte = n land 2 <> 0 in
  let is_short = n land 4 <> 0 in
  let is_char = n land 8 <> 0 in
  let is_int = n land 16 <> 0 in
  (if is_bool && is_byte && is_short && is_char && is_int then 
    set#add (TBasic Int2Bool)
  else 
    begin
      (if is_bool && is_byte then set#add (TBasic ByteBool) 
      else 
	begin 
	  if is_bool then set#add (TBasic Bool) ;
	  if is_byte then set#add (TBasic Byte) 
	end) ;
      if is_short then set#add (TBasic Short) ;
      if is_char then set#add (TBasic Char) ;
      if is_int then set#add (TBasic Int) ;
    end) ;
  if n land 32 <> 0 then set#add (TBasic Long) ;
  if n land 64 <> 0 then set#add (TBasic Float) ;
  if n land 128 <> 0 then set#add (TBasic Double) ;
  set

(* Returns true if cinfo implements cni or an interface which is a subinterface of cni *) 
let rec is_subinterface (cinfo: class_info_int) (cni: class_name_int) = 
  let interfaces = cinfo#get_interfaces in
  let cni_index = cni#index in
  try
    if List.exists (fun i -> i#index = cni_index) interfaces then true
    else 
      let is_sub i = 
        let i_info = app#get_class i in
        is_subinterface i_info cni in
      List.exists is_sub interfaces
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "is-subinterface"
        (LBLOCK [ STR "Finding subinterfaces for " ; cinfo#get_class_name#toPretty ;
                  STR " and " ; cni#toPretty ; STR ": " ; p ]) ;
      raise (JCH_failure
               (LBLOCK [ STR "is-subinterface " ; cinfo#get_class_name#toPretty ;
                         STR " and " ; cni#toPretty ; STR ": " ; p ]))
    end

(* Returns true if cinfo or a superclass of cinfo implements the interface cni *) 
let rec implements_interface (cinfo: class_info_int) (cni: class_name_int) =
  try
    let supra_class_implements_interface () = 
      if cinfo#has_super_class then 
        let cn = cinfo#get_super_class in  
        let cn_info = app#get_class cn in 
        implements_interface cn_info cni 
      else false in
    if cinfo#implements_interface cni then true
    else if supra_class_implements_interface () then
      true
    else 
      let interfaces = cinfo#get_interfaces in
      let is_subinterface_ cn = 
        let cn_info = app#get_class cn in 
        is_subinterface cn_info cni in
      List.exists is_subinterface_ interfaces
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "implements interface"
        (LBLOCK [ STR "Establish implementation relation for " ;
                  cinfo#get_class_name#toPretty ; STR " and " ;
                  cni#toPretty ; STR ": " ; p ]) ;
      raise (JCH_failure
               (LBLOCK [ STR "implements_interface " ; cinfo#get_class_name#toPretty ;
                         STR " and " ; cni#toPretty ; STR ": " ; p ]))
    end
      
(* Returns true is cn1 is a descendant of cn2 or implements cn2 or is a sub-interface *)
let is_subclass cn1 cn2 = 
  try
    if cn1#name = cn2#name then true 
    else if cn2#name = "java.lang.Object" then true
    else if cn1#name = "java.lang.Object" then cn2#name = "java.lang.Object" 
    else if app#is_descendant cn1 cn2 then true
    else if app#is_descendant cn2 cn1 then false
    else
      begin
        let cn1_info = app#get_class cn1 in
        (* Not all classname have a corresponding class *)
        if cn1_info#is_missing then 
	  begin
	    raise (JCH_failure (STR "missing class"))
	  end ;
        if cn1_info#is_interface then 
	  is_subinterface cn1_info cn2
        else 
	  implements_interface cn1_info cn2 
      end
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "is_subclass"
        (LBLOCK [ STR "is-subclass: " ; cn1#toPretty ; STR " and " ; cn2#toPretty ;
                  STR ": " ; p ]) ;
      raise (JCH_failure
               (LBLOCK [ STR "is-subclass: " ; cn1#toPretty ; STR " and " ;
                         cn2#toPretty ; STR ": " ; p ]))
    end


(* Returns true if vtype1 is a descendant of vtype2  or implements vtype2 of 
 * is a sub-interface of vtype2 *)
let rec is_subtype vtype1 vtype2 = 
    match (vtype1, vtype2) with 
    | (TBasic t1, TBasic t2) -> t1 = t2
    | (TObject _, TBasic Object) -> true
    | (TObject (TArray t1), TObject (TArray t2)) -> is_subtype t1 t2
    | (TBasic Object, TObject (TClass cn)) 
    | (TObject (TArray _), TObject (TClass cn)) -> cn#name = "java.lang.Object" 
    | (TObject (TClass cn1), TObject (TClass cn2)) -> is_subclass cn1 cn2 
    | _ -> false


(* Returns true if it is a subtype but not equal *)
(* If one of the classes was not loaded it returns false. *)
let is_strict_subtype vtype1 vtype2 = 
  let is_object vt = 
    match vt with 
    | TBasic Object -> true
    | TObject TClass cn -> cn#name = "java.lang.Object" 
    | _ -> false in
  if compare_value_types vtype1 vtype2 = 0 then false 
  else if is_object vtype1 && is_object vtype2 then false 
  else is_subtype vtype1 vtype2

(* Returns true of the range of numeric type t1 is included in the range of 
 * numeric type t2 *)
let is_int_subtype t1 t2 = 
  match (t1, t2) with 
  | (TBasic Bool, _) -> true
  | (TBasic Byte, TBasic Bool) -> false
  | (TBasic Byte, _) -> true
  | (TBasic Short, TBasic Bool) 
  | (TBasic Short, TBasic Byte)
  | (TBasic Short, TBasic Char) -> false
  | (TBasic Short, _) -> true
  | (TBasic Char, TBasic Bool) 
  | (TBasic Char, TBasic Byte) 
  | (TBasic Char, TBasic Short) -> false
  | (TBasic Char, _) -> true
  | (TBasic Int, TBasic Int) -> true
  | _ -> false 

(* It eliminates from the set the types that are a subtype of another element 
 * in the class *)
let reduce_set set = 
  let t_set = t_set_from_list set#toList in
  match t_set with 
  | SYM_TYPE_SET set -> 
      let new_set = new TypeCollections.set_t in
      let add_type vt = 
	try (* for the case when one of the classes was not loaded *)
	  if List.exists (is_strict_subtype vt) set#toList then ()
	  else new_set#add vt 
	with _ -> new_set#add vt in
      set#iter add_type ;
      SYM_TYPE_SET new_set
  | _ -> t_set

let st_type_set = ref None
let set_st_type_set set = st_type_set := Some set
let get_st_type_set () = Option.get !st_type_set

(* The domain represents sets of types. The empty set = BOTTOM *) 
class type_set_t bottom top num_opt (type_list: value_type_t list) =
  object (self: 'a) 

    val types : t_set_t = 
      if bottom then BOTTOM 
      else if top then TOP 
      else 
	match num_opt with 
	| Some n -> NUM_TYPE_SET n
	| _ -> 
	    if type_list = [] then BOTTOM 
	    else
	      reduce_set (TypeCollections.set_of_list type_list)

    method private get_types = types 
    method private get_st_types = 
      get_st_type_set () 
	
   (* I am not sure what this is for so I will use it to make available internal data *)
    method kind = 
      set_st_type_set types ;
      "?"

    method isBottom = 
      match types with
      | BOTTOM -> true
      | _ -> false

    method isTop = 
      match types with
      | TOP -> true
      | _ -> false 
	
    method equal (s: 'a) =
      let _ = s#kind in
      match (types, self#get_st_types) with
      | (BOTTOM, BOTTOM) -> true
      | (TOP, TOP) -> true
      | (SYM_TYPE_SET s1, SYM_TYPE_SET s2) -> s1#equal s2
      | (NUM_TYPE_SET n1, NUM_TYPE_SET n2) -> n1 = n2
      | _ -> false

    method leq (s: 'a) =
      let _ = s#kind in
      match (types, self#get_st_types) with
      | (BOTTOM, _) -> true
      | (_, TOP) -> true
      | (SYM_TYPE_SET s1, SYM_TYPE_SET s2) -> 
	  if s1#equal s2 then true
	  else
	    let is_sub_list list1 list2 = 
	      try (* for the case when one of the classes was not loaded *)
		List.for_all (fun t1 -> List.exists (fun t2 -> is_subtype t1 t2) list2) list1 
	      with _ -> false in
	    is_sub_list s1#toList s2#toList 
      |	(NUM_TYPE_SET n1, NUM_TYPE_SET n2) -> 
	  n1 <= n2
      | _ -> false

    (* a numeric variable cannot have multiple types so numeric types are 
     * intersected *)	  
    method join (s: 'a) =
      let _ = s#kind in (* store the types *)
      match (types, self#get_st_types) with
      | (BOTTOM, _) -> s
      | (_, BOTTOM) -> {< >}
      | (TOP, _) -> {< >}
      | (_, TOP) -> s
      | (SYM_TYPE_SET s1, SYM_TYPE_SET s2) -> 
	  {< types = reduce_set (s1#union s2) >}
      |	(NUM_TYPE_SET n1, NUM_TYPE_SET n2) -> 
	  {< types = NUM_TYPE_SET (n1 lor n2) >} 
      |	_ -> {< types = TOP >}


    method private get_common_subtypes list1 list2 = 
      let new_set = new TypeCollections.set_t in
      let add list t = 
	try (* for the case when one of the classes was not loaded *)
	  if List.exists (fun t' -> is_subtype t t') list then new_set#add t 
	with _ -> new_set#add t in 
      List.iter (add list2) list1 ;
      List.iter (add list1) list2 ;
      new_set


    method meet (s: 'a) =
      let _ = s#kind in 
      match (types, self#get_st_types) with
      | (BOTTOM, _) -> {< types = BOTTOM >}
      | (_, BOTTOM) -> {< types = BOTTOM >}
      | (TOP, _) -> s
      | (_, TOP) -> {< >}
      | (SYM_TYPE_SET s1, SYM_TYPE_SET s2) -> 
	  let new_set = self#get_common_subtypes s1#toList s2#toList in
	  if new_set#isEmpty then {< types = BOTTOM >} 
	  else {< types = reduce_set new_set >}
      |	(NUM_TYPE_SET n1, NUM_TYPE_SET n2) -> 
	  {< types = NUM_TYPE_SET (n1 land n2) >}
      |	_ -> {< types = BOTTOM >}


    method widening = self#join

    method narrowing = self#meet

    method marshal = 
      match types with
      | BOTTOM -> CHExternalValues.EVX_STRING "_|_"
      | TOP -> CHExternalValues.EVX_STRING "{...}"
      | SYM_TYPE_SET s -> 
	 let strs =
           (List.map (fun t ->
                CHExternalValues.EVX_STRING (value_type_to_string t)) s#toList) in
	  CHExternalValues.EVX_LIST strs 
      |	NUM_TYPE_SET n -> CHExternalValues.EVX_STRING (string_of_int n)


    method toPretty =
      match types with
      | BOTTOM -> STR "_|_"
      | TOP -> STR "{...}"
      | SYM_TYPE_SET s -> LBLOCK [STR "SYM_SET "; s#toPretty]   
      |	NUM_TYPE_SET n -> LBLOCK [STR "NUM_SET "; (decode n)#toPretty] 

  end

let top_type_set = new type_set_t false true None []

let bottom_type_set =  new type_set_t true false None [] 

let mk_type_set ts = new type_set_t false false None ts

let mk_num_type_set n = new type_set_t false false (Some n) [] 

let get_types () = get_st_type_set ()

let int2bool_type_set = new type_set_t false false (Some 31) []
let long2bool_type_set = new type_set_t false false (Some 63) []

(* Takes a list of types, which are supposed to be types of arrays 
   and returns the types for the elements of the array *)
let mk_elem_type_set array_types = 
  let _ = array_types#kind in
  match get_st_type_set () with 
  | SYM_TYPE_SET set -> 
      if set#isEmpty then bottom_type_set 
      else 
	let has_object = ref false in
	let rec add_elem_type res ts =
	  match ts with 
	  | (TObject (TArray vt)) :: rest_ts -> add_elem_type (vt :: res) rest_ts 
	  | (TBasic Object) :: rest_ts -> 
	      has_object := true ;
	      add_elem_type res rest_ts 
	  | (TObject (TClass cn)) :: rest_ts -> 
	      if cn#name = "java.lang.Object" then 
		begin 
		  has_object := true ;
		  add_elem_type res rest_ts 
		end
	      else [] 
	  | [] -> res
	  | _ -> [] in
	let type_list = add_elem_type [] set#toList in
	if type_list = [] then 
	  if !has_object then top_type_set
	  else bottom_type_set 
	else mk_type_set type_list
  | TOP -> top_type_set
  | _ -> bottom_type_set
  
let is_num_type_set set = 
  let _ = set#kind in
  match get_st_type_set () with 
  | NUM_TYPE_SET _ -> true
  | _ -> true

let is_sym_type_set set = 
  let _ = set#kind in
  match get_st_type_set () with 
  | SYM_TYPE_SET _ -> true
  | _ -> true

let get_type_list set = 
  let _ = set#kind in
  match get_st_type_set () with 
  | SYM_TYPE_SET set -> set#toList 
  | NUM_TYPE_SET n -> (decode n)#toList
  | _ -> [] 

let get_type_list_compact set = 
  let _ = set#kind in
  match get_st_type_set () with 
  | SYM_TYPE_SET set -> set#toList 
  | NUM_TYPE_SET n -> (decode_compact n)#toList
  | _ -> [] 

let get_types set = 
  let _ = set#kind in
  get_st_type_set () 

let simple_union_type_sets set1 set2 = 
  match (get_types set1, get_types set2) with 
  | (TOP, _) 
  | (_, TOP) -> top_type_set
  | (BOTTOM, _) -> set2
  | (_, BOTTOM) -> set1
  | (SYM_TYPE_SET tset1, SYM_TYPE_SET tset2) -> 
      begin
	let tset = tset1#clone in
	let add_type t = 
	  if tset1#has t then () else tset#add t in
	tset2#iter add_type ;
	mk_type_set tset#toList 
      end
  | (NUM_TYPE_SET n1, NUM_TYPE_SET n2) -> mk_num_type_set (n1 lor n2)
  | _ -> top_type_set
  
let get_number set = 
  set#kind ;
  match get_st_type_set () with 
  | SYM_TYPE_SET set -> -1
  | NUM_TYPE_SET n -> n
  | _ -> -1
