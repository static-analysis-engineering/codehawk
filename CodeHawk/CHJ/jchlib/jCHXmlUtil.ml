(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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
open CHBounds
open CHIntervals
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary


let make_desc args r = match r with
  | Some ty -> make_method_descriptor ~arguments:args ~return_value:ty ()
  | _ -> make_method_descriptor ~arguments:args ()

let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end

(* ----------------------------------------------------------------- Indices *)

let write_xml_indices (node:xml_element_int) (indices:int list) =
  let indices = List.sort Stdlib.compare indices in
  let maxlen = 20 in
    let split (n:int) (l:int list) =
      let rec loop i p l =
	if i = n then 
	  (List.rev p,l)
	else loop (i+1) ((List.hd l)::p) (List.tl l) in
      if (List.length l) <= n then (l,[]) else loop 0 [] l in
    let make_string l = String.concat "," (List.map string_of_int l) in
    let rec make_strings l result =
      let llen = List.length l in
      if llen <= maxlen then
	List.rev ((make_string l) :: result)
      else
	let (lpre,lsuf) = split maxlen l in
	(make_strings lsuf ((make_string lpre) :: result)) in
    if (List.length indices) > 0 then
      let ixstrings = make_strings indices [] in
      match ixstrings with 
      | [] -> () 
      | [ s ] -> node#setAttribute "ixs" s ;
      | l ->
	node#appendChildren (List.map (fun s ->
	  let iNode = xmlElement "ix-list" in
	  begin iNode#setAttribute "ixs" s ; iNode end) l)
    else
      node#setIntAttribute "size" 0

let nsplit (separator:char) (s:string):string list =
  let result = ref [] in
  let len = String.length s in
  let start = ref 0 in
  try
    begin
      while !start < len do
        let s_index =
          try String.index_from s !start separator with Not_found -> len in
        let substring = String.sub s !start (s_index - !start) in
        begin
	  result := substring :: !result ;
	  start := s_index + 1
        end 
      done;
      !result
    end
  with
  | Invalid_argument _ ->
     raise (JCH_failure (LBLOCK [STR "Error in nsplit: "; STR s]))


let read_xml_indices (node:xml_element_int) =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  let getcc = node#getTaggedChildren in
  let get_indices s = List.map int_of_string (nsplit ',' s) in
  if has "ixs" then 
    get_indices (get "ixs")
  else
    let strings =
      List.map (fun iNode -> iNode#getAttribute "ixs") (getcc "ix-list") in
    get_indices (String.concat "," strings)

(* --------------------------------------------------------------- variable_t *)

let chvariable_type_to_string (vt:variable_type_t) = 
  match vt with
  | NUM_LOOP_COUNTER_TYPE -> "NUM_LOOP_COUNTER"
  | NUM_TMP_VAR_TYPE -> "T_NUMERICAL"
  | SYM_TMP_VAR_TYPE -> "T_SYMBOLIC"
  | NUM_TMP_ARRAY_TYPE -> "T_NUMERICAL[]"
  | SYM_TMP_ARRAY_TYPE -> "T_SYMBOLIC[]"
  | NUM_VAR_TYPE -> "NUMERICAL"
  | SYM_VAR_TYPE -> "SYMBOLIC"
  | NUM_ARRAY_TYPE -> "NUMERICAL[]"
  | SYM_ARRAY_TYPE -> "SYMBOLIC[]"
  | _ ->
     raise
       (JCH_failure (
            STR "struct and table type not supported in saving to xml"))


let string_to_chvariable_type (s:string) =
  match s with
  | "NUM_LOOP_COUNTER" -> NUM_LOOP_COUNTER_TYPE
  | "T_NUMERICAL" -> NUM_TMP_VAR_TYPE
  | "T_SYMBOLIC" -> SYM_TMP_VAR_TYPE
  | "T_NUMERICAL[]" -> NUM_TMP_ARRAY_TYPE
  | "T_SYMBOLIC[]" -> SYM_TMP_ARRAY_TYPE
  | "NUMERICAL" -> NUM_VAR_TYPE
  | "SYMBOLIC" -> SYM_VAR_TYPE
  | "NUMERICAL[]" -> NUM_ARRAY_TYPE
  | "SYMBOLIC[]" -> SYM_ARRAY_TYPE
  | s ->
     raise
       (JCH_failure
          (LBLOCK [STR "Not a valid CH variable type: "; STR s]))


let write_xml_variable (node:xml_element_int) (var:variable_t) =
  let set = node#setAttribute in
  begin
    (match var#getName#getAttributes with [] -> () | atts ->
      node#appendChildren (List.map (fun att ->
	let anode = xmlElement "attr" in
	begin anode#setAttribute "v" att ; anode end) atts) ) ;
    set "vn" var#getName#getBaseName ;
    set "vt" (chvariable_type_to_string var#getType) ;
  end

let read_xml_variable (node:xml_element_int):variable_t =
  let get = node#getAttribute in
  let getcc = node#getTaggedChildren in
  let name = get "vn" in
  let vtype = string_to_chvariable_type (get "vt") in
  let atts = List.map (fun anode -> anode#getAttribute "v") (getcc "attr") in
  let sym = new symbol_t ~atts name in
  new variable_t sym vtype

(* -------------------------------------------------------- ASM representation *)

let basic_type_to_asm_string (t:java_basic_type_t) =
  match t with
  | Int -> "I"
  | Short -> "S"
  | Char -> "C"
  | Byte -> "B"
  | Bool -> "Z"
  | Long -> "J"
  | Float -> "F"
  | Double -> "D"
  | Int2Bool -> "XIZX"
  | ByteBool -> "XBZX"
  | Object -> "XLX"
  | Void -> "V"


let rec value_type_to_asm_string (v:value_type_t) =
  match v with
  | TBasic t -> basic_type_to_asm_string t
  | TObject t -> object_type_to_asm_string t
    
and object_type_to_asm_string (v:object_type_t) =
  match v with
  | TClass cn -> "L" ^ (string_replace '.' "/" cn#name) ^ ";"
  | TArray vt -> "[" ^ (value_type_to_asm_string vt)

let rec value_type_to_asm_cnix_string (v:value_type_t) =
  match v with
  | TBasic t -> basic_type_to_asm_string t
  | TObject t -> object_type_to_asm_cnix_string t

and object_type_to_asm_cnix_string (v:object_type_t) =
  match v with
  | TClass cn -> "L" ^ (string_of_int cn#index) ^ ";"
  | TArray vt -> "[" ^ (value_type_to_asm_cnix_string vt)
    
let method_arguments_to_asm_string (ms:method_signature_int) =
  String.concat "_" (List.map value_type_to_asm_string ms#descriptor#arguments)

(* ----------------------------------------------------------------- Constants *)

let max_string_size = 1000

let p2s = string_printer#print

let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l
    
let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done ;
    !h
  end
    
let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c -> 
    if !found then
      ()
    else if Char.code c = 10 then      (* NL *)
      ()
    else if (Char.code c) < 32 || (Char.code c) > 126 then 
      found  := true) s in
  !found

let replace_control_characters s =
  String.map (fun c ->
      if (Char.code c) < 32 || (Char.code c) > 126 then
        'x'
      else
        c) s

let write_xml_constant_string (node:xml_element_int) (tag:string) (s:string) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let len = String.length s in
  let toolong = len > max_string_size in
  let hasx = has_control_characters s in
  match (toolong,hasx) with
  | (false,false) -> set tag s
  | (false,true) -> set (tag ^ "x") (hex_string s)
  | (true,false) -> seti (tag ^ "_len") len 
  | (true,true) -> seti (tag ^ "_lenx") len

(* --------------------------------------------------------------- Xml basic types *)   


let write_xml_asm_parameter (node:xml_element_int) (index:int) (v:value_type_t) =
  begin
    node#setIntAttribute "nr" index ;
    node#setAttribute "type" (value_type_to_asm_string v)
  end

let write_xml_asm_method_signature
      (node:xml_element_int) (ms:method_signature_int) =
  let append = node#appendChildren in
  begin
    append (List.mapi (fun i a ->
      let aNode = xmlElement "arg" in
      begin
        write_xml_asm_parameter aNode (i+1) a;
        aNode
      end) ms#descriptor#arguments) ;
    match ms#descriptor#return_value with
      Some v -> 
	let rNode = xmlElement "return" in
	begin
	  rNode#setAttribute "type" (value_type_to_asm_string v) ;
	  append [ rNode ]
	end
    | _ -> () 
  end

let write_xml_asm_value_types (node:xml_element_int) (types:value_type_t list) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  match types with
  | [] -> ()
  | [ t ] -> set "type" (value_type_to_asm_string t)
  | l ->
     let lNode = xmlElement "types" in
     begin
       lNode#appendChildren
	 (List.map (fun t ->
	      let tNode = xmlElement "type" in
	      let set = tNode#setAttribute in
	      begin set "type" (value_type_to_asm_string t); tNode end) l);
       append [ lNode ]
     end

let write_xml_asm_cnix_value_types
      (node:xml_element_int) (types:value_type_t list) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  match types with
  | [] -> ()
  | [ t ] -> set "ty" (value_type_to_asm_cnix_string t)
  | l ->
     let lNode = xmlElement "types" in
     begin
       lNode#appendChildren
	 (List.map (fun t ->
	      let tNode = xmlElement "type" in
	      let set = tNode#setAttribute in
	      begin set "type" (value_type_to_asm_cnix_string t); tNode end) l);
       append [ lNode ]
     end
 				
let write_xml_interval (node:xml_element_int) (i:interval_t) =
  if i#isBottom then
    node#setAttribute "bottom" "true"
  else if i#isTop then
    node#setAttribute "top" "true"
  else match i#singleton with
  | Some n -> node#setPrettyAttribute "value" n#toPretty
  | _ ->
    begin
      (match i#getMin#getBound with
      | MINUS_INF -> ()
      | PLUS_INF -> node#setAttribute "lb" "plus-inf"
      | NUMBER n -> node#setPrettyAttribute "lb" n#toPretty);
      (match i#getMax#getBound with
      | MINUS_INF -> node#setAttribute "ub" "minus-inf"
      | PLUS_INF -> ()
      | NUMBER n -> node#setPrettyAttribute "ub" n#toPretty)
    end
