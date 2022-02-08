(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(** Utilities to build xml files *)

open Unix

(* chlib *)
open CHBounds   
open CHIntervals
open CHMaps   
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil   
open CHUtil
   
module H = Hashtbl


exception XmlDocumentError of int * int * pretty_t

type doc_spec_t = {
  namespaceURI : string;
  xsi: string;
  schema : string
}

type attribute_format_t = 
| FANL
| FAttr of string
| FAttrL of string * int   (* minimum length *)

type attribute_format_list_t = attribute_format_t list

let attribute_formats = Hashtbl.create 3

let set_attribute_format (element_name:string) (format: attribute_format_list_t) =
	H.add attribute_formats element_name format

let has_attribute_format (element_name:string) = H.mem attribute_formats element_name

let get_attribute_format (element_name:string) =
  try
    H.find attribute_formats element_name
  with
    Not_found -> []

(* Standard header of an xml file *)
let doc_spec = {
  namespaceURI = "http://api.codehawk.kt.com/OutputSchema";
  xsi = "http://www.w3.org/2001/XMLSchema-instance" ;
  schema ="http://api.codehawk.kt.com/OutputSchema OutputSchema2.xsd "
}

let indent = 2

(* -----------------------------------------------------------------------------
   String utilities
   ----------------------------------------------------------------------------- *)

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
  let _ = String.iter (fun c -> if (Char.code c) < 32 || (Char.code c) > 126 then 
      found  := true) s in
  !found

let replace_lst = [ ('&', "&amp;") ; ('<',"&lt;")  ; ('>',"&gt;") ;
		    ('"',"&quot;") ; ('\'',"&apos;") ; (char_of_int 0, "NULL") ]

let replace = string_replace

(* Replace xml-objectionable characters with standard replacement strings;
   Replace strings with non-printable characters with hex strings            *)
let sanitize (s:string):string =
(*  let s = if has_control_characters s then "__xx__" ^ (hex_string s) else s in *)
  List.fold_left (fun sa (c,r) -> replace c r sa) s replace_lst
(*  let s = List.fold_left (fun sa (c,r) -> replace c r sa) s replace_lst in
	UTF8.to_string (UTF8.of_string s) *)

(* Replace xml-objectional characters with standard replacement strings *)
let rec sanitize_pretty (p:pretty_t):pretty_t = 
  match p with
    STR s -> STR (sanitize s)
  | LBLOCK l -> LBLOCK (List.map (fun p -> sanitize_pretty p) l)
  | INDENT (n,p) -> INDENT (n, sanitize_pretty p)
  | _ -> p

(* Convert standard Unix time representation to a string *)
let time_to_string (f:float):string = 
  let tm = Unix.localtime f in
  let sp ip = if ip < 10 then LBLOCK [ STR "0" ; INT ip ] else INT ip in
  let p = LBLOCK [ sp (tm.tm_year + 1900) ; STR "-" ; sp (tm.tm_mon + 1) ;
                   STR "-" ; sp tm.tm_mday ; STR " " ;
                   sp tm.tm_hour ; STR ":" ;
                   sp tm.tm_min ; STR ":" ;
                   sp tm.tm_sec ] in
(*  let p = LBLOCK [ sp (tm.tm_mon + 1) ; STR "/" ; sp tm.tm_mday ; 
		   STR "/" ; sp (tm.tm_year + 1900) ;
		   STR " " ; sp tm.tm_hour ; 
		   STR ":" ; sp tm.tm_min ; 
		   STR ":" ; sp tm.tm_sec ] in *)
  pretty_to_string p

let current_time_to_string ():string = time_to_string (Unix.gettimeofday ())

let stri (i:int):string = string_of_int i
let bool_to_string (b:bool):string = if b then "true" else "false"


(* -------------------------------------------------------------------------------
   Node creation
   ------------------------------------------------------------------------------- *)

class type xml_element_int =
object ('a)

  (* setters *)
  method appendChildren: 'a list -> unit
  method setText: string -> unit
  method setNameString: string -> unit
  method setGroupString: string -> unit
  method setAttribute: string -> string -> unit
  method setIntAttribute: string -> int -> unit
  method setIntListAttribute: string -> int list -> unit
  method setPrettyAttribute: string -> pretty_t -> unit
  method setYesNoAttribute: string -> bool -> unit
  method setBoolAttribute: string -> bool -> unit
  method setLineNumber: int -> unit
  method setColumnNumber: int -> unit

  (* accessors *)
  method getTag: string
  method getChild: 'a
  method getTaggedChild: string -> 'a 
  method getChildren: 'a list
  method getTaggedChildren: string -> 'a list
  method getAttribute: string -> string
  method getIntAttribute: string -> int
  method getIntListAttribute: string -> int list
  method getYesNoAttribute: string -> bool
  method getBoolAttribute: string -> bool
  method getDefaultAttribute: string -> string -> string
  method getDefaultIntAttribute: string -> int -> int
  method getOptAttribute: string -> string option
  method getOptIntAttribute: string -> int option
  method getText: string
  method getLineNumber: int
  method getColumnNumber: int

  (* predicates *)
  method hasOneChild: bool
  method hasChildren: bool
  method hasOneTaggedChild: string -> bool
  method hasTaggedChildren: string -> bool
  method hasAttributes: bool
  method hasNamedAttribute: string -> bool
  method hasText: bool
  method isEmpty: bool

  (* printing *)
  method toPretty: pretty_t
end

class type xml_document_int =
object
  method setNode: xml_element_int -> unit
  method getRoot: xml_element_int
  method toPretty: pretty_t
end

let raise_error line col msg =
  let fullMsg = LBLOCK [ STR "(" ; INT line ; STR "," ; INT col ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml document error" fullMsg ;
    raise (XmlDocumentError (line,col,msg))
  end

class xml_element_t (tag:string):xml_element_int =
object (self: 'a)
  val tag = tag
  val mutable children:'a list = []
  val mutable text: string option = None
  val mutable attributes = StringMap.empty
  val mutable line_number = 0
  val mutable column_number = 0
  val mutable namestring = None
  val mutable groupstring = None

  method private raise_error msg =
    let fullMsg = LBLOCK [ STR "(" ; INT self#getLineNumber ; STR "," ;
                           INT self#getColumnNumber ; 
			   STR ")" ; msg ] in
    begin
      ch_error_log#add "xml document error" fullMsg ;
      raise (XmlDocumentError(self#getLineNumber, self#getColumnNumber, msg))
    end

  method setLineNumber (n:int) = line_number <- n
  method setColumnNumber (n:int) = column_number <- n

  method getLineNumber = line_number
  method getColumnNumber = column_number

  method hasOneChild = match children with [c] -> true | _ -> false
  method hasChildren = match children with [] -> false | _ -> true

  method hasOneTaggedChild (childtag:string) =
    match (List.filter (fun n -> n#getTag = childtag) children) with
      [c] -> true
    | _ -> false

  method hasTaggedChildren (childtag:string) =
    match (List.filter (fun n -> n#getTag = childtag) children) with
      [] -> false
    | _ -> true

  method hasAttributes = not (StringMap.is_empty attributes)

  method hasNamedAttribute (attname:string) =
    match StringMap.get attname attributes with
      Some _ -> true
    | _ -> false

  method isEmpty = not (self#hasChildren || self#hasAttributes)

  method hasText = match text with Some _ -> true | _ -> false

  method getText:string =
    match text with
      Some s -> s
    | _ ->
      raise_error self#getLineNumber self#getColumnNumber
	(LBLOCK [ STR "Element " ; STR tag ; STR " does not have text" ])

  method getTag:string = tag

  method getChild:'a =
    match children with
    | [] -> raise_error self#getLineNumber self#getColumnNumber
	                (LBLOCK [ STR "Element " ;
                                  STR tag ; STR " does not have any children " ])
    | [c] -> c
    | _ ->
       raise_error
         self#getLineNumber self#getColumnNumber
         (LBLOCK [ STR "Element " ; STR tag ; STR " has more than one child "])

  method getTaggedChild (childtag:string):'a =
    let tagged_children = self#getTaggedChildren childtag in
    match tagged_children with
    | [] ->
       raise_error
         self#getLineNumber self#getColumnNumber 
	 (LBLOCK [
              STR "Element ";
              STR tag;
              STR " does not have any children with tag ";
	      STR childtag;
	      pretty_print_list children (fun c -> STR c#getTag) " [" "," "]"])
    | [c] -> c
    | _ ->
       raise_error
         self#getLineNumber
         self#getColumnNumber
         (LBLOCK [
              STR "Element ";
              STR tag;
              STR " has multiple children with tag ";
              STR childtag])

  method getTaggedChildren (childtag:string):'a list =
    List.filter (fun n -> (n#getTag = childtag)) children

  method getChildren: 'a list = children

  method getAttribute (attribute_tag:string):string =
    match StringMap.get attribute_tag attributes with
    | Some s -> s
    | _ ->
       raise_error
         self#getLineNumber self#getColumnNumber
	 (LBLOCK [
              STR "Element ";
              STR tag;
              STR " does not have an attribute ";
	      STR attribute_tag])

  method getIntAttribute (attribute_tag:string):int =
    let attribute = self#getAttribute attribute_tag in
    try
      int_of_string attribute
    with
    | Failure _
    | Invalid_argument _ ->
       raise_error
         self#getLineNumber self#getColumnNumber
	 (LBLOCK [
              STR "Element ";
              STR tag;
              STR " attribute ";
              STR attribute_tag;
	      STR " is not an integer (value: ";
              STR attribute ; STR ")"])

  (* Return a list of integers or an empty list if the tag is not present. *)
  method getIntListAttribute (attribute_tag: string): int list =
    if self#hasNamedAttribute attribute_tag then
      let attribute = self#getAttribute attribute_tag in
      try
        let slist = string_nsplit ',' attribute in
        List.map int_of_string slist
      with
      | Failure _
        | Invalid_argument _ ->
         raise_error
           self#getLineNumber
           self#getColumnNumber
           (LBLOCK [
                STR "Element ";
                STR tag;
                STR " attribute ";
                STR attribute_tag;
                STR " is not a list of integers (value: ";
                STR attribute;
                STR ")"])
    else
      []

  method getYesNoAttribute (attribute_tag:string):bool =
    try
      let attr_value = self#getAttribute attribute_tag in
      match attr_value with
      | "yes" -> true
      | "no"  -> false
      | _ ->
	 raise_error
           self#getLineNumber self#getColumnNumber
	   (LBLOCK [ STR "Attribute " ; STR attribute_tag ; STR " of element " ; 
		     STR tag ; STR " has value " ; STR attr_value ;
                     STR " (expected yes/no)" ])
    with
    | XmlDocumentError _ -> false

  method getBoolAttribute (attribute_tag:string):bool =
    let attrValue = self#getAttribute attribute_tag in
    match attrValue with
    | "true" -> true
    | "false" -> false
    | _ ->
       raise_error
         self#getLineNumber self#getColumnNumber
	 (LBLOCK [ STR "Attribute " ; STR attribute_tag ; STR " of element " ; 
		   STR tag ; STR " has value " ; STR attrValue ;
                   STR " (expected yes/no)" ])
      
  method getDefaultAttribute (attribute_tag:string) (default_value:string):string =
    if self#hasNamedAttribute attribute_tag then
      self#getAttribute attribute_tag 
    else
      default_value
    
  method getDefaultIntAttribute (attribute_tag:string) (default_value:int):int =
    try
      if self#hasNamedAttribute attribute_tag then
	self#getIntAttribute attribute_tag
      else
	default_value
    with
    | XmlDocumentError _ -> default_value
	                  
  method getOptAttribute (attribute_tag:string):string option =
    if self#hasNamedAttribute attribute_tag then
      Some (self#getAttribute attribute_tag)
    else
      None
    
  method getOptIntAttribute (attribute_tag:string):int option =
    try
      if self#hasNamedAttribute attribute_tag then
	Some (self#getIntAttribute attribute_tag)
      else
	None
    with
    | XmlDocumentError _ -> None
	                      
  method setText (s:string) =
    match children with
    | [] -> text <- Some s
    | _ ->
       failwith "Cannot set text on element with child nodes\n"
      
  method appendChildren (cl:'a list) = 
    match text with
    | None -> children <- children @ cl
    | Some t ->
       failwith ("Cannot append childnodes to element with text data: " ^ t)
      
  method setAttribute (attr:string) (attr_value:string) =
    attributes <- StringMap.add attr attr_value attributes  
    
  method setIntAttribute (attr:string) (attr_value:int) =
    self#setAttribute attr (string_of_int attr_value)

  (* only set the attribute if the list is non-empty *)
  method setIntListAttribute (attr: string) (attr_value: int list) =
    match attr_value with
    | [] -> ()
    | l ->
       let slist = String.concat "," (List.map string_of_int l) in
       self#setAttribute attr slist
    
  method setPrettyAttribute (attr:string) (attr_value:pretty_t) =
    self#setAttribute attr (string_printer#print attr_value)
    
  method setYesNoAttribute (attr:string) (b:bool) =
    self#setAttribute attr (if b then "yes" else "no")
    
  method setBoolAttribute (attr:string) (b:bool) =
    self#setAttribute attr (if b then "true" else "false")
    
  method setNameString (s:string) = namestring <- Some s
                                  
  method setGroupString (s:string) = groupstring <- Some s
                                   
  method private attributes_to_pretty:pretty_t = 
    let numAtts = List.length (StringMap.listOfPairs attributes) in
    let atts = ref [] in
    let pp = ref [] in
    let attr k v = LBLOCK [ STR " " ; STR (sanitize k) ; STR "=" ; STR "\"" ; 
			    STR (sanitize v) ; STR "\"" ] in
    let len_attr k v len =  fixed_length_pretty (attr k v) len in
    let _ =
      if has_attribute_format tag then
	let format = get_attribute_format tag in
	let _ =
          List.iter (fun f ->
	      match f with
	      | FANL ->
                 pp := (fixed_length_pretty (STR " ") ((String.length tag)+1)) :: NL :: !pp
	      | FAttr k -> 
	         begin
	           match StringMap.get k attributes with 
	           | Some v -> begin atts := k :: !atts ; pp := (attr k v) :: !pp end
	           | _ -> ()
	         end
	      | FAttrL (k,len) ->
	         begin
	           match StringMap.get k attributes with
	           | Some v -> begin atts := k :: !atts ; pp := len_attr k v len :: !pp end
	           | _ -> ()
	         end) format in
	match !pp with 
	| [ NL ] -> pp := [] 
	| _ :: NL :: tl when (List.length !atts) = numAtts -> pp := tl
	| _ -> () in
    StringMap.fold 
      (fun k v a -> 
	if List.mem k !atts then a else
	  LBLOCK [ a ; attr k v ]) attributes (LBLOCK (List.rev !pp))
    
  method toPretty:pretty_t = 
    let cp = List.map (fun c -> c#toPretty) children in
    let ap = self#attributes_to_pretty in
    let ns = match namestring with
      | Some s ->
         let len = 70 - (indent + String.length s) in
         let len = if len < 0 then 0 else len in
         LBLOCK [ STR "<!-- " ; STR (string_repeat "~" len) ;
                  STR " " ; STR s ; STR " -->" ; NL ]
      | _ -> STR "" in
    let gs = match groupstring with
      | Some s ->
         let len = 70 - (indent + String.length s) in
         let len = if len < 0 then 0 else len in
         let len = len/2 in
         LBLOCK [ STR "<!-- " ; STR (string_repeat "=" len) ;
                  STR " " ; STR s ; STR " " ; 
                  STR (string_repeat "=" len) ; STR "  -->" ; NL ]
      | _ -> STR "" in         
    let elementtxt =
      match text with
      | Some s ->
         INDENT (
             indent,
             LBLOCK [
	         STR "<" ; STR tag ; ap ; STR ">" ; STR (sanitize s) ; 
	         STR "</" ; STR tag ; STR ">" ; NL ])
      | _ ->
         match cp with
	 | [] ->
            INDENT(
	        indent, LBLOCK [
	                    STR "<" ; STR tag ; ap ; STR "/>" ; NL ;
	      ])
         | _ ->
            LBLOCK [
	        STR "<" ; STR tag ; ap ; STR ">" ; NL ;
	        INDENT (indent,LBLOCK cp)  ;
                STR "</" ; STR tag ; STR ">" ; NL ] in
    LBLOCK [ gs ; ns ; elementtxt ]
    
end
  
class xml_document_t:xml_document_int =
object
  
  val mutable docnode = new xml_element_t "topnode"
                      
  method setNode (n:xml_element_t) = docnode <- n
                                   
  method getRoot = docnode
                 
  method toPretty =
    LBLOCK [
        STR "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" ; NL ;
        (* STR "<?xml-stylesheet type=\"text/xsl\" href=\"" ; STR " " ; STR "\"?>" ; NL ; *)
        docnode#toPretty
      ]
    
end
  
let xmlDocument () = new xml_document_t
let xmlElement tag = new xml_element_t tag
                   
let xml_string (tag:string) (v:string) =
  let e = xmlElement tag in
  begin
    e#setText v;
    e
  end
  
let xml_pretty (tag:string) (v:pretty_t) =
  xml_string tag (string_printer#print v)
  
let xml_attr_int (tag:string) (attr:string) (v:int) =
  let e = xmlElement tag in
  begin
    e#setIntAttribute attr v ;
    e
  end
  
let xml_attr_string (tag:string) (attr:string) (v:string) =
  let e = xmlElement tag in
  begin
    e#setAttribute attr v;
    e
  end
  
let ch_xml_header () = xml_attr_string "ch-header" "date" (current_time_to_string ())
                     
let xml_interval (i:interval_t) =
  let e = xmlElement "range" in
  match i#singleton with
  | Some num -> begin e#setAttribute "value" num#toString ; e end
  | _ ->
     let low = i#getMin#getBound in
     let high = i#getMax#getBound in
     let _ = 
       match low with 
       | NUMBER num -> e#setAttribute "low" num#toString
       | _ -> () in
     let _ =
       match high with
       | NUMBER num -> e#setAttribute "high" num#toString 
       | _ -> () in
     e
     
     
(* -------------------------------------------------------------------------------
   Write list of integers as a sequence of nodes with comma-separated values
   ------------------------------------------------------------------------------- *)
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

