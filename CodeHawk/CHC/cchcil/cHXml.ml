(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
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
   ============================================================================= *)

open Unix

(* cchcil *)
open CHCMaps
open CHPrettyPrint
open CHUtilities

exception XmlDocumentError of int * int * pretty_t

type doc_spec_t = {
  namespaceURI : string;
  xsi: string;
  schema : string
}

(* Standard header of an xml file *)
let doc_spec = {
  namespaceURI = "http://api.codehawk.kt.com/OutputSchema";
  xsi = "http://www.w3.org/2001/XMLSchema-instance" ;
  schema ="http://api.codehawk.kt.com/OutputSchema OutputSchema2.xsd "
}

let indent = 1

(* -----------------------------------------------------------------------------
   String utilities
   ----------------------------------------------------------------------------- *)

let replace_lst = [ ('&', "&amp;") ; ('<',"&lt;")  ; ('>',"&gt;") ;
		    ('"',"&quot;") ; ('\'',"&apos;") ; (char_of_int 0, "NULL") ]

let replace_string_lst = [ ("\n", "&#10;" ) ]

let replace = string_replace
let replace_string = string_replace_string

(* Replace xml-objectionable characters with standard replacement strings *)
let sanitize (s:string):string =
	let str1 = List.fold_left (fun sa (c,r) -> replace c r sa) s replace_lst in
	List.fold_left (fun sa (o,r) -> replace_string o r sa) str1 replace_string_lst

(* Replace xml-objectional characters with standard replacement strings *)
let rec sanitize_pretty (p:pretty_t):pretty_t = 
  match p with
    STR s -> STR (sanitize s)
  | LBLOCK l ->
      LBLOCK (List.map (fun p -> sanitize_pretty p) l)
  | INDENT (n,p) ->
      INDENT (n, sanitize_pretty p)
  | _ -> p

(* Convert standard Unix time representation to a string *)
let time_to_string (f:float):string = 
  let tm = Unix.localtime f in
  let sp ip = if ip < 10 then LBLOCK [ STR "0" ; INT ip ] else INT ip in
  let p = LBLOCK [ sp (tm.tm_mon + 1) ; STR "/" ; sp tm.tm_mday ; 
		   STR "/" ; sp (tm.tm_year + 1900) ;
		   STR " " ; sp tm.tm_hour ; 
		   STR ":" ; sp tm.tm_min ; 
		   STR ":" ; sp tm.tm_sec ] in
    string_printer#print p

let current_time_to_string () =
  let t = Unix.gettimeofday () in time_to_string t

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
  method setAttribute: string -> string -> unit
  method setIntAttribute: string -> int -> unit
  method setPrettyAttribute: string -> pretty_t -> unit
  method setBoolAttribute: string -> bool -> unit
  method setYesNoAttribute: string -> bool -> unit
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
  method getYesNoAttribute: string -> bool
  method getDefaultAttribute: string -> string -> string
  method getDefaultIntAttribute: string -> int -> int
  method getOptAttribute: string -> string option
  method getOptIntAttribute: string -> int option
  method getText: string
  method getLineNumber: int
  method getColumnNumber: int

  (* predicates *)
  method hasChild: bool
  method hasChildren: bool
  method hasTaggedChild: string -> bool
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
    raise (XmlDocumentError (line,col,fullMsg))
  end

class xml_element_t (tag:string):xml_element_int =
object (self: 'a)
  val tag = tag
  val mutable children:'a list = []
  val mutable text: string option = None
  val mutable attributes = StringMap.empty
  val mutable line_number = 0
  val mutable column_number = 0

  method private raise_error msg =
    let fullMsg =
      LBLOCK [ STR "(" ; INT self#getLineNumber ; STR "," ;
               INT self#getColumnNumber ; STR ")" ; msg ] in
    begin
      raise (XmlDocumentError(self#getLineNumber, self#getColumnNumber, fullMsg))
    end

  method setLineNumber (n:int) = line_number <- n
  method setColumnNumber (n:int) = column_number <- n

  method getLineNumber = line_number
  method getColumnNumber = column_number

  method hasChild = match children with [c] -> true | _ -> false
  method hasChildren = match children with [] -> false | _ -> true

  method hasTaggedChild (childtag:string) =
    match (List.filter (fun n -> n#getTag = childtag) children) with
    | [c] -> true
    | _ -> false

  method hasTaggedChildren (childtag:string) =
    match (List.filter (fun n -> n#getTag = childtag) children) with
    | [] -> false
    | _ -> true

  method hasAttributes = not (StringMap.is_empty attributes)

  method hasNamedAttribute (attname:string) =
    match StringMap.get attname attributes with
    | Some _ -> true
    | _ -> false

  method isEmpty = not (self#hasChildren || self#hasAttributes)

  method hasText = match text with Some _ -> true | _ -> false

  method getText:string =
    match text with
    | Some s -> s
    | _ ->
      raise_error self#getLineNumber self#getColumnNumber
	(LBLOCK [ STR "Element " ; STR tag ; STR " does not have text" ])

  method getTag:string = tag

  method getChild:'a =
    match children with
    | [] ->
       raise_error
         self#getLineNumber self#getColumnNumber
	 (LBLOCK [ STR "Element " ; STR tag ; STR " does not have any children " ])
    | [c] -> c
    | _ -> raise_error self#getLineNumber self#getColumnNumber
      (LBLOCK [ STR "Element " ; STR tag ; STR " has more than one child "])

  method getTaggedChild (childtag:string):'a =
    let tagged_children = self#getTaggedChildren childtag in
    match tagged_children with
    | [] ->
       raise_error
         self#getLineNumber self#getColumnNumber 
	 (LBLOCK [ STR "Element " ; STR tag ;
                   STR " does not have any children with tag " ; STR childtag ;
		   pretty_print_list children (fun c -> STR c#getTag) " [" "," "]" ])
    | [c] -> c
    | _ ->
       raise_error
         self#getLineNumber self#getColumnNumber
         (LBLOCK [ STR "Element " ; STR tag ;
                   STR " has multiple children with tag " ; STR childtag ])

  method getTaggedChildren (childtag:string):'a list =
    List.filter (fun n -> (n#getTag = childtag)) children

  method getChildren: 'a list = children

  method getAttribute (attribute_tag:string):string =
    match StringMap.get attribute_tag attributes with
    | Some s -> s
    | _ ->
       raise_error
         self#getLineNumber self#getColumnNumber
	 (LBLOCK [ STR "Element " ; STR tag ;
                   STR " does not have an attribute " ; STR attribute_tag ])
      
  method getIntAttribute (attribute_tag:string):int =
    let attribute = self#getAttribute attribute_tag in
    try
      int_of_string attribute
    with
    | Invalid_argument _ ->
       raise_error
         self#getLineNumber self#getColumnNumber
	 (LBLOCK [ STR "Element " ; STR tag ; STR " attribute " ; STR attribute_tag ; 
		   STR " is not an integer (value: " ; STR attribute ; STR ")" ])
      
  method getYesNoAttribute (attribute_tag:string):bool =
    try
      let attr_value = self#getAttribute attribute_tag in
      match attr_value with
      |	"yes" -> true
      | "no"  -> false
      | _ ->
	 raise_error
           self#getLineNumber self#getColumnNumber
	   (LBLOCK [ STR "Attribute " ; STR attribute_tag ; STR " of element " ; 
		     STR tag ; STR " has value " ; STR attr_value ;
                     STR " (expected yes/no)" ])
    with
    | XmlDocumentError _ -> false
                          
  method getDefaultAttribute (attribute_tag:string) (default_value:string):string =
    try
      self#getAttribute attribute_tag 
    with
    | XmlDocumentError _ -> default_value

  method getDefaultIntAttribute (attribute_tag:string) (default_value:int):int =
    try
      self#getIntAttribute attribute_tag
    with
    | XmlDocumentError _ -> default_value

  method getOptAttribute (attribute_tag:string):string option =
    try
      Some (self#getAttribute attribute_tag)
    with
    | XmlDocumentError _ -> None

  method getOptIntAttribute (attribute_tag:string):int option =
    try
      Some (self#getIntAttribute attribute_tag)
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
    | Some _ ->
       failwith "Cannot append childnodes to element with text data\n"
      
  method setAttribute (attr:string) (attr_value:string) =
    attributes <- StringMap.add attr attr_value attributes  
    
  method setIntAttribute (attr:string) (attr_value:int) =
    self#setAttribute attr (string_of_int attr_value)
    
  method setPrettyAttribute (attr:string) (attr_value:pretty_t) =
    self#setAttribute attr (string_printer#print attr_value)
    
  method setYesNoAttribute (attr:string) (b:bool) =
    self#setAttribute attr (if b then "yes" else "no")
    
  method setBoolAttribute (attr:string) (b:bool) =
    self#setAttribute attr (if b then "true" else "false")
    
  method private attributes_to_pretty:pretty_t = 
    StringMap.fold 
      (fun k v a ->
        LBLOCK [ a ; STR  " " ; STR (sanitize k) ; STR "=" ; STR "\"" ;
	         STR (sanitize v) ; STR "\""
      ] ) attributes (LBLOCK [])
    
  method toPretty:pretty_t = 
    let cp = List.map (fun c -> c#toPretty) children in
    let ap = self#attributes_to_pretty in
    match text with
    | Some s ->
       INDENT (
	   indent, LBLOCK [
	               STR "<" ; STR tag ; ap ; STR ">" ; STR (sanitize s) ; 
	               STR "</" ; STR tag ; STR ">" ; NL 
	 ])
    | _ ->
       match cp with
	 [] -> INDENT(
		   indent, LBLOCK [
		               STR "<" ; STR tag ; ap ; STR "/>" ; NL ;
		 ])
       | _ -> INDENT(
		  indent, LBLOCK [
		              STR "<" ; STR tag ; ap ; STR ">" ; NL ;
		              LBLOCK cp ; STR "</" ; STR tag ; STR ">" ; NL ;
		])
	    
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
  
let max_string_size = 1000
                    
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
  let _ =
    String.iter (fun c -> 
        if !found then
          ()
        else if Char.code c = 10 then      (* NL *)
          ()
        else if (Char.code c) < 32 || (Char.code c) > 126 then 
          found  := true) s in
  !found

let write_xml_constant_string (node:xml_element_int) (tag:string) (s:string) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let len = String.length s in
  let hasx = has_control_characters s in
  let _ = seti (tag ^ "-len") len in
  if hasx then
    set (tag ^ "-x") (hex_string s)
  else
    set tag s
  
  
