(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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

(** Utilities to read xml files *)


(* =============================================================================
   The implementation in this file is based on the document:

   Extensible Markup Language (XML) 1.0 (Fifth Edition)
   W3C Recommendation 26 November 2008
   http://www.w3.org/TR/xml/
   ============================================================================= *)

(* chlib *)
open CHCommon
open CHPretty

(* chutil *)
open CHXmlDocument

exception XmlParseError of int * int * pretty_t

exception XmlReaderError of int * int * pretty_t

exception IllFormed


let utf8_length = [|        (* Char byte length according to first UTF-8 byte. *)
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 
  0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 
  0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 
  0; 0; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 
  2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 
  4; 4; 4; 4; 4; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0 |]

let read_utf8 getchar =
  let b0 = getchar () in
  let check c = if c then () else raise IllFormed in
  match utf8_length.(b0) with
  | 0 -> raise IllFormed
  | 1 -> b0
  | 2 ->
     let b1 = getchar () in
     begin
       check ((b1 lsr 6) = 0b10) ;
       ((b0 land 0x1F) lsl 6) lor 
	 ((b1 land 0x3F))
     end
  | 3 ->
     let b1 = getchar () in
     let b2 = getchar () in
     begin
       check ((b2 lsr 6) = 0b10) ;
       (match b0 with
	| 0xE0 -> check (b1 >= 0xA0 && b1 <= 0xBF)
	| 0xED -> check (b1 >= 0x80 && b1 <= 0x9F)
	| _ -> check ((b1 lsr 6) = 0b10));
       ((b0 land 0x0F) lsl 12) lor 
	 ((b1 land 0x3F) lsl  6) lor 
	   ((b2 land 0x3F))
     end
  | 4 ->
     let b1 = getchar () in
     let b2 = getchar () in
     let b3 = getchar () in
     begin
       check ((b3 lsr 6) = 0b10) ;
       check ((b2 lsr 6) = 0b10) ;
       (match b0 with 
	| 0xF0 -> check (b1 >= 0x90 && b1 <= 0xBF)
	| 0xF4 -> check (b1 >= 0x80 && b1 <= 0x8F)
	| _ -> check ((b1 lsr 6) = 0b10) );
       ((b0 land 0x07) lsl 18) lor
	 ((b1 land 0x3F) lsl 12) lor
	   ((b2 land 0x3F) lsl  6) lor
	     ((b3 land 0x3F))
     end
  | _ -> assert false
       
let in_range c lower_bound upper_bound = c >= lower_bound && c <= upper_bound
                                       
(* ---------------------------------------------------------------------------- 
 * Char	::= #x9 | #xA | #xD                                                     
 *      |   [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF]	        
 * ---------------------------------------------------------------------------- *)
let is_char c =
  (c = 0x0009)
  || (c = 0x000A)
  || (c = 0x000D)
  || (in_range c 0x0030 0xD7FF)
  || (in_range c 0xE000 0xFFFD)
  || (in_range c 0x10000 0x10FFFF)

let is_digit c = in_range c 0x0030 0x0039

let is_hex_digit c = 
  (in_range c 0x0030 0x0039)
  || (in_range c 0x0041 0x0046)
  || (in_range c 0x0061 0x0066)

(* ----------------------------------------------------------------------------
 * White Space
 * [3] S	   ::=  (#x20 | #x9 | #xD | #xA)+
 * --------------------------------------------------------------------------- *)
let is_white_space = function 
  | 0x0020 | 0x0009 | 0x000D | 0x000A -> true
  | _ -> false
       
(* ---------------------------------------------------------------------------- 
 * Names and Tokens                                                             
 * [4] NameStartChar ::= ":" | [A-Z] | "_" | [a-z] 
 *                   |   [#xC0-#xD6] | [#xD8-#xF6] | [#xF8-#x2FF] 
 *                   |   [#x370-#x37D] | [#x37F-#x1FFF] | [#x200C-#x200D] 
 *                   |   [#x2070-#x218F] | [#x2C00-#x2FEF] | [#x3001-#xD7FF] 
 *                   |   [#xF900-#xFDCF] | [#xFDF0-#xFFFD] | [#x10000-#xEFFFF]
 * [4a] NameChar     ::= NameStartChar | "-" | "." | [0-9] | #xB7 
 *                   |   [#x0300-#x036F] | [#x203F-#x2040]
 * [5] Name	     ::= NameStartChar (NameChar)*
 * [6] Names	     ::= Name (#x20 Name)*
 * [7] Nmtoken	     ::= (NameChar)+
 * [8] Nmtokens	     ::= Nmtoken (#x20 Nmtoken)*
 * ---------------------------------------------------------------------------- *)

let is_name_start_char c =
  (in_range c 0x0061 0x007A)       (* a-z *) 
  || (in_range c 0x0041 0x005A)    (* A-Z *)
  || (c = 0x005F)                  (*  _  *)
  || (c = 0x003A)                  (*  :  *)
  || (in_range c 0x00C0 0x00D6) 
  || (in_range c 0x00D8 0x00F6) 
  || (in_range c 0x00F8 0x02FF) 
  || (in_range c 0x0370 0x037D) 
  || (in_range c 0x037F 0x1FFF)
  || (in_range c 0x200C 0x200D)
  || (in_range c 0x2070 0x218F)
  || (in_range c 0x2C00 0x2FEF)
  || (in_range c 0x3001 0xD7FF)
  || (in_range c 0xF900 0xFDCF)
  || (in_range c 0xFDF0 0xFFFD)
  || (in_range c 0x10000 0xEFFFF) 

let is_name_char c =
  (is_name_start_char c)    
  || (c = 0x002D)                   (*  -  *)
  || (c = 0x002E)                   (*  .  *)
  || (c = 0x00B7)
  || (in_range c 0x0030 0x0039)     (* 0-9 *)
  || (in_range c 0x0300 0x036F)
  || (in_range c 0x203F 0x2040)


module XString = struct
  type t = string
  let empty = ""
  let length = String.length
  let append = ( ^ )
  let lowercase = String.lowercase_ascii
  let iter f s =
    let len = String.length s in
    let pos = ref ~-1 in
    let get () =
      incr pos ;
      if !pos = len then raise Exit else
	Char.code (String.get s !pos) in
    try 
      while true do f (read_utf8 get) done
    with
    | Exit -> ()
  let of_string s = s
  let to_utf8 f v x = f v x
  let compare = String.compare
end
               
let string_equal s1 s2 = (XString.compare s1 s2) = 0
                       
module XHashtbl =
  Hashtbl.Make
    (struct 
      type t = XString.t
      let equal = string_equal
      let hash = Hashtbl.hash 
    end)
  
module XBuffer = struct
  type string = XString.t
  type t = Buffer.t
  exception Full
  let create = Buffer.create
  let add_char = Buffer.add_char
  let add_uchar buffer uchar =
    try
      let store c = Buffer.add_char buffer (Char.chr c) in
      if uchar <= 0x007F then
	store uchar
      else if uchar <= 0x07FF then
	begin
	  store (0xC0 lor (uchar lsr 6));
	  store (0x80 lor (uchar land 0x3f)) 
	end
      else if uchar <= 0xFFFF then
	begin
	  store (0xE0 lor (uchar lsr 12));
	  store (0x80 lor ((uchar lsr 6) land 0x3F)) ;
	  store (0x80 lor (uchar land 0x3F))
	end
      else 
	begin
	  store (0xF0 lor (uchar lsr 18));
	  store (0x80 lor ((uchar lsr 12) land 0x3F));
	  store (0x80 lor ((uchar lsr 6 ) land 0x3F));
	  store (0x80 lor (uchar land 0x3F))
	end
    with
    | Failure _ -> raise Full
                 
  let clear = Buffer.clear
  let contents = Buffer.contents
  let length = Buffer.length
end
               
class type xml_reader_int =
  object
    method readDocument: unit
    method getDocument: xml_document_int
  end
  
let c_end_of_file = max_int
                  
let c_ampersand        = 0x0026   (* & *)
let c_carriage_return  = 0x000D   (* carriage_return *)
let c_colon            = 0x003A   (* : *)
let c_double_quote     = 0x0022   (* quote *)
let c_exclamationmark  = 0x0021   (* ! *)
let c_equals           = 0x003D   (* = *)
let c_D                = 0x0044   (* D *)
let c_F                = 0x0046   (* F *)
let c_greaterthan      = 0x003E   (* > *)
let c_leftbracket      = 0x005B   (* [ *) 
let c_lessthan         = 0x003C   (* < *)
let c_minus            = 0x002D   (* - *)
let c_newline          = 0x000A   (* newline *)
let c_nine             = 0x0039   (* 9 *)
let c_questionmark     = 0x003F   (* ? *)
let c_rightbracket     = 0x005D   (* ] *)
let c_semicolon        = 0x003B   (* ; *)
let c_single_quote     = 0x0027   (* ' *)
let c_sharp            = 0x0023   (* # *)
let c_space            = 0x0020   (* space *)
let c_slash            = 0x002F   (* / *)
let c_x                = 0x0078   (* x *)
                       
let encodings = [ "utf-8" ; "utf-16" ; "ascii" ; "us-ascii" ; "iso-8859-1" ]
              
let predefined_entities =
  let tbl = XHashtbl.create 5 in
  let add_entry k v = XHashtbl.add tbl (XString.of_string k) (XString.of_string v) in
  begin
    add_entry "lt" "<" ;
    add_entry "gt" ">" ;
    add_entry "amp" "&" ;
    add_entry "apos" "'" ;
    add_entry "quot" "\"" ;
    tbl
  end
  
type delimiter_t =
  LEof
| LStartTag 
| LEndTag 
| LProcInstr 
| LText
| LComment
| LCDATA

class xml_reader_t (ch:IO.input) =
object (self)
     
  val mutable ch = ch
  val mutable pos = (fun () -> 0)
  val mutable char_la = 0
  val mutable delim_la = LEof
  val mutable line_no = 1
  val mutable col_no = 1
  val mutable prev_white_space = true
  val name_buffer = XBuffer.create 17
  val data_buffer = XBuffer.create 17
  val mutable encoding = ""
  val xmldocument = xmlDocument ()
  val mutable carriage_return = false
                              
  method getDocument = xmldocument
                     
  method input_unicode = read_utf8 (fun () -> IO.read_byte ch)
                       
  method fill_name_buffer c = XBuffer.add_uchar name_buffer c
  method fill_data_buffer c = XBuffer.add_uchar data_buffer c
                            
  method fill_data_strip c =
    if is_white_space c then
      prev_white_space <- true
    else
      begin
	(if prev_white_space && XBuffer.length data_buffer <> 0 then
	   self#fill_data_buffer c_space);
	prev_white_space <- false ;
	self#fill_data_buffer c
      end
    
    
  method private skip_white_space =
    while (is_white_space char_la) do self#next_char done
    
  method end_of_file =
    let _ = self#skip_white_space in
    char_la = c_end_of_file
    
  method private read_char expected_char =
    if char_la = expected_char then
      self#next_char
    else
      raise (XmlParseError
               (line_no, col_no,
		LBLOCK [ STR "Expected to see " ; INT expected_char ;
                         STR ", but found " ; INT char_la ]))
    
  method private check_char_la predicate msg =
    if predicate char_la then
      ()
    else
      raise (XmlParseError (line_no, col_no, msg))
    
  method private check_name name allowed_names =
    let str_check = fun s1 s2 -> XString.compare s1 s2 in
    if List.exists (fun s -> (str_check name s) = 0) allowed_names then
      ()
    else
      raise (XmlParseError
               (line_no, col_no,
		LBLOCK [ STR "Expected: " ;
			 pretty_print_list allowed_names (fun s -> STR s) "[" "," "]" ;
			 STR ", but found: " ; STR name ]))
    
  method private next_char = 
    let advance () = 
      if char_la = c_newline then
	begin 
	  line_no <- line_no + 1 ; 
	  col_no <- 1 ;
	end
      else
	col_no <- col_no + 1 in
    try
      begin
	advance ();
	char_la <- self#input_unicode;
	(if carriage_return && char_la = c_newline then
	   char_la <- self#input_unicode);
	(if char_la = c_carriage_return then
	   begin
	     carriage_return <- true ;
	     char_la <- c_newline
	   end
	 else
	   carriage_return <- false)
      end 
    with
    | IO.No_more_input -> 
       char_la <- c_end_of_file
      
  method private read_name = 
    begin
      XBuffer.clear name_buffer ;
      self#check_char_la
        is_name_start_char
	(LBLOCK [ INT char_la ; STR " is not a valid starting character of a name "]) ;
      self#fill_name_buffer char_la ;
      self#next_char ;
      while is_name_char char_la do
	begin
	  self#fill_name_buffer char_la ;
	  self#next_char
	end
      done;
      XBuffer.contents name_buffer
    end     
    
  method private read_delimiter = 
    delim_la <-
      if char_la = c_end_of_file then
	LEof
      else if char_la <> c_lessthan then
	LText
      else
	begin
	  self#read_char c_lessthan ;
	  if char_la = c_questionmark then
	    begin
	      self#next_char ;
	      LProcInstr
	    end
	  else if char_la = c_exclamationmark then
	    begin
	      self#next_char ;
	      if char_la = c_minus then
		begin
		  self#next_char ;
		  self#read_char c_minus ;
		  LComment
		end
	      else if char_la = c_D then
		begin
		  LProcInstr
		end
	      else if char_la = c_leftbracket then
		begin
		  self#next_char ;
		  self#check_name self#read_name ["CDATA"] ;
		  self#read_char c_leftbracket ;
		  LCDATA
		end
	      else
		raise (XmlParseError
                         ( line_no, col_no,
			   (LBLOCK [ STR "Illegal character sequence at <! "])))
	    end
	  else if char_la = c_slash then
	    begin
	      self#next_char ;
	      LEndTag
	    end
	  else
	    LStartTag
	end
    
  (* --------------------------------------------------------------------------- 
   * Document
   * [1] document ::= prolog element Misc*                                           
   * --------------------------------------------------------------------------- *)

  method readDocument =
    let (c,p) = IO.pos_in ch in
    begin
      ch <- c ;
      pos <- p ;
      self#next_char ;
      self#read_delimiter ;
      self#readProlog ;
      xmldocument#setNode self#readElement 
    end
    
  (* ------------------------------------------------------------------------- 
   * Literals
   * [9] EntityValue       ::= '"' ([^%&"] | PEReference | Reference)* '"'
   *	                   |   "'" ([^%&'] | PEReference | Reference)* "'"
   * [10] AttValue         ::= '"' ([^<&"] | Reference)* '"'
   *		           |   "'" ([^<&'] | Reference)* "'"
   * [11] SystemLiteral	   ::= ('"' [^"]* '"') | ("'" [^']* "'")
   * [12] PubidLiteral	   ::= 	'"' PubidChar* '"' | "'" (PubidChar - "'")* "'"
   * [13] PubidChar	   ::= 	#x20 | #xD | #xA | [a-zA-Z0-9] | [-'()+,./:=?;!*#@$_%]
   * ------------------------------------------------------------------------- *)

  method private readAttValue =
    begin
      self#skip_white_space ;
      self#check_char_la
        (fun c -> c = c_single_quote || c = c_double_quote)
	(LBLOCK [ STR "Expected single or double quote but found " ; INT char_la ]) ;
      let quot = char_la in
      self#next_char ;
      self#skip_white_space ;
      XBuffer.clear data_buffer ;
      prev_white_space <- true ;
      while (char_la <> quot) do
	begin 
	  self#check_char_la
            (fun c -> c <> c_lessthan) 
	    (LBLOCK [ STR "Unexpected character in attribute value " ; INT char_la ]) ;
	  if char_la = c_ampersand then
	    XString.iter self#fill_data_strip self#readEntityReference
	  else
	    begin
	      self#fill_data_strip char_la ;
	      self#next_char
	    end
	end
      done ;
      self#next_char ;
      XBuffer.contents data_buffer
    end 
    
  (* -------------------------------------------------------------------------
   * Character Data
   * [14] CharData ::=	[^<&]* - ([^<&]* ']]>' [^<&]* )
   * ------------------------------------------------------------------------- *)

  method readCharData =
    begin
      XBuffer.clear data_buffer;
      while char_la <> c_lessthan do
	if char_la = c_ampersand then 
	  XString.iter self#fill_data_buffer self#readEntityReference
	else
	  begin
	    self#fill_data_buffer char_la ;
	    self#next_char
	  end
      done;
      self#read_delimiter ;
      XBuffer.contents data_buffer
    end
    
    
  (* -------------------------------------------------------------------------
   * Comments
   * [15] Comment ::= '<!--' ((Char - '-') | ('-' (Char - '-')))* '-->'
   * ------------------------------------------------------------------------- *)
  method private readComment =
    begin
      let incomment = ref true in
      while !incomment do
	while char_la <> c_minus do self#next_char done ;
	self#next_char ;
	if char_la = c_minus then 
	  begin
	    self#next_char ;
	    if char_la = c_greaterthan then
	      begin
		self#next_char ;
		incomment := false
	      end
	  end
      done ;
      self#skip_white_space ;
      self#read_delimiter
    end
    
  (* -------------------------------------------------------------------------
   * CDATA section
   *  [18]   	CDSect	   ::=   	 CDStart CData CDEnd
   *  [19]   	CDStart	   ::=   	'<![CDATA['
   *  [20]   	CData	   ::=   	(Char* - (Char* ']]>' Char* ))
   *  [21]   	CDEnd	   ::=   	']]>'
   * ------------------------------------------------------------------------- *)
  method private readCDATA =
    begin
      let incdata = ref true in
      while !incdata do
	while char_la <> c_rightbracket do self#next_char done ;
	self#next_char ;
	if char_la = c_rightbracket then
	  begin
	    self#next_char ;
	    if char_la = c_greaterthan then
	      begin
		self#next_char ;
		incdata := false
	      end
	  end
      done;
      self#skip_white_space ;
      self#read_delimiter
    end
    
  (* -------------------------------------------------------------------------
   * Prolog
   * [22] prolog	::= XMLDecl? Misc* (doctypedecl Misc*  )?
   * [23] XMLDecl	::= '<?xml' VersionInfo EncodingDecl? SDDecl? S? '?>'
   * [24] VersionInfo	::= S 'version' Eq ("'" VersionNum "'" | '"' VersionNum '"')
   * [25] Eq	        ::= S? '=' S?
   * [26] VersionNum	::= '1.' [0-9]+
   * [27] Misc	        ::= Comment | PI | S
   * ------------------------------------------------------------------------- *)
 
  method private readProlog =
    begin
      self#readXmlDecl ;
      self#readDoctypeDecl
    end
    
  method private readXmlDecl =
    match delim_la with
      LProcInstr ->
      begin
	self#check_name self#read_name ["xml"] ;
	self#skip_white_space ;
	self#check_name self#read_name ["version"]  ;
	self#skip_white_space ;
	self#read_char c_equals ;
	self#skip_white_space ;
	self#check_name self#readAttValue [ "1.0" ; "1.1" ] ;
	self#skip_white_space ;
	(if char_la <> c_questionmark then
	   let name = self#read_name in
	   if string_equal name "encoding" then 
	     begin
	       self#readEncoding  ;
	       self#skip_white_space ;
	       if char_la <> c_questionmark then
		 begin
		   self#check_name self#read_name [ "standalone" ] ;
		   self#readStandalone
		 end 
	     end
	   else 
	     begin
	       self#check_name self#read_name [ "standalone" ] ;
	       self#readStandalone 
	     end );
	self#skip_white_space ;
	self#read_char c_questionmark ;
	self#read_char c_greaterthan ;
	self#skip_white_space ;
	self#read_delimiter 
      end	
    | _ -> ()
         
  (* -------------------------------------------------------------------------
   * Document Type Definition
   * [28] doctypedecl ::= '<!DOCTYPE' S Name (S ExternalID)? S? ('[' intSubset ']' S?)? '>'
   * [28a] DeclSep    ::= PEReference | S 	
   * [28b] intSubset  ::= (markupdecl | DeclSep)*
   * [29]  markupdecl ::= elementdecl | AttlistDecl | EntityDecl | NotationDecl | PI | Comment 	
   * ------------------------------------------------------------------------- *)

  method readDoctypeDecl =
    match delim_la with
      LProcInstr ->
      begin
	while char_la <> c_greaterthan do self#next_char done ;
	self#read_char c_greaterthan ;
	self#skip_white_space ;
	self#read_delimiter
      end
    | _ ->
       ()
      
  (* --------------------------------------------------------------------------
   * Standalone Document Declaration
   * [32] SDDecl ::= S 'standalone' Eq (("'" ('yes' | 'no') "'") | ('"' ('yes' | 'no') '"')) 	
   * -------------------------------------------------------------------------- *)

  method private readStandalone =
    begin
      self#skip_white_space ;
      self#read_char c_equals ;
      self#skip_white_space ;
      self#check_name self#readAttValue [ "yes" ; "no" ]
    end
    
  (* ------------------------------------------------------------------------- 
   * Element
   * [39] element  ::= 	EmptyElemTag
   *		   |    STag content ETag
   * ------------------------------------------------------------------------- *)

  method readElement =
    let (tag, atts) = self#readStartTag in
    let node = xmlElement tag in
    let _ = node#setLineNumber line_no in
    let _ = node#setColumnNumber col_no in
    let _ = List.iter (fun (a,v) -> node#setAttribute a v) atts in
    if char_la = c_slash then
      begin
	self#read_char c_slash ;
	self#read_char c_greaterthan ;
	self#skip_white_space ;
	self#read_delimiter ;
	node
      end
    else if char_la = c_greaterthan then
      begin
	self#read_char c_greaterthan ;
	self#skip_white_space ;
	self#read_delimiter ;
	if delim_la = LText then
	  begin
	    node#setText self#readCharData ;
	    self#readEndTag tag ;
	    node
	  end
	else
	  let children = self#readContent in
	  begin 
	    self#readEndTag tag ;
	    node#appendChildren children  ;
	    node
	  end
      end
    else
      raise (XmlParseError
               (line_no, col_no,
		STR "Expected to see \ or > "))
    
  (* -------------------------------------------------------------------------
   * Start-tag
   * [40] STag	     ::= '<' Name (S Attribute)* S? '>'	
   * [41] Attribute  ::= Name Eq AttValue 
   * ------------------------------------------------------------------------- *)

  method readStartTag =
    let atts = ref [] in
    let name = self#read_name in
    begin
      self#skip_white_space ;
      while char_la <> c_slash && char_la <> c_greaterthan do
	atts := self#readAttribute :: !atts ;
	self#skip_white_space
      done ;
      (name, !atts)
    end
    
  method readAttribute =
    let key = self#read_name in
    let _ = self#read_char c_equals in
    let v = self#readAttValue in
    (key,v)
    
  (* -------------------------------------------------------------------------
   * End-tag
   * [42] ETag	   ::=  '</' Name S? '>'
   * ------------------------------------------------------------------------- *)

  method readEndTag tag =
    begin
      let name = self#read_name  in
      begin
	self#check_name name [tag] ;
	self#skip_white_space ;
	self#read_char c_greaterthan ;
	self#skip_white_space ;
	self#read_delimiter
      end
    end
    
  (* -------------------------------------------------------------------------
   * Content of Elements
   * [43] content  ::= CharData? ((element | Reference | CDSect | PI | Comment) CharData?)*
   * ------------------------------------------------------------------------- *)

  method readContent =
    let content = ref [] in
    begin
      while delim_la = LStartTag || delim_la = LComment || delim_la = LCDATA do
	if delim_la = LStartTag then
	  content := self#readElement :: !content
	else if delim_la = LComment then
	  self#readComment
	else
	  self#readCDATA
      done;
      List.rev !content
    end
    
  (* -------------------------------------------------------------------------
   * Tags for Empty Elements
   * [44] EmptyElemTag  ::= '<' Name (S Attribute)* S? '/>'	
   * ------------------------------------------------------------------------- *)

  (* -------------------------------------------------------------------------
   * Character Reference
   * [66] CharRef   ::=	'&#' [0-9]+ ';'
   *		    |   '&#x' [0-9a-fA-F]+ ';'	
   * ------------------------------------------------------------------------- *)

  method readCharRef =
    let v = ref 0 in
    let convert c = 
      if c <= c_nine then c-48
      else if c <= c_F then c-55
      else c - 87 in
    begin
      XBuffer.clear name_buffer;
      self#next_char ;
      if char_la = c_semicolon then
        raise (XmlParseError
                 (line_no, col_no,
		  (LBLOCK [ STR "Unexpected empty string in char_ref" ])))
      else
        begin
          try
            if char_la = c_x then
              begin
                self#fill_name_buffer char_la;
                self#next_char ;
                while (char_la <> c_semicolon) do
                  begin
                    self#fill_name_buffer char_la ;
                    if is_hex_digit char_la then
                      begin
                        v := !v * 16 + (convert char_la) ;
                        self#next_char
                      end
                    else raise Exit
                  end
                done
              end
            else
              while (char_la <> c_semicolon) do
                begin
                  self#fill_name_buffer char_la;
                  if is_digit char_la then
                    begin
                      v := !v * 10 + (char_la - 48) ;
                      self#next_char
                    end
                  else
                    raise Exit
                end
              done
          with
          | Exit ->
             begin
               v := -1 ;
               while (char_la <> c_semicolon) do
                 begin
                   self#fill_name_buffer char_la ;
                   self#next_char
                 end
               done
             end
	end;
      if is_char !v then
	begin
	  XBuffer.clear name_buffer ;
	  self#fill_name_buffer !v;
	  XBuffer.contents name_buffer
	end
      else
        raise (XmlParseError (line_no, col_no, STR "Illegal char ref"))
    end
    
  (* -------------------------------------------------------------------------
   * Entity Reference
   * [67] Reference	   ::= EntityRef | CharRef
   * [68] EntityRef	   ::= '&' Name ';'	
   * [69] PEReference	   ::= '%' Name ';'	
   * ------------------------------------------------------------------------- *)
  method readEntityReference =
    begin
      self#next_char ;
      if char_la = c_sharp then
	self#readCharRef
      else
	self#readEntityRef
    end
    
  method readEntityRef =
    let name = self#read_name in
    begin
      self#read_char c_semicolon ;
      try
        XHashtbl.find predefined_entities name 
      with
        Not_found ->
        raise (XmlParseError
                 (line_no, col_no,
                  (LBLOCK [ STR "Unknown entity reference: " ; 
                            STR name ])))
    end
    
  (* -------------------------------------------------------------------------
   * Encoding Declaration
   * [80] EncodingDecl ::= S 'encoding' Eq ('"' EncName '"' | "'" EncName "'" )
   * [81] EncName      ::= [A-Za-z] ([A-Za-z0-9._] | '-')*
   * ------------------------------------------------------------------------- *)

  method private readEncoding =
    begin
      self#skip_white_space ;
      self#read_char c_equals ;
      self#skip_white_space ;
      let enc = XString.lowercase self#readAttValue in
      self#check_name enc encodings;
      encoding <- enc 
    end
    
end
  
let readXmlDocument (filename:string) =
  let channel = open_in_bin filename in
  let ch = IO.input_channel channel in
  let reader = new xml_reader_t ch in
  begin
    reader#readDocument ;
    close_in channel ;
    reader#getDocument ;
  end
  
let readXmlDocumentString (s:string) =
  let ch = IO.input_string s in
  let reader = new xml_reader_t ch in
  begin
    reader#readDocument ;
    reader#getDocument ;
  end
  
