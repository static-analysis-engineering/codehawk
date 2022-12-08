(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* =============================================================================
   The implementation in this file is based on the document:

   Microsoft Portable Executable and Common Object File Format Specification,
   Revision 8.2 - September 21, 2010.
   ============================================================================= *)


(* chlib *)
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHDemangler
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibpe *)
open BCHLibPETypes

module TR = CHTraceResult


class pe_symboltable_entry_t =
object (self)

  val mutable name = ""
  val mutable name_low = wordzero
  val mutable name_high = wordzero
  val mutable stValue = wordzero
  val mutable sectionNumber = 0
  val mutable stType = 0
  val mutable storageClass = 0
  val mutable numberOfAuxSymbols = 0
  val mutable auxiliaryEntries = []

  val mutable stackAdjustment = 0

  method read (ch:pushback_stream_int) =
    try
      begin
      (* 0, 8, Name ------------------------------------------------------------
	 The name of the symbol, represented by a union of three structures. An
	 array of 8 bytes is used if the name is not more than 8 bytes long; 
	 otherwise the lower order four bytes are zero and the high-order four
	 bytes contain the offset into string table
	 ----------------------------------------------------------------------- *)
	name_low  <- ch#read_doubleword ;
	name_high <- ch#read_doubleword ;
	
      (* 8, 4, Value -----------------------------------------------------------
	 The value that is associated with the symbol. The interpretation of 
	 field depends on SectionNumber and StorageClass. A typical meaning is 
	 the relocatable address
	 ----------------------------------------------------------------------- *)
	stValue <- ch#read_doubleword ;
	
      (* 12, 2, SectionNumber --------------------------------------------------
	 The signed integer that idenitifies the section, using a one-based 
	 index into the section table.
	 ----------------------------------------------------------------------- *)
	sectionNumber <- ch#read_i16 ;
	
      (* 14, 2, Type -----------------------------------------------------------
	 A number that represents type. Microsoft tools set this field to 0x20
	 (function) or 0x0 (not a function).
	 ----------------------------------------------------------------------- *)
	stType <- ch#read_ui16 ;
	
      (* 16, 1, StorageClass ---------------------------------------------------
	 An enumerated value that represents storage class.
	 ----------------------------------------------------------------------- *)
	storageClass <- ch#read_byte ;
	
      (* 17, 1, NumberOfAuxSymbols ---------------------------------------------
	 The number of auxiliary symbol table entries that follow this record.
	 ----------------------------------------------------------------------- *)
	numberOfAuxSymbols <- ch#read_byte ;
	
	for i=1 to numberOfAuxSymbols do
          self#read_auxiliary_entry ch
	done ;
	
	1 + numberOfAuxSymbols
      end
    with
	IO.No_more_input ->
	  begin
	    ch_error_log#add "no more input" (STR "pe_symbol_table_entry_t#read") ;
	    raise IO.No_more_input
	  end

  method private extract_stack_adjustment =
    try
      let i = String.index name '@' in
      let suff = string_suffix name (i+1) in
      int_of_string suff
    with
    | _ -> 0

  method read_auxiliary_entry ch =
    try
      let s = ch#really_nread 18 in auxiliaryEntries <- s :: auxiliaryEntries
    with
	IO.No_more_input ->
	  begin
	    ch_error_log#add "no more input" 
	      (STR "pe_symbol_table_entry_t#read_auxiliary_entry") ;
	    raise IO.No_more_input
	  end

  method set_name (s:string) =
    if name_low#equal wordzero then
      let offset = name_high#to_int - 4 in
      try
	let len = 
	  let i = ref 0 in
	  begin while not (Char.code (s.[offset + (!i)]) = 0) do i := !i + 1 done; !i end in
	let n = String.sub s offset len in
	begin
	  name <- n ;
	  stackAdjustment <- self#extract_stack_adjustment ;
	  (stackAdjustment,name)
	end
      with
	_ ->
	  begin
	    ch_error_log#add "symbol table" 
	      (LBLOCK [ STR "set_name; Offset: " ; INT offset ; STR s ]) ;
	    (0, "ch_unknown_ch")
	  end
    else
      let l = name_low#to_string_fragment in
      let h = name_high#to_string_fragment in
      begin
        name <- l ^ h ;
	stackAdjustment <- self#extract_stack_adjustment ;
        (stackAdjustment, name)
      end
	
  method is_function = stType = 32
  method get_address = stValue
  method get_name = name

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti t i = if i = 0 then () else node#setIntAttribute t i in
    let setx t x = if x#equal wordzero then () else set t x#to_hex_string in
    begin
      set "name" name ;
      setx "st-value" stValue ;
      seti "section-number" sectionNumber ;
      seti "symbol-type" stType ;
      seti "storage-class" storageClass ;
      seti "number-of-aux-symbols" numberOfAuxSymbols
    end

  method read_xml (node:xml_element_int) =
    let get = node#getAttribute in
    let has = node#hasNamedAttribute in
    let geti t = if has t then node#getIntAttribute t else 0 in
    let getx t =
      if has t then
        TR.tget_ok (string_to_doubleword (get t))
      else
        wordzero in
    begin
      name <- get "name";
      stValue <- getx "st-value";
      sectionNumber <- geti "section-number" ;
      stType <- geti "symbol-type" ;
      storageClass <- geti "storage-class" ;
      numberOfAuxSymbols <- geti "number-of-aux-symbols"
    end
    
    
  method toPretty = LBLOCK [
    STR "Name               " ; STR name ; NL ;
    STR "Value              " ; STR stValue#to_hex_string ; NL ;
    STR "SectionNumber      " ; INT sectionNumber ; NL ;
    STR "Type               " ; INT stType ; NL ;
    STR "StorageClass       " ; INT storageClass ; NL ;
    STR "NumberOfAuxSymbols " ; INT numberOfAuxSymbols ; NL ]
    
end
 
class pe_symboltable_t:pe_symboltable_int  =
object (self)

  val mutable imageBase = wordzero
  val mutable baseOfCode = wordzero
  val symboltable = new StringCollections.table_t
  val function_address_name_table = Hashtbl.create 1
  val function_name_address_table = Hashtbl.create 1

  method reset =
    begin
      imageBase <- wordzero;
      baseOfCode <- wordzero;
      symboltable#removeList symboltable#listOfKeys;
      Hashtbl.clear function_address_name_table;
      Hashtbl.clear function_name_address_table 
    end

  (* ------------------------------------------------------ auxiliary functions *)

  method private add_function_address_name (dw:doubleword_int) (name:string) =
    Hashtbl.add function_address_name_table dw#index name

  method private mem_function_address_name (dw:doubleword_int):bool =
    Hashtbl.mem function_address_name_table dw#index

  method private find_function_address_name (dw:doubleword_int):string =
    try
      Hashtbl.find function_address_name_table dw#index
    with
      Not_found ->
	begin
	  ch_error_log#add
            "invocation error"
	    (LBLOCK [
                 STR "pe_symbol_table_t#find_function_address_name: ";
                 STR "No name found for ";
		 dw#toPretty]);
	  raise
            (Invocation_error "pe_symbol_table_t#find_function_address_name")
	end
	  
  method private fold_function_address_name fn initial_value =
    Hashtbl.fold (fun k v a -> 
        fn (TR.tget_ok (index_to_doubleword k)) v a)
      function_address_name_table initial_value
      
  method private add_function_name_address (name:string) (address:doubleword_int) =
    Hashtbl.add function_name_address_table name address

  method private find_function_name_address (name:string):doubleword_int =
    Hashtbl.find function_name_address_table name

  (* ================================================================== Setters *)

  method set_image_base (b:doubleword_int) = imageBase <- b
  method set_base_of_code (b:doubleword_int) = baseOfCode <- b 

  (* ================================================================== Readers *)

  method read 
      (start_address:doubleword_int) 
      (number_of_entries:doubleword_int) 
      (exeString:string) =
    try
      let ch = make_pushback_stream exeString in
      let lst = ref [] in
      let n = number_of_entries#to_int in
      let c = ref 0 in
      begin
	while (!c < n) do
          let entry = new pe_symboltable_entry_t in
          begin
            c := !c + entry#read ch ;
            lst := entry :: !lst
          end
	done ;
	let stringtable_size = ch#read_doubleword#to_int in 
	let stringtable = ch#really_nread (stringtable_size - 4) in
	List.iter (fun e -> self#resolve_entry e stringtable) !lst ;
      end
    with
      IO.No_more_input ->
	ch_error_log#add "no more input"
	  (LBLOCK [ STR "Unable to read the symbol table " ])

  method private record_name e =
    let address = (e#get_address#add imageBase)#add baseOfCode in
    let name = e#get_name in
    let name =
      try
	let i = String.index name '@' in
	if i>0 then String.sub name 0 i else name
      with
	_ -> name in
    let name = if name.[0] = '_' then string_suffix name 1 else name in
    let dname = demangle name in
    let isTable = dname = "vftable" || dname = "vbtable" in
    begin
      (if isTable then () else
         (functions_data#add_function address)#add_name name) ;
      self#add_function_address_name address name ;
      self#add_function_name_address name address
    end
	  
  method private resolve_entry e s = 
    let (stack_adjustment,name) = e#set_name s in
    begin
      symboltable#set name e ;
      if e#is_function then self#record_name e else ()
    end
      
  (* ================================================================ Accessors *)
      
  method get_function_name (dw:doubleword_int) = 
    try
      self#find_function_address_name dw
    with
      Not_found ->
	begin
	  ch_error_log#add "invocation error"
	    (LBLOCK [ STR "pe_symbol_table_t#get_function_name: No name found for " ; 
		      dw#toPretty]);
	  raise (Invocation_error "pe_symbol_table_t#get_function_name")
	end
	  
	  
  method get_function_address (fname:string) = 
    try
      self#find_function_name_address fname
    with
      Not_found ->
	begin
	  ch_error_log#add
            "invocation error"
	    (LBLOCK [
                 STR "pe_symbol_table_t#find_function_address: ";
                 STR "No address found for ";
		 STR fname]);
	  raise
            (Invocation_error "pe_symbol_table_t#find_function_address")
	end
	  
	  
  (* ================================================================ Predicates *)
	  
  method has_function_name (dw:doubleword_int) = self#mem_function_address_name dw
    
  (* ======================================================================== xml *)

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    symboltable#iter (fun _ v ->
        let sNode = xmlElement "symbol" in
        begin
          v#write_xml sNode;
          append [sNode]
        end)

  method read_xml (node:xml_element_int) =
    List.iter (fun sNode ->
      let entry = new pe_symboltable_entry_t in
      begin 
	entry#read_xml sNode ; 
	symboltable#set entry#get_name entry ;
	if entry#is_function then self#record_name entry
      end) (node#getTaggedChildren "symbol")

  (* ============================================================ Pretty printing *)
    
  method toPretty = 
    let symbols = symboltable#fold (fun a k v -> 
      LBLOCK [ a ; NL ; STR k ; NL ; INDENT (3, v#toPretty) ] ) (STR "Symbols") in
    let f_addresses = self#fold_function_address_name 
      (fun k v a ->
	LBLOCK [ a ; NL ; STR k#to_hex_string ; STR ": " ; STR v ]) 
      (STR "Function addresses") in
    LBLOCK [ symbols ; NL ; f_addresses ]
      
      
end
  

let pe_symboltable = new pe_symboltable_t
