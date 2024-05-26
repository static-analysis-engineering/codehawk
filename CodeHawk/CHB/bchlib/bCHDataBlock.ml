(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper
open BCHByteUtilities


module H = Hashtbl
module TR = CHTraceResult


let extract_offset_range s =
  let ch = make_pushback_stream s in
  let len = String.length s in
  let min = ref 0 in
  let max = ref 0 in
  let _ = while ch#pos < len do
      let b = ch#read_byte in 
      if b = 204 then () else
	if b < !min then min := b
	else if b > !max then max := b
	else ()
    done in
  (!min,!max)
  

class data_block_t 
  ?(is_offset_table=false)
  (start_address:doubleword_int) 
  (end_address:doubleword_int) 
  (bname:string):data_block_int =
object (self:'a)

  val mutable data_string = None
  val mutable data_table = H.create 3
  val mutable name = bname
  val mutable end_address = end_address

  method compare (other:'a) =
    let l0 = start_address#compare other#get_start_address in
    if l0 = 0 then end_address#compare other#get_end_address else l0

  method set_data_string s = data_string <- Some s

  method truncate (a: doubleword_int) =
    let newlength =
      fail_tvalue
        (trerror_record (STR "data_block#truncate:new_length"))
        (a#subtract_to_int start_address) in
    begin
      (match data_string with
       | Some s
            when self#get_length > newlength && (String.length s > newlength) ->
          data_string <- Some (String.sub s 0 newlength)
       | _ -> ());
      end_address <- a
    end
    
  method get_start_address = start_address
    
  method get_end_address   = end_address

  method get_name = name

  method set_name s = name <- s

  method set_data_table (items: (string * string) list) =
    List.iter (fun (a, s) -> H.add data_table a s) items

  method get_length =
    fail_tvalue
      (trerror_record (STR "data_block:get_length"))
      (end_address#subtract_to_int start_address)

  method get_data_string =
    match data_string with
    | Some s -> s
    | _ ->
       begin
         ch_error_log#add
           "invocation error" (LBLOCK [STR "data_block#get_data_string"]);
         raise (Invocation_error "data_block#get_data_string")
       end

  method get_offset_range =
    if is_offset_table then
      match data_string with
      | Some s -> Some (extract_offset_range s)
      | _ -> None
    else
      raise
        (BCH_failure
	   (LBLOCK [
                STR "Block at ";
                start_address#toPretty;
		STR " is not an offset table block "]))
      
  method has_name = not (name = "data")

  method is_offset_table = is_offset_table 
    
  method has_data_string = match data_string with Some _ -> true | _ -> false
    
  method write_xml (node:xml_element_int) = 
    let set = node#setAttribute in
    let seta t a = set t a#to_hex_string in
    begin
      seta "start" start_address ;
      seta "end" end_address ;
      (if name="data" then () else set "name" name) ;
      (if is_offset_table then set "offsets" "yes")
    end
      
  method toPretty =
    match data_string with Some s -> STR s | _ -> STR "data-string not set"

  method private seh4_scopetable_to_string = 
    let ch = make_pushback_stream self#get_data_string in
    let numRecords = ((String.length self#get_data_string) - 16) / 12 in
    let gsc = ch#read_doubleword#to_hex_string in
    let gscx = ch#read_doubleword#to_hex_string in
    let ehc = ch#read_doubleword#to_hex_string in
    let ehcx = ch#read_doubleword#to_hex_string in
    let records = ref [] in
    let read_record () =
      let enc = ch#read_doubleword#to_hex_string in
      let ff = ch#read_doubleword#to_hex_string in
      let hf = ch#read_doubleword#to_hex_string in
      let recStr = 
      "  Record.EnclosingLevel : " ^ enc ^ "\n" ^
      "  Record.FilterFunc     : " ^ ff ^ "\n" ^
      "  Record.HandlerFunc    : " ^ hf  in
      records := recStr :: !records in
    let header = 
        "GSCookieOffset   : " ^ gsc ^ "\n" ^
	"GSCookieXOROffset: " ^ gscx ^ "\n" ^
	"EHCookieOffset   : " ^ ehc ^ "\n" ^
	"EHCookieXOROffset: " ^ ehcx ^ "\n" in
    let _ = for _i = 1 to numRecords do read_record () done in
    header ^ (String.concat "\n" (List.rev !records))

  method private seh4_to_string =
    let str = self#get_data_string in
    let ch = make_pushback_stream str in
    let len = String.length str in
    let records = ref [] in
    let address = ref start_address in
    begin
      for _i = 0 to ((len / 4) - 1) do
	begin
	  records := (!address, ch#read_doubleword#to_hex_string) :: !records;
	  address := !address#add_int 4
	end 
      done;
      String.concat "\n" 
	(List.map
           (fun (a,v) -> "  " ^ a#to_hex_string ^ "  " ^ v) (List.rev !records))
    end

  method private data_table_to_string =
    let items =
      List.sort
        Stdlib.compare (H.fold (fun a s acc -> (a, s)::acc) data_table []) in
    String.concat "\n" (List.map (fun (a, s) -> a ^ "  " ^ s) items)

  method private rawdata_to_string =
    let len = self#get_length in
    let data = self#get_data_string in
    let alignedAddress = get_aligned_address start_address in
    if len <= 16 || alignedAddress#equal start_address then
      rawdata_to_string data start_address
    else
      let offset =
        fail_tvalue
          (trerror_record (STR "datablock#rawdata_to_string"))
          (alignedAddress#subtract_to_int start_address) in
      let suffix = String.sub data offset (len - offset) in
      let prefix = String.sub data 0 offset in
      (rawdata_to_string prefix start_address) ^ "\n" ^ 
	(rawdata_to_string suffix alignedAddress)

  method private largerawdata_to_string =
    let len = self#get_length in
    let data = self#get_data_string in
    let alignedAddr = get_1kaligned_address start_address in
    let offset =
      fail_tvalue
        (trerror_record (STR "datablock#largerawdata_to_string"))
        (alignedAddr#subtract_to_int start_address) in
    let data1 = String.sub data 0 offset in
    let datar = String.sub data offset (len - offset) in
    let addrr = start_address#add_int offset in
    let rec collect d addr acc =
      let dlen = String.length d in
      if dlen <= 1024 then
	(addr,d) :: acc
      else
	let df = String.sub d 0 1024 in
	let dr = String.sub d 1024 (dlen - 1024) in
	collect dr (addr#add_int 1024) ((addr,df) :: acc) in
    let rawdatastrings =
      (start_address,data1) :: (List.rev (collect datar addrr [])) in
    String.concat
      "\n" (List.map (fun (a,s) -> rawdata_to_string s a) rawdatastrings)

  method toString =
    let len = self#get_length in    
    if self#has_name && name = "zeroes" then
      "\n" ^ (string_repeat "-" 80) ^ "\nData block of zeroes: "
      ^ start_address#to_hex_string ^ " - "
      ^ end_address#to_hex_string  ^ " (size: "
      ^ (string_of_int len) ^ " bytes)\n" ^ (string_repeat "-" 80)
    else
      let sName = if self#has_name then (" (Name: " ^ name ^ ")") else "" in
      let sData =
        if self#has_data_string then 
	  (if name = "seh4_scopetable" then
	     self#seh4_scopetable_to_string
           else if name = "seh4" then
             self#seh4_to_string
           else if name = "data_table" then
             self#data_table_to_string
	   else if len > 1024 then
	     self#largerawdata_to_string
	   else
	     self#rawdata_to_string)
        else 
	  start_address#to_hex_string ^ " - " ^ end_address#to_hex_string in
      let sOffsettable = if is_offset_table then " (offset table)" else "" in
      let sLength = " (size: " ^ (string_of_int len) ^ " bytes)" in
      "\n"
      ^ (string_repeat "~" 80)
      ^ "\n"
      ^ "Data block"
      ^ sName
      ^ sLength
      ^ sOffsettable
      ^ "\n"
      ^ (string_repeat "~" 80)
      ^ "\n"
      ^ sData
      ^ "\n"
      ^ (string_repeat "=" 80)
      ^ "\n"
      
end


let make_data_block 
    ?(is_offset_table=false)
    (start_address:doubleword_int) 
    (end_address:doubleword_int) 
    (name:string): data_block_int TR.traceresult =
  let name = if name = "" then "data" else name in
  if start_address#equal end_address then
    Error [
        "make_data_block:zero-length data block:"
        ^ start_address#to_hex_string]
  else
    Ok (new data_block_t ~is_offset_table start_address end_address name)


let read_xml_data_block (node:xml_element_int): data_block_int TR.traceresult =
  let get = node#getAttribute in
  let geta t = string_to_doubleword (node#getAttribute t) in
  let has = node#hasNamedAttribute in
  let startAddress = geta "start" in
  let endAddress = geta "end" in
  let name = if has "name" then get "name" else "data" in
  TR.tbind
    ~msg:("BCHDataBlock.read_xml_data_block: " ^ (get "start"))
    (fun saddr ->
      TR.tbind
        ~msg:("BCHDataBlock.read_xml_data_block: " ^ (get "end"))
        (fun eaddr -> make_data_block saddr eaddr name)
        endAddress)
    startAddress


let create_jumptable_offset_block  
      (base:doubleword_int)
      (section_base:doubleword_int)
      (section:string)
      (jtlen:int): data_block_int TR.traceresult =
  TR.tbind
    ~msg:("create_jumptable_offset_block:invalid base address: "
          ^ base#to_hex_string)
    (fun pos ->
      let ch = make_pushback_stream section in
      let len = String.length section in
      let _ = ch#skip_bytes pos in
      let b = ref ch#read_byte in
      let _ =
        while (!b < jtlen || !b = 204) && ch#pos < len do
          b := ch#read_byte
        done in
      let endw = section_base#add_int (ch#pos - 1) in
      make_data_block ~is_offset_table:true base endw "jumptable offsets")
    (base#subtract_to_int section_base)


let find_seh4_struct
      (ch: pushback_stream_int)
      (len: int)
      (start_addr: doubleword_int):data_block_int TR.traceresult =
  let _ = ch#skip_bytes 8 in  (* EHCookieOffset ; EHCookeXOROffset *) 
  let screc = ref ch#read_doubleword in
  let min2 = TR.tget_ok (string_to_doubleword "0xfffffffe") in
  let sehlen = ref 16 in
  begin
    while !screc#equal min2 || !screc#equal wordzero && ch#pos < len - 12 do
      begin
	ch#skip_bytes 8;
	screc := ch#read_doubleword;
	sehlen := !sehlen + 12 
      end
    done;
    make_data_block start_addr (start_addr#add_int !sehlen) "seh4_scopetable"
  end


let find_seh4_structures_in_section (base:doubleword_int) (section:string) =
  let len = String.length section in
  let min2 = TR.tget_ok (string_to_doubleword "0xfffffffe") in
  let structs = ref [] in
  begin
    for i = 0 to 3 do
      let ch = make_pushback_stream section in
      begin
	ch#skip_bytes i;
	while ch#pos < len - 4 do
	  let dw = ch#read_doubleword in
	  if dw#equal min2 then               (* GSCookieOffset *)
	    let dw = ch#read_doubleword in     
	    if dw#equal wordzero then                  (* GSCookieXOROffset *)
	      let startAddr = base#add_int (ch#pos - 8) in
	      TR.titer
                (fun db ->
                  if db#get_length > 16 then
                    structs := db :: !structs)
              (find_seh4_struct ch len startAddr)
	done 
      end 
    done;
    !structs
  end


let find_seh4_structures 
    (read_only_section_strings:(doubleword_int * string) list) =
  List.concat
    (List.map (fun (base,s) ->
         find_seh4_structures_in_section base s)
       read_only_section_strings)

