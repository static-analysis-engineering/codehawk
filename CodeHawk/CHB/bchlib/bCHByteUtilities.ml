(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes


module DoublewordCollections = CHCollections.Make
  (struct
    type t = doubleword_int
    let compare dw1 dw2 = dw1#compare dw2
    let toPretty dw = STR dw#to_fixed_length_hex_string
   end)

let is_printable c = (c >= 32 && c < 127) 
  
let is_printable_char c = is_printable (Char.code c)

let byte_to_string (b:int):string = 
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l

let get_aligned_address (a:doubleword_int) =
  let n16 = mkNumerical 16 in
  let n = a#to_numerical in
  if (n#modulo n16)#equal numerical_zero then 
    a
  else
    let n = ((n#div n16)#mult n16)#add n16 in
    numerical_to_doubleword n

let get_1kaligned_address (a:doubleword_int) =
  let n1024 = mkNumerical 1024 in
  let n = a#to_numerical in
  if (n#modulo n1024)#equal numerical_zero then
    a
  else
    let n = ((n#div n1024)#mult n1024)#add n1024 in
    numerical_to_doubleword n

(* return the byte_string to a string containing 16 bytes in hexadecimal form
   per line *)
let rawdata_to_string ?(markwritten:(doubleword_int list option)) (byte_string:string) 
    (start_address:doubleword_int):string =
  let ch = IO.input_string byte_string in
  let current_address = ref start_address in
  let len = String.length byte_string in
  let lines = len / 16 in
  let remaining_bytes = len mod 16 in
  let s = ref "" in
  let a = Array.make 16 0 in
  let pr_marked:(doubleword_int -> string) = 
    match markwritten with
      Some l -> 
	let mwset = new DoublewordCollections.set_t in
	let _ = mwset#addList l in
	fun address -> 
	  let ws = ref "" in
	  let aa = ref address in
	  begin
	    for i = 1 to 4 do
	      (if mwset#has !aa then ws := !ws ^ "W " else ws := !ws ^ ". " );
	      aa := (!aa)#add_int 4
	    done;
	    !ws
	  end
    | _ -> fun _ -> "" in
  let bytes_to_line_output () =
    begin
      s := !s ^ !current_address#to_fixed_length_hex_string ;
      s := !s ^ " " ;
      for i=0 to 3 do
	for j=0 to 3 do
	  s := !s ^ (byte_to_string a.(4*i+j));
	done;
	s := !s ^ " " ;
      done;
      s := !s ^ " " ^ (pr_marked !current_address) ^ " " ;
      s := !s ^ " " ;
      for i=0 to 15 do
	if is_printable a.(i) then
          s := !s ^ (Printf.sprintf "%c" (Char.chr a.(i)))
        else
          s := !s ^ "."
      done;
      s := !s ^ (Printf.sprintf "\n")
    end in
  begin
    for i=0 to lines-1 do 
      begin
	for j=0 to 15 do a.(j) <- IO.read_byte ch done;
	bytes_to_line_output ();
	current_address := !current_address#add_int 16 
      end
    done;
    (if remaining_bytes > 0 then
      let k = ref 0 in
      let m = ref 0 in
      for j=0 to remaining_bytes-1 do a.(j) <- IO.read_byte ch done;
      begin
	s := !s ^ !current_address#to_fixed_length_hex_string ;
	s := !s ^ " " ; 
	while (4*(!k) + (!m)) < remaining_bytes do
	  while (4*(!k) + (!m)) < remaining_bytes && !m < 4 do
	    s := !s ^ (byte_to_string a.(4*(!k)+(!m)));
	    m := !m + 1 ;
	  done ;
	  k := !k + 1;
	  m := 0 ;
	  s := !s ^ " " ;
	done ;
	for i=0 to (16 - remaining_bytes) do s := !s ^ "  " done ;
	for i=0 to remaining_bytes-1 do
	  if is_printable a.(i) then
            s := !s ^ (Printf.sprintf "%c" (Char.chr a.(i)))
          else
            s := !s ^ "."
	done
      end) ;
    !s
  end

let write_xml_raw_data_block
    (node:xml_element_int) 
    (byte_string:string) 
    (start_address:doubleword_int) =
  let append = node#appendChildren in
  let ch = IO.input_string byte_string in
  let currentAddr = ref start_address in
  let len = String.length byte_string in
  let lines = len / 16 in
  let remainingBytes = len mod 16 in
  let nodes = ref [] in
  let a = Array.make 16 0 in
  let get_char i =
    if is_printable a.(i) then
      Printf.sprintf "%c" (Char.chr a.(i))
    else
      "." in
  let write_xml_line lNode = 
    let s = ref "" in
    let p = ref "" in
    begin
      (for i = 0 to 3 do
         for j=0 to 3 do
           s := !s ^ (byte_to_string a.(4*i+j))
         done; s := !s ^ " "
       done) ;
      (for i = 0 to 15 do p := !p ^ (get_char i) done);
      lNode#setAttribute "bytes" !s ;
      lNode#setAttribute "print" !p ;
    end in
  let write_xml_partial_line lNode = 
    let s = ref "" in
    let p = ref "" in
    begin
      (for i = 0 to remainingBytes-1 do
         s := !s ^ (byte_to_string a.(i))
       done) ;
      (for i = 0 to remainingBytes-1 do
         p := !p ^ (get_char i)
       done) ;
      lNode#setAttribute "bytes" !s ;
      lNode#setAttribute "print" !p ;
      lNode#setIntAttribute "length" remainingBytes
    end in
  begin
    for i=0 to lines-1 do
      let lNode = xmlElement "aline" in
      begin
	lNode#setAttribute "va" !currentAddr#to_hex_string ;
	for j=0 to 15 do a.(j) <- IO.read_byte ch done;
	write_xml_line lNode ;
	nodes := lNode :: !nodes ;
	currentAddr := !currentAddr#add_int 16
      end
    done;
    (if remainingBytes > 0 then
	let lNode = xmlElement "aline" in
	begin
	  lNode#setAttribute "va" !currentAddr#to_hex_string ;
	  for j=0 to remainingBytes-1 do a.(j) <- IO.read_byte ch done;
	  write_xml_partial_line lNode ;
	  nodes := lNode  :: !nodes
	end) ;
    append (List.rev !nodes)
  end

let write_xml_raw_data
    (node:xml_element_int) 
    (byte_string:string) 
    (start_address:doubleword_int) =
  let blocksize = 160000 in
  let rec strdivide str len result =
    let strlen = String.length str in
    if strlen <= len then 
      List.rev (str::result)
    else
      let strpre = String.sub str 0 len in
      let strsuf = String.sub str len (strlen - len) in
      strdivide strsuf len (strpre :: result) in
  let strblocks = strdivide byte_string blocksize [] in
  begin
    node#appendChildren (List.mapi (fun i bstr ->
      let bNode = xmlElement "ablock" in
      let addr = start_address#add_int (i * blocksize) in
      begin
	write_xml_raw_data_block bNode bstr addr ;
	bNode#setIntAttribute "block" i ;
	bNode
      end) strblocks) ;
    node#setIntAttribute "blocks" (List.length strblocks)
  end


let read_xml_raw_data_block (node:xml_element_int) =
  let bNodes = node#getTaggedChildren "aline" in
  let ch = IO.output_string () in
  begin
    List.iter (fun n ->
      let has = n#hasNamedAttribute in
      let geti = n#getIntAttribute in
      let byteString = n#getAttribute "bytes" in
      if has "length" then 
	for i = 0 to (geti "length") - 1 do 
	  let s = "0x" ^ (String.sub byteString (i*2) 2) in
	  try
	    let b = int_of_string s in IO.write_byte ch b 
	  with Failure _ ->
	    begin
	      pr_debug [ STR "Failure (length): " ; STR s ; NL ] ;
	      raise (Failure "int-of-string") 
	    end
	done
      else
	for i = 0 to 3 do
	  for j = 0 to 3 do 
	    let s = "0x" ^ (String.sub byteString ((i*9) + (j*2)) 2) in
	    try
	      let b = int_of_string s in IO.write_byte ch b 
	    with Failure _ ->
	      begin
		pr_debug [ STR "Failure: " ; STR s ; NL ] ;
		raise (Failure "int-of-string") 
	      end
	  done
	done) bNodes ;
      IO.close_out ch
  end

let write_doubleword_to_bytestring (dw:doubleword_int) =
  let ch = IO.output_string () in
  let hexstring = dw#to_fixed_length_hex_string in
  begin
    for i = 0 to 3 do
      let s = "0x" ^ (String.sub hexstring ((3-i)*2) 2) in
      try
	let b = int_of_string s in IO.write_byte ch b
      with Failure _ ->
	begin
	  pr_debug [ STR "Failure: " ; STR s ; NL ] ;
	  raise (Failure "int-of-string") 
	end
    done ;
    IO.close_out ch
  end
      

let read_xml_raw_data (node:xml_element_int) =
  String.concat
    "" (List.map read_xml_raw_data_block (node#getTaggedChildren "ablock"))

let byte_string_to_spaced_string (byte_string:string):string =
  let ch = IO.input_string byte_string in
  let s = ref "" in
  let len = String.length byte_string in
  begin
    for i = 0 to len-1 do s := !s ^ (byte_to_string (IO.read_byte ch)) ^ " " done;
    !s
  end

let byte_string_to_printed_string (byte_string:string):string =
  let ch = IO.input_string byte_string in
  let s = ref "" in
  let len = String.length byte_string in
  begin
    for i = 0 to len-1 do s := !s ^ (byte_to_string (IO.read_byte ch)) done;
    !s
  end
  
(* converts a little-endian hex string for a doubleword extracted by pattern 
   matching to the corresponding doubleword string *)
let littleendian_hexstring_todwstring (s:string) =
  let b = Bytes.of_string s in
  let bnew = Bytes.copy b in
  let cp pn po = Bytes.set bnew pn (Bytes.get b po) in
  begin
    cp 0 6 ;
    cp 1 7 ;
    cp 2 4 ;
    cp 3 5 ;
    cp 4 2 ;
    cp 5 3 ;
    cp 6 0 ;
    cp 7 1 ;
    "0x" ^ Bytes.to_string bnew
  end

let littleendian_hexstring_towstring (s:string) =
  let b = Bytes.of_string s in
  let bnew = Bytes.copy b in
  let cp pn po = Bytes.set bnew pn (Bytes.get b po) in
  begin
    cp 0 2 ;
    cp 1 3 ;
    cp 2 0 ;
    cp 3 1 ;
    "0x" ^ Bytes.to_string bnew
  end
  
let decode_string_aux (s:string) (va:doubleword_int) 
    (enc:(string * doubleword_int * doubleword_int * doubleword_int * int)) = 
  let (_, start, size, key, width) = enc in
  let offset =
    try
      (start#subtract va)#to_int + width
    with
    | Invalid_argument s ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in decode_string_aux at address with ";
                 STR "start: ";
                 start#toPretty;
                 STR "; va: ";
                 va#toPretty;
                 STR ": ";
                 STR s])) in
  let prefix = String.sub s 0 offset in
  let encstring = String.sub s offset size#to_int in
  let suffix =
    String.sub
      s (offset + size#to_int) ((String.length s) - (offset + size#to_int)) in
  try
    let ch = IO.input_string encstring in
    if width = 4 then
      let read_doubleword ch =
	let l = IO.read_ui16 ch in
	let h = IO.read_ui16 ch in
	make_doubleword l h in
      let result = ref prefix in
      begin
	for i = 0 to ((size#to_int / 4) - 2) do
	  let dw = read_doubleword ch in
	  let decoded = dw#xor key in
	  result := !result ^ (write_doubleword_to_bytestring decoded) ;
	done;
	!result ^ suffix
      end
    else if width = 1 then
      let result = ref prefix in
      begin
	for i = 0 to size#to_int - 1 do
	  let b = IO.read_byte ch in
	  let decoded = b lxor key#to_int in
	  let ch = IO.output_string () in
	  let _ = IO.write_byte ch decoded in
	  let bs = IO.close_out ch in
	  result := !result ^ bs
	done;
	!result ^ suffix
      end
    else
      s
  with
    _ ->
    let encoding_to_pretty (ty,va,size,key,width) =
      LBLOCK [
          STR "(";
          STR ty;
          STR ",";
          va#toPretty;
          STR ",";
          size#toPretty;
	  STR ",";
          key#toPretty;
          STR ",";
          INT width] in
	begin
	  pr_debug [
              STR "Error in decode_string with ";
	      encoding_to_pretty enc;
              NL;
	      STR " and string length ";
	      INT (String.length encstring);
              STR " and base address ";
              va#toPretty;
              NL;
	      STR " and offset ";
              INT offset;
              NL] ;
	raise (BCH_failure (STR "Error in decoding"))
      end


let decode_string (str:string) (va:doubleword_int) 
      (encodings:
         (string * doubleword_int * doubleword_int * doubleword_int * int) list) =
  List.fold_left (fun s e -> decode_string_aux s va e) str encodings


let read_hex_stream_file (filename:string) =
  let ch = open_in filename in
  let outch  = IO.output_string () in
  let _ = try
      while true do
        let line = input_line ch in
        for i = 0 to 39 do
          let s = "0x" ^ (String.sub line (i*2) 2) in
          try
            let b = int_of_string s in IO.write_byte outch b
          with
          | Failure _ ->
             begin
               pr_debug [ STR "Failure in reading stream file: "; STR s; NL] ;
               raise (Failure "read_stream:int_of_string")
             end
        done
      done
    with _ -> () in
  IO.close_out outch
