(* =============================================================================
   CodeHawk Binary Analyzer 
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

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper


class jumptable_t
        ?(end_address: doubleword_int option=None)
        ~(start_address: doubleword_int)
        ~(targets      : doubleword_int list):jumptable_int =
object (self)

  val end_address =
    match end_address with
    | Some e -> e
    | _ -> start_address#add_int ((List.length targets) * 4)
  val mutable startaddress_valid = true 

  method invalidate_startaddress = startaddress_valid <- false

  method get_start_address = start_address
  method get_end_address   = end_address

  method get_all_targets = 
    let tgts = if startaddress_valid then targets else List.tl targets in
    let tgts =
      List.fold_left
        (fun acc t ->
          if List.mem t#to_hex_string acc then acc else t#to_hex_string :: acc)
        [] tgts in
    List.map string_to_doubleword tgts

  method get_targets (base:doubleword_int) (lb:int) (ub:int) =
    List.map snd (self#get_indexed_targets base lb ub)

  method get_length = (end_address#subtract start_address)#to_int

  method get_indexed_targets (base:doubleword_int) (tableLb:int) (tableUb:int)  =
    let baseOffset =                              (* userIndex - tableIndex *)
      if base#lt start_address then
	(start_address#subtract base)#to_int / 4
      else
	(base#subtract start_address)#to_int * (-1) / 4 in
    (* let tableLb = lb - baseOffset in
    let tableUb = ub - baseOffset in *)
    if tableLb >= 0 && tableUb < List.length targets then
      let result = ref [] in
      begin
	for i = tableLb to tableUb do
	  result := (i + baseOffset, List.nth targets i) :: !result
	done;
	List.rev !result
      end
    else
      begin
	ch_error_log#add "jump table range"
	  (LBLOCK [ STR "table-lowerbound: " ; INT tableLb ; STR "; table-upperbound: " ; 
		    INT tableUb ; STR "; table-length: " ; INT (List.length targets) ]) ;
	[]
      end
    
  method includes_address (addr:doubleword_int) =
    start_address#le (addr#add_int 4) && addr#le end_address &&
      ((addr#lt start_address && (start_address#subtract addr)#to_int mod 4 = 0) ||
      (start_address#le addr && (addr#subtract start_address)#to_int mod 4 = 0))

  method toPretty
           ~(is_function_entry_point:(doubleword_int -> bool))
           ~(get_opt_function_name:(doubleword_int -> string option)) =
    STR (self#toString ~is_function_entry_point ~get_opt_function_name)

  method toString
           ~(is_function_entry_point:doubleword_int -> bool)
           ~(get_opt_function_name:doubleword_int -> string option):string =
    let jumpTableString = String.concat "\n" 
      (List.mapi 
	 (fun i t -> 
	   "    " ^ (start_address#add_int (i*4))#to_hex_string ^ "  " ^ 
	     t#to_hex_string ^ " (" ^
	     (string_of_int i) ^ ")" ^
	     (if is_function_entry_point t then " (F)" else "") ^
	     (match get_opt_function_name t with Some s -> "  " ^ s | _ -> "")) targets) in
    (string_repeat "~" 80) ^ "\n" ^ "Jump table at " ^ start_address#to_hex_string ^ " (" ^
      (string_of_int (List.length targets)) ^ " targets)" ^ 
      (if startaddress_valid then "" else " (startaddress not included)") ^ "\n" ^ 
      (string_repeat "~" 80) ^ "\n" ^
      jumpTableString ^ "\n" ^ (string_repeat "=" 80) ^ "\n"
      
  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    begin
      append (List.map (fun t ->
	let tNode = xmlElement "tgt" in 
	begin tNode#setAttribute "a" t#to_hex_string ; tNode end) targets) ;
      set "start" start_address#to_hex_string ;
      (if startaddress_valid then () else set "startaddress-valid" "no")
    end
      
end


let make_jumptable
      ?(end_address: doubleword_int option=None)
      ~(start_address:doubleword_int)
      ~(targets:doubleword_int list) =
  new jumptable_t ~end_address ~start_address ~targets


let split_jumptable
      ~(jumptable:jumptable_int)
      ~(sizes:int list):jumptable_int list =
  let startaddr = jumptable#get_start_address in
  let alltargets = jumptable#get_all_targets in
  let (_,jtables) =
    List.fold_left (fun (offset,jts) size ->
        let addr = startaddr#add_int (offset *  4) in
        let targets = list_sub alltargets offset size in
        let newtable = new jumptable_t addr targets in
        (offset + size, newtable::jts)) (0,[]) sizes in
  jtables

let read_xml_jumptable (node:xml_element_int) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let geta n t = string_to_doubleword (n#getAttribute t) in
  let isinvalid = has "startaddress-valid" && (get "startaddress-valid") = "no" in
  let getcc = node#getTaggedChildren in
  let startAddress = geta node "start" in
  let targets = List.map (fun n -> geta n "a") (getcc "tgt") in
  let table = make_jumptable startAddress targets in
  begin
    (if isinvalid then table#invalidate_startaddress) ;
    table
  end


(* we consider a range of doublewords a jump table if it consists of at least three
 * valid code addresses
*)
let find_jumptable is_code_address ch len start_address target1 =
  let rec extract_jumptable start targets =
    let maxDiff = int_to_doubleword 10000 in
    let t1 = List.nth targets 0 in
    let t2 = List.nth targets 1 in
    let diff = if t1#le t2 then t2#subtract t1 else t1#subtract t2 in
    if maxDiff#lt diff then
      if (List.length targets) > 2 then
	extract_jumptable (start#add_int 4) (List.tl targets)
      else
	None
    else
      Some (make_jumptable start targets) in
  if ch#pos < len-4 then
    let target2 = ch#read_doubleword in
    if is_code_address target2 then
      if ch#pos < len - 4 then
	let target3 = ch#read_doubleword in
	if is_code_address target3 then
	  if ch#pos < len - 4 then
	    let targets = ref [ target3 ; target2 ; target1 ] in
	    let target = ref ch#read_doubleword in
	    begin
	      while is_code_address !target do
		targets := !target :: !targets ;
		if ch#pos <= len - 4 then target := ch#read_doubleword else target := wordzero
	      done;
	      extract_jumptable start_address (List.rev !targets)
	    end
	  else None
	else None
      else None
    else None
  else None
    
let find_jumptables_in_section
    (base:doubleword_int)
    (is_code_address:doubleword_int -> bool)
    (section:string) =
  let len = String.length section in
  let tables = ref [] in
  if len >= 4 then
    begin
      for i = 0 to 3 do
	let ch = make_pushback_stream section in
	begin
	  ch#skip_bytes i ;
	  while ch#pos <= len - 4 do
	    let dw = ch#read_doubleword in
	    if is_code_address dw then
	      let startAddress = base#add_int (ch#pos - 4) in
	      let optTable = find_jumptable is_code_address ch len startAddress dw in
	      match optTable with Some t -> tables := t :: !tables | _ -> ()
	  done
	end
      done;
      !tables
    end
  else
    []

let find_jumptables 
    ~(is_code_address:doubleword_int -> bool) 
    ~(read_only_section_strings:(doubleword_int * string) list) =
  List.concat 
    (List.map (fun (base,s) -> find_jumptables_in_section base is_code_address s) 
       read_only_section_strings)
    
    

let find2_jumptable is_code_address ch len start_address target1 =
  if ch#pos < len-4 then
    let target2 = ch#read_doubleword in
    if is_code_address target2 then
      if ch#pos < len - 4 then
	let targets = ref [ target2 ; target1 ] in
	let target = ref ch#read_doubleword in
	begin
	  while is_code_address !target do
	    targets := !target :: !targets ;
	    if ch#pos <= len - 4 then target := ch#read_doubleword else target := wordzero
	  done;
	  Some (make_jumptable start_address (List.rev !targets))
	end
      else None
    else None
  else None

let create_jumptable 
    ~(base:doubleword_int) 
    ~(section_base:doubleword_int)
    ~(is_code_address:doubleword_int -> bool)
    ~(section_string:string) =
  try
    let len = String.length section_string in
    let pos = (base#subtract section_base)#to_int in
    let ch = make_pushback_stream section_string in
    let _ = ch#skip_bytes pos in
    let dw = ch#read_doubleword in
    if is_code_address dw then
      find2_jumptable is_code_address ch len base dw
    else
      None
  with
  | Invalid_argument s ->
    begin
      ch_error_log#add "create jumptable" (LBLOCK [ STR "Error: " ; STR s ]) ;
      None
    end
  | _ ->
    begin
      ch_error_log#add "create jumptable" (LBLOCK [ STR "Unknown error" ]) ;
      None
    end
    
