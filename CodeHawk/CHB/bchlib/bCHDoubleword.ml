(* =============================================================================
   CodeHawk Binary Analyzer 
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

(* chlib *)
open CHPretty
open CHNumerical
open CHLanguage

(* chutil *)
open CHLogger
open CHTraceResult

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHUtilities

module B = Big_int_Z
module TR = CHTraceResult

(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e9   = 512
let e10  = 1024
let e15  = e7 * e8
let e16  = e8 * e8
let e31  = e15 * e16
let e32  = e16 * e16
let ffff = e16 - 1
let ffff_ffff = e32 - 1

let bige31 = B.big_int_of_int e31
let bige32 = B.big_int_of_int e32

let nume31 = mkNumerical e31
let nume32 = mkNumerical e32


let rec pow2 n =
  match n with
  | 0 -> 1
  | 1 -> 2
  | 2 -> 4
  | 3 -> 8
  | 4 -> 16
  | 5 -> 32
  | 6 -> 64
  | 7 -> e7
  | 8 -> e8
  | 9 -> e9
  | 10 -> e10
  | n ->
    let b = pow2 (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else 2)


(* utility functions *)
let get_nibbles v n =
  let rec aux v pos nibbles =
    if pos = n then nibbles 
    else aux (v lsr 4) (pos+1) ((v mod 16) :: nibbles) in
  aux v 0 []


let get_bytes v n =
  let rec aux v pos bytes =
    if pos = n then bytes
    else aux (v lsr 8) (pos+1) ((v mod 256) :: bytes) in
  aux v 0 []


let dw_index_to_pretty (index:dw_index_t) = INT index


(* doubleword_t ---------------------------------------------------------------
   32-bit word constructed from an unsigned 64-bit integer (immutable)
   ---------------------------------------------------------------------------- *)
class doubleword_t (n:int):doubleword_int =
object (self:'a)

  val unsigned_value:int = n

  method value = unsigned_value

  method index = unsigned_value

  (* --------------------------------------------------------~---- comparison -- *)

  method equal (other:'a) = other#index = self#index
  method compare (other:'a) = Stdlib.compare self#index other#index
  method lt (other:'a) = self#index < other#index
  method le (other:'a) = self#index <= other#index

  (* -----------------------------------------------------~---~--- conversion -- *)
    
  method to_int = unsigned_value
  method to_big_int = B.big_int_of_int unsigned_value
  method to_numerical = mkNumerical unsigned_value

  method to_time_date_string:string =
    if unsigned_value = 0 || unsigned_value = ffff_ffff then 
      self#to_fixed_length_hex_string
    else
      make_date_and_time_string (Unix.localtime (float unsigned_value))
	
  method to_char_string:string option =
    if unsigned_value = 0 then
      None
    else
      let is_printable c = (c >= 32 && c < 127) || c = 10 || c = 0 in
      let pc i = if i = 0 then "'\\0'" else Printf.sprintf "'%c'" (Char.chr i) in
      let bytes = get_bytes unsigned_value 4 in
      if List.for_all is_printable bytes then
	match bytes with [b4; b3; b2; b1] ->
	  Some ("[" ^ (pc b1) ^ " " ^ (pc b2) ^ " " ^ (pc b3) ^ " " ^ (pc b4) ^ "]")
	  | _ -> None
      else
	None

  method to_string_fragment:string =
    let bytes = get_bytes unsigned_value 4 in
    let pc i = if i=0 then "" else Printf.sprintf "%c" (Char.chr i) in
    match bytes with
    |[b4; b3; b2; b1] -> (pc b1) ^ (pc b2) ^ (pc b3) ^ (pc b4)
    | _ ->
       begin
	 ch_error_log#add
           "internal error"
	   (LBLOCK [
                STR "doubleword_t#to_string_fragment: ";
		pretty_print_list bytes (fun b -> INT b) "[" "; " "]"]);
	 raise (Internal_error "doubleword_t#to_string_fragment")
       end

  method to_string:string =
    let bytes = get_bytes unsigned_value 4 in
    let pc i = Printf.sprintf "%c" (Char.chr i) in
    match bytes with
    | [b1; b2; b3; b4 ] -> (pc b1) ^ (pc b2) ^ (pc b3) ^ (pc b4)
    | _ ->
       begin
	 ch_error_log#add
           "internal error"
	   (LBLOCK [
                STR "doubleword_t#to_string_fragment: ";
		pretty_print_list bytes (fun b -> INT b) "[" "; " "]"]);
	 raise (Internal_error "doubleword_t#to_string_fragment")
       end

  method to_fixed_length_hex_string:string =
    let nibbles = get_nibbles unsigned_value 8 in
    match nibbles with
    | [n8; n7; n6; n5; n4; n3; n2; n1] ->
       Printf.sprintf "%x%x%x%x%x%x%x%x" n8 n7 n6 n5 n4 n3 n2 n1
    | _ ->
       begin
	 ch_error_log#add
           "internal error"
	   (LBLOCK [
                STR "doubleword_t#fixed_length_hex_string inconsistent value: ";
		pretty_print_list nibbles (fun n -> INT n) "[" "; " "]"]);
	 raise (Internal_error "doubleword_t#to_fixed_length_hex_string")
       end

  method to_fixed_length_hex_string_le:string =
    let nibbles = get_nibbles unsigned_value 8 in
    match nibbles with
    | [n8; n7; n6; n5; n4; n3; n2; n1] ->
       Printf.sprintf "%x%x%x%x%x%x%x%x" n2 n1 n4 n3 n6 n5 n8 n7
    | _ ->
       begin
         ch_error_log#add
           "internal error"
           (LBLOCK [
                STR "doubleword_t#fixed_length_hex_string_le inconsistent value: ";
                pretty_print_list nibbles (fun n -> INT n) "[" "; " "]"]);
         raise (Internal_error "doubleword_t#to_fixed_length_hex_string_le")
       end

  method to_hex_string:string =
    let nibbles = get_nibbles unsigned_value 8 in
    match nibbles with
    | [n8; n7; n6; n5; n4; n3; n2; n1] ->
       begin
	 match n8 with
	 | 0 -> begin match n7 with
		| 0 -> begin match n6 with
		       | 0 -> begin match n5 with
			      | 0 -> begin match n4 with
			             | 0 -> begin match n3 with
				            | 0 -> begin match n2 with
				                   | 0 -> Printf.sprintf "0x%x" n1
				                   | _ -> Printf.sprintf "0x%x%x" n2 n1 end
				            | _ -> Printf.sprintf "0x%x%x%x" n3 n2 n1 end
			             | _ -> Printf.sprintf "0x%x%x%x%x" n4 n3 n2 n1 end
			      | _ -> Printf.sprintf "0x%x%x%x%x%x" n5 n4 n3 n2 n1 end
		       | _ -> Printf.sprintf "0x%x%x%x%x%x%x" n6 n5 n4 n3 n2 n1 end
		| _ -> Printf.sprintf "0x%x%x%x%x%x%x%x" n7 n6 n5 n4 n3 n2 n1 end
	 | _ -> Printf.sprintf "0x%x%x%x%x%x%x%x%x" n8 n7 n6 n5 n4 n3 n2 n1 end
    | _ ->
       begin
	 ch_error_log#add
           "invalid argument"
	   (LBLOCK [
                pretty_print_list nibbles (fun i -> INT i) "[" "; " "]"; NL]);
	 raise (Internal_error "doubleword_t#to_hex_string")
       end


  method to_signed_hex_string:string =
    if unsigned_value < e31 then
      self#to_hex_string
    else
      let signedValue = abs (unsigned_value - e32) in
      "-" ^ ({< unsigned_value = signedValue >})#to_hex_string
		     
  method to_signed_numerical:numerical_t =
    if unsigned_value < e31 then
      self#to_numerical
    else
      self#to_numerical#sub (mkNumerical e32)
		    
  (* ------------------------------------------------------------- operations -- *)

  method unset_highest_bit =
    if self#is_highest_bit_set then
      {< unsigned_value = unsigned_value - e31 >}
    else
      {< >}

  method subtract (other: 'a): 'a traceresult =
    if other#value <= self#value then
      Ok {< unsigned_value = self#value - other#value >}
    else
      Error [
          "dw#subtract_int: "
          ^ (self#to_hex_string)
          ^ ", "
          ^ other#to_hex_string]

  method subtract_int (i: int): 'a traceresult =
    if i<= unsigned_value then
      Ok {< unsigned_value = unsigned_value - i >}
    else
      Error [
          "dw#subtract_int: "
          ^ (self#to_hex_string)
          ^ ", "
          ^ (string_of_int i)]

  method subtract_to_int (other: 'a): int traceresult =
    if other#value <= self#value then
      Ok (self#value - other#value)
    else
      Error [
          "dw#subtract_to_int: "
          ^ (self#to_hex_string)
          ^ ", "
          ^ (other#to_hex_string)]

  method add (other: 'a) =
    let sum = self#index + other#index in
    {< unsigned_value = sum mod e32 >}

  method add_int (i: int):'a =
    let sum = unsigned_value + i in
    {< unsigned_value = sum mod e32 >}

  method multiply_int (i: int):'a traceresult =
    let product = i * unsigned_value in
    if product <= ffff_ffff then
      Ok {< unsigned_value = product >}
    else
      Error [
          "dw#multiply_int: "
          ^ (self#to_hex_string)
          ^ ", "
          ^ (string_of_int i)]

  method xor (other:'a) =
    {< unsigned_value = (self#to_int lxor other#to_int) mod e32 >}


  (* -----------------------------------------------------~---~---- accessors -- *)

  method get_low = unsigned_value mod e16

  method get_high = unsigned_value / e16

  method get_bits_set =
    let rec aux pos v bits =
      if pos = 32 then bits 
      else if v mod 2 = 1 then aux (pos+1) (v lsr 1) (pos::bits)
      else aux (pos+1) (v lsr 1) bits in
    aux 0 unsigned_value []

  (* return the value of the given bit (zero-based) *)
  method get_bitval (pos: int) =
    if pos < 0 || pos > 31 then
      raise
        (BCH_failure
           (LBLOCK [STR "Error in get_bitval at "; INT pos]))
    else
      if self#is_nth_bit_set pos then 1 else 0

  method get_reverse_bitval (refsize: int) (pos: int) =
    if pos < 0 || pos >= refsize || refsize > 32 then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Error in get_reverse_bitval at ";
                INT pos;
                STR " with refsize ";
                INT refsize]))
    else
      let maxindex = refsize - 1 in
      self#get_bitval (maxindex - pos)

  (* return the value of bits highpos through lowpos (inclusive, zero-based) *)
  method get_segval (highpos:int) (lowpos:int) =
    if highpos > 31 || lowpos < 0 || highpos < lowpos then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Error in get_segval: ";
                STR "highpos: ";
                INT highpos;
                STR "; lowpos: ";
                INT lowpos]))
    else if highpos = lowpos then
      if self#is_nth_bit_set highpos then 1 else 0
    else
      let r = unsigned_value lsr lowpos in
      r mod (pow2 ((highpos-lowpos) + 1))

  (* return the value of bits lowpos through highpos (inclusive, zero-based)
   * where the numbering is reversed with respect to the reference size *)
  method get_reverse_segval (refsize: int) (lowpos: int) (highpos: int) =
    if lowpos < 0 || highpos >= refsize || refsize > 32 then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Error in get_reverse_segval: ";
                STR "lowpos: ";
                INT lowpos;
                STR "; highpos: ";
                INT highpos;
                STR "; refsize: ";
                INT refsize]))
    else
      let maxindex = refsize - 1 in
      self#get_segval (maxindex - lowpos) (maxindex - highpos)


  (* --------------------------------------------------------~---- predicates -- *)

  method is_highest_bit_set = (unsigned_value lsr 31) = 1

  method is_nth_bit_set (n:int) =
    if n >= 0  && n < 32 then
      (unsigned_value lsr n) mod 2 = 1
    else
      begin
	ch_error_log#add "invalid argument"
	  (LBLOCK [ STR "is_nth_bit_set: " ; INT n ; STR " is out of range"]) ;
	raise (Invalid_argument "doubleword_t#is_nth_bit_set")
      end

  (* --------------------------------------------------------------- printing -- *)

  method toPretty = STR self#to_hex_string

end


let wordzero = new doubleword_t 0
let wordmax  = new doubleword_t ffff_ffff

let wordnegone = wordmax
let wordnegtwo = new doubleword_t (e32 - 2)


let create_doubleword (n: int): doubleword_result =
  if n >= 0 && n < e32 then
    Ok (new doubleword_t n)
  else if abs n <= e31 then
    Ok (new doubleword_t (n + e32))
  else
    Error ["create_doubleword:out-of-range:" ^ (string_of_int n)]


let make_doubleword (l: int) (h: int): doubleword_result =
  if l < 0 || l >= e16 then
    Error ["make_doubleword:low-out-of-range:" ^ (string_of_int l)]
  else if h < 0 || h > e16 then
    Error ["make_doubleword:high-out-of-range:" ^ (string_of_int h)]
  else
    Ok (new doubleword_t ((h * e16) + l))


let index_to_doubleword (index: dw_index_t): doubleword_result =
  create_doubleword index


let int_to_doubleword (i: int): doubleword_result = create_doubleword i


let align_doubleword (dw: doubleword_int) (alignment: int): doubleword_result =
  if alignment <= 0 then
    Error ["align_doubleword with alignment:" ^ (string_of_int alignment)]
  else
    let rem = dw#to_int mod alignment in
    if rem = 0 then
      Ok dw
    else
      int_to_doubleword (((dw#to_int / alignment) + 1) * 4)


let big_int_to_doubleword (bi: B.big_int): doubleword_result =
  let intb =
    try
      Ok (B.int_of_big_int bi)
    with
    | _ ->
       Error [
           "big_int_to_doubleword:error in conversion to int:"
           ^ (B.string_of_big_int bi)] in
  TR.tbind create_doubleword intb


let numerical_to_doubleword (num:numerical_t): doubleword_result =
  let intnum =
    try
      Ok num#toInt
    with
    | _ ->
       Error [
           "numerical_to_doubleword:error in conversion to int:"
           ^ num#toString] in
  TR.tbind create_doubleword intnum


let dw_index_to_int (index:dw_index_t) = index


let int_to_dw_index (index:int) = index


let string_to_doubleword (s: string): doubleword_result =
  let i64 =
    try
      Ok (Int64.of_string s)
    with
    | _ ->
       Error ["string_to_doubleword:error in conversion to Int64:" ^ s] in
  let bi = TR.tmap B.big_int_of_int64 i64 in
  TR.tbind big_int_to_doubleword bi


let numerical_to_hex_string (num: numerical_t): string TR.traceresult =
  TR.tmap
    ~msg:"numerical_to_hex_string"
    (fun dw -> dw#to_hex_string)
    (numerical_to_doubleword num)


let numerical_to_signed_hex_string (num: numerical_t): string TR.traceresult =
  let big_val = num#getNum in
  let abs_val = B.abs_big_int big_val in
  TR.tmap
    ~msg:"numerical_to_signed_hex_string"
    (fun dw ->
      if B.lt_big_int big_val B.zero_big_int then
        "-" ^ dw#to_hex_string
      else
        dw#to_hex_string)
    (big_int_to_doubleword abs_val)


let symbol_to_doubleword (symbol:symbol_t): doubleword_result =
  match symbol#getAttributes with
  | s :: _ -> string_to_doubleword s
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "Symbol cannot be converted to doubleword: ";
               symbol#toPretty]))


let doubleword_to_symbol (name:string) ?(atts=[]) (dw: doubleword_int) =
  try
    new symbol_t ~atts:(dw#to_hex_string::atts) name
  with
  | BCH_failure p ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "doubleword_to_symbol: ";
               STR name;
               STR ", ";
               dw#toPretty;
               STR " (";
               p;
               STR ")"]))
