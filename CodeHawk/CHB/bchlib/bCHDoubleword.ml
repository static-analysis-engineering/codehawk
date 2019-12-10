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
open CHNumerical
open CHLanguage

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHUtilities

module B = Big_int_Z

(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31  = e15 * e16
let e32  = e16 * e16
let ffff = e16 - 1
let ffff_ffff = e32 - 1

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

(*
type dw_index_t = int
*)

let dw_index_to_pretty (index:dw_index_t) = INT index
  (* LBLOCK [ STR "(" ; INT (fst index) ; STR "," ; INT (snd index) ; STR ")" ] *)

(** doubleword_t ---------------------------------------------------------------
    32-bit word constructed from an unsigned 64-bit integer (immutable)
    ---------------------------------------------------------------------------- *)
class doubleword_t (n:int):doubleword_int =
object (self:'a)

  val unsigned_value:int = n

  method index = unsigned_value

  (* --------------------------------------------------------~---- comparison -- *)

  method equal (other:'a) = other#index = self#index
  method compare (other:'a) = Pervasives.compare self#index other#index
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
	match bytes with [ b4 ; b3 ; b2 ; b1 ] ->
	  Some ("[" ^ (pc b1) ^ " " ^ (pc b2) ^ " " ^ (pc b3) ^ " " ^ (pc b4) ^ "]")
	  | _ -> None
      else
	None

  method to_string_fragment:string =
    let bytes = get_bytes unsigned_value 4 in
    let pc i = if i=0 then "" else Printf.sprintf "%c" (Char.chr i) in
    match bytes with
	[ b4 ; b3 ; b2 ; b1 ] -> (pc b1) ^ (pc b2) ^ (pc b3) ^ (pc b4)
      | _ ->
	begin
	  ch_error_log#add "internal error"
	    (LBLOCK [ STR "doubleword_t#to_string_fragment: " ;
		      pretty_print_list bytes (fun b -> INT b) "[" "; " "]" ]) ;
	  raise (Internal_error "doubleword_t#to_string_fragment")
	end

  method to_string:string =
    let bytes = get_bytes unsigned_value 4 in
    let pc i = Printf.sprintf "%c" (Char.chr i) in
    match bytes with
	[ b1 ; b2 ; b3 ; b4 ] -> (pc b1) ^ (pc b2) ^ (pc b3) ^ (pc b4)
      | _ ->
	begin
	  ch_error_log#add "internal error"
	    (LBLOCK [ STR "doubleword_t#to_string_fragment: " ;
		      pretty_print_list bytes (fun b -> INT b) "[" "; " "]" ]) ;
	  raise (Internal_error "doubleword_t#to_string_fragment")
	end

  method to_fixed_length_hex_string:string =
    let nibbles = get_nibbles unsigned_value 8 in
    match nibbles with
	[ n8 ; n7 ; n6 ; n5 ; n4 ; n3 ; n2 ; n1 ] ->
	  Printf.sprintf "%x%x%x%x%x%x%x%x" n8 n7 n6 n5 n4 n3 n2 n1
      | _ -> 
	begin
	  ch_error_log#add "internal error" 
	    (LBLOCK [ STR "doubleword_t#fixed_length_hex_string inconsistent value: " ;
		      pretty_print_list nibbles (fun n -> INT n) "[" "; " "]" ]) ;
	  raise (Internal_error "doubleword_t#to_fixed_length_hex_string")
	end

  method to_hex_string:string =
    let nibbles = get_nibbles unsigned_value 8 in
    match nibbles with
	[ n8 ; n7 ; n6 ; n5 ; n4 ; n3 ; n2 ; n1 ] ->
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
	  ch_error_log#add "invalid argument"
	    (LBLOCK [ pretty_print_list nibbles (fun i -> INT i) "[" "; " "]" ; NL ]) ;
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

  method subtract (other:'a):'a =
    if other#index <= self#index then
      {< unsigned_value = self#index - other#index >}
    else
      begin
	ch_error_log#add "invalid argument"
	  (LBLOCK [ STR "Unable to subtract doubleword -- difference is negative: " ;
		    INT self#index ; STR " - " ; INT other#index ;
		    STR " (" ; self#toPretty ; STR " - " ; other#toPretty ; STR ")" ]) ;
	raise (Invalid_argument "doubleword_t#subtract")
      end

  method subtract_int (i:int):'a =
    if i<= unsigned_value then
      {< unsigned_value = unsigned_value - i >}
    else
      begin
	ch_error_log#add "invalid argument"
	  (LBLOCK [ STR "Unable to subtract int -- difference is negative: " ;
		    INT unsigned_value ; STR " - " ; INT i ;  
		    STR " (" ; self#toPretty ; STR " - " ; INT i ; STR ")" ]) ;
	raise (Invalid_argument "doubleword_t#subtract_int")
      end


  method add (other:'a) =
    let sum = self#index + other#index in
    if sum <= ffff_ffff then
      {< unsigned_value = sum >}
    else
      {< unsigned_value = (sum - ffff_ffff) - 1 >}

  method add_int (i:int):'a =
    let sum = unsigned_value + i in
    if sum <= ffff_ffff then
      {< unsigned_value = sum >}
    else
      begin
	ch_error_log#add
          "invalid argument" 
	  (LBLOCK [ STR "Unable to add int -- sum exceeds 32 bits: " ;
                    INT unsigned_value ; STR " + " ; INT i ]) ;
	raise (Invalid_argument "doubleword_t#add_int")
      end


  method multiply_int (i:int):'a =
    let product = i * unsigned_value in
    if product <= ffff_ffff then
      {< unsigned_value = product >}
    else
      begin
	ch_error_log#add "invalid argument"
	  (LBLOCK [ STR "Unable to multiply int -- product exceeds 32 bits: " ;
		    INT unsigned_value ; STR " * " ; INT i ]) ;
	raise (Invalid_argument "doubleword_t#multiply_int")
      end

  method xor (other:'a) =
    {< unsigned_value = self#to_int lxor other#to_int >}


  (* -----------------------------------------------------~---~---- accessors -- *)

  method get_low = unsigned_value mod e16

  method get_high = unsigned_value / e16

  method get_bits_set =
    let rec aux pos v bits =
      if pos = 32 then bits 
      else if v mod 2 = 1 then aux (pos+1) (v lsr 1) (pos::bits)
      else aux (pos+1) (v lsr 1) bits in
    aux 0 unsigned_value []

  (* --------------------------------------------------------~---- predicates -- *)

  method is_highest_bit_set = (unsigned_value lsr 31) = 1

  method is_nth_bit_set (n:int) =
    if n >=0  && n < 32 then
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

let create_doubleword (n:int) =
  let sanitized_n = 
    if n >= 0 && n < e32 then n
    else if abs n <= e31 then n + e32
    else
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [ STR "create_doubleword: " ; INT n ;
                    STR " cannot be represented as a 32 bit value" ]);
	raise (Invalid_argument "create_doubleword")
      end in
  new doubleword_t sanitized_n


(* create a doubleword from two 16-bit words, low and high resp *)
let make_doubleword (l:int) (h:int) = 
  try
    create_doubleword ((h * e16) + l)
  with
      Invalid_argument _ ->
	begin
	  ch_error_log#add
            "invalid argument"
	    (LBLOCK [ STR "make_doubleword with low: " ;
                      INT l ; STR "; high: " ; INT h ]) ;
	  raise (Invalid_argument "make_doubleword")
	end

(* return the doubleword associated with a hash index value *)
let index_to_doubleword (index:dw_index_t) = 
  try
    create_doubleword index
  with
      Invalid_argument _ ->
	begin
	  ch_error_log#add
            "invalid argument" (LBLOCK [ STR "index_to_doubleword: " ; 
					 INT index ; STR ")" ]) ;
	  raise (Internal_error "index_to_doubleword")
	end

(* create a doubleword from an integer *)
let int_to_doubleword i = 
  try
    create_doubleword i
  with
      Invalid_argument _ ->
	begin
	  ch_error_log#add
            "invalid argument" (LBLOCK [ STR "int_to_doubleword: " ; INT i ]) ;
	  raise (Invalid_argument "int_to_doubleword")
	end

let big_int_to_doubleword bi = 
  try
    create_doubleword (B.int_of_big_int bi)
  with
      Invalid_argument _ ->
	begin
	  ch_error_log#add
            "invalid argument" 
	    (LBLOCK [ STR "big_int_to_doubleword: " ; INT (B.int_of_big_int bi) ]) ;
	  raise (Invalid_argument "big_int_to_doubleword")
	end
    | Failure _ ->
      begin
	ch_error_log#add
          "invalid argument" 
	  (LBLOCK [ STR "big_int_to_doubleword: (too large for int)" ;
                    STR (B.string_of_big_int bi) ]);
	raise (Invalid_argument "big_int_to_doubleword")
      end

let numerical_to_doubleword (num:numerical_t) =
  try
    big_int_to_doubleword num#getNum
  with
      Invalid_argument _ ->
	begin
	  ch_error_log#add "invalid argument"
	    (LBLOCK [ STR "numerical_to_doubleword: " ; num#toPretty ]) ;
	  raise (Invalid_argument "numerical_to_doubleword")
	end

let dw_index_to_string (index:dw_index_t) =
  (index_to_doubleword index)#to_numerical#toString

let string_to_dw_index (s:string) = 
  try
    (numerical_to_doubleword (mkNumericalFromString s))#index
  with
    Invalid_argument _ ->
      begin
	ch_error_log#add "invalid argument" 
	  (LBLOCK [ STR "string_to_dw_index: " ; STR s ]);
	raise (Invalid_argument "string_to_dw_index")
      end	

let dw_index_to_int (index:dw_index_t) = index

let int_to_dw_index (index:int) = index

let string_to_doubleword s =
  try
    let i64 = Int64.of_string s in
    let bi = B.big_int_of_int64 i64 in
    big_int_to_doubleword bi
  with
      Invalid_argument _ ->
	begin
	  ch_error_log#add
            "invalid argument" (LBLOCK [ STR "string_to_doubleword: " ; STR s ]) ;
	  raise (Invalid_argument ("string_to_doubleword:" ^ s))
	end
    | Failure f ->
      begin
	ch_error_log#add "invalid argument" 
	  (LBLOCK [ STR "string_to_doubleword (" ; STR f ; STR "): " ; STR s ]);
	raise (Invalid_argument ("string_to_doubleword:" ^ s))
      end

let numerical_to_hex_string num = 
  try
    (big_int_to_doubleword num#getNum)#to_hex_string
  with
      Invalid_argument _ ->
	begin 
	  ch_error_log#add
            "invalid argument"
            (LBLOCK [ STR "numerical_to_hex_string: " ; num#toPretty ]) ;
	  raise (BCH_failure
                   (LBLOCK [ STR "numerical_to_hex_string" ; num#toPretty ]))
	end

let numerical_to_signed_hex_string num = 
  try
    let big_val = num#getNum in
    let abs_val = B.abs_big_int big_val in
    let dw = big_int_to_doubleword abs_val in
    if B.lt_big_int big_val B.zero_big_int then
      "-" ^ dw#to_hex_string
    else
      dw#to_hex_string
  with
    Invalid_argument _ ->
      begin
	ch_error_log#add
          "invalid argument" 
	  (LBLOCK [ STR "numerical_to_signed_hex_string: " ; num#toPretty ]);
	raise (Invalid_argument "numerical_to_signed_hex_string")
      end

let symbol_to_doubleword (symbol:symbol_t) =
  match symbol#getAttributes with
    s :: _ -> string_to_doubleword s
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR "Symbol cannot be converted to doubleword: " ;
                        symbol#toPretty ]))

let doubleword_to_symbol (name:string) ?(atts=[]) (dw:doubleword_int) = 
  new symbol_t ~atts:(dw#to_hex_string::atts) name
