(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
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

(* Utility to wrap input for big or little endian *)

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHTraceResult

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHImmediate

module B = Big_int_Z

let bii = B.big_int_of_int
let bii32 = B.big_int_of_int32

let exp2 p  = B.power_int_positive_int 2 p
let e16 = exp2 16


class virtual stream_wrapper_t (input: IO.input):stream_wrapper_int =  
object
  
  method read = IO.read input
  method nread i = Bytes.to_string (IO.nread input i)
  method really_nread i = Bytes.to_string (IO.really_nread input i)
  method input s i j = IO.input input (Bytes.of_string s) i j
  method close_in = IO.close_in input
    
  method read_byte = IO.read_byte input
  method read_signed_byte = IO.read_signed_byte input
  method virtual read_ui16 : int
  method virtual read_ui16 : int
  method virtual read_i16 : int
  method virtual read_i32 : int
  method virtual read_real_i32 : int32
  method virtual read_i64 : int64
  method virtual read_double : float
  method read_string = IO.read_string input
  method read_line = IO.read_line input
    
  method virtual read_doubleword : doubleword_int
end


class little_endian_stream_wrapper_t (input:IO.input) =  
object
  inherit stream_wrapper_t input
    
  method read_ui16 = IO.read_ui16 input
  method read_i16 = IO.read_i16 input
  method read_i32 = IO.read_i32 input
  method read_real_i32 = IO.read_real_i32 input
  method read_i64 = IO.read_i64 input
  method read_double = IO.read_double input
    
  method read_doubleword =
    let l = IO.read_ui16 input in
    let h = IO.read_ui16 input in
    make_doubleword l h
end


class big_endian_stream_wrapper_t (input:IO.input) =  
object
  inherit stream_wrapper_t input
    
  method read_ui16 = IO.BigEndian.read_ui16 input
  method read_i16 = IO.BigEndian.read_i16 input
  method read_i32 = IO.BigEndian.read_i32 input
  method read_real_i32 = IO.BigEndian.read_real_i32 input
  method read_i64 = IO.BigEndian.read_i64 input
  method read_double = IO.BigEndian.read_double input
    
  method read_doubleword =
    let l = IO.BigEndian.read_ui16 input in
    let h = IO.BigEndian.read_ui16 input in
    make_doubleword h l
end

let make_little_endian_stream_wrapper input =
  let p = new little_endian_stream_wrapper_t input in
  (p : little_endian_stream_wrapper_t :> stream_wrapper_int)

let make_big_endian_stream_wrapper input =
  let p = (new big_endian_stream_wrapper_t input) in
  (p : big_endian_stream_wrapper_t :> stream_wrapper_int)


class pushback_stream_t ?(little_endian=true) (s:string):pushback_stream_int =
object (self)

  val mutable ch = 
    let input = IO.input_string s in
    if little_endian then 
      new little_endian_stream_wrapper_t input 
    else 
      new big_endian_stream_wrapper_t input
  val mutable pos = 0
  val s = s

  method pos = pos

  method sub (pos: int) (len: int) =
    try
      Ok (String.sub s pos len)
    with
    | Invalid_argument m -> Error [m]

  method skip_bytes n = 
    try
      begin
	pos <- pos + n ; 
	let input = IO.input_string (string_suffix s pos) in
	if little_endian then
	  ch <- new little_endian_stream_wrapper_t input
	else
	  ch <- new big_endian_stream_wrapper_t input
      end
    with
    | Invocation_error s
    | Invalid_argument s ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Unable to skip ";
                 INT n;
                 STR " bytes: ";
		 STR s]))

  method read = begin pos <- pos+1 ; ch#read end

  method nread n =
    let s = ch#nread n in begin pos <- pos + (String.length s) ; s end

  method really_nread n = begin pos <- pos + n ; ch#really_nread n end

  method read_byte = begin pos <- pos + 1 ; ch#read_byte end

  method read_signed_byte = begin pos <- pos + 1 ; ch#read_signed_byte end

  method read_ui16 = begin pos <- pos + 2 ; ch#read_ui16 end

  method read_i16  = begin pos <- pos + 2 ; ch#read_i16 end

  method read_i32 = begin pos <- pos + 4 ; ch#read_i32 end

  method read_real_i32 = begin pos <- pos + 4 ; ch#read_real_i32 end

  method read_i64 = begin pos <- pos + 8 ; ch#read_i64 end

  method read_string = 
    let s = ch#read_string in begin pos <- pos + (String.length s) + 1 ; s end

  method read_doubleword = begin pos <- pos + 4 ; ch#read_doubleword end

  method read_num_signed_doubleword = mkNumerical_big (bii32 self#read_real_i32)

  method read_num_signed_word = mkNumerical_big (bii self#read_i16)

  method read_num_signed_byte = mkNumerical_big (bii self#read_signed_byte)

  method read_num_unsigned_byte = mkNumerical_big (bii self#read_byte)

  method read_imm_signed_byte = make_immediate true 1 (bii self#read_signed_byte)

  method read_imm_signed_word = make_immediate true 2 (bii self#read_i16)

  method read_imm_signed_doubleword =
    make_immediate true 4 (bii32 self#read_real_i32)

  method read_imm_signed n = 
    match n with
    | 1 -> self#read_imm_signed_byte
    | 2 -> self#read_imm_signed_word
    | 4 -> self#read_imm_signed_doubleword
    | _ -> raise (Invalid_argument ("read_immediate_signed: " ^ (string_of_int n)))

  method read_imm_unsigned_byte = make_immediate false 1 (bii self#read_byte)

  method read_imm_unsigned_word = make_immediate false 2 (bii self#read_ui16)

  method read_imm_unsigned_doubleword = 
    let l = self#read_ui16 in
    let h = self#read_ui16 in
    let v = B.add_big_int (B.mult_big_int (bii h) e16) (bii l) in
    make_immediate false 4 v

  method read_imm_unsigned n =
    match n with
    | 1 -> self#read_imm_unsigned_byte
    | 2 -> self#read_imm_unsigned_word
    | 4 -> self#read_imm_unsigned_doubleword
    | _ -> raise (Invalid_argument ("read_immediate_unsigned: " ^ (string_of_int n)))

  method read_null_terminated_string =
    let maxLen = 1000 in
    let a = Array.make maxLen 0 in
    let i = ref 0 in
    try
      begin
	a.(!i) <- self#read_byte ;
	while a.(!i) != 0 && !i < maxLen-1 do
	  i := !i + 1;
	  a.(!i) <- self#read_byte
	done;
	let s = Bytes.create !i in
	begin
	  for j=0 to !i-1 do
            (* s.[j] <- Char.chr a.(j) *)
            Bytes.set s j (Char.chr a.(j)) 
          done;
	  (if !i = maxLen - 1 then
	     chlog#add
               "string length"
	       (LBLOCK [
                    STR "String length exceeds ";
                    INT maxLen;
		    STR "characters (cut short)"]));
	  Bytes.to_string s
	end
      end
    with
      Invalid_argument _ ->
	begin
	  ch_error_log#add
            "invalid input"
	    (LBLOCK [
                 STR "read_null_terminated_string: longer than 1000 characters"]);
	  raise (Invalid_input "read_null_terminated_string")
	end
    | IO.No_more_input ->
      begin
	ch_error_log#add "no more input" (STR "read_null_terminated_string");
	raise IO.No_more_input
      end

  method read_sized_unicode_string =
    let len = self#read_ui16 in
    let s = Bytes.create len in
    try
      begin
	for i=0 to len-1 do
	  begin
	    (* s.[i] <- Char.chr self#read_byte ; *)
            Bytes.set s i (Char.chr self#read_byte) ;
	    ignore self#read_byte ;
	  end
	done;
	Bytes.to_string s
      end
    with
      IO.No_more_input ->
	begin
	  pr_debug [ STR "No more input in read_sized_unicode_string" ; NL ] ;
	  raise IO.No_more_input
	end

  method pushback n =
    begin
      pos <- pos - n ; 
      let input = IO.input_string (string_suffix s pos) in
      if little_endian then
	ch <- new little_endian_stream_wrapper_t input
      else
	ch <- new big_endian_stream_wrapper_t input
    end

end


let make_pushback_stream ?(little_endian=true) (s:string) =
  new pushback_stream_t ~little_endian s
