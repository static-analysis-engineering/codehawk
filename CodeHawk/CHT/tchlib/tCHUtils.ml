(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

let buffer_size = 256


let string_of_unit () = "()"


let string_of_char c = Printf.sprintf "%C" c


let string_of_string s = Printf.sprintf "%S" s


let string_of_bytes (b: bytes) = Printf.sprintf "%S" (Bytes.to_string b)


let string_of_buffer x = string_of_string (Buffer.contents x)


let make_string_of_list (f: 'a -> string) (l: 'a list): string =
  let buf = Buffer.create buffer_size in
  begin
    Buffer.add_string buf "[";
    List.iter (fun x ->
        begin
          Buffer.add_string buf (f x);
          Buffer.add_string buf "; "
        end) l;
    Buffer.add_string buf "]";
    Buffer.contents buf
  end


let make_string_of_option (f: 'a -> string) (x: 'a option): string =
  match x with
  | Some v -> "Some(" ^ (f v) ^ ")"
  | None -> "None"


let make_string_of_tuple2
      (f1: 'a -> string) (f2: 'b -> string) ((x1, x2): 'a * 'b): string =
  let v1 = f1 x1 in
  let v2 = f2 x2 in
  Printf.sprintf "(%s, %s)" v1 v2


let make_string_of_int_tuple2 (t: int * int) =
  make_string_of_tuple2 string_of_int string_of_int t


let make_string_of_int_tuple2_list (l: (int * int) list) =
  make_string_of_list make_string_of_int_tuple2 l
