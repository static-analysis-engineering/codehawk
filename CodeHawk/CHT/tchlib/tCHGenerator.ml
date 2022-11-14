(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
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

(* tchlib *)
open TCHTestApi


module U = TCHUtils


let make_random () = Random.State.make_self_init ()


let make_random_seed (x: int) = Random.State.make [|x|]


let make_random_full (x: int array) = Random.State.make x


(* 64 bit compatible int generator *)
let random_state_int_generate: (random_t -> int -> int) =
  match Sys.word_size with
  | 32 -> Random.State.int
  | 64 ->
     (fun r x ->
       if x < 1073741824 then
         Random.State.int r x
       else
         Int64.to_int (Random.State.int64 r (Int64.of_int x)))
  | _ -> assert false


(* Predefined generators *)

let unit = ((fun r -> ignore (Random.State.bool r)), U.string_of_unit)


let bool = ((fun r -> Random.State.bool r), string_of_bool)


let make_bool (w1: int) (w2: int) =
  if w1 < 0 then invalid_arg ("TCHGenerator.make_bool: w1");
  if w2 < 0 then invalid_arg ("TCHGenerator.make_bool: w2");
  ((fun r ->
    let w = random_state_int_generate r (w1 + w2) in
    w < w1),
   string_of_bool)


let create_int_functions
      (id: string)
      (gen: random_t -> int -> int)
      (max: int)
      (neg: int -> int)
      (add: int -> int -> int)
      (sub: int -> int -> int)
      (prn: int -> string) =
  let id' = "TCHGenerator.make_" ^ id in
  let std_gen =
    ((fun r ->
      let s = Random.State.bool r in
      let x = gen r max in
      if s then x else neg x),
     prn) in
  let pos_gen = ((fun r -> gen r max), prn) in
  let neg_gen = ((fun r -> neg (gen r max)), prn) in
  let make (x: int) (y: int) =
    if (Stdlib.compare x y) >= 0 then invalid_arg id';
    ((fun r -> let d = sub y x in add (gen r d) x), prn) in
  (std_gen, pos_gen, neg_gen, make)


let int, pos_int, neg_int, make_int =
  create_int_functions
    "int"
    random_state_int_generate
    max_int
    (~-)
    (+)
    (-)
    string_of_int


let char = ((fun r -> Char.chr (Random.State.int r 256)), Char.escaped)


let create_digit n =
  ((fun r -> Char.chr ((Random.State.int r n) + (Char.code '0'))), Char.escaped)


let digit = create_digit 10


let digit_bin = create_digit 2


let digit_hex =
  ((fun r ->
    let x = Random.State.int r 16 in
    if x < 10 then
      Char.chr (x + (Char.code '0'))
    else
      Char.chr ((x - 10) + (Char.code 'A'))), Char.escaped)


let letter =
  ((fun r ->
    let c = Random.State.bool r in
    let l = Random.State.int r 26 in
    let x = Char.chr (l + (Char.code 'a')) in
    if c then Char.uppercase_ascii x else x), Char.escaped)


let alphanum =
  ((fun r ->
    let x = Random.State.int r 63 in
    if x < 10 then
      Char.chr (x + (Char.code '0'))
    else if x = 10 then
      '_'
    else if (x >= 11) && (x <= 36) then
      Char.chr ((x - 11) + (Char.code 'a'))
    else
      Char.chr ((x - 37) + (Char.code 'A'))), Char.escaped)


let string (gen_l: int generator_t) (gen_c: char generator_t) =
  ((fun r ->
    let len = (fst gen_l) r in
    let res = Bytes.create len in
    begin
      for i = 0 to pred len do Bytes.set res i ((fst gen_c) r) done;
      Bytes.to_string res
    end), U.string_of_string)


let strings
      (sep: string)
      (gen_l: int generator_t)
      (gen_s: string generator_t):string generator_t =
  let sep = Bytes.of_string sep in
  ((fun r ->
    let len = (fst gen_l) r in
    let lst = ref [] in
    begin
      for _i = 1 to len do
        lst := (Bytes.of_string ((fst gen_s) r)) :: !lst
      done;
      Bytes.to_string (Bytes.concat sep (List.rev !lst))
    end), U.string_of_string)


let number (gen_i: int generator_t) = string gen_i digit


let number_bin (gen_i: int generator_t) = string gen_i digit_bin


let number_hex (gen_i: int generator_t) = string gen_i digit_hex


let word (gen_i: int generator_t) = string gen_i letter


let words (gen_i: int generator_t) (gen_i': int generator_t): string generator_t =
  strings "  " gen_i (word gen_i')

                                      
let float =
  ((fun r ->
    let s = Random.State.bool r in
    let x = Random.State.float r max_float in
    if s then x else -.x), string_of_float)


let make_float (x: float) (y: float): float generator_t =
  if (Stdlib.compare x y) >= 0 then invalid_arg "TCHGenerator.make_float";
  ((fun r -> let d = y -. x in (Random.State.float r d) +. x), string_of_float)
