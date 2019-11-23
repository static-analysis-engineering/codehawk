(*
 * ExtString - Additional functions for string manipulations.
 * Copyright (C) 2003 Nicolas Cannasse
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

exception Invalid_string

open ExtBytes

module String = struct

include String

let starts_with str p =
  if length str < length p then 
    false
  else
    let rec loop str p i =
      if i = length p then true else
      if unsafe_get str i <> unsafe_get p i then false
      else loop str p (i+1)
    in
    loop str p 0

let ends_with s e =
  if length s < length e then
    false
  else
    let rec loop s e i =
      if i = length e then true else
      if unsafe_get s (length s - length e + i) <> unsafe_get e i then false
      else loop s e (i+1)
    in
    loop s e 0

let find_from str pos sub =
  let sublen = length sub in
  if sublen = 0 then
    0
  else
    let found = ref 0 in
    let len = length str in
    try
      for i = pos to len - sublen do
        let j = ref 0 in
        while unsafe_get str (i + !j) = unsafe_get sub !j do
          incr j;
          if !j = sublen then begin found := i; raise Exit; end;
        done;
      done;
      raise Invalid_string
    with
      Exit -> !found

let find str sub = find_from str 0 sub

let exists str sub =
  try
    ignore(find str sub);
    true
  with
    Invalid_string -> false

let strip ?(chars=" \t\r\n") s =
  let p = ref 0 in
  let l = length s in
  while !p < l && contains chars (unsafe_get s !p) do
    incr p;
  done;
  let p = !p in
  let l = ref (l - 1) in
  while !l >= p && contains chars (unsafe_get s !l) do
    decr l;
  done;
  sub s p (!l - p + 1)

let split str sep =
  let p = find str sep in
  let len = length sep in
  let slen = length str in
  sub str 0 p, sub str (p + len) (slen - p - len)

let nsplit str sep =
  if str = "" then []
  else if sep = "" then raise Invalid_string
  else
    let rec loop acc pos =
      if pos > String.length str then
        List.rev acc
      else
        let i = try find_from str pos sep with Invalid_string -> String.length str in
        loop (String.sub str pos (i - pos) :: acc) (i + String.length sep)
    in
    loop [] 0

let join = concat

let slice =
  let clip max x = if x > max then max else if x < 0 then 0 else x in
  fun ?(first=0) ?(last=Sys.max_string_length) s ->
    let len = String.length s in
    let i = if first = 0 then 0 else clip len (if first < 0 then len + first else first) in
    let j = if last = Sys.max_string_length then len else clip len (if last < 0 then len + last else last) in
    if i>=j || i=len then
      make 0 ' '
    else
      sub s i (j-i)

let lchop s =
  if s = "" then "" else sub s 1 (length s - 1)

let rchop s =
  if s = "" then "" else sub s 0 (length s - 1)

let of_int = string_of_int

let of_float = string_of_float

let of_char = make 1

let to_int s =
  try
    int_of_string s
  with
    _ -> raise Invalid_string

let to_float s =
  try
    float_of_string s
  with
    _ -> raise Invalid_string

let enum s =
  let l = length s in
  let rec make i =
    Enum.make 
    ~next:(fun () ->
      if !i = l then
        raise Enum.No_more_elements
      else
        let p = !i in
        incr i;
        unsafe_get s p
      )
    ~count:(fun () -> l - !i)
    ~clone:(fun () -> make (ref !i))
  in
  make (ref 0)

let of_enum e =
  let l = Enum.count e in
  let s = Bytes.create l in
  let i = ref 0 in
  Enum.iter (fun c -> Bytes.unsafe_set s !i c; incr i) e;
        (* 's' doesn't escape and will never be mutated again *)
  Bytes.unsafe_to_string s

(* fold_left and fold_right by Eric C. Cooper *)
let fold_left f init str =
  let n = String.length str in
  let rec loop i result =
    if i = n then result
    else loop (i + 1) (f result str.[i])
  in
  loop 0 init

let fold_right f str init =
  let n = String.length str in
  let rec loop i result =
    if i = 0 then result
    else
      let i' = i - 1 in
      loop i' (f str.[i'] result)
  in
  loop n init

(* explode and implode from the OCaml Expert FAQ. *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let implode l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> Bytes.set res i c; imp (i + 1) l in
  let s = imp 0 l in
  (* 's' doesn't escape and will never be mutated again *)
  Bytes.unsafe_to_string s

let replace_chars f s =
  let len = String.length s in
  let tlen = ref 0 in
  let rec loop i acc =
    if i = len then
      acc
    else 
      let s = f (unsafe_get s i) in
      tlen := !tlen + length s;
      loop (i+1) (s :: acc)
  in
  let strs = loop 0 [] in
  let sbuf = Bytes.create !tlen in
  let pos = ref !tlen in
  let rec loop2 = function
    | [] -> ()
    | s :: acc ->
      let len = length s in
      pos := !pos - len;
      blit s 0 sbuf !pos len;
      loop2 acc
  in
  loop2 strs;
        (* 'sbuf' doesn't escape and will never be mutated again *)
  Bytes.unsafe_to_string sbuf

let replace ~str ~sub ~by =
  try
    let i = find str sub in
    (true, (slice ~last:i str) ^ by ^ 
                   (slice ~first:(i+(String.length sub)) str))
        with
    Invalid_string -> (false, String.sub str 0 (String.length str))
(*
#if OCAML < 403
let uppercase_ascii = uppercase
let lowercase_ascii = lowercase
let capitalize_ascii = capitalize
let uncapitalize_ascii = uncapitalize

let equal = (=)
#endif

#if OCAML < 404
let split_on_char sep s =
  let r = ref [] in
  let j = ref (length s) in
  for i = length s - 1 downto 0 do
    if unsafe_get s i = sep then begin
      r := sub s (i + 1) (!j - i - 1) :: !r;
      j := i
    end
  done;
  sub s 0 !j :: !r
#endif

#if OCAML < 405

let rec index_rec_opt s lim i c =
  if i >= lim then None else
  if unsafe_get s i = c then Some i else index_rec_opt s lim (i + 1) c

let index_opt s c = index_rec_opt s (length s) 0 c

let index_from_opt s i c =
  let l = length s in
  if i < 0 || i > l then invalid_arg "ExtString.index_from_opt" else
  index_rec_opt s l i c

let rec rindex_rec_opt s i c =
  if i < 0 then None else
  if unsafe_get s i = c then Some i else rindex_rec_opt s (i - 1) c

let rindex_opt s c = rindex_rec_opt s (length s - 1) c

let rindex_from_opt s i c =
  if i < -1 || i >= length s then
    invalid_arg "ExtString.rindex_from_opt"
  else
    rindex_rec_opt s i c

#endif
 *)
end
