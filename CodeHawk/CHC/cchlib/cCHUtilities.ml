(* =============================================================================
   CodeHawk C Analyzer
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

open Unix

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHPrettyUtil

(* Facilities to manipulate jar files *)

exception CCHFailure of pretty_t
exception No_file_found of string


let replace_dot s =
  let s = Bytes.copy (Bytes.of_string s) in
  for i = 0 to Bytes.length s - 1 do
    if Bytes.get s i = '.' then Bytes.set s i '_'
  done;
  Bytes.to_string s


let is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _, _) -> false


let exists_file s: (string * Zip.in_file) -> bool =
  let s = s ^ ".xml" in
  function (_,jar) ->
    (try
       begin
         ignore (Zip.find_entry jar s); true end with Not_found -> false)

let open_path s:(string * Zip.in_file) option =
  if Filename.check_suffix s ".jar" && is_file s then
    begin
      Some (s, Zip.open_in s)
    end
  else
    begin
      None
    end

let lookup_summary name: (string * Zip.in_file) -> string =
  let filename = name ^ ".xml" in
  function (_, jar) ->
            try
              Zip.read_entry jar (Zip.find_entry jar filename)
            with
            | Not_found -> raise (No_file_found name)


let rec fold_directories (f: 'b -> 'a) file : 'b list -> 'a = function
  | [] -> raise (No_file_found file)
  | path :: tl -> try f path with No_file_found _ -> fold_directories f file tl


let rec fold_directories_for_existence (f: 'b -> 'a) file : 'b list -> 'a = function
  | [] -> false
  | path :: tl -> f path || fold_directories_for_existence f file tl


let has_summary_file path c =
  fold_directories_for_existence (fun path -> exists_file c path) c path


let get_summary_file path c =
  fold_directories (fun path -> lookup_summary c path) c path


let apply_to_xml_jar f other name =
  let jar = Zip.open_in name in
  begin
    List.iter
      (fun e ->
	if Filename.check_suffix e.Zip.filename ".xml" then
	  f e.Zip.filename (Zip.read_entry jar e)
	else
	  other jar e) (Zip.entries jar);
    Zip.close_in jar
  end


(* Time printing utilities *)
let date_time_to_string (f:float):string =
  let tm = Unix.localtime f in
  let sp ip = if ip < 10 then LBLOCK [STR "0"; INT ip] else INT ip in
  let p =
    LBLOCK [
        sp (tm.tm_mon + 1); STR "/"; sp tm.tm_mday;
	STR "/"; sp (tm.tm_year + 1900);
	STR " "; sp tm.tm_hour;
	STR ":"; sp tm.tm_min;
	STR ":"; sp tm.tm_sec] in
  string_printer#print p


let time_to_string (f:float):string =
  let tm = Unix.localtime f in
  let sp ip = if ip < 10 then LBLOCK [STR "0"; INT ip] else INT ip in
  let p = LBLOCK [
    STR " "; sp tm.tm_hour;
    STR ":"; sp tm.tm_min;
    STR ":"; sp tm.tm_sec] in
  string_printer#print p


let get_slice lst index count =
  if index < 0 || count < 0 || (List.length lst) < index + count then
    None
  else
    let rec aux l i n result =
      if i > 0 then aux (List.tl l) (i-1) n result
      else if n > 0 then aux (List.tl l) 0 (n-1) ((List.hd l) :: result)
      else List.rev result in
    Some (aux lst index count [])


let hex_string = CHUtil.hex_string


let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c ->
    if !found then
      ()
    else if Char.code c = 10 then      (* NL *)
      ()
    else if (Char.code c) < 32 || (Char.code c) > 126 then
      found  := true) s in
  !found


let mk_num_range (lb:numerical_t) (ub:numerical_t) =
  let one = numerical_one in
  let rec aux x y result =
    if x#gt y then
      result
    else if x#equal y then
      x::result
    else aux x (y#sub one) (y::result) in
  aux lb (ub#sub one)  []
