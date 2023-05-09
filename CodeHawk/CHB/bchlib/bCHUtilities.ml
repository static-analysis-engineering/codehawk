(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHPretty
open CHIntervals

(* chutil *)
open CHFileIO
open CHLogger

(* bchlib *)
open BCHLibTypes

module H = Hashtbl

let tracked_functions = ref [ ]

let set_tracked_functions l = tracked_functions := l

let track_function ?(iaddr="") faddr p =
  if List.mem faddr#to_hex_string !tracked_functions then
    let msg =
      match iaddr with
      | "" -> p
      | _ -> LBLOCK [ STR iaddr ; STR ": " ; p ] in
    chlog#add ("tracked:" ^ faddr#to_hex_string) msg


let get_date_and_time () =
  let tm = Unix.localtime (Unix.time ()) in
  let day = tm.tm_wday in
  let date = tm.tm_mday in
  let month = tm.tm_mon + 1 in
  let year = tm.tm_year + 1900 in
  let hrs = tm.tm_hour in
  let mins = tm.tm_min in
  let day =
    match day with
    | 0 -> "Sun"
    | 1 -> "Mon"
    | 2 -> "Tue"
    | 3 -> "Wed"
    | 4 -> "Thu"
    | 5 -> "Fri"
    | 6 -> "Sat"
    | _ -> 
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [STR "get_date_and_time: Unexpected weekday: "; INT day]);
	raise (Invalid_argument "get_date_and_time")
      end in
  Printf.sprintf "%s %d-%d-%d at %d:%02d" day year month date hrs mins


let today = get_date_and_time ()


let starttime = ref (Unix.gettimeofday ())


let set_starttime (t: float) = starttime := t


let timing () =
  let diff = (Unix.gettimeofday ()) -. !starttime in
  "[" ^ (Printf.sprintf "%f" diff) ^ "]"


let make_date_and_time_string (tm:Unix.tm) =
  let yr = tm.tm_year + 1900 in
  let mn = tm.tm_mon + 1 in
  let md = tm.tm_mday in
  let wd = tm.tm_wday + 1 in
  let hr = tm.tm_hour in
  let min = tm.tm_min in
  let sec = tm.tm_sec in
  let month =
    match mn with
    | 1 -> "Jan"
    | 2 -> "Feb"
    | 3 -> "Mar"
    | 4 -> "Apr"
    | 5 -> "May"
    | 6 -> "Jun"
    | 7 -> "July"
    | 8 -> "Aug"
    | 9 -> "Sep"
    | 10 -> "Oct"
    | 11 -> "Nov"
    | 12 -> "Dec"
    | _ -> 
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [
               STR "make_date_and_time: Unexected value for month: ";
               INT mn]);
	raise (Invalid_argument "make_date_and_time")
      end in
  let day =
    match wd with
    | 1 -> "Sun"
    | 2 -> "Mon"
    | 3 -> "Tue"
    | 4 -> "Wed"
    | 5 -> "Thu"
    | 6 -> "Fri"
    | 7 -> "Sat"
    | _ -> 
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [
               STR "make_date_and_time_string: Unexpected value of day: ";
               INT wd]);
	raise (Invalid_argument "make_date_and_time") 
      end in
  Printf.sprintf "%s %s %d %d:%d:%d %d" day month md hr min sec yr


(* Continuous logging *)
    
let activity_log = ref ""
let results_log = ref ""
  
let initialize_activity_log s = 
  let filename = s ^ "_ch_activity_log" in
  begin
    file_output#saveFile
      filename
      (LBLOCK [STR "CodeHawk activity log for "; STR s; NL; NL]);
    activity_log := filename
  end
    
let initialize_results_log s =
  let filename = s ^ "_ch_results_log" in
  begin
    file_output#saveFile
      filename
      (LBLOCK [STR "CodeHawk results log for "; STR s; NL; NL]);
    results_log := filename
  end
    
let log_activity p =
  if !activity_log = "" then
    pr_debug [STR "Warning: Activity log is not initialized"; NL]
  else
    let msg = LBLOCK [STR (get_date_and_time ()); STR ": "; p; NL] in
    file_output#appendToFile !activity_log msg
      
let log_result p =
  if !results_log = "" then
    pr_debug [STR "Warning: Results log is not initialized"; NL]
  else
    file_output#appendToFile !results_log (LBLOCK [p; NL])
      
let translation_log = mk_logger ()
let disassembly_log = mk_logger ()


(* Facilities to manipulate jar files *)
  
exception No_file_found of string
    
let replace_dot s =
  let newstring = Bytes.copy (Bytes.of_string s) in
  for i = 0 to (Bytes.length newstring) - 1 do
    if (Bytes.get newstring i) = '.' then
      Bytes.set newstring i '_'
  done;
  Bytes.to_string newstring
 
let replace_slash s = 
  if s = "" then s else
    if s.[0] = '/' then 
      "_slashfwd_" ^ (String.sub s 1 ((String.length s) - 1)) else s
   
let is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _,_) -> false
    
let exists_file s: (string * Zip.in_file) -> bool =
  let s = s ^ ".xml" in
  function (_,jar) ->
    (try 
       begin ignore (Zip.find_entry jar s) ; true end 
     with Not_found -> false)
    
let open_path s:(string * Zip.in_file) option = 
  if Filename.check_suffix s ".jar" && is_file s then
    begin
      chlog#add "jar file" (LBLOCK [ STR "Opening jar file " ; STR s ]) ;
      Some (s, Zip.open_in s)
    end
  else
    begin
      chlog#add "jar file" (LBLOCK [ STR "Unable to open jar file " ; STR s ]) ;
      None
    end
      
let lookup_summary name: (string * Zip.in_file) -> string =
  let filename = name ^ ".xml" in
  function (_, jar) -> 
    try Zip.read_entry jar (Zip.find_entry jar filename) with
      Not_found -> raise (No_file_found name)
	
let rec fold_directories (f: 'b -> 'a) file : 'b list -> 'a = function
  | [] -> raise (No_file_found file)
  | path :: tl -> try f path with No_file_found _ -> fold_directories f file tl
    
let rec fold_directories_for_existence
          (f: 'b -> 'a) file : 'b list -> 'a = function
  | [] -> false
  | path :: tl -> f path || fold_directories_for_existence f file tl
    
let has_summary_file path c =
  fold_directories_for_existence (fun path -> exists_file c path) c path
    
let get_summary_file path c =
  fold_directories (fun path -> lookup_summary c path) c path

let lookup_file filename: (string * Zip.in_file) -> string =
  function (_, jar) -> 
    try Zip.read_entry jar (Zip.find_entry jar filename) with
      Not_found -> raise (No_file_found filename)

let get_file_from_jar path c =
  try
    Some (fold_directories (fun path -> lookup_file c path) c path)
  with
    No_file_found _ -> None
    
let apply_to_xml_jar f other jar =
  List.iter
    (fun e ->
      if Filename.check_suffix e.Zip.filename ".xml" then
	f e.Zip.filename (Zip.read_entry jar e)
      else
	other jar e) (Zip.entries jar)
    
    
    
(* facilities to associate strings with sum types *)
    
    
let add_to_sumtype_tables
    (toTable:('a,string) Hashtbl.t) 
    (fromTable:(string,'a) Hashtbl.t) 
    (stype:'a) 
    (name:string) =
  begin
    Hashtbl.add toTable stype name ;
    Hashtbl.add fromTable name stype
  end
    
let get_string_from_table
      (tablename:string) (table:('a, string) Hashtbl.t) (stype:'a) =
  if Hashtbl.mem table stype then
    Hashtbl.find table stype
  else
    raise (Invalid_argument ("get_string_from_table " ^ tablename))
      
let get_sumtype_from_table
      (tablename:string) (table:(string, 'a) Hashtbl.t) (name:string) =
  if Hashtbl.mem table name then
    Hashtbl.find table name
  else
    raise
      (Invalid_argument ("get_sumtype_from_table " ^ tablename ^ ": " ^ name))
      
let is_string_of_sumtype (table:(string, 'a) Hashtbl.t) (name:string) =
  Hashtbl.fold (fun k _ a -> a || k = name) table false

let get_sumtype_table_keys (table:('a, string) Hashtbl.t) =
  H.fold (fun k _ a -> k::a) table []
    
    
    
(* comparison utilities *)
    
let interval_compare (i1:interval_t) (i2:interval_t) =
  let min1 = i1#getMin in
  let min2 = i2#getMin in
  if min1#lt min2 then -1 
  else if min2#lt min1 then 1
  else 
    let max1 = i1#getMax in
    let max2 = i2#getMax in
    if max1#lt max2 then -1
    else if max2#lt max1 then 1
    else 0


(* Compares two lists; if they are of unequal length, the shorter is smaller,
   if they have the same length, the element-wise comparison decides.
 *)
let list_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int): int =
  let length = List.length in
  if (length l1) < (length l2) then
    -1
  else if (length l1) > (length l2) then
    1
  else
    List.fold_right2
      (fun e1 e2 a -> if a = 0 then (f e1 e2) else a) l1 l2 0


let optvalue_compare (o1:'a option) (o2:'a option) (f:'a -> 'a -> int): int =
  match (o1,o2) with
  | (Some v1, Some v2) -> f v1 v2
  | (Some _, _) -> -1
  | (_, Some _) -> 1
  | (None,None) -> 0

      
let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l
    
let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1
    do h := !h ^ (byte_to_string (IO.read_byte ch)) done;
    !h
  end
    
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
