(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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
open CHCommon
open CHPretty

(* chutil *)
open CHPrettyUtil

exception CHIOFailure of string

(* Convert standard Unix time representation to a string *)
let time_to_string (f:float):string = 
  let tm = Unix.localtime f in
  let sp ip = if ip < 10 then LBLOCK [ STR "0" ; INT ip ] else INT ip in
  let p = LBLOCK [
              sp (tm.tm_year + 1900) ; STR "-" ; sp (tm.tm_mon + 1) ;
              STR "-" ; sp tm.tm_mday ; STR " " ;
              sp tm.tm_hour ; STR ":" ;
              sp tm.tm_min ; STR ":" ;
              sp tm.tm_sec ] in
  pretty_to_string p

let file_kind_to_string (k:Unix.file_kind) =
  match k with
  | S_REG -> "regular file"
  | S_DIR -> "directory"
  | S_CHR -> "character device"
  | S_BLK -> "block device"
  | S_LNK -> "symbolic link"
  | S_FIFO -> "named pipe"
  | S_SOCK -> "socket"

let file_permissions_to_string (p:Unix.file_perm) = string_of_int p
  
let stats_to_pretty (stats:Unix.stats) =
  LBLOCK [
      STR "device number          : " ; INT stats.st_dev ; NL ;
      STR "inode number           : " ; INT stats.st_ino ; NL ;
      STR "file kind              : " ; STR (file_kind_to_string stats.st_kind) ; NL ;
      STR "access rights          : " ; STR (file_permissions_to_string stats.st_perm) ; NL ;
      STR "number of links        : " ; INT stats.st_nlink ; NL ;
      STR "user id (owner)        : " ; INT stats.st_uid ; NL ;
      STR "group id               : " ; INT stats.st_gid ; NL ;
      STR "device minor number    : " ; INT stats.st_rdev ; NL ;
      STR "size in bytes          : " ; INT stats.st_size ; NL ;
      STR "last access time       : " ; STR (time_to_string stats.st_atime) ; NL ;
      STR "last modification time : " ; STR (time_to_string stats.st_mtime) ; NL ;
      STR "last status change time: " ; STR (time_to_string stats.st_ctime) ; NL ]

let stats_to_string (stats:Unix.stats) = pretty_to_string (stats_to_pretty stats)

class type file_output_int =
  object
    method setProjectSourcePath: string -> unit
    method setProjectResultPath: string -> unit
    method setProjectName: string -> unit
    method saveFile: string -> pretty_t -> unit
    method saveStringToFile: string -> string -> unit
    method appendToFile: string -> pretty_t -> unit
  end


class file_output_t:file_output_int =
object (self)

  val mutable project_source_path: string = Unix.getcwd ()
  val mutable project_result_path: string = Unix.getcwd ()
  val mutable project_name: string = "CH_Analysis"

  method setProjectSourcePath (s:string) = 
    let source_path =
      if Filename.is_relative s
      then
	Filename.concat (Unix.getcwd ()) s
      else 
	s in
      project_source_path <- source_path

  method setProjectResultPath (s:string) = 
    let result_path =
      if Filename.is_relative s
      then
	Filename.concat (Unix.getcwd ()) s
      else 
	s in
      project_result_path <- result_path

  method setProjectName (s:string) = project_name <- s

  method private substitute_prefix (name:string) =
    let pre_len = (String.length project_source_path) + 1 in
    let name = String.sub name pre_len ((String.length name) - pre_len) in
      Filename.concat project_result_path name

  method private substitute_extension (old_ext:string) (new_ext:string) (name:string) =
    if Filename.check_suffix name old_ext then
      let fname = Filename.chop_extension name in
	fname ^ "." ^ new_ext
    else
      failwith ("Filename does not have expected extension: " ^ name ^ 
		  " (expected to have " ^ old_ext ^ ")")

  method private toStream stream contents =
    let p = new pretty_printer_t stream in
      p#print contents

  method saveStringToFile (name:string) (contents:string) =
    try
      let fout = open_out name in
      begin
	output_string fout contents ;
	flush fout ;
	close_out fout
      end
    with
      Sys_error e ->
         let stats = Unix.stat name in
         let msg = "Error opening " ^ name ^ " for writing: " ^ e ^ "\n"
                   ^ (stats_to_string stats) in
	raise (CHIOFailure msg)

  (* save the contents to a file with the given name and extension *)
  method saveFile (name:string) (contents:pretty_t) =
(*    let _ = pr_debug [ STR "saving file " ; STR name ; NL ] in *)
    let fout = 
      try
	open_out name
      with
      | Sys_error e ->
         let stats = Unix.stat name in
         let msg = "Error opening " ^ name ^ " for writing: " ^ e ^ "\n"
                   ^ (stats_to_string stats) in
	 failwith msg in
    begin
      self#toStream fout contents;
      flush fout;
      close_out_noerr fout
    end

  (* append the contents to a file with the given name *)
  method appendToFile (name:string) (contents:pretty_t) =
    let fout = 
      try
	open_out_gen [Open_append ; Open_creat ] 0o644 name
      with
      |	Sys_error e -> 
	 failwith ("Cannot append to file: " ^ name ^ ": " ^ e) in
    begin
      self#toStream fout contents ;
      flush fout ;
      close_out_noerr fout
    end

end

let file_output = new file_output_t
  
(* Return the filename relative to the given directory; if the filename
   is absolute, but not in a subdirectory of the given directory, the
   function fails
*)
let relativize_filename (filename:string) (directory:string):string =
  if Filename.is_relative filename then
    filename
  else
    let len = String.length directory in
    let sub = String.sub filename 0 len in
    if sub = directory then
      String.sub filename (len+1) ((String.length filename) - (len+1))
    else
      failwith ("relativize_filename: Unable to relativize " ^ filename ^ 
		" with respect to " ^ directory ^ "\n")

(* Add full directory name to the file name *)
let absolute_name (s:string):string =
  if Filename.is_relative s then
    Filename.concat (Unix.getcwd ()) s
  else
    s
    
let rec normalize_path (s:string):string =
  let len = String.length s in
  if len <= 1 then
    s
  else
    if String.contains s '.' then
      let dotindex = String.index s '.' in
      if dotindex + 2 < len && (String.get s (dotindex+1)) = '.'
         && (String.get s (dotindex+2)) = '/' then
        if String.rcontains_from s dotindex '/' then
          let slsindex = String.rindex_from s dotindex '/' in
          if slsindex > 0 && String.rcontains_from s (slsindex-1) '/' then
            let sls2index = String.rindex_from s (slsindex-1) '/' in
            let s1 = String.sub s 0 sls2index in
            let s2 = String.sub s (dotindex + 2) (len - (dotindex + 2)) in
            normalize_path (String.concat "" [ s1 ; s2 ])
          else if slsindex > 0 then
            normalize_path (String.sub s (dotindex + 3) (len - (dotindex + 3)))
          else    (* no second slash found *)
            raise (CHFailure (LBLOCK [ STR "Error in normalize_path: " ; STR s ]))
        else      (* no first slash found *)
          raise (CHFailure (LBLOCK [ STR "Error in normalize_path: " ; STR s ]))
      else        (* just one dot *)
        if dotindex + 1 < len && String.get s (dotindex+1) = '/' then
          let s1 = String.sub s 0 dotindex in
          let s2 = String.sub s (dotindex + 2) (len - (dotindex + 2)) in
          normalize_path (String.concat "" [ s1 ; s2 ])
        else
          raise (CHFailure (LBLOCK [ STR "Error in normalize_path: " ; STR s ]))
    else   (* no dots *)
      s
  
  
