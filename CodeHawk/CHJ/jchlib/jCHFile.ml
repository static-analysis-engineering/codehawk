(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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

(* extlib *)
open ExtList

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes


exception No_class_found of string


let sep =
  match Sys.os_type with
    | "Unix"
    | "Cygwin" -> ":"
    | "Win32" -> ";"
    | _ -> assert false


let replace_dot (s:string) =
  let s = Bytes.copy (Bytes.of_string s) in
    for i = 0 to Bytes.length s - 1 do
      if Bytes.get s i = '.' then Bytes.set s i '/'
    done;
    Bytes.to_string s


let is_dir d =
  try
    (Unix.stat d).Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error (Unix.ENOENT, _,_) -> false


let is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _,_) -> false


type cp_unit_t =
  | Directory of string
  | JarFile of string * Zip.in_file
  | WarFile of string * Zip.in_file


let cp_unit_to_pretty (u:cp_unit_t) =
  match u with Directory s | JarFile (s, _) | WarFile (s, _) -> STR s


type class_path_t = cp_unit_t list


let class_path_to_pretty (cp:class_path_t) =
  pretty_print_list cp cp_unit_to_pretty "" ":" ""


let open_path s =
  if is_dir s then
    Some (Directory s)
  else
    if (Filename.check_suffix s ".jar"
        || Filename.check_suffix s ".zip")
       && is_file s then
      begin
	pr_debug [NL; STR "Opening jar file "; STR s; NL];
	Some (JarFile (s,Zip.open_in s))
      end
    else
      if (Filename.check_suffix s ".war") && is_file s
      then
	begin
	  pr_debug [NL; STR "Opening war file "; STR s; NL];
	  Some (WarFile (s,Zip.open_in s))
	end
      else None


type _directories = string list

let _make_directories dirs =
  match ExtString.String.nsplit dirs sep with
  | [] -> [Filename.current_dir_name]
  | cp -> List.filter is_dir cp


let get_classpath_units cp = ExtString.String.nsplit cp sep


(* Accepts wildcard as a basename in a classpath unit.
   Note that a classpath unit with a wildcard cannot be directly passed
   in as a commandline option, because the wildcard will be expanded by
   the OS before it is passed to the program. Similarly for setting the
   CLASSPATH environment variable: one cannot set
   export CLASSPATH=/home/user/* , but instead it has to be set with
   export CLASSPATH=/home/user/*:. or similar.
*)
let class_path cp =
  let cp_list =
    match ExtString.String.nsplit cp sep with
      | [] -> []  (* [Filename.current_dir_name] *)
      | cp -> cp
  in
  let cp_list = List.map (fun cp_unit ->
    let len = String.length cp_unit in
    if len > 0 && cp_unit.[len-1] = '*' then
      let name = Filename.dirname cp_unit in
      name
    else
      cp_unit) cp_list in
   List.filter_map open_path  (* cp_with_jars @ *) cp_list


let close_class_path =
  List.iter
    (function
    | Directory _ -> ()
    | JarFile (_, jar) | WarFile (_, jar) -> Zip.close_in jar)


(* Search for class c in a given directory or jar file *)
let lookup c : cp_unit_t -> JCHRawClass.raw_class_t =
  let c = replace_dot c ^ ".class" in
  function path ->
    try
      let (ch,origin,md5) =
	match path with
	| Directory d ->
	  if is_file (Filename.concat d c) then
	    let ch = open_in_bin (Filename.concat d c) in
	    let md5 = Digest.file (Filename.concat d c) in
	    (IO.input_channel ch, d, md5)
	  else
            raise Not_found
	| JarFile (s, jar) ->
	  let e = Zip.find_entry jar c in
	  let classString = Zip.read_entry jar e in
	  let ch = IO.input_string classString in
	  let md5 = Digest.string classString in
	  (ch,s,md5)
	| WarFile (s,jar) ->
	  let war_c = "WEB-INF/classes/" ^ c in
	  let e = Zip.find_entry jar war_c in
	  let classString = Zip.read_entry jar e in
	  let ch = IO.input_string classString in
	  let md5 = Digest.file classString in
	  (ch, s, md5) in
      let c = JCHParse.parse_class_low_level ch origin md5 in
      begin
        IO.close_in ch;
        c
      end
    with
    | IO.Input_closed ->
       raise
         (JCH_failure
            (LBLOCK [STR "IO.Input_closed encountered in lookup "; STR c]))
    | Not_found ->
       raise (No_class_found c)
    | JCH_class_structure_error s ->
       raise
         (JCH_failure
            (LBLOCK [STR "Class structure error in "; STR c; STR ": "; s]))


let rec fold_directories (f: 'b -> 'a) file : 'b list -> 'a = function
  | [] -> raise (No_class_found file)
  | class_path :: q ->
      try f class_path
      with No_class_found _ ->
	fold_directories f file q


let get_class_low (class_path:class_path_t) cs =
  let cname = cs#name in
    fold_directories
      (fun path -> lookup cname path)
      cname
      class_path


let get_class class_path c =
  try
    let class_low = get_class_low class_path c in
    JCHRaw2IF.low2high_class class_low
  with
  | IO.Input_closed ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "IO.Input_closed encountered when reading "; STR c#name]))


let rec fold_directories_for_existence
          (f: 'b -> 'a) file : 'b list -> 'a  = function
  | [] -> false
  | class_path :: q ->
    try
      f class_path || fold_directories_for_existence f file q
    with
    | IO.Input_closed ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "IO.Input_closed encountered when searching directories"]))


let exists_file c :cp_unit_t -> bool =
  let c = replace_dot c ^ ".xml" in
  function path ->
    match path with
    | Directory d -> is_file (Filename.concat d c)
    | JarFile (_, jar) ->
       (try
          begin
            ignore (Zip.find_entry jar c);
            true
          end
        with
        | Not_found -> false)
    | _ -> false


let lookup_summary c : cp_unit_t -> string =
  let c = replace_dot c ^ ".xml" in
  function path ->
    try
      match path with
      | Directory d ->
         if is_file (Filename.concat d c) then
	   let maxStringSize = Sys.max_string_length in
	   let ch = open_in_bin (Filename.concat d c) in
	   Bytes.to_string (IO.nread (IO.input_channel ch) maxStringSize)
	 else
           raise Not_found
      | JarFile (_, jar) -> Zip.read_entry jar (Zip.find_entry jar c)
      | _ ->
         raise Not_found
    with
    | Not_found -> raise (No_class_found c)
    | IO.Input_closed ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "IO.Input_closed encountered when looking up summary ";
		 STR c]))


let get_summary_manifest path =
  try
    match path with
    | JarFile (_, jar) ->
       Zip.read_entry jar (Zip.find_entry jar "META-INF/MANIFEST.MF")
    | _ -> "no manifest found"
  with
    _ -> "error in get_manifest"


let has_summary_class class_path c =
  fold_directories_for_existence
    (fun path -> exists_file c#name path) c#name class_path


let get_summary_class class_path c =
  fold_directories (fun path -> lookup_summary c#name path) c#name class_path


let apply_to_jar ?(xcludes=[]) f other s =
  try
    if
      (Filename.check_suffix s ".jar"
       || Filename.check_suffix s ".war"
       || Filename.check_suffix s ".zip") && is_file s	then
      let jar = Zip.open_in s in
      let is_included filename =
        not (List.exists (fun s ->
                 let slen = String.length s in
                 (String.length filename) > slen
                 && (String.sub filename 0 slen) = s) xcludes) in
      begin
        List.iter
          (function e ->
             let cfilename = e.Zip.filename in
             if is_included cfilename
                && Filename.check_suffix cfilename ".class" then
	       let classString = Zip.read_entry jar e in
	       let md5 = Digest.string classString in
	       let input = IO.input_string classString in
	       (try
	          let c = JCHParse.parse_class_low_level input s md5 in
	          begin
                    f c;
                    IO.close_in input
                  end
	        with
	        | JCH_class_structure_error e ->
		   begin
		     ch_error_log#add
                       "error in class file"
                       (LBLOCK [STR s; STR "; "; STR cfilename; STR ": "; e]);
		     IO.close_in input
		   end
                | IO.No_more_input ->
                   begin
                     ch_error_log#add
                       "no more input" (LBLOCK [STR s; STR ": "; STR cfilename]);
                     IO.close_in input
                   end
                | JCH_failure p ->
                   begin
                     ch_error_log#add
                       "failure in class file"
                       (LBLOCK [STR s; STR "; "; STR cfilename; STR ": "; p]);
                     IO.close_in input
                   end)
	     else
	       other jar e) (Zip.entries jar);
	Zip.close_in jar
      end
    else
      raise (No_class_found s)
  with
  | JCH_class_structure_error e ->
     ch_error_log#add "file corruption" (LBLOCK [STR s; STR "; "; e])
  | IO.Input_closed ->
     raise
       (JCH_failure
          (LBLOCK [STR "IO.Input_closed encountered in apply_to_jar "]))
  | No_class_found classname ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "No class found in apply_to_jar ";
               STR s;
               STR ": ";
               STR classname]))


let apply_to_xml_jar f other s =
  if Filename.check_suffix s ".jar" && is_file s then
    let jar = Zip.open_in s in
    List.iter
      (fun e ->
	if Filename.check_suffix e.Zip.filename ".xml" then
	  f e.Zip.filename (Zip.read_entry jar e)
	else
	  other jar e) (Zip.entries jar);
    Zip.close_in jar
  else
    raise
      (JCH_failure (LBLOCK [STR "No class found in apply_to_xml_jar "; STR s]))
