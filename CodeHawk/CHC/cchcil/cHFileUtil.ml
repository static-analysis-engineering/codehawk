(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
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

(* cchcil *)
open CHPrettyPrint
open CHUtilities

class type file_output_int =
object
  method saveFile: string -> pretty_t -> unit
  method saveStringToFile: string -> string -> unit
  method appendToFile: string -> pretty_t -> unit
end

let project_path_prefix = ref ""

class file_output_t =
object (self)
						
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
    | Sys_error e ->
	raise (CCFailure (STR ("Unable to write to file " ^ name ^ ": " ^ e)))
					
  (* save the contents to a file with the given name and extension *)
  method saveFile (name:string) (contents:pretty_t) =
    let fout = 
      try
	open_out name
      with
      | _ ->
	 failwith ("Cannot create output file: " ^ name) in
    begin
      self#toStream fout contents;
      flush fout;
      close_out fout
    end
			
  (* append the contents to a file with the given name *)
  method appendToFile (name:string) (contents:pretty_t) =
    let fout = 
      try
	open_out_gen [Open_append ; Open_creat ] 0o644 name
      with
      |	_ -> 
        failwith ("Cannot append to file: " ^ name) in
    begin
      self#toStream fout contents ;
      flush fout ;
      close_out fout
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
  let has_directory_dot s =
    (String.contains s '.')
    && (let dotindex = String.index s '.' in
        (String.contains_from s dotindex '/')
        && (let slashindex = String.index_from s dotindex '/' in
            (slashindex - dotindex = 1)
            || ((slashindex - dotindex = 2) && String.get s (dotindex+1) = '.'))) in
  let len = String.length s in
  if len <= 1 then
    s
  else
    if has_directory_dot s then
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
            raise (CCFailure (LBLOCK [ STR "Error in normalize_path: " ; STR s ]))
        else      (* no first slash found *)
          raise (CCFailure (LBLOCK [ STR "Error in normalize_path: " ; STR s ]))
      else        (* just one dot *)
        if dotindex + 1 < len && String.get s (dotindex+1) = '/' then
          let s1 = String.sub s 0 dotindex in
          let s2 = String.sub s (dotindex + 2) (len - (dotindex + 2)) in
          normalize_path (String.concat "" [ s1 ; s2 ])
        else
          raise (CCFailure (LBLOCK [ STR "Error in normalize_path: " ; STR s ]))
    else   (* no dots *)
      s

  (* the location filename is either a filename with an absolute path or a 
     a filename with a path relative to the project path (project_path_prefix) *)
let get_location_filename project_path_prefix locpath locfile =
  let has_project_path_prefix name =
    let pre_len = String.length project_path_prefix in
    if String.length name > pre_len then
      let fsub = String.sub name 0 pre_len in 
      fsub = project_path_prefix 
    else
      false in
  let add_preprocessor_path path name =
    let path_len = String.length path in
    if  path_len > 2 then
      (String.sub path 0 (path_len - 1)) ^ name
    else
      name in
  let substitute_prefix name = 
    let pre_len = (String.length project_path_prefix) + 1 in
    String.sub name pre_len ((String.length name) - pre_len)  in
  let get_filename path file =
    if path = "" then file else
      let absoluteName =
        if Filename.is_relative file then
          add_preprocessor_path path file
        else
          file in
      if has_project_path_prefix absoluteName then
	normalize_path (substitute_prefix absoluteName)
      else
	normalize_path absoluteName in
  get_filename locpath locfile
