(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
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

(* chutil *)
open CHFileIO


let project_path_prefix = ref ""

  
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
  get_filename (normalize_path locpath) (normalize_path locfile)
