(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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

(* chlib *)
open CHPretty

exception CHIOFailure of string

class type file_output_int =
  object
    method setProjectSourcePath: string -> unit
    method setProjectResultPath: string -> unit
    method setProjectName: string -> unit
    method saveFile: string -> pretty_t -> unit
    method saveStringToFile: string -> string -> unit
    method appendToFile: string -> pretty_t -> unit
  end

val file_output: file_output_int

val relativize_filename: string -> string -> string
(* returns the filename relative to the given directory;
   if the filename is absolute, but not in a subdirectory
   of the given directory the function fails *)
  
val absolute_name: string -> string
(* add the current working directory to the filename *)

val normalize_path: string -> string
(* remove . and .. from path names; if the filename
   is relative the function fails if removing .. would result
   in a parent directory of the path *)
  
