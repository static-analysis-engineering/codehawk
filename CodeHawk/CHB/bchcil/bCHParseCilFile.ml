(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs LLC

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

(* cil *)
open GoblintCil
open Errormsg
open Frontc

(* chlib *)
open CHPretty

(* bchlib *)
open BCHBCFiles
open BCHBCTypes
open BCHBCTypeUtil
open BCHCilToCBasic



let parse_cil_file ?(computeCFG=true) ?(removeUnused=true) (filename: string) =
  try
    let cilfile = Frontc.parse filename () in
    let _ = if computeCFG then Cfg.computeFileCFG cilfile in
    let _ = if removeUnused then RmUnused.removeUnused cilfile in
    let bcfile = cil_file_to_bcfile cilfile in
    begin
      bcfiles#add_bcfile bcfile;
      List.iter (fun g ->
          match g with
          | GCompTagDecl (compinfo, loc) ->
             bcfiles#update_global (GCompTagDecl (layout_fields compinfo, loc))
          | GCompTag (compinfo, loc) ->
             bcfiles#update_global (GCompTag (layout_fields compinfo, loc))
          | _ -> ()) bcfile.bglobals
    end
  with
  | ParseError s ->
     begin
       pr_debug [STR "Error when parsing (CIL) "; STR filename; NL];
       exit 1
     end
  | e ->
     begin
       pr_debug [STR "Error when parsing (other exception): "; STR filename; NL];
       pr_debug [STR (Printexc.to_string e); NL];
       exit 1
     end
    
