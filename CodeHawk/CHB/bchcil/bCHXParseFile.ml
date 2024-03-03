(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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
open Frontc

(* chlib *)
open CHCommon
open CHPretty

(* chutil *)
open CHFileIO
open CHXmlDocument

(* bchlib *)
open BCHBCDictionary
open BCHBCTypes
open BCHBCWriteXml
open BCHCilToCBasic


let filename = ref ""

let speclist = []

let usage_msg = "parseFile <absolute filename of preprocessed source file>"

let read_args () = Arg.parse speclist (fun s -> filename := s) usage_msg


let get_bch_root (filename:string):xml_element_int =
  let root = xmlElement "binary-analysis" in
  let hNode = xmlElement "header" in
  let cNode = xmlElement "created" in
  begin
    cNode#setAttribute "file" filename;
    cNode#setAttribute "time" (current_time_to_string ());
    root#appendChildren [hNode];
    hNode#appendChildren [cNode];
    root
  end
                 

let main () =
  try
      let _ = read_args () in
      let _ = pr_debug [STR "Parsing "; STR !filename; NL]  in
      let cilfile = Frontc.parse !filename () in
      let _ = Cfg.computeFileCFG cilfile in
      let _ = RmUnused.removeUnused cilfile in
      let bcfile = cil_file_to_bcfile cilfile in
      let fns =
        List.fold_left (fun a g ->
            match g with
            | GFun (fdec, _loc) -> fdec :: a
            | _ -> a) [] bcfile.bglobals in
      let doc = xmlDocument () in
      let root = get_bch_root "bc_file.c" in
      let filenode = xmlElement "c-file" in
      let fnsnode = xmlElement "functions" in
      let bcdict = xmlElement "bc-dictionary" in
      begin
        doc#setNode root;
        root#appendChildren [filenode];
        filenode#appendChildren [fnsnode];
        filenode#appendChildren [bcdict];
        (List.iter (fun f ->
             let n = xmlElement "function" in
             begin
               write_xml_function_definition n f;
               fnsnode#appendChildren [n]
             end) fns);
        write_xml_bcfile filenode bcfile "bc_file.c";
        bcdictionary#write_xml bcdict;
        Printf.printf "\nSaving cfile: %s\n" "bc_file.c";
        file_output#saveFile "bc_file.c" doc#toPretty
      end
  with
  | ParseError s ->
     begin
       pr_debug [
           STR "Error when parsing (CIL) "; STR !filename; STR "; "; STR s; NL];
       exit 1
     end
  | CHFailure p ->
     begin
       pr_debug [STR "Error when parsing "; STR !filename; STR ": "; p; NL];
       exit 1
     end
  | e ->
     begin
       pr_debug [
           STR "Error when parsing (other exception): "; STR !filename; NL];
       pr_debug [STR (Printexc.to_string e); NL];
       exit 1
     end


let _ = Printexc.print main ()
                     
