(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: A. Cody Schuffelen
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
  
open Parser
open Lexing

(* chlib *)
open CHCommon
open CHLanguage
open CHOnlineCodeSet   
open CHPretty
open CHStaticChecker

(* chifparser *)
open ParseError

module F = LanguageFactory;;

let symbol ?(atts = []) s = new symbol_t ~atts:atts s;;

let pp = new pretty_printer_t stdout;;
let system = F.mkSystem(symbol "mysystem")
let staticChecker = (new static_checker_t system);;

let rec printList prettyList =
  match prettyList with
  | [] -> ()
  | first :: rest -> (pp#print (first#toPretty) ; system#addProcedure first ; printList rest)
;;

let parse_local_lib_file filename =
  try
    let chan = open_in filename in
    let lexbuf = Lexing.from_channel chan in
    let lib = Parser.program Lexer.token lexbuf in
    begin
      printList lib ;
      staticChecker#checkAll
    end
    
  with
  | CHFailure s -> (pp#print s ; Printf.eprintf "\n")
  | Parse_failure (line,pos,str) ->
     print_endline ("Parsing Failure: Line " ^ string_of_int line
                    ^ ", Character " ^ string_of_int pos ^ ":: " ^ str)
  | CHStaticCheck sc -> (pp#print sc ; Printf.eprintf "\n")
  | e -> Printf.eprintf "Unexpected exception : %s \n" (Printexc.to_string e);
(*
  begin
  (* pr_debug [ libToPretty lib ] ; *)
  statistics#inc_files ;
  statistics#add_functions len;
  Printf.printf "saving %s (%d function models)\n" name len;
  dump_binary_file name lib
  end*)
;;

let read_args () =
  let speclist =
    [("-file",Arg.Rest (parse_local_lib_file), 
      "file names of system model files")
    ] in
  let usage_msg = "usage: libparser -file <chif file>" in
  Arg.parse speclist (fun s -> ()) usage_msg
;;

let main () =
  read_args ()
;;

main();;
