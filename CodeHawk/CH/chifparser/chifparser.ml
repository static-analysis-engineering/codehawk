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

module F = LanguageFactory

let parse_file filename =
  try
    let chan = open_in filename in
    let lexbuf = Lexing.from_channel chan in
    let lib = Parser.program Lexer.token lexbuf in
    let system = F.mkSystem (new symbol_t filename) in
    let staticChecker = (new static_checker_t system) in
    begin
      List.iter (fun p -> system#addProcedure p) lib ;
      staticChecker#checkAll ;
      lib
    end
      
  with
  | CHFailure s -> 
      (pr_debug [ s ] ; Printf.eprintf "\n" ; raise (CHFailure s))
  | Parse_failure (line,pos,str) -> 
      begin
	print_endline ("Parsing Failure: Line " ^ string_of_int line
                       ^ ", Character " ^ string_of_int pos ^ ":: " ^ str) ;
	raise (CHFailure (STR "parse error"))
      end
  | CHStaticCheck sc -> 
      (pr_debug [ sc ] ; Printf.eprintf "\n" ; raise (CHFailure (STR "Static checker")))
  | e -> 
      begin
	Printf.eprintf "Unexpected exception : %s \n" (Printexc.to_string e ); 
	raise (CHFailure (STR "error"))
      end


