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
open CHLanguage
open CHOnlineCodeSet

module LF = LanguageFactory

type cmd_t = (code_t, cfg_t) command_t

type nested_cmd_t =
  | CBLOCK of nested_cmd_t list
  | CCMD of cmd_t
  | CNOP
  
let mkCode = LF.mkCode

let make_nested_nop () = CNOP
let make_nested_cmd (cmd:cmd_t) = CCMD cmd
let make_nested_cmd_block (l:nested_cmd_t list) = CBLOCK l

let rec flatten (ccmd:nested_cmd_t) =
  match ccmd with
  | CCMD _ -> [ ccmd ]
  | CBLOCK l -> flatten_nested_cmd_list l
  | CNOP -> [] 

and flatten_nested_cmd_list (l:nested_cmd_t list) =
  List.fold_right (fun c a -> (flatten c) @ a) l []

let nested_cmds_2_cmds (ccmds:nested_cmd_t list):cmd_t list =
  let ccmd2cmd c =
    match c with
    | CCMD cmd -> cmd
    | _ -> failwith ("Problem with ccmd flattening") in
  let l = List.map ccmd2cmd (flatten_nested_cmd_list ccmds) in
  List.filter (fun c -> match c with SKIP -> false | _ -> true) l

let nested_cmd_2_cmds (ccmd:nested_cmd_t) = 
  nested_cmds_2_cmds (flatten ccmd)

let make_nested_branch_cmd (l:(nested_cmd_t list list)):nested_cmd_t =
  match l with
  | [] -> make_nested_nop ()
  | [ s ] -> make_nested_cmd_block s
  | _ ->
     let flatlists = List.map flatten_nested_cmd_list l in
     let codelists = List.map (fun s -> mkCode (nested_cmds_2_cmds s)) flatlists in
     make_nested_cmd (BRANCH codelists)
