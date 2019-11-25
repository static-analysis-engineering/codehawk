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
   
type cmd_t = (code_t, cfg_t) command_t

type nested_cmd_t =
  | CBLOCK of nested_cmd_t list
  | CCMD of cmd_t
  | CNOP

val make_nested_nop: unit -> nested_cmd_t
val make_nested_cmd: cmd_t -> nested_cmd_t
val make_nested_cmd_block: nested_cmd_t list -> nested_cmd_t
val make_nested_branch_cmd: nested_cmd_t list list -> nested_cmd_t

val flatten: nested_cmd_t -> nested_cmd_t list
val flatten_nested_cmd_list: nested_cmd_t list -> nested_cmd_t list
  
val nested_cmd_2_cmds: nested_cmd_t -> cmd_t list
val nested_cmds_2_cmds: nested_cmd_t list -> cmd_t list
