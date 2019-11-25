(* =============================================================================
   CodeHawk C Analyzer 
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
open CHPretty
open CHLanguage
open CHOnlineCodeSet

(* xprlib *)
open XprTypes

(* chutil *)
open CHNestedCommands

(* chanalyze *)
open CCHAnalysisTypes

val c_cmd_to_pretty: c_cmd_t -> pretty_t

val make_c_nop: unit -> c_cmd_t
val make_c_cmd: cmd_t -> c_cmd_t
val make_c_cmd_block: c_cmd_t list -> c_cmd_t

val make_operation: string -> int -> variable_t list -> c_cmd_t
val make_c_branch: c_cmd_t list list -> c_cmd_t

val is_c_nop: c_cmd_t -> bool

val flatten: c_cmd_t -> c_cmd_t list
val flatten_nested_cmd_list: c_cmd_t list -> c_cmd_t list

val ccmd2cmd  : c_cmd_t -> cmd_t
val ccmd2cmds : c_cmd_t -> cmd_t list
val ccmds2cmds: c_cmd_t list -> cmd_t list

val filter_out_skips: cmd_t list -> cmd_t list

val make_transaction:    symbol_t -> bool -> c_cmd_t list -> cmd_t
val make_labeled_transaction: int -> bool -> c_cmd_t list -> cmd_t

val make_command:    symbol_t -> cmd_t list -> cmd_t
val make_labeled_command: int -> cmd_t list -> cmd_t

val make_branch: cmd_t list list -> cmd_t
val make_loop: cmd_t list -> cmd_t list -> cmd_t list -> cmd_t
val make_call: string -> bindings_t -> cmd_t
val make_assert: boolean_exp_t -> cmd_t
val make_nop: unit -> cmd_t
val make_break: string -> cmd_t
val make_breakout_block: string -> cmd_t list -> cmd_t
val make_abstract_vars: variable_t list -> cmd_t

val make_symbolic_assign: variable_t -> xpr_t -> c_cmd_t
val insert_symbols: variable_t list -> symbol_t list -> c_cmd_t
