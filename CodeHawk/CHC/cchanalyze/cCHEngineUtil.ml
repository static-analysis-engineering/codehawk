(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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


(** {1 symbol_t utilities} *)

let symbol ?(atts = []) s = new symbol_t ~atts:atts s

let numbersymbol ?(atts = []) n s = new symbol_t ~atts:atts ~seqnr:n s

let symbol2string s = List.hd s#getSymbol

let getSymbolNumber s = s#getSeqNumber

let add_to_symbol sym s =
  let name_lst = sym#getSymbol in
  let num = getSymbolNumber sym in
  let newname = (List.hd name_lst) ^ "_" ^ s in
    new symbol_t ~atts:(List.tl name_lst) ~seqnr:num newname


(** {1 variable_t utilities} *)

let variable2string (v:variable_t):string =
  let name = symbol2string v#getName in
  let suffix = v#getSuffix in
    name ^ (if suffix = 0 then "" else "_" ^ (string_of_int suffix))


(** {1 operation_t utilities} *)

let getOperationName op = symbol2string (op.op_name)

let getOperationSeqNumber op = getSymbolNumber (op.op_name)


(** {1 system creation} *)

let mkCode = LF.mkCode

let mkScope ?(tmp_base = "tmp") () = LF.mkScope ~tmp_base:tmp_base ()

let mkState sym cmds = LF.mkState sym (mkCode cmds)

let mkCFG entry_state exit_state = LF.mkCFG entry_state exit_state

let mkProcedure = LF.mkProcedure

let mkSystem = LF.mkSystem
