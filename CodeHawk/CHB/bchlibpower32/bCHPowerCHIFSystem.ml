(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs LLC

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

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerTypes


module LF = CHOnlineCodeSet.LanguageFactory


let make_pwr_proc_name (addr: doubleword_int) =
  doubleword_to_symbol "proc" addr


class pwr_chif_system_t: pwr_chif_system_int =
object

  val mutable system = LF.mkSystem (new symbol_t "pwr-analysis-system")

  method reset = system <- LF.mkSystem (new symbol_t "pwr-analysis-system")

  method add_pwr_procedure (p: procedure_int) = system#addProcedure p

  method get_pwr_procedure_names = system#getProcedures

  method get_pwr_system = system

  method get_pwr_procedure (faddr: doubleword_int) =
    let procname = make_pwr_proc_name faddr in
    if system#hasProcedure procname then
      system#getProcedure procname
    else
      let msg =
        LBLOCK [
            STR "CHIF procedure for "; faddr#toPretty; STR " not found"] in
      begin
        ch_error_log#add "chif system" msg;
        raise (BCH_failure msg)
      end

  method has_pwr_procedure (faddr: doubleword_int) =
    system#hasProcedure (make_pwr_proc_name faddr)

end


let pwr_chif_system = new pwr_chif_system_t
