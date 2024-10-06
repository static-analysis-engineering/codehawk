(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2024  Aarno Labs LLC

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

(* bchlibarm32 *)
open BCHARMTypes


module LF = CHOnlineCodeSet.LanguageFactory


let make_arm_proc_name (addr:doubleword_int) = doubleword_to_symbol "proc" addr


class arm_chif_system_t:arm_chif_system_int =
object

  val mutable system = LF.mkSystem (new symbol_t "arm-analysis-system")

  method reset = system <- LF.mkSystem (new symbol_t "arm-analysis-system")

  method add_arm_procedure (p:procedure_int) = system#addProcedure p

  method add_arm_definitions_procedure (p: procedure_int) = system#addProcedure p

  method get_arm_procedure_names = system#getProcedures

  method get_arm_system = system

  method get_arm_procedure (faddr:doubleword_int) =
    let procname = make_arm_proc_name faddr in
    if system#hasProcedure procname then
      system#getProcedure procname
    else
      let msg =
        LBLOCK [ STR "CHIF procedure for "; faddr#toPretty;
                 STR " not found"] in
      begin
        ch_error_log#add "chif system" msg;
        raise (BCH_failure msg)
      end

  method has_arm_procedure (faddr: doubleword_int) =
    system#hasProcedure (make_arm_proc_name faddr)

end

let arm_chif_system = new arm_chif_system_t
                          
