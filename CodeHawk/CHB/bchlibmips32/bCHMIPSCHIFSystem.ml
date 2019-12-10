(* =============================================================================
   CodeHawk Binary Analyzer 
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

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSTypes

module LF =  CHOnlineCodeSet.LanguageFactory

let make_mips_proc_name (addr:doubleword_int) = doubleword_to_symbol "proc" addr

class mips_chif_system_t:mips_chif_system_int =
object (self)

  val mutable system = LF.mkSystem (new symbol_t "mips-analysis-system")

  method reset = system <- LF.mkSystem (new symbol_t "mips-analysis-system")

  method add_mips_procedure (p:procedure_int) = system#addProcedure p

  method get_mips_procedure_names = system#getProcedures

  method get_mips_system = system

  method get_mips_procedure (faddr:doubleword_int) =
    let procname = make_mips_proc_name faddr in
    if system#hasProcedure procname then
      system#getProcedure procname
    else
      let msg = LBLOCK [ STR "CHIF procedure for " ; faddr#toPretty ;
                         STR " not found" ] in
      begin
        ch_error_log#add "chif system" msg ;
        raise (BCH_failure msg)
      end

  method has_mips_procedure (faddr:doubleword_int) =
    system#hasProcedure (make_mips_proc_name faddr)

end

let mips_chif_system = new mips_chif_system_t
