(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchlibx86 *)
open BCHLibx86Types

module LF = CHOnlineCodeSet.LanguageFactory
module TR = CHTraceResult


let make_proc_name address = doubleword_to_symbol "proc" address


class location_collector_t (proc_name:symbol_t) =
object (self: _)

  inherit code_walker_t as super

  val mutable locations = []

  method walkCmd cmd =
    match cmd with
      OPERATION { op_name=opName ; op_args = opargs } ->
	begin
	  match opName#getBaseName with
	    "invariant" ->
	      locations <- opName :: locations
	  | _ ->
	    ()
	end
    | _ -> super#walkCmd cmd

  method get_locations = locations
end
	    

class chif_system_t:chif_system_int = 
object (self)

  val mutable system = LF.mkSystem (new symbol_t "binary-analysis system")

  method reset = system <- LF.mkSystem (new symbol_t "binary-analysis system")

  method add_procedure (p:procedure_int) = system#addProcedure p

  method get_procedure_names = system#getProcedures

  method get_system = system

  method get_procedure (procName: symbol_t) =
    if system#hasProcedure procName then
      system#getProcedure procName 
    else
      begin
	ch_error_log#add "invocation error" (STR "chif_system#get_procedure");
	raise
          (BCH_failure
	     (LBLOCK [STR "chif_system#get_procedure: "; procName#toPretty]))
      end

  method get_procedure_by_address (fa:doubleword_int) =
    let procName = make_proc_name fa in
    if system#hasProcedure procName then
      system#getProcedure procName 
    else
      begin
	ch_error_log#add
          "invocation error" (STR "chif_system#get_procedure_by_address");
	raise
          (BCH_failure
	     (LBLOCK [STR "chif_system#get_procedure_by_address: "; fa#toPretty]))
      end

  method get_procedure_by_index (index:dw_index_t) =
    self#get_procedure_by_address (TR.tget_ok (index_to_doubleword index))

  method get_procedure_count = List.length system#getProcedures

  method has_procedure (procName:symbol_t) = system#hasProcedure procName

  method has_procedure_by_address (function_address:doubleword_int) =
    let procName = make_proc_name function_address in
    system#hasProcedure procName

  method has_procedure_by_index (index:dw_index_t) =
    self#has_procedure_by_address (TR.tget_ok (index_to_doubleword index))

  method get_procedure_locations (procName:symbol_t) =
    let collector = new location_collector_t procName in
    let proc = self#get_procedure procName in
    let _ = collector#walkCode proc#getBody in
    let locations = collector#get_locations in
    List.map (fun locName -> (procName, locName)) locations

end


let chif_system = new chif_system_t
