(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open CHNumerical

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHMemoryAccesses

(* bchlibx86 *)
open BCHAssemblyFunction
open BCHAssemblyInstruction
open BCHLibx86Types
open BCHOperand
open BCHX86Opcodes
open BCHX86OpcodeRecords

let record_argument_reads (acc:memory_accesses_int) (floc:floc_int) = ()
                                                                    
let record_known_pointer_argument_accesses (acc:memory_accesses_int) (floc:floc_int) = ()

let record_call_memory_accesses (acc:memory_accesses_int) (floc:floc_int) = 
  if floc#has_call_target
     && floc#get_call_target#is_semantics_valid then
    begin
      record_argument_reads acc floc ;
      record_known_pointer_argument_accesses acc floc
    end

let record_instr_memory_accesses (acc:memory_accesses_int) (floc:floc_int) 
                                 (instr:assembly_instruction_int) = ()

let record_memory_accesses (f:assembly_function_int) =
  let faddr = f#get_address in
  let finfo = get_function_info faddr in
  let mrecord = finfo#get_memory_access_record in
  match mrecord#get_accesses with 
  | [] ->
    begin
      f#iteri (fun faddr ctxtiaddr instr -> 
	  try
            let loc = ctxt_string_to_location faddr ctxtiaddr in
	    let floc = get_floc loc in
	    record_instr_memory_accesses mrecord floc instr 
	  with
	  | Invocation_error s ->
	     ch_error_log#add
               "record memory accesses"
	       (LBLOCK [ faddr#toPretty ; STR "," ; STR ctxtiaddr ; STR ": " ; STR s ])) ;
    end
  | _ -> ()
