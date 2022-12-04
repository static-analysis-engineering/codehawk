(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs, LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHFunctionInfo
open BCHFloc
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation
open BCHSystemInfo
open BCHUtilities

(* bchlibarm32 *)
open BCHARMOpcodeRecords
open BCHARMTypes

module H = Hashtbl


class arm_assembly_function_t
        (faddr:doubleword_int)
        (blocks:arm_assembly_block_int list)
        (successors:(ctxt_iaddress_t * ctxt_iaddress_t) list)
      :arm_assembly_function_int =
object (self)

  val blocktable =
    let t = H.create 3 in
    let _ = List.iter (fun b -> H.add t b#get_context_string b) blocks in
    t
  val successortable =
    let t = H.create 3 in
    let _ = List.iter (fun (src,tgt) -> H.add t src tgt) successors in
    t

  method get_address = faddr

  method get_blocks = blocks

  method get_block (bctxt:ctxt_iaddress_t) =
    if H.mem blocktable bctxt then
      H.find blocktable bctxt
    else
      begin
        ch_error_log#add
          "invocation error"
          (LBLOCK [ STR "arm_assembly_function#get_block: ";
                    STR bctxt ]);
        raise
          (BCH_failure
             (LBLOCK [ STR "No assembly block found at " ; STR bctxt;
                       STR " in function " ; faddr#toPretty ]))
      end

  method get_instruction (iaddr:doubleword_int) =
    try
      let block =
        List.find (fun b -> b#includes_instruction_address iaddr) blocks in
      block#get_instruction iaddr
    with
    | Not_found ->
       let msg = LBLOCK [ STR "arm_assembly_function#get_instruction: ";
                          iaddr#toPretty ] in
       begin
         ch_error_log#add "invocation error" msg;
         raise (BCH_failure msg)
       end

  method get_bytes_as_hexstring =
    let s = ref "" in
    let _ = self#iter (fun b -> s := !s ^ b#get_bytes_as_hexstring) in
    !s

  method get_instruction_count =
    List.fold_left (fun a b -> a + b#get_instruction_count) 0 blocks

  method get_block_count = List.length blocks

  method get_function_md5 =
    byte_string_to_printed_string (Digest.string self#get_bytes_as_hexstring)

  method iter (f:arm_assembly_block_int -> unit) =
    List.iter (fun b -> f b) self#get_blocks

  method itera (f:ctxt_iaddress_t -> arm_assembly_block_int -> unit) =
    List.iter (fun b -> f b#get_context_string b) self#get_blocks

  method iteri
           (f:doubleword_int
            -> ctxt_iaddress_t
            -> arm_assembly_instruction_int
            -> unit) =
    List.iter (fun (b:arm_assembly_block_int) ->
        b#itera (fun iaddr instr -> f faddr iaddr instr)) self#get_blocks

  method populate_callgraph (callgraph:callgraph_int) =
    self#iteri (fun _ iaddr instr -> ())

  method includes_instruction_address (va:doubleword_int) =
    List.exists (fun b -> b#includes_instruction_address va) blocks

  method toPretty =
    LBLOCK (List.map (fun b -> LBLOCK [ b#toPretty ; NL ]) blocks)

end

let make_arm_assembly_function
      (va:doubleword_int)
      (blocks:arm_assembly_block_int list)
      (successors:(ctxt_iaddress_t * ctxt_iaddress_t) list) =
  let blocks =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string) blocks in
  new arm_assembly_function_t va blocks successors
