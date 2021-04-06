(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs LLC

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
open CHIntervals
open CHNumerical
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open Xsimplify

(* bchlib *)
open BCHApiParameter
open BCHBasicTypes
open BCHByteUtilities
open BCHConstantDefinitions
open BCHCPURegisters
open BCHFloc   
open BCHFunctionApi
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMDictionary
open BCHARMDisassemblyUtils
open BCHARMLoopStructure
open BCHARMOperand
open BCHARMOpcodeRecords
open BCHARMTypes

module B = Big_int_Z
module H = Hashtbl

let x2p = xpr_formatter#pr_expr

let bd = BCHDictionary.bdictionary
let ixd = BCHInterfaceDictionary.interface_dictionary

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let get_multiplier (n:numerical_t) =
  int_constant_expr (pow 2 n#toInt)

class arm_opcode_dictionary_t
        (faddr:doubleword_int)
        (vard:vardictionary_int): arm_opcode_dictionary_int =
object (self)

  val sp_offset_table = mk_index_table "sp-offset-table"
  val instrx_table = mk_index_table "instrx-table"
  val xd = vard#xd

  val mutable tables = []

  initializer
    tables <- [
      sp_offset_table;
      instrx_table
    ]

  method index_sp_offset (o:(int * interval_t)) =
    let (level,offset) = o in
    let key = ([],[level; xd#index_interval offset]) in
    sp_offset_table#add key

  method get_sp_offset (index:int) =
    let (tags, args) = sp_offset_table#retrieve index in
    let a = a "sp-offset" args in
    (a 0, xd#get_interval (a 1))

  (* Legend for tags:
     "nop": instruction is no-op,
     "save": saving a register to the stack,
     "a:" (prefix,arg-key) (if present should be first): 
          a: address xpr; x: xpr; v: variable ; l: literal int ; s: string
   *)

  method index_instr
           (instr:arm_assembly_instruction_int)
           (floc:floc_int) =
    (*
    let rewrite_expr x: xpr_t =
      try
        let rec expand x =
          match x with
          | XVar v
               when floc#env#is_global_variable v
                    && elf_header#is_program_address
                         (floc#env#get_global_variable_address v) ->
             num_constant_expr
               (elf_header#get_program_value
                  (floc#env#get_global_variable_address v))#to_numerical
          | XVar v when floc#env#is_symbolic_value v ->
             expand (floc#env#get_symbolic_value_expr v)
          | XOp (op, l) -> XOp (op, List.map expand l)
          | _ -> x in
        let xpr =
          floc#inv#rewrite_expr (expand x) floc#env#get_variable_comparator in
        simplify_xpr (expand xpr)
      with IO.No_more_input ->
            begin
              pr_debug [STR "Error in rewriting expression: ";
                        x2p x;
                        STR ": No more input";
                        NL];
              raise IO.No_more_input
            end in *)
    let key =
      match instr#get_opcode with
      | _ -> ([], []) in
    instrx_table#add key

  method write_xml_sp_offset
           ?(tag="isp") (node:xml_element_int) (o:int * interval_t) =
    node#setIntAttribute tag (self#index_sp_offset o)

  method write_xml_instr
           ?(tag="iopx")
           (node:xml_element_int)
           (instr:arm_assembly_instruction_int)
           (floc:floc_int) =
    try
      node#setIntAttribute tag (self#index_instr instr floc)
    with
    | BCH_failure p ->
       let msg =
         LBLOCK [STR "Error in writing xml instruction: ";
                 floc#l#i#toPretty;
                 STR "  ";
                 instr#toPretty;
                 STR ": ";
                 p] in
       raise (BCH_failure msg)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end

let mk_arm_opcode_dictionary = new arm_opcode_dictionary_t
      
