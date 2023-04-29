(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs LLC

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
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHIndexTable
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open XprUtil
open Xsimplify

(* bchlib *)
open BCHFtsParameter
open BCHBasicTypes
open BCHByteUtilities
open BCHConstantDefinitions
open BCHCPURegisters
open BCHDoubleword
open BCHFloc   
open BCHFunctionInterface
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo

(* bchlibelf *)
open BCHELFHeader

(* bchlibpower32 *)
open BCHPowerOperand
open BCHPowerTypes


module B = Big_int_Z
module H = Hashtbl
module TR = CHTraceResult


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


class pwr_opcode_dictionary_t
        (faddr: doubleword_int)
        (vard: vardictionary_int): pwr_opcode_dictionary_int =
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
           (instr: pwr_assembly_instruction_int)
           (floc: floc_int) =
    let varinv = floc#varinv in
    let rewrite_expr ?(restrict:int option) (x: xpr_t): xpr_t =
      try
        let xpr =
          floc#inv#rewrite_expr x floc#env#get_variable_comparator in
        let xpr = simplify_xpr xpr in
        let xpr =
          let vars = variables_in_expr xpr in
          let varssize = List.length vars in
          if varssize = 1 then
            let xvar = List.hd vars in
            if floc#env#is_frozen_test_value xvar then
              let (testvar, testiaddr, _) = floc#env#get_frozen_variable xvar in
              let testloc = ctxt_string_to_location floc#fa testiaddr in
              let testfloc = get_floc testloc in
              let extxprs = testfloc#inv#get_external_exprs testvar in
              let extxprs =
                List.map (fun e -> substitute_expr (fun v -> e) xpr) extxprs in
              (match extxprs with
               | [] -> xpr
               | _ -> List.hd extxprs)
            else
              xpr
          else
            xpr in
        match (restrict, xpr) with
        | (Some 4, XConst (IntConst n)) ->
           if n#geq numerical_e32 then
             XConst (IntConst (n#sub numerical_e32))
           else
             xpr
        | _ ->
           xpr
      with IO.No_more_input ->
            begin
              pr_debug [
                  STR "Error in rewriting expression: ";
                  x2p x;
                  STR ": No more input";
                  NL];
              raise IO.No_more_input
            end in

    let mk_instrx_data
          ?(vars: variable_t list = [])
          ?(xprs: xpr_t list = [])
          ?(rdefs: int list = [])
          ?(uses: int list = [])
          ?(useshigh: int list = [])
          () =
      let varcount = List.length vars in
      let xprcount = List.length xprs in
      let rdefcount = List.length rdefs in
      let defusecount = List.length uses in
      let defusehighcount = List.length useshigh in
      let varstring = string_repeat "v" varcount in
      let xprstring = string_repeat "x" xprcount in
      let rdefstring = string_repeat "r" rdefcount in
      let defusestring = string_repeat "d" defusecount in
      let defusehighstring = string_repeat "h" defusehighcount in
      let tagstring =
        "a:"
        ^ varstring
        ^ xprstring
        ^ rdefstring
        ^ defusestring
        ^ defusehighstring in
      let varargs = List.map xd#index_variable vars in
      let xprargs = List.map xd#index_xpr xprs in
      (tagstring, varargs @ xprargs @ rdefs @ uses @ useshigh) in

    let key =
      match instr#get_opcode with
      | Add (_, _, _, rd, ra, rb, _, _, _) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xrb = rb#to_expr floc in
         let rhs = XOp (XPlus, [xra; xrb]) in
         let rrhs = rewrite_expr rhs in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xra; xrb; rhs; rrhs]
             () in
         ([tagstring], args)

      | AddImmediate (_, _, _, _, _, rd, ra, simm, _) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xsimm = simm#to_expr floc in
         let rhs = XOp (XPlus, [xra; xsimm]) in
         let rrhs = rewrite_expr rhs in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xra; xsimm; rhs; rrhs]
             () in
         ([tagstring], args)

      | BranchLink (_, tgt, _)
           when floc#has_call_target
                && floc#get_call_target#is_signature_valid ->
         let args = List.map snd floc#get_pwr_call_arguments in
         let vrd = (pwr_gp_register_op 3 WR)#to_variable floc in
         let rv = floc#env#mk_return_value floc#cia in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[rv]
             ~xprs:args
             () in
         let tags = tagstring :: ["call"] in
         let args =
           args @ [ixd#index_call_target floc#get_call_target#get_target] in
         (tags, args)

      | LoadImmediate (_, _, shifted, rd, imm) ->
         let vrd = rd#to_variable floc in
         let ximm =
           if shifted then
             imm#to_shifted_expr 16
           else
             imm#to_expr floc in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[ximm]
             () in
         ([tagstring], args)

      | LoadWordZero (_, _, rd, ra, mem) ->
         let vrd = rd#to_variable floc in
         let xra = ra#to_expr floc in
         let xaddr = mem#to_address floc in
         let vmem = mem#to_variable floc in
         let xmem = mem#to_expr floc in
         let rxmem = rewrite_expr xmem in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd; vmem]
             ~xprs:[xra; xmem; rxmem; xaddr]
             () in
         ([tagstring], args)

      | MoveFromLinkRegister (_, rd, lr) ->
         let vrd = rd#to_variable floc in
         let xlr = lr#to_expr floc in
         let rxlr = rewrite_expr xlr in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xlr; rxlr]
             () in
         ([tagstring], args)

      | MoveRegister (_, _, rd, rs) ->
         let vrd = rd#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vrd]
             ~xprs:[xrs; rxrs]
             () in
         ([tagstring], args)

      | MoveToLinkRegister (_, lr, rs) ->
         let vlr = lr#to_variable floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vlr]
             ~xprs:[xrs; rxrs]
             () in
         ([tagstring], args)

      | OrImmediate (_, _, shifted, _, ra, rs, uimm, _) ->
         let vra = ra#to_variable floc in
         let xrs = rs#to_expr floc in
         let xuimm =
           if shifted then
             uimm#to_shifted_expr 16
           else
             uimm#to_expr floc in
         let xrhs = XOp (XBOr, [xrs; xuimm]) in
         let rxrhs = rewrite_expr xrhs in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vra]
             ~xprs:[xrs; xuimm; xrhs; rxrhs]
             () in
         ([tagstring], args)

      | StoreWord (_, _, rs, ra, mem) ->
         let vmem = mem#to_variable floc in
         let xaddr = mem#to_address floc in
         let xrs = rs#to_expr floc in
         let rxrs = rewrite_expr xrs in
         let xra = ra#to_expr floc in
         let rxra = rewrite_expr xra in
         let (tagstring, args) =
           mk_instrx_data
             ~vars:[vmem]
             ~xprs:[xrs; rxrs; xra; rxra; xaddr]
             () in
         ([tagstring], args)

      | _ -> ([], []) in
    instrx_table#add key

  method write_xml_sp_offset
           ?(tag="isp") (node: xml_element_int) (o: int * interval_t) =
    node#setIntAttribute tag (self#index_sp_offset o)

  method write_xml_instr
           ?(tag="iopx")
           (node: xml_element_int)
           (instr: pwr_assembly_instruction_int)
           (floc: floc_int) =
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

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end


let mk_pwr_opcode_dictionary = new pwr_opcode_dictionary_t
      
