(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs, LLC

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


(* Documentation reference:
 * ========================
 * ARM Architecture Reference Manual
 * ARMv7-A and ARMv7-R edition, March 29, 2018
 *)

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStrings

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMTypes

(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16

let rec pow2 n =
  match n with
  | 0 -> 1
  | 1 -> 2
  | n -> 
    let b = pow2 (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else 2)
        
let stri = string_of_int

let decompose_arm_instr (dw:doubleword_int):arm_instr_class_t =
  let dwint = dw#to_int in
  let opc = (dwint lsr 25) mod 8 in
  let get_cond () = dw#get_segval 31 28 in
  match opc with
  | 0 ->
     let cond = get_cond () in
     let op = dw#get_segval 24 21 in
     let opx = dw#get_bitval 20 in
     let rn = dw#get_segval 19 16 in
     let rd = dw#get_segval 15 12 in
     let rs = dw#get_segval 11 8 in
     let opy = dw#get_bitval 7 in
     let shift = dw#get_segval 6 5 in
     let reg = dw#get_bitval 4 in
     let rm = dw#get_segval 3 0 in                                 
     DataProcRegType (cond,op,opx,rn,rd,rs,opy,shift,reg,rm)
  | 1 ->
     let cond = get_cond () in
     let op = dw#get_segval 24 21 in
     let opx = dw#get_bitval 20 in
     let rn = dw#get_segval 19 16 in
     let rd = dw#get_segval 15 12 in
     let rotate = dw#get_segval 11 8 in
     let imm = dw#get_segval 7 0 in
     DataProcImmType (cond,op,opx,rn,rd,rotate,imm)
  | 2 ->
     let cond = get_cond () in
     let p = dw#get_bitval 24 in
     let u = dw#get_bitval 23 in
     let opx = dw#get_bitval 22 in
     let w = dw#get_bitval 21 in
     let opy = dw#get_bitval 20 in
     let rn = dw#get_segval 19 16 in
     let rd = dw#get_segval 15 12 in
     let imm = dw#get_segval 11 0 in
     LoadStoreImmType (cond,p,u,opx,w,opy,rn,rd,imm)
  | 3 when (dw#get_bitval 4) = 1 ->
     let cond = get_cond () in
     let op1 = dw#get_segval 24 20 in
     let data1 = dw#get_segval 19 16 in
     let rd = dw#get_segval 15 12 in
     let data2 = dw#get_segval 11 8 in
     let op2 = dw#get_segval 7 5 in
     let rn = dw#get_segval 3 0 in
     MediaType (cond,op1,data1,rd,data2,op2,rn)
  | 3 ->
     let cond = get_cond () in
     let p = dw#get_bitval 24 in
     let u = dw#get_bitval 23 in
     let opx = dw#get_bitval 22 in
     let w = dw#get_bitval 21 in
     let opy = dw#get_bitval 20 in
     let rn = dw#get_segval 19 16 in
     let rd = dw#get_segval 15 12 in
     let imm = dw#get_segval 11 7 in
     let shift = dw#get_segval 6 5 in
     let opz = dw#get_bitval 4 in
     let rm = dw#get_segval 3 0 in
     LoadStoreRegType (cond,p,u,opx,w,opy,rn,rd,imm,shift,opz,rm)
  | 4 ->
     let cond = get_cond () in
     let p = dw#get_bitval 24 in
     let u = dw#get_bitval 23 in
     let opx = dw#get_bitval 22 in
     let w = dw#get_bitval 21 in
     let opy = dw#get_bitval 20 in
     let rn = dw#get_segval 19 16 in
     let opz = dw#get_bitval 15 in
     let reglist = dw#get_segval 14 0 in
     BlockDataType (cond,p,u,opx,w,opy,rn,opz,reglist)
  | 5 ->
     let cond = get_cond () in
     let opx = dw#get_bitval 24 in
     let offset = dw#get_segval 23 0 in
     BranchLinkType (cond,opx,offset)
  | _ ->
     SupervisorType (0,0)

let arm_instr_class_to_string (c:arm_instr_class_t):string =
  match c with
  | DataProcRegType (cond,op,opx,rn,rd,rs,opy,shift,reg,rm) ->
     "DataProcRegType("
     ^ String.concat "," (List.map stri [cond; op; opx; rn; rd; rs; opy; shift; reg; rm ])
     ^ ")"
  | DataProcImmType (cond,op,opx,rn,rd,rotate,imm) ->
     "DataProcImmType("
     ^ String.concat "," (List.map stri [cond; op; opx; rn; rd; rotate; imm ])
     ^ ")"
  | LoadStoreImmType (cond,p,u,opx,w,opy,rn,rd,imm) ->
     "LoadStoreImmType("
     ^ String.concat "," (List.map stri [cond; p; u; opx; w; opy; rn; rd; imm])
     ^ ")"
  | LoadStoreRegType (cond,p,u,opx,w,opy,rn,rd,imm,shift,opz,rm) ->
     "LoadStoreRegType("
     ^ String.concat "," (List.map stri [cond; p; u; opx; w; opy; rn; rd; imm; shift; opz; rm ])
     ^ ")"
  | MediaType (cond,op1,data1,rd,data2,op2,rn) ->
     "MediaType("
     ^ String.concat "," (List.map stri [cond; op1; data1; rd; data2; op2; rn])
     ^ ")"
  | BlockDataType (cond,p,u,opx,w,opy,rn,opz,reglist) ->
     "BlockDataType("
     ^ String.concat "," (List.map stri [cond; p; u; opx; w; opy; rn; opz; reglist])
     ^ ")"
  | BranchLinkType (cond,opx,offset) ->
     "BranchLinkType("
     ^ String.concat "," (List.map stri [cond; opx; offset])
     ^ ")"
  | _ -> "SupervisorType"
