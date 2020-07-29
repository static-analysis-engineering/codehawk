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
open CHLanguage

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

(* bchlibmips32 *)
open BCHMIPSOpcodeRecords
open BCHMIPSTypes

let stri = string_of_int

(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8

let select_mips_reg = function
  | 0 -> MRzero
  | 1 -> MRat
  | 2 -> MRv0
  | 3 -> MRv1
  | 4 -> MRa0
  | 5 -> MRa1
  | 6 -> MRa2
  | 7 -> MRa3
  | 8 -> MRt0
  | 9 -> MRt1
  | 10 -> MRt2
  | 11 -> MRt3
  | 12 -> MRt4
  | 13 -> MRt5
  | 14 -> MRt6
  | 15 -> MRt7
  | 16 -> MRs0
  | 17 -> MRs1
  | 18 -> MRs2
  | 19 -> MRs3
  | 20 -> MRs4
  | 21 -> MRs5
  | 22 -> MRs6
  | 23 -> MRs7
  | 24 -> MRt8
  | 25 -> MRt9
  | 26 -> MRk0
  | 27 -> MRk1
  | 28 -> MRgp
  | 29 -> MRsp
  | 30 -> MRfp
  | 31 -> MRra
  | _ -> raise (BCH_failure (STR "Error in select_mips_reg: reg > 31"))

let code_to_mips_fp_format c =
  match c with
  | 16 -> FPSingle
  | 17 -> FPDouble
  | 20 -> FPFixedWord
  | 21 -> FPFixedLong
  | 22 -> FPPair
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR "Invalid code for mips-fp-format: " ; INT c ]))

let decompose_instr (dw:doubleword_int):mips_instr_format_t =
  let dwlow = dw#get_low in
  let dwhigh = dw#get_high in
  let opcode = dwhigh lsr 10 in
  match opcode with
  (* opcode:6, rs:5, rt:5, rd:5, shamt:5, funct:6 *)
  | 0 ->
     let funct = dwlow mod 64 in
     let rs = (dwhigh lsr 5) mod 32 in
     let rd = dwlow lsr 11 in
     (match funct with
      | 1 ->
         let cc = (dwhigh lsr 2) mod 8 in
         let tf = dwhigh mod 2 in
         FPMCType (opcode,rs,cc,tf,rd,funct)
      | 12 ->
         let rt = dwhigh mod 32 in
         let shamt = (dwlow lsr 6) mod 32 in
         let code = shamt + (32 * (rd + (32 * (rt + (32 * rs ))))) in
         SyscallType code
      | _ ->
         let rt = dwhigh mod 32 in
         let shamt = (dwlow lsr 6) mod 32 in
         RType (opcode,rs,rt,rd,shamt,funct) )
  (* opcode:6, address:26 *)
  | 2 | 3 ->
     let upper = dwhigh mod 1024 in
     let addr = dwlow + (upper lsl 16) in
     JType (opcode,addr)
  (* opcode:6, rs:5, rt:5, immediate:16 *)
  | 1 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 20 | 21 | 22 | 23
    | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42
    | 43 | 44 | 45 | 46 | 48 | 49 | 53 | 56 | 57 | 61 ->
     let rs = (dwhigh lsr 5) mod 32 in
     let rt = dwhigh mod 32 in
     let offset = if dwlow < e15 then dwlow else dwlow - e16 in  (* signed *)
     IType (opcode,rs,rt,offset)
  (* SPECIAL2:28, rs:5, rt:5, rd:5, shamt:5, funct:6 *)
  | 28 ->
     let rs = (dwhigh lsr 5) mod 32 in
     let rt = dwhigh mod 32 in
     let rd = dwlow lsr 11 in
     let shamt = (dwlow lsr 6) mod 32 in
     let funct = dwlow mod 64 in
     R2Type (opcode,rs,rt,rd,shamt,funct)
  (* COP1:6, fmt:5, ft:5, fs:5, cc:3, 0:2, function:6 *)
  | 17 ->
     let fmt = (dwhigh lsr 5) mod 32 in
     (match fmt with
      | 0 | 2 | 4 | 6 ->
         let rt = dwhigh mod 32 in
         let fs = dwlow lsr 11 in
         FPRIType (opcode,fmt,rt,fs)
      | 16 | 17 | 20 | 21 | 22 ->
         let fnct = dwlow mod 64 in
         let ft = dwhigh mod 32 in
         let fs = dwlow lsr 11 in         
         if fnct < 32 then
           let fd = (dwlow lsr 6) mod 32 in
           FPRType (opcode,fmt,ft,fs,fd,fnct)
         else
           let cc = (dwlow lsr 8) mod 8 in
           let cond = fnct mod 16 in
           FPCompareType (opcode,fmt,ft,fs,cc,cond)
      | 8 ->
         let sub = (dwhigh lsr 5) mod 32 in
         let cc = (dwhigh lsr 2) mod 8 in
         let nd = (dwhigh lsr 1) mod 2 in
         let tf = dwhigh mod 2 in
         let offset = if dwlow < e15 then dwlow else dwlow - e16 in  (* signed *)         
         FPICCType (opcode,sub,cc,nd,tf,offset)
      | _ ->
         let ft = dwhigh mod 32 in
         let fs = dwlow lsr 11 in
         let cc = (dwlow lsr 8) mod 32 in
         let fnct = dwlow mod 64 in
         FPCompareType (opcode,fmt,ft,fs,cc,fnct))
  | _ ->
     raise (BCH_failure (LBLOCK [  STR "Opcode: " ; INT opcode ;
                                   STR " encountered in decompose_instr" ]))

     
let instr_format_to_string (fmt:mips_instr_format_t) =
  let rec faux flds s =
    match flds with
    | [] -> s ^ ")"
    | [ i ] -> s ^ (stri i) ^ ")"
    | h::tl -> faux tl (s ^ (stri h) ^ ",")  in
  let f flds = faux flds "(" in
  match fmt with
  | SyscallType code ->
     "SC(" ^ (string_of_int code) ^ ")"
  | RType (opcode,rs,rt,rd,shamt,funct) ->
     "R" ^ (f [ opcode ; rs ; rt ; rd ; shamt ; funct ])
  | R2Type (opcode,rs,rt,rd,shamt,funct) ->
     "R2" ^  (f [ opcode ; rs ; rt ; rd ; shamt ; funct ])
  | JType (opcode,addr) ->
     "J" ^ (f [ opcode ; addr ])
  | IType (opcode,rs,rt,imm) ->
     "I" ^ (f [ opcode ; rs ; rt ; imm ])
  | FPMCType (opcode,rs,cc,tf,rd,funct) ->
     "FPMC" ^ (f [ opcode ; rs ; cc ; tf ; rd ; funct ])
  | FPRMCType (opcode,fmt,cc,tf,fs,fd,funct) ->
     "FPRMC" ^ (f [ opcode ; fmt ; cc ; tf ; fs ; fd ; funct ])
  | FPRType (opcode,fmt,ft,fs,fd,funct) ->
     "FPR" ^ (f [ opcode ; fmt ; ft ; fs ; fd ; funct ])
  | FPRIType (opcode,sub,rt,fs) ->
     "FPRI" ^ (f [ opcode ; sub ; rt ; fs ])
  | FPCompareType (opcode,fmt,ft,fs,cc,fnct) ->
     "FPCompare" ^ (f [ opcode ; fmt ; ft ; fs ; cc ; fnct ])
  | FPICCType (opcode,sub,cc,nd,tf,offset) ->
     "FPICC" ^ (f [ opcode ; sub ; cc ; nd ; tf ; offset ])
       
let is_conditional_jump_instruction opcode =
  match opcode with
  | BranchLTZero _
    | BranchLTZeroLikely _
    | BranchLEZero _
    | BranchLEZeroLikely _
    | BranchGEZero _
    | BranchGEZeroLikely _
    | BranchGTZero _
    | BranchGTZeroLikely _
    | BranchEqual _
    | BranchEqualLikely _
    | BranchNotEqual _
    | BranchNotEqualLikely _-> true
  | _ -> false

let get_conditional_jump_expr floc opcode:xpr_t =
  let mkxpr op = op#to_expr floc in
  let zero = zero_constant_expr in
  match opcode with
  | BranchLTZero (r,_) -> XOp (XLt, [ mkxpr r ; zero ])
  | BranchLTZeroLikely (r,_) -> XOp (XLt, [ mkxpr r ; zero ])
  | BranchLEZero (r,_) -> XOp (XGt, [ mkxpr r ; zero ])
  | BranchLEZeroLikely (r,_) -> XOp (XGt, [ mkxpr r ; zero ])
  | BranchGEZero (r,_) -> XOp (XGe, [ mkxpr r ; zero ])
  | BranchGEZeroLikely (r,_) -> XOp (XGe, [ mkxpr r ; zero ])
  | BranchGTZero (r,_) -> XOp (XGt, [ mkxpr r ; zero ])
  | BranchGTZeroLikely (r,_) -> XOp (XGt, [ mkxpr r ; zero ])
  | BranchEqual (r1,r2,_) ->  XOp (XEq, [ mkxpr r1 ; mkxpr r2 ])
  | BranchEqualLikely (r1,r2,_) -> XOp (XEq, [ mkxpr r1 ; mkxpr r2 ])
  | BranchNotEqual (r1,r2,_) -> XOp (XNe, [ mkxpr r1 ; mkxpr r2 ])
  | BranchNotEqualLikely (r1,r2,_) -> XOp (XNe, [ mkxpr r1 ; mkxpr r2 ])
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR "Opcode " ; STR (mips_opcode_to_string opcode) ;
                        STR " is not a conditional jump instruction" ]))

let is_fp_conditional_jump_instruction opcode =
  match opcode with
  | BranchFPFalse _
    | BranchFPTrue _
    | BranchFPFalseLikely _
    | BranchFPTrueLikely _ -> true
  | _ -> false

let is_direct_jump_instruction opcode =
  is_conditional_jump_instruction opcode
  || is_fp_conditional_jump_instruction opcode
  || (match opcode with | Branch _ | Jump _ -> true | _ -> false)

let is_jump_instruction opcode =
  is_direct_jump_instruction opcode
  || (match opcode with JumpRegister _ -> true | _ -> false)

let is_indirect_jump_instruction opcode =
  match opcode with JumpRegister _ -> true | _ -> false

let get_indirect_jump_instruction_register opcode  =
  match opcode with
  | JumpRegister op -> op#get_register
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR "Opcode " ; STR (mips_opcode_to_string opcode) ;
                        STR " is not an indirect jump instruction" ]))

let is_halt_instruction opcode =
  match opcode with Halt -> true | _ -> false

let is_return_instruction opcode =
  match opcode with Return -> true |  _ -> false

let get_direct_jump_target_address opcode =
  match opcode with
  | BranchLTZero (_,op)
    | BranchLTZeroLikely (_,op)
    | BranchLEZero (_,op)
    | BranchLEZeroLikely (_,op)
    | BranchGEZero (_,op)
    | BranchGEZeroLikely (_,op)
    | BranchGTZero (_,op)
    | BranchGTZeroLikely (_,op)
    | BranchEqual (_,_,op)
    | BranchEqualLikely (_,_,op)
    | BranchNotEqual (_,_,op)
    | BranchNotEqualLikely  (_,_,op)
    | BranchFPFalse (_,op)
    | BranchFPTrue (_,op)
    | BranchFPFalseLikely (_,op)
    | BranchFPTrueLikely (_,op)
    | Branch op
    | Jump op when op#is_absolute_address -> op#get_absolute_address
  | _ ->
     raise (BCH_failure (LBLOCK [ STR (mips_opcode_to_string opcode) ;
                                  STR " is not a direct jump" ]))

let is_direct_call_instruction opcode =
  match opcode with
  | BranchLTZeroLink _ | BranchGEZeroLink _ | BranchLink _ | JumpLink _ -> true
  | _ -> false

let is_indirect_call_instruction opcode =
  match opcode with JumpLinkRegister _ -> true | _ -> false

let get_direct_call_target_address opcode =
  match opcode with
  | BranchLTZeroLink (_,op)
    | BranchGEZeroLink (_,op)
    | BranchLink op
    | JumpLink op when op#is_absolute_address -> op#get_absolute_address
  | _ ->
     raise (BCH_failure (LBLOCK [ STR  (mips_opcode_to_string opcode) ;
                                  STR " is not a direct call instruction" ]))


let get_string_reference (floc:floc_int) (xpr:xpr_t) =
  try
    match xpr with
    | XConst (IntConst num) ->
      let address = numerical_to_doubleword num in
      begin
	match elf_header#get_string_at_address address with
	| Some str ->
	  begin
	    string_table#add_xref address str floc#fa floc#cia ;
            chlog#add "add string" (LBLOCK [ floc#l#toPretty ; STR "; " ; STR str ]) ;
	    Some str
	  end
	| _ -> None
      end
    | XOp (XPlus, [ XVar v ; XConst (IntConst num) ]) ->
      if floc#env#has_initialized_string_value v num#toInt then
	Some (floc#env#get_initialized_string_value v num#toInt)
      else
	None
    | _ -> None
  with
  | _ -> None
