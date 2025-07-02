(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2024  Aarno Labs LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHJumpTable
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMOpcodeRecords
open BCHARMPseudocode
open BCHARMTypes
open BCHDisassembleThumbInstruction


module H = Hashtbl
module TR = CHTraceResult


let armd = BCHARMDictionary.arm_dictionary


class arm_jumptable_t
        ?(db: data_block_int option=None)
        ~(end_address: doubleword_int)
        ~(start_address: doubleword_int)
        ~(default_target: doubleword_int)
        ~(targets: (doubleword_int * int list) list)
        ~(index_operand: arm_operand_int)
        ():arm_jumptable_int =
object (self)

  method start_address = start_address

  method end_address = end_address

  method target_addrs = List.map fst targets

  method indexed_targets = targets

  method default_target = default_target

  method index_operand = index_operand

  method has_offset_table =
    match db with Some _ -> true | _ -> false

  method to_jumptable =
    TR.tget_ok
      (make_indexed_jumptable
         ~end_address:self#end_address
         ~start_address
         ~indexed_targets:self#indexed_targets
         ~default_target)

  method toCHIF (_faddr: doubleword_int) = []

  method write_xml (node: xml_element_int) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    begin
      append
        (List.map (fun (tgtaddr, indices) ->
             let tNode = xmlElement "tgt" in
             begin
               tNode#setAttribute "a" tgtaddr#to_hex_string;
               tNode#setAttribute
                 "cvs" (String.concat "," (List.map string_of_int indices));
               tNode
             end) self#indexed_targets);
      set "default" self#default_target#to_hex_string;
      set "start" self#start_address#to_hex_string;
      set "end" self#end_address#to_hex_string;
      seti "indexopix" (armd#index_arm_operand self#index_operand)
    end

  method toPretty =
    LBLOCK [
        STR "targets:[";
        pretty_print_list
          self#indexed_targets
          (fun (tgt, ixs) ->
            LBLOCK [
                tgt#toPretty;
                STR ", ";
                pretty_print_list ixs (fun i -> INT i) "[" "," "]";
                STR "; "]) "[[" ";" "]]"]

end


(** By default it is assumed that the jumptable internally consists of
    a list of addresses that make up the targets, and their position in the list
    indicates the index to which they are applicable.

    The jumptable may also consist of a list of offsets. In this case a datablock
    is to be created for those offsets and passed with the db argument.*)
let make_arm_jumptable
      ?(db: data_block_int option=None)
      ~(end_address: doubleword_int)
      ~(start_address: doubleword_int)
      ~(default_target: doubleword_int)
      ~(targets: (doubleword_int * int) list)
      ~(index_operand: arm_operand_int)
      () =
  let tgts = H.create 5 in
  let _ =
    List.iter (fun (tgt, v) ->
        let index = tgt#to_int in
        let entry =
          if H.mem tgts index then
            H.find tgts index
          else
            [] in
        H.replace tgts index (v::entry)) targets in
  let indexedtargets =
    H.fold (fun k v acc ->
        (TR.tget_ok (int_to_doubleword k), (List.sort Stdlib.compare v))::acc)
      tgts [] in
  let indexedtargets =
    List.sort (fun (a1, _) (a2, _) ->
        Stdlib.compare a1#to_int a2#to_int) indexedtargets in
  new arm_jumptable_t
    ~end_address:end_address
    ~db:db
    ~start_address:start_address
    ~default_target:default_target
    ~targets:indexedtargets
    ~index_operand
    ()


let find_instr
      (testf: arm_assembly_instruction_int -> bool)
      (offsets: int list)
      (addr: doubleword_int): arm_assembly_instruction_int option =
  List.fold_left
    (fun acc offset ->
      match acc with
      | Some _ -> acc
      | _ ->
         let caddr = addr#add_int offset in
         (match TR.to_option (get_arm_assembly_instruction caddr) with
          | Some cinstr ->
             if testf cinstr then
               Some cinstr
             else
               None
          | _ -> None)) None offsets


(* Return true if [instr] is a CMP instruction with first operand equal to
   [reg] and second argument an immediate value *)
let cmp_reg_imm_test (reg: arm_reg_t) (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | Compare (_, rn, imm, _) ->
     rn#is_register && rn#get_register = reg && imm#is_immediate
  | _ -> false


(* Return true if [instr] is an ADR instruction with first operand
   equal to [reg] *)
let adr_reg_test (reg: arm_reg_t) (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | Adr (_, rd, _) -> rd#is_register && rd#get_register = reg
  | _ -> false


(* Return true if [instr] is an ADD instruction with first and second
   operand equal to [reg1] and third operand equal to [reg2]*)
let add_reg_test
      (reg1: arm_reg_t) (reg2: arm_reg_t) (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | Add (_, ACCAlways, rd, rn, rm, _) ->
     rd#is_register
     && rn#is_register
     && rm#is_register
     && rd#get_register = reg1
     && rn#get_register = reg1
     && rm#get_register = reg2
  | _ -> false


let addtest (reg: arm_reg_t) (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | Add (_, ACCAlways, rd, rn, _, _) ->
     rd#is_register
     && rn#is_register
     && rd#get_register = reg
     && rn#get_register = reg
  | _ -> false


let ldrtest
      (tmpreg: arm_reg_t)
      (basereg: arm_reg_t)
      (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | LoadRegister (ACCAlways, rt, rn, rm, _, true) ->
     rt#is_register
     && rt#get_register = tmpreg
     && rn#is_register
     && rn#get_register = basereg
     && rm#is_register
  | _ -> false


let ldrs2test
      (tmpreg: arm_reg_t)
      (basereg: arm_reg_t)
      (indexreg: arm_reg_t)
      (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | LoadRegister (ACCAlways, rt, rn, rm, mem, false) ->
     let _ =
       chlog#add "ldrs2-test"
         (LBLOCK [instr#get_address#toPretty;
                  STR ": ";
                  STR (BCHARMOpcodeRecords.arm_opcode_to_string instr#get_opcode);
                  STR " with ";
                  STR (BCHCPURegisters.armreg_to_string tmpreg);
                  STR ", ";
                  STR (BCHCPURegisters.armreg_to_string basereg);
                  STR ", ";
                  STR (BCHCPURegisters.armreg_to_string indexreg)
         ]) in
     rt#is_register
     && rt#get_register = tmpreg
     && rn#is_register
     && rn#get_register = basereg
     && rm#is_register
     && rm#get_register = indexreg
     && (match mem#get_kind with
         | ARMOffsetAddress (_, _, offset, _, _, _, _) ->
            (match offset with
             | ARMShiftedIndexOffset (_, ARMImmSRT (SRType_LSL, 2), _) -> true
             | _ -> false)
         | _ -> false)
  | _ -> false


let ldrbtest
      (basereg: arm_reg_t)
      (indexreg: arm_reg_t)
      (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | LoadRegisterByte (ACCAlways, rt, rn, rm, _, false) ->
     rt#is_register
     && rn#is_register
     && rm#is_register
     && rt#get_register = basereg
     && rn#get_register = basereg
     && rm#get_register = indexreg
  | _ -> false


let ldrhtest
      (basereg: arm_reg_t)
      (indexreg: arm_reg_t)
      (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | LoadRegisterHalfword (ACCAlways, rt, rn, rm, _, false) ->
     rt#is_register
     && rn#is_register
     && rm#is_register
     && rt#get_register = basereg
     && rn#get_register = basereg
     && rm#get_register = indexreg
  | _ -> false



let  lsl1test (reg: arm_reg_t) (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | LogicalShiftLeft (_, ACCAlways, rd, rn, imm, false) ->
     rd#is_register
     && rn#is_register
     && imm#is_immediate
     && rd#get_register = reg
     && rn#get_register = reg
     && imm#to_numerical#equal numerical_one
  | _ -> false


let bhi_test (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | Branch (ACCUnsignedHigher, _, _) -> true
  | _ -> false


let bcs_test (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | Branch (ACCCarrySet, _, _) -> true
  | _ -> false


(* TBB patterns (in Thumb-2)

   size is obtained from the CMP instruction's immediate value
   table start address is address of TBB/TBH + 4

   [2 bytes] CMP          R1, #0x2    : offset -4
   [2 bytes] BHI          0x12144
   [4 bytes] TBB          [PC, R1]    : 3 targets

   [2 bytes] CMP          R1, #0x5    : offset -6
   [4 bytes] BHI.W        0x4acec
   [4 bytes] TBB          [PC, R1]    : 6 targets

   [4 bytes] CMP.W        R9, #0x7    : offset -6
   [2 bytes] BHI          0x1103d6
   [4 bytes] TBB          [PC, R9]    : 8 targets

   [4 bytes] CMP.W        R10, #0x7   : offset -8
   [4 bytes] BHI.W        0xc1ff2
   [4 bytes] TBB          [PC, R10]   : 8 targets

   TBH patterns (in Thumb-2)

   [2 bytes] CMP          R1, #0x4    : offset -4
   [2 bytes] BHI          0x4bed6
   [2 bytes] TBH          [PC, R1]    : 5 targets

   [2 bytes] CMP          R2, #0x2e   : offset -6
   [4 bytes] BHI.W        0x4bea8
   [4 bytes] TBH          [PC, R2]    : 47 targets

   [4 bytes] CMP.W        R11, #0x7   : offset -8
   [4 bytes] BHI.W        0xc1ff8
   [4 bytes] TBH          [PC, R11]   : 8 targets
 *)


(* Return a compare instruction with the size of the table if such exists *)
let is_table_branch
      (tbinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int * arm_assembly_instruction_int) option =
  match tbinstr#get_opcode with
  | TableBranchByte (_, basereg, indexop, _)
    | TableBranchHalfword (_, basereg, indexop, _)
       when basereg#get_register = ARPC ->
     let indexreg = indexop#get_register in
     let testf = cmp_reg_imm_test indexreg in
     let addr = tbinstr#get_address in
     let optcmpinstr = find_instr testf [(-4); (-6); (-8)] addr in
     let optbhiinstr = find_instr bhi_test [(-2); (-4)] addr in
     (match (optcmpinstr, optbhiinstr) with
      | (Some cmpinstr, Some bhiinstr) -> Some (cmpinstr, bhiinstr)
      | _ -> None)
  | _ -> None


let create_arm_table_branch
      (ch: pushback_stream_int)
      (tbinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_table_branch tbinstr with
  | None -> None
  | Some (cmpinstr, bhiinstr) ->
     let opcode = tbinstr#get_opcode in
     match (cmpinstr#get_opcode, bhiinstr#get_opcode) with
     | (Compare (_, _, imm, _), Branch (_, tgtop, _))
          when imm#is_immediate && tgtop#is_absolute_address ->
        let addr = tbinstr#get_address in
        let defaulttgt = tgtop#get_absolute_address in
        let size = imm#to_numerical#toInt in
        let jtaddr = addr#add_int 4 in
        let targets = ref [] in
        let (jtype, end_address, indexop) =
          match opcode with
          | TableBranchByte (_, _, indexop, _) ->
             let size = if size mod 2 = 0 then size + 1 else size in
             let _ =
               for i = 0 to size do
                 let byte = ch#read_byte in
                 if byte > 0 then
                   let tgt = addr#add_int ((2 * byte) + 4) in
                   targets := (tgt, i) :: !targets
               done in
             ("tbb", jtaddr#add_int (size + 1), indexop)
          | TableBranchHalfword (_, _, indexop, _) ->
             let _ =
               for i = 0 to size do
                 let hw = ch#read_ui16 in
                 let tgt = addr#add_int ((2 * hw) + 4) in
                 targets := (tgt, i) :: !targets
               done in
             ("tbh", jtaddr#add_int (2 * (size + 1)), indexop)
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Unexpected opcode in create_arm_table_branch: ";
                       STR (arm_opcode_to_string opcode)])) in
        let jt =
          make_arm_jumptable
            ~end_address
            ~start_address:jtaddr
            ~default_target:defaulttgt
            ~targets:(List.rev !targets)
            ~index_operand:indexop
            () in
        let instrs = [cmpinstr; bhiinstr; tbinstr] in
        begin
          (* system_info#add_jumptable jt;
          !arm_assembly_instructions#set_jumptables [jt]; *)
          (if collect_diagnostics () then
             ch_diagnostics_log#add
               "table-branch jumptable"
               (LBLOCK [
                    STR jtype;
                    STR " with base: ";
                    jtaddr#toPretty;
                    STR "; targets: ";
                    INT (List.length !targets)]));
          Some (instrs, jt)
        end
     | _ -> None


(* LDR patterns (in Thumb-2)

   size is obtained from CMP instruction's immediate value
   table start address is obtained from the ADR instruction

   [2 bytes] CMP indexreg, maxcase
   [4 bytes] BHI.W default_address
   [2 bytes] ADR basereg, start_address
   [4 bytes] LDR.W PC, [basereg, indexreg, LSL #2]

   Example:
   [2 bytes] 0x13c3c2  CMP          R4, #0xf6
   [4 bytes] 0x13c3c4  BHI.W        0x13c93e
   [2 bytes] 0x13c3c8  ADR          R3, 0x13c3d0
   [4 bytes] 0x13c3ca  LDR.W        PC, [R3, R4,LSL #2]
 *)
let is_ldr_jumptable
      (ldrinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int             (* CMP instr *)
       * arm_assembly_instruction_int           (* BHI instr *)
       * arm_assembly_instruction_int) option = (* ADR isntr *)
  match ldrinstr#get_opcode with
  | LoadRegister (_, dst, baseregop, indexregop, _, true)
       when dst#get_register = ARPC && indexregop#is_register ->
     let indexreg = indexregop#get_register in
     let cmptestf = cmp_reg_imm_test indexreg in
     let addr = ldrinstr#get_address in
     let optcmpinstr = find_instr cmptestf [(-8)] addr in
     (match optcmpinstr with
      | Some cmpinstr ->
         let basereg = baseregop#get_register in
         let adrtestf = adr_reg_test basereg in
         let optadrinstr = find_instr adrtestf [(-2)] addr in
         let optbhiinstr = find_instr bhi_test [(-6)] addr in
         (match (optadrinstr, optbhiinstr) with
          | (Some adrinstr, Some bhiinstr) -> Some (cmpinstr, bhiinstr, adrinstr)
          | _ -> None)
      | _ -> None)
  | _ -> None


let create_arm_ldr_jumptable
      (ch: pushback_stream_int)
      (ldrinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_ldr_jumptable ldrinstr with
  | None -> None
  | Some (cmpinstr, bhiinstr, adrinstr) ->
     (match (cmpinstr#get_opcode, bhiinstr#get_opcode, adrinstr#get_opcode) with
      | (Compare (_, indexregop, imm, _), Branch (_, tgtop, _), Adr (_, _, addrop))
           when tgtop#is_absolute_address && addrop#is_absolute_address ->
         let iaddr = ldrinstr#get_address in
         let defaulttgt = tgtop#get_absolute_address in
         let size = imm#to_numerical#toInt in
         let jtaddr = addrop#get_absolute_address in
         let skips = (TR.tget_ok (jtaddr#subtract_to_int iaddr)) - 4 in
         let _ = if skips > 0 then ch#skip_bytes skips in
         let targets = ref [] in
         let _ =
           for i = 0 to size do
             let tgt = ch#read_doubleword in
             targets := ((align_dw tgt 2), i) :: !targets
           done in
         let jt:arm_jumptable_int =
           make_arm_jumptable
             ~end_address:(jtaddr#add_int (4 * (List.length !targets)))
             ~start_address:jtaddr
             ~default_target:defaulttgt
             ~targets:(List.rev !targets)
             ~index_operand:indexregop
             () in
         let instrs = [cmpinstr; bhiinstr; adrinstr; ldrinstr] in
         begin
           (* system_info#add_jumptable jt;
           !arm_assembly_instructions#set_jumptables [jt]; *)
           (if collect_diagnostics () then
              ch_diagnostics_log#add
                "ldr-jumptable"
                (LBLOCK [
                     STR "base: ";
                     jtaddr#toPretty;
                     STR "; targets: ";
                     INT (List.length !targets)]));
           Some (instrs, jt)
         end
      | _ -> None)


(* LDRLS pattern in ARM

    CMP    indexreg, maxcase
    LDRLS  PC, [PC, indexreg, LSL #2]
    B      default case

    Example:
    CMP          R3, #0x5
    LDRLS        PC, [PC, R3,LSL #2]
    B            0x190e0
 *)
let is_ldrls_jumptable
      (ldrinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int              (* CMP instr *)
       * arm_assembly_instruction_int) option =  (* B instr *)
  match ldrinstr#get_opcode with
  | LoadRegister (ACCNotUnsignedHigher, dst, _baseregop, indexregop, _, false)
       when dst#get_register = ARPC && indexregop#is_register ->
     let indexreg = indexregop#get_register in
     let cmptestf = cmp_reg_imm_test indexreg in
     let addr = ldrinstr#get_address in
     let optcmpinstr = find_instr cmptestf [(-4); (-16)] addr in
     (match optcmpinstr with
      | Some cmpinstr ->
         let branchtestf instr =
           match instr#get_opcode with
           | Branch (ACCAlways, _, false) -> true | _ -> false in
         let optbranchinstr = find_instr branchtestf [(4)] addr in
         (match optbranchinstr with
          | Some branchinstr ->
             Some (cmpinstr, branchinstr)
          | _ -> None)
      | _ -> None)
  | _ -> None


let create_arm_ldrls_jumptable
      (ch: pushback_stream_int)
      (ldrinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_ldrls_jumptable ldrinstr with
  | None -> None
  | Some (cmpinstr, branchinstr) ->
     (match (cmpinstr#get_opcode, branchinstr#get_opcode) with
      | (Compare (_, indexregop, imm, _), Branch (_, tgtop, _))
           when tgtop#is_absolute_address ->
         let iaddr = ldrinstr#get_address in
         let defaulttgt = tgtop#get_absolute_address in
         let size = imm#to_numerical#toInt in
         let jtaddr = iaddr#add_int 8 in
         let targets = ref [] in
         let _ =
           for i = 0 to size do
             let tgt = ch#read_doubleword in
             targets := (tgt, i) :: !targets
           done in
         let jt:arm_jumptable_int =
           make_arm_jumptable
             ~end_address:(jtaddr#add_int ((List.length !targets) * 4))
             ~start_address:jtaddr
             ~default_target:defaulttgt
             ~targets:(List.rev !targets)
             ~index_operand:indexregop
             () in
         let instrs = [cmpinstr; ldrinstr; branchinstr] in
         begin
           (if collect_diagnostics () then
              ch_diagnostics_log#add
                "ldrls-jumptable"
                (LBLOCK [
                     STR "base: ";
                     jtaddr#toPretty;
                     STR ": targets: ";
                     INT (List.length !targets)]));
           Some (instrs, jt)
         end
      | _ -> None)


(* ADDLS pattern (in ARM)

   [4 bytes] CMP    indexreg, maxcase
   [4 bytes] ADDLS  PC, PC, indexreg, LSL#2
   [4 bytes] B      default case
   [4 bytes] B      case 0
   [...]     B
   [4 bytes] B      case maxcase
 *)
let is_addls_pc_jumptable
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int               (* CMP instr *)
       * arm_assembly_instruction_int) option =   (* ADDLS instr *)
  match addpcinstr#get_opcode with
  | Add (_, ACCNotUnsignedHigher, rd, rn, baseregop, false)
       when rd#is_pc_register
            && rn#is_pc_register
            && baseregop#is_shifted_register ->
     let addr = addpcinstr#get_address in
     let cmptestf (instr: arm_assembly_instruction_int) =
       match instr#get_opcode with
       | Compare (_, rn, imm, _) -> rn#is_register && imm#is_immediate
       | _ -> false in
     let optcmpinstr = find_instr cmptestf [(-4)] addr in
     (match optcmpinstr with
      | Some cmpinstr ->
         (match cmpinstr#get_opcode with
          | Compare (_, indexregop, _, _) ->
             let indexreg = indexregop#get_register in
             (match baseregop#get_kind with
              | ARMShiftedReg (basereg, ARMImmSRT (SRType_LSL, 2)) ->
                 if basereg = indexreg then
                   Some (cmpinstr, addpcinstr)
                 else
                   None
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None


let create_addls_pc_jumptable
      (_ch: pushback_stream_int)
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_addls_pc_jumptable addpcinstr with
  | None -> None
  | Some (cmpinstr, addlspcinstr) ->
     match cmpinstr#get_opcode with
     | Compare (_, index_operand, imm, _) ->
        let maxcase = imm#to_numerical#toInt in
        let iaddr = addlspcinstr#get_address in
        let default_target = iaddr#add_int 4 in
        let start_address = default_target in
        let end_address = default_target in
        let targets =
          List.init (maxcase + 1) (fun i -> (iaddr#add_int (8 + (4 * i)), i)) in
        let jt =
          make_arm_jumptable
            ~end_address
            ~start_address
            ~default_target
            ~targets
            ~index_operand () in
        Some ([cmpinstr; addlspcinstr], jt)
     | _ -> None


(* ADD-PC-LDRB patterns (in Thumb-2)

   size is obtained from CMP instruction's immediate value
   table start address is obtained from the ADR instruction

   [2 bytes] CMP  indexreg, maxcase
   [2 bytes] BCS  default address
   [2 bytes] ADR  basereg, start_address
   [2 bytes] LDRB basereg, [basereg, indexreg]
   [2 bytes] LSLS basereg, basereg, 1
   [2 bytes] ADD  PC, PC, basereg

   Example:
   [2 bytes] 0x40179be8  1b 28  CMP     R0, #0x1b
   [2 bytes] 0x40179bea  4d d2  BCS     0x40179c88 (default case)
   [2 bytes] 0x40179bec  01 a3  ADR     R3, 0x40179bf4
   [2 bytes] 0x40179bee  1b 5c  LDRB    R3, [R3, R0]
   [2 bytes] 0x40179bf0  5b 00  LSLS    R3, R3, #1
   [2 bytes] 0x40179bf2  9f 44  ADD     PC, PC, R3
 *)
let is_add_pc_b_jumptable
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int              (* CMP instr *)
       * arm_assembly_instruction_int            (* BCS instr *)
       * arm_assembly_instruction_int            (* ADR instr *)
       * arm_assembly_instruction_int            (* LDRB instr *)
       * arm_assembly_instruction_int) option =  (* LSLS instr *)
  match addpcinstr#get_opcode with
  | Add (_, ACCAlways, rd, rn, baseregop, false)
       when rd#is_pc_register && rn#is_pc_register && baseregop#is_register ->
     let addr = addpcinstr#get_address in
     let basereg = baseregop#get_register in
     let cmptestf (instr: arm_assembly_instruction_int) =
       match instr#get_opcode with
       | Compare (_, rn, imm, _) -> rn#is_register && imm#is_immediate
       | _ -> false in
     let optcmpinstr = find_instr cmptestf [(-10)] addr in
     (match optcmpinstr with
      | Some cmpinstr ->
         (match cmpinstr#get_opcode with
          | Compare (_, indexregop, _, _) ->
             let indexreg = indexregop#get_register in
             let adrtestf = adr_reg_test basereg in
             let ldrbtestf = ldrbtest basereg indexreg in
             let lsl1testf = lsl1test basereg in
             let optadrinstr = find_instr adrtestf [(-6)] addr in
             let optbcsinstr = find_instr bcs_test [(-8)] addr in
             let optldrbinstr = find_instr ldrbtestf [(-4)] addr in
             let optlslinstr = find_instr lsl1testf [(-2)] addr in
             (match (optbcsinstr, optadrinstr, optldrbinstr, optlslinstr) with
              | (Some bcsinstr, Some adrinstr, Some ldrbinstr, Some lslinstr) ->
                 Some (cmpinstr, bcsinstr, adrinstr, ldrbinstr, lslinstr)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None


let create_arm_add_pc_b_jumptable
      (ch: pushback_stream_int)
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_add_pc_b_jumptable addpcinstr with
  | None -> None
  | Some (cmpinstr, bcsinstr, adrinstr, ldrbinstr, lslinstr) ->
     (match (cmpinstr#get_opcode, bcsinstr#get_opcode, adrinstr#get_opcode) with
      | (Compare (_, indexregop, imm, _),
         Branch (_, tgtop, _),
         Adr (_, _baseregop, addrop))
           when tgtop#is_absolute_address && addrop#is_absolute_address ->
         let iaddr = addpcinstr#get_address in
         let defaulttgt = tgtop#get_absolute_address in
         let size = imm#to_numerical#toInt in
         let jtaddr = addrop#get_absolute_address in
         let skips = TR.tget_ok (jtaddr#subtract_to_int iaddr) in
         let skips = skips - 2 in
         let _ =
           if skips > 0 then
             for _i = 1 to skips do ignore (ch#read_byte) done in
         let targets = ref [] in
         let _ =
           for i = 0 to (size-1) do
             let offset = ch#read_byte in
             targets := (iaddr#add_int (4 + (2 * offset)), i) :: !targets
           done in
         let _ = if size mod 2 = 1 then ignore ch#read_byte in
         let endaddr =
           if size mod 2 = 1 then
             jtaddr#add_int (size + 1)
           else
             jtaddr#add_int size in
         let jt:arm_jumptable_int =
           make_arm_jumptable
             ~end_address:endaddr
             ~start_address:jtaddr
             ~default_target:defaulttgt
             ~targets:(List.rev !targets)
             ~index_operand:indexregop
             () in
         let instrs =
           [cmpinstr; bcsinstr; adrinstr; ldrbinstr; lslinstr; addpcinstr] in
         begin
           Some (instrs, jt)
         end
      | _ -> None)


(* ADD-PC-LDRH patterns (in Thumb-2)

   size is obtained from CMP instruction's immediate value
   table start address is obtained from the ADR instruction

   [2 bytes] CMP  indexreg, maxcase
   [2 bytes] BCS  default address
   [2 bytes] ADR  basereg, start_address
   [2 bytes] ADDS basereg, basereg, indexreg
   [2 bytes] LDRH basereg, [basereg, indexreg]
   [2 bytes] LSLS basereg, basereg, 1
   [2 bytes] ADD  PC, PC, basereg
 *)
let is_add_pc_h_jumptable
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int               (* CMP instr *)
       * arm_assembly_instruction_int             (* BCS instr *)
       * arm_assembly_instruction_int             (* ADR instr *)
       * arm_assembly_instruction_int             (* ADDS instr *)
       * arm_assembly_instruction_int             (* LDRH instr *)
       * arm_assembly_instruction_int) option =   (* LSLS instr *)
  match addpcinstr#get_opcode with
  | Add (_, ACCAlways, rd, rn, baseregop, false)
       when rd#is_pc_register && rn#is_pc_register && baseregop#is_register ->
     let addr = addpcinstr#get_address in
     let basereg = baseregop#get_register in
     let cmptestf (instr: arm_assembly_instruction_int) =
       match instr#get_opcode with
       | Compare (_, rn, imm, _) -> rn#is_register && imm#is_immediate
       | _ -> false in
     let optcmpinstr = find_instr cmptestf [(-12)] addr in
     (match optcmpinstr with
      | Some cmpinstr ->
         (match cmpinstr#get_opcode with
          | Compare (_, indexregop, _, _) ->
             let indexreg = indexregop#get_register in
             let adrtestf = adr_reg_test basereg in
             let addtestf = add_reg_test basereg indexreg in
             let ldrhtest = ldrhtest basereg indexreg in
             let lsl1testf = lsl1test basereg in
             let optadrinstr = find_instr adrtestf [(-8)] addr in
             let optbcsinstr = find_instr bcs_test [(-10)] addr in
             let optaddinstr = find_instr addtestf [(-6)] addr in
             let optldrhinstr = find_instr ldrhtest [(-4)] addr in
             let optlslinstr = find_instr lsl1testf [(-2)] addr in
             (match
                (optbcsinstr,
                 optadrinstr,
                 optaddinstr,
                 optldrhinstr,
                 optlslinstr) with
              | (Some bcsinstr,
                 Some adrinstr,
                 Some addinstr,
                 Some ldrhinstr,
                 Some lslinstr) ->
                 Some
                   (cmpinstr, bcsinstr, adrinstr, addinstr, ldrhinstr, lslinstr)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None


let create_arm_add_pc_h_jumptable
      (ch: pushback_stream_int)
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_add_pc_h_jumptable addpcinstr with
  | None -> None
  | Some (cmpinstr, bcsinstr, adrinstr, _, ldrhinstr, lslinstr) ->
     (match (cmpinstr#get_opcode, bcsinstr#get_opcode, adrinstr#get_opcode) with
      | (Compare (_, indexregop, imm, _),
         Branch (_, tgtop, _),
         Adr (_, _baseregop, addrop))
           when tgtop#is_absolute_address && addrop#is_absolute_address ->
         let iaddr = addpcinstr#get_address in
         let branchtgt = tgtop#get_absolute_address in
         let size = imm#to_numerical#toInt in
         let jtaddr = addrop#get_absolute_address in
         let bibytes = ch#read_ui16 in
         let branchinstr =
           disassemble_thumb_instruction ch branchtgt bibytes in
         (match branchinstr with
          | Branch (ACCAlways, defop, _) ->
             let defaulttgt = defop#get_absolute_address in
             let skips = TR.tget_ok (jtaddr#subtract_to_int branchtgt) in
             let skips = skips - 2 in
             let _ =
               if skips > 0 then
                 let _ =
                   chlog#add
                     "add-pc-h jumptable"
                     (LBLOCK [
                          iaddr#toPretty;
                          STR "  ";
                          STR "Skip ";
                          INT skips;
                          STR " bytes"]) in
                 for _i = 1 to skips do
                   let b = ch#read_byte in
                   chlog#add
                     "add-pc-h jumptable: skip"
                     (LBLOCK [iaddr#toPretty; STR "  skip "; INT b])
                 done in
             let targets = ref [] in
             let _ =
               for i = 0 to (size - 1) do
                 let offset = ch#read_ui16 in
                 targets := (iaddr#add_int (4 + (2 * offset)), i) :: !targets
               done in
             let endaddr = jtaddr#add_int (2 * size) in
             let jt:arm_jumptable_int =
               make_arm_jumptable
                 ~end_address:endaddr
                 ~start_address:jtaddr
                 ~default_target:defaulttgt
                 ~targets:(List.rev !targets)
                 ~index_operand:indexregop
                 () in
             let instrs =
               [cmpinstr; bcsinstr; adrinstr; ldrhinstr; lslinstr; addpcinstr] in
             Some (instrs, jt)
          | _ -> None)
      | _ -> None)


let create_arm_add_pc_jumptable
      (ch: pushback_stream_int)
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_add_pc_b_jumptable addpcinstr with
  | Some _ ->
     create_arm_add_pc_b_jumptable ch addpcinstr
  | _ ->
     create_arm_add_pc_h_jumptable ch addpcinstr


(* ADD-PC-LDR patterns (in ARM)

   size is obtained from CMP instruction's immediate value
   table start address is obtained from the ADR instruction

   [4 bytes] CMP indexreg, maxcase
   [4 bytes] BHI default address
   [4 bytes] ADR basereg, start_address
   [4 bytes] LDR scindexreg, [basereg, indexreg, LSL#2]
   [4 bytes] ADD PC, basereg, scindexreg

   Notes: These instructions always appear in the same order, but they may
   be arbitrarily interleaved with other instructions, hence the large number
   of offsets in finding the various instructions below.

   Notes: encountered in a binary compiled with clang 18.1.3 on an arm64 host,
   cross-compiled to arm32.
 *)
let is_arm_add_pc_adr_jumptable
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int               (* CMP instr *)
       * arm_assembly_instruction_int             (* BHI instr *)
       * arm_assembly_instruction_int             (* ADR instr *)
       * arm_assembly_instruction_int) option =   (* LDR instr *)
  match addpcinstr#get_opcode with
  | Add (_, ACCAlways, rd, baseregop, scindexregop, false)
       when rd#is_pc_register
            && baseregop#is_register
            && scindexregop#is_register ->
     let addr = addpcinstr#get_address in
     let basereg = baseregop#get_register in
     let scindexreg = scindexregop#get_register in  (* scaled index register *)
     let cmptestf (instr: arm_assembly_instruction_int) =
       match instr#get_opcode with
       | Compare (_, rn, imm, _) -> rn#is_register && imm#is_immediate
       | _ -> false in
     let cmpinstr_o =
       find_instr cmptestf [(-16); (-20); (-24); (-28); (-32); (-36)] addr in
     (match cmpinstr_o with
      | Some cmpinstr ->
         (match cmpinstr#get_opcode with
          | Compare (_, indexregop, _imm, _)  ->
             let indexreg = indexregop#get_register in
             let adrtestf = adr_reg_test basereg in
             let ldrs2testf = ldrs2test scindexreg basereg indexreg in
             let adrinstr_o = find_instr adrtestf [(-8); (-12)] addr in
             let bhiinstr_o = find_instr bhi_test [(-12); (-16)] addr in
             let ldrs2instr_o = find_instr ldrs2testf [(-4); (-8)] addr in
             let _ =
               if Option.is_none adrinstr_o then
                 chlog#add "adr-jump table failure"
                   (LBLOCK [addpcinstr#get_address#toPretty; STR ": adrinstr"]) in
             let _ =
               if Option.is_none bhiinstr_o then
                 chlog#add "adr-jump table failure"
                   (LBLOCK [addpcinstr#get_address#toPretty; STR ": bhiinstr"]) in
             let _ =
               if Option.is_none ldrs2instr_o then
                 chlog#add "adr-jump table failure"
                   (LBLOCK [addpcinstr#get_address#toPretty; STR ": ldrs2instr"]) in
             (match (bhiinstr_o, adrinstr_o, ldrs2instr_o) with
              | (Some bhiinstr, Some adrinstr, Some ldrs2instr) ->
                 Some (cmpinstr, bhiinstr, adrinstr, ldrs2instr)
              | _ -> None)
          | _ ->
             let _ =
               chlog#add "arm-jumptable cmpinstr failure"
                 (LBLOCK [addpcinstr#get_address#toPretty]) in
             None)
      | _ ->
         let _ =
           chlog#add "arm-jumptable cmpinstr failure (not found)"
             (LBLOCK [addpcinstr#get_address#toPretty]) in
         None)
  | _ -> None


let create_arm_add_pc_adr_jumptable
      (ch: pushback_stream_int)
      (addpcinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_arm_add_pc_adr_jumptable addpcinstr with
  | None ->
     begin
       chlog#add "arm-jumptable: add-pc-addr (None)"
         (LBLOCK [addpcinstr#get_address#toPretty]);
       None
     end
  | Some (cmpinstr, bhiinstr, adrinstr, ldrinstr) ->
     match (cmpinstr#get_opcode,
            bhiinstr#get_opcode,
            adrinstr#get_opcode,
            ldrinstr#get_opcode) with
     | (Compare (_, _, imm, _),
        Branch (_, tgtop, _),
        Adr (_, _, adrop),
        LoadRegister (_, dstregop, _, _, _, _))
          when tgtop#is_absolute_address && adrop#is_absolute_address ->
        let iaddr = addpcinstr#get_address in
        let defaulttgt = tgtop#get_absolute_address in
        let size = imm#to_numerical#toInt in
        let jtaddr = adrop#get_absolute_address in
        let targets = ref [] in
        let _ =
          for i = 0 to size do
            let offset = ch#read_num_signed_doubleword in
            targets := (iaddr#add_int (4 + offset#toInt), i) :: !targets
          done in
        let endaddr = jtaddr#add_int (4 + (4 * size)) in
        let jt:arm_jumptable_int =
          make_arm_jumptable
            ~end_address:endaddr
            ~start_address:jtaddr
            ~default_target:defaulttgt
            ~targets:(List.rev !targets)
            ~index_operand:dstregop
            () in
        let instrs =
          [cmpinstr; bhiinstr; adrinstr; ldrinstr; addpcinstr] in
        begin
          chlog#add "arm-jumptable: add_pc_addr"
            (LBLOCK [addpcinstr#get_address#toPretty;
                     STR ": of size: ";
                     INT size]);
          Some (instrs, jt)
        end
     | _ ->
        begin
          chlog#add "arm-jumptable: add_pc_addr"
            (LBLOCK [addpcinstr#get_address#toPretty;
                     STR ": unsuccesful"]);
          None
        end

(* format of BX-based jumptable (in Thumb-22):

   Type 1
   [2 bytes] CMP indexreg, maxcase
   [2 bytes] BHI default_address
   [2 bytes] ADR basereg, start address
   [4 bytes] LDR.W indexreg, [basereg, indexreg, LSL#2]
   [2 bytes] ADD basereg, basereg, indexreg
   [2 bytes] BX basereg

   Type 2
   [4 bytes] CMP.W indexreg, maxcase
   [4 bytes] BHI.W default_address
   [2 bytes] ADR basereg, start_address
   [4 bytes] LDR.W tmpreg, [basereg, indexreg, LSL#2]
   [2 bytes] ADDS basereg, basereg, tmpreg
   [2 bytes] BX basereg

   Type 3
   [2 bytes] CMP indexreg, maxcase
   [4 bytes] BHI.W default_address
   [2 bytes] ADR basereg, start_address
   [4 bytes] LDR.W indexreg, [basereg, indexreg, LSL#2]
   [2 bytes] ADD basereg, indexreg
   [2 bytes] BX basereg
 *)
let is_bx_jumptable
      (bxinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int              (* CMP instr *)
       * arm_assembly_instruction_int            (* BHI instr *)
       * arm_assembly_instruction_int            (* ADR instr *)
       * arm_assembly_instruction_int            (* LDR instr *)
       * arm_assembly_instruction_int) option =  (* ADD instr *)
  let opcode = bxinstr#get_opcode in
  match opcode with
  | BranchExchange (ACCAlways, baseregop) when baseregop#is_register ->
     let addr = bxinstr#get_address in
     let basereg = baseregop#get_register in
     let addtestf = addtest basereg in
     let optaddinstr = find_instr addtestf [(-2)] addr in
     (match optaddinstr with
      | Some addinstr ->
         (match addinstr#get_opcode with
          | Add (_, _, _rd, _rn, rm, _) ->
             let tmpreg = rm#get_register in
             let ldrtestf = ldrtest tmpreg basereg in
             let optldrinstr = find_instr ldrtestf [(-6)] addr in
             (match optldrinstr with
              | Some ldrinstr ->
                 (match ldrinstr#get_opcode with
                  | LoadRegister (_, _, _, rm, _, _) ->
                     let indexreg = rm#get_register in
                     let adrtestf = adr_reg_test basereg in
                     let optadrinstr = find_instr adrtestf [(-8)] addr in
                     (match optadrinstr with
                      | Some adrinstr ->
                         let cmptestf = cmp_reg_imm_test indexreg in
                         let optcmpinstr =
                           find_instr cmptestf [(-12); (-14); (-16)] addr in
                         let optbhiinstr =
                           find_instr bhi_test [(-10); (-12)] addr in
                         (match (optcmpinstr, optbhiinstr) with
                          | (Some cmpinstr, Some bhiinstr) ->
                             Some (cmpinstr, bhiinstr, adrinstr, ldrinstr, addinstr)
                          | _ -> None)
                      | _ -> None)
                  | _ -> None)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None


let bx_instrs_consistent
      (cmpinstr: arm_assembly_instruction_int)
      (adrinstr: arm_assembly_instruction_int)
      (ldrinstr: arm_assembly_instruction_int)
      (addinstr: arm_assembly_instruction_int) =
  match (
    cmpinstr#get_opcode,
    adrinstr#get_opcode,
    ldrinstr#get_opcode,
    addinstr#get_opcode) with
  | (Compare (_, cmp_r1, _, _),
     Adr (_, adr_r1, _),
     LoadRegister (_, ldr_r1, ldr_r2, ldr_r3, _, _),
     Add (_, _, add_r1, add_r2, add_r3, _)) ->
     (List.fold_left (fun acc r ->
          acc && r#is_register)
        true [cmp_r1; adr_r1; ldr_r1; ldr_r2; ldr_r3; add_r1; add_r2; add_r3])
     && (let indexreg = cmp_r1#get_register in
         let basereg = adr_r1#get_register in
         (ldr_r1#get_register = indexreg           (* Type 1, 3 *)
          && ldr_r2#get_register = basereg
          && ldr_r3#get_register = indexreg
          && add_r1#get_register = basereg
          && add_r2#get_register = basereg
          && add_r3#get_register = indexreg)
         ||
           (let tmpreg = ldr_r1#get_register in
            (ldr_r2#get_register = basereg         (* Type 2 *)
             && ldr_r3#get_register = indexreg
             && add_r1#get_register = basereg
             && add_r2#get_register = basereg
             && add_r3#get_register = tmpreg)))
  | _ -> false


let create_arm_bx_jumptable
      (ch: pushback_stream_int)
      (bxinstr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match is_bx_jumptable bxinstr with
  | None -> None
  | Some (cmpinstr, bhiinstr, adrinstr, ldrinstr, addinstr) ->
     let addr = bxinstr#get_address in
     let _ =
       assert (
           let cond = bx_instrs_consistent cmpinstr adrinstr ldrinstr addinstr in
           begin
             (if not cond then
                ch_error_log#add
                  "arm-bx jumptable condition not recognized"
                  (LBLOCK [
                       STR "create_arm_bx_jumptable: check assertion at address: ";
                       addr#toPretty;
                       NL]));
             cond
           end) in
     let (defaulttgt, size, indexregop) =
       match (cmpinstr#get_opcode, bhiinstr#get_opcode) with
       | (Compare (_, indexregop, cmp_imm, _), Branch (_, tgtop, _))
            when tgtop#is_absolute_address && cmp_imm#is_immediate ->
          (tgtop#get_absolute_address, cmp_imm#to_numerical#toInt, indexregop)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "Internal error in create_bx_jumptable:size"])) in
     let jtaddr =
       match adrinstr#get_opcode with
       | Adr (_, _, adr_imm) -> adr_imm#get_absolute_address
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "Internal error in create_bx_jumptable:jtaddr"])) in
     let skips = (TR.tget_ok (jtaddr#subtract_to_int addr)) - 2 in
     let _ = if skips > 0 then ch#skip_bytes skips in
     let targets = ref [] in
     let _ =
       for i = 0 to size do
         let tgtoffset = ch#read_imm_signed_doubleword in
         match tgtoffset#to_int with
         | Some intoffset ->
            (* compensate for BX bit in address *)
            let tgt = jtaddr#add_int (intoffset - 1) in
            targets := (tgt, i) :: !targets
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "create_bx_jumptable: error in offset: ";
                      tgtoffset#toPretty;
                      STR " at address ";
                      addr#toPretty]))
       done in
     let jt:arm_jumptable_int =
       make_arm_jumptable
         ~end_address:(jtaddr#add_int (4 * (List.length !targets)))
         ~start_address:jtaddr
         ~default_target:defaulttgt
         ~targets:(List.rev !targets)
         ~index_operand:indexregop
         () in
     let instrs = [
         cmpinstr; bhiinstr; adrinstr; ldrinstr; addinstr; bxinstr] in
     begin
       (* system_info#add_jumptable jt;
       !arm_assembly_instructions#set_jumptables [jt]; *)
       (if collect_diagnostics () then
          ch_diagnostics_log#add
            "bx-jumptable"
            (LBLOCK [
                 STR "base: ";
                 jtaddr#toPretty;
                 STR "; targets";
                 INT (List.length !targets)]));
       Some (instrs, jt)
     end
