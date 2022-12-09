(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022      Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHJumpTable
open BCHLibTypes
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMOpcodeRecords
open BCHARMPseudocode
open BCHARMTypes


module H = Hashtbl
module TR = CHTraceResult


class arm_jumptable_t
        ?(end_address: doubleword_int option=None)
        ~(start_address: doubleword_int)
        ~(default_target: doubleword_int)
        ~(targets: (doubleword_int * int list) list):arm_jumptable_int =
object (self)

  method start_address = start_address

  method end_address = end_address

  method target_addrs = List.map fst targets

  method indexed_targets = targets

  method default_target = default_target

  method to_jumptable =
    TR.tget_ok
      (make_jumptable
         ~end_address:self#end_address
         ~start_address
         ~targets:(self#default_target :: self#target_addrs))

  method toCHIF (faddr: doubleword_int) = []

  method write_xml (node: xml_element_int) = ()

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


let make_arm_jumptable
      ?(end_address: doubleword_int option=None)
      ~(start_address: doubleword_int)
      ~(default_target: doubleword_int)
      ~(targets: (doubleword_int * int) list) =
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
    ~start_address:start_address
    ~default_target:default_target
    ~targets:indexedtargets


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


let bhi_test (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | Branch (ACCUnsignedHigher, _, _) -> true
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
        let (jtype, end_address) =
          match opcode with
          | TableBranchByte _ ->
             let size = if size mod 2 = 0 then size + 1 else size in
             let _ =
               for i = 0 to size do
                 let byte = ch#read_byte in
                 if byte > 0 then
                   let tgt = addr#add_int ((2 * byte) + 4) in
                   targets := (tgt, i) :: !targets
               done in
             ("tbb", jtaddr#add_int (size + 1))
          | TableBranchHalfword _ ->
             let _ =
               for i = 0 to size do
                 let hw = ch#read_ui16 in
                 let tgt = addr#add_int ((2 * hw) + 4) in
                 targets := (tgt, i) :: !targets
               done in
             ("tbh", jtaddr#add_int (2 * (size + 1)))
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Unexpected opcode in create_arm_table_branch: ";
                       STR (arm_opcode_to_string opcode)])) in           
        let jt =
          make_arm_jumptable
            ~end_address:(Some end_address)
            ~start_address:jtaddr
            ~default_target:defaulttgt
            ~targets:(List.rev !targets) in
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
      | (Compare (_, _, imm, _), Branch (_, tgtop, _), Adr (_, _, addrop))
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
             ~end_address:(Some (jtaddr#add_int (4 * (List.length !targets))))
             ~start_address:jtaddr
             ~default_target:defaulttgt
             ~targets:(List.rev !targets) in
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


(* format of BX-based jumptable (in Thumb2):
   
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
          | Add (_, _, rd, rn, rm, _) ->
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
                pr_debug [
                    STR "create_arm_bx_jumptable: check assertion at address: ";
                    addr#toPretty;
                    NL]);
             cond
           end) in
     let (defaulttgt, size) =
       match (cmpinstr#get_opcode, bhiinstr#get_opcode) with
       | (Compare (_, _, cmp_imm, _), Branch (_, tgtop, _))
            when tgtop#is_absolute_address && cmp_imm#is_immediate ->
          (tgtop#get_absolute_address, cmp_imm#to_numerical#toInt)
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
         ~end_address:(Some (jtaddr#add_int (4 * (List.length !targets))))
         ~start_address:jtaddr
         ~default_target:defaulttgt
         ~targets:(List.rev !targets) in
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
