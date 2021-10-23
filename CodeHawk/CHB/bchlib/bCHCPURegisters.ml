(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2021      Aarno Labs LLC

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
open BCHLibTypes
open BCHUtilities
open BCHXmlUtil

module H = Hashtbl


let starts_with (s:string) (p:string) =
  let slen = String.length s in
  let plen = String.length p in
  if slen < plen then
    false
  else
    (String.sub s 0 plen) = p

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ;
             INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

let full_reg_of_reg = function
  | Al | Ah | Ax | Eax -> Eax
  | Cl | Ch | Cx | Ecx -> Ecx
  | Dl | Dh | Dx | Edx -> Edx
  | Bl | Bh | Bx | Ebx -> Ebx
  | Sp | Esp -> Esp
  | Bp | Ebp -> Ebp
  | Si | Esi -> Esi
  | Di | Edi -> Edi 

let full_registers = [ Esp ; Ebp ; Eax ; Ebx ; Ecx ; Edx ; Esi ; Edi ]

let cpuregs_to_string_table = H.create 23
let cpuregs_from_string_table = H.create 23

let segregs_to_string_table = H.create 7
let segregs_from_string_table = H.create 7

let mipsregs_to_string_table = H.create 32
let mipsregs_from_string_table = H.create 32

let mips_special_regs_to_string_table = H.create 3
let mips_special_regs_from_string_table = H.create 3

let armregs_to_string_table = H.create 17
let armregs_from_string_table = H.create 17

let arm_special_regs_to_string_table = H.create 3
let arm_special_regs_from_string_table = H.create 3


let _ = List.iter (fun (r,s) -> 
  add_to_sumtype_tables cpuregs_to_string_table cpuregs_from_string_table r s)
  [ (Eax,"eax") ; (Ebx,"ebx") ; (Ecx,"ecx") ; (Edx,"edx") ;
    (Ebp,"ebp") ; (Esp,"esp") ; (Esi,"esi") ; (Edi,"edi") ;
    (Ax,"ax")   ; (Bx,"bx")   ; (Cx,"cx")   ; (Dx,"dx") ;
    (Sp,"sp")   ; (Bp,"bp")   ; (Si,"si")   ; (Di,"di") ;
    (Al,"al")   ; (Bl,"bl")   ; (Cl,"cl")   ; (Dl,"dl") ;
    (Ah,"ah")   ; (Bh,"bh")   ; (Ch,"ch")   ; (Dh,"dh") ]

let cpureg_to_string (r:cpureg_t) = 
  get_string_from_table "cpuregs_to_string_table" cpuregs_to_string_table r

let cpureg_from_string (name:string) = 
  get_sumtype_from_table "cpuregs_from_string_table" cpuregs_from_string_table name


let _ = List.iter (fun (r,s) -> 
  add_to_sumtype_tables segregs_to_string_table segregs_from_string_table r s)
  [ (StackSegment, "%ss") ;
    (CodeSegment , "%cs") ;
    (DataSegment , "%ds") ;
    (ExtraSegment, "%es") ;
    (FSegment    , "%fs") ;
    (GSegment    , "%gs") ]

let segment_to_string (r:segment_t) =
  get_string_from_table "segregs_to_string_table" segregs_to_string_table r

let segment_from_string (name:string) =
  get_sumtype_from_table "segregs_from_string_table" segregs_from_string_table name


let _ =
  List.iter (fun (r,s) ->
      add_to_sumtype_tables mipsregs_to_string_table mipsregs_from_string_table r s)
            [ (MRzero,"$zero"); (MRat,"$at"); (MRv0,"$v0"); (MRv1,"$v1");
              (MRa0,"$a0"); (MRa1,"$a1"); (MRa2,"$a2"); (MRa3,"$a3");
              (MRt0,"$t0"); (MRt1,"$t1"); (MRt2,"$t2"); (MRt3,"$t3");
              (MRt4,"$t4"); (MRt5,"$t5"); (MRt6,"$t6"); (MRt7,"$t7");
              (MRs0,"$s0"); (MRs1,"$s1"); (MRs2,"$s2"); (MRs3,"$s3");
              (MRs4,"$s4"); (MRs5,"$s5"); (MRs6,"$s6"); (MRs7,"$s7");
              (MRt8,"$t8"); (MRt9,"$t9"); (MRk0,"$k0"); (MRk1,"$k1");
              (MRgp,"$gp"); (MRsp,"$sp"); (MRfp,"$fp"); (MRra,"$ra") ]

let mips_regular_registers = get_sumtype_table_keys mipsregs_to_string_table

let mipsreg_to_string (r:mips_reg_t) =
  get_string_from_table "mipsregs_to_string_table" mipsregs_to_string_table r

let mipsreg_from_string (name:string) =
  get_sumtype_from_table "mipsregs_from_string_table" mipsregs_from_string_table name

let get_mipsreg_argument (index:int) =
  match index with
  | 0 -> MRa0
  | 1 -> MRa1
  | 2 -> MRa2
  | 3 -> MRa3
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Argument index out of range: "; INT index]))

let mips_temporaries = [
    MRa0 ; MRa1 ; MRa2 ; MRa3 ;
    MRt0 ; MRt1 ; MRt2 ; MRt3 ; MRt4 ; MRt5 ; MRt6 ; MRt7 ; MRt8 ; MRt9 ]


let _ =
  List.iter (fun (r,s) ->
      add_to_sumtype_tables
        mips_special_regs_to_string_table
        mips_special_regs_from_string_table r s)
    [(MMHi,"hi"); (MMLo,"lo")]

let mips_special_reg_to_string (r:mips_special_reg_t) =
  get_string_from_table
    "mips_special_regs_to_string_table" mips_special_regs_to_string_table r

let mips_special_reg_from_string (name:string) =
  get_sumtype_from_table
    "mips_special_regs_from_string_table" mips_special_regs_from_string_table name

let _ =
  List.iter (fun (r,s) ->
      add_to_sumtype_tables armregs_to_string_table armregs_from_string_table r s)
    [ (AR0,"R0");
      (AR1,"R1");
      (AR2,"R2");
      (AR3,"R3");
      (AR4,"R4");
      (AR5,"R5");
      (AR6,"R6");
      (AR7,"R7");
      (AR8,"R8");
      (AR9,"R9");
      (AR10,"R10");
      (AR11,"R11");
      (AR12,"R12");
      (ARSP,"SP");
      (ARLR,"LR");
      (ARPC,"PC") ]

let arm_regular_registers = get_sumtype_table_keys armregs_to_string_table


let armreg_to_string (r:arm_reg_t) =
  get_string_from_table "armregs_to_string_table" armregs_to_string_table r


let arm_extension_reg_type_to_string (t: arm_extension_reg_type_t): string =
  match t with
  | XSingle -> "S"
  | XDouble -> "D"
  | XQuad -> "Q"


let arm_extension_reg_to_string (t: arm_extension_reg_type_t) (ix: int) =
  (arm_extension_reg_type_to_string t) ^ (string_of_int ix)


let armreg_from_string (name:string) =
  get_sumtype_from_table
    "armregs_from_string_table" armregs_from_string_table name

let _ =
  List.iter (fun (r,s) ->
      add_to_sumtype_tables
        arm_special_regs_to_string_table
        arm_special_regs_from_string_table r s)
    [(APSR, "APSR"); (FPSCR, "FPSCR"); (APSR_nzcv, "APSR_nzcv")]


let arm_special_reg_to_string (r: arm_special_reg_t) =
  get_string_from_table
    "arm_special_regs_to_string_table" arm_special_regs_to_string_table r


let arm_special_reg_from_string (name:string) =
  get_sumtype_from_table
    "arm_special_regs_from_string_table" arm_special_regs_from_string_table name


let register_from_string (name: string) =
  if H.mem cpuregs_from_string_table name then
    CPURegister (cpureg_from_string name)
  else if H.mem armregs_from_string_table name then
    ARMRegister (armreg_from_string name)
  else if H.mem mipsregs_from_string_table name then
    MIPSRegister (mipsreg_from_string name)
  else
    raise
      (BCH_failure
         (LBLOCK [
              STR "No x86, mips, or arm register found with name "; STR name]))

let get_armreg_argument (index: int) =
  match index with
  | 0 -> AR0
  | 1 -> AR1
  | 2 -> AR2
  | 3 -> AR3
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Index out of range for get_armreg_argument: ";
                   INT index]))
  
let is_register name = is_string_of_sumtype cpuregs_from_string_table name
  
let cpureg_to_asm_string reg = (cpureg_to_string reg)

let cpureg_option_to_string reg =
  match reg with Some r -> cpureg_to_asm_string r | None -> ""


let register_compare r1 r2 =
  match (r1, r2) with
  | (CPURegister c1, CPURegister c2) ->
     Stdlib.compare (cpureg_to_string c1) (cpureg_to_string c2)
  | (CPURegister _, _) -> -1
  | (_, CPURegister _) -> 1
  | (ARMRegister a1, ARMRegister a2) ->
     Stdlib.compare (armreg_to_string a1) (armreg_to_string a2)
  | (ARMRegister _, _) -> -1
  | (_, ARMRegister _) -> 1
  | (ARMSpecialRegister r1, ARMSpecialRegister r2) ->
     Stdlib.compare (arm_special_reg_to_string r1) (arm_special_reg_to_string r2)
  | (ARMSpecialRegister _, _) -> -1
  | (_, ARMSpecialRegister _) -> 1
  | (ARMExtensionRegister (s1, i1), ARMExtensionRegister (s2, i2)) ->
     Stdlib.compare (s1, i1) (s2, i2)
  | (ARMExtensionRegister _, _) -> -1
  | (_, ARMExtensionRegister _) -> 1
  | (MIPSRegister m1, MIPSRegister m2) ->
     Stdlib.compare (mipsreg_to_string m1) (mipsreg_to_string m2)
  | (MIPSRegister _, _) -> -1
  | (_, MIPSRegister _) -> 1
  | (MIPSSpecialRegister s1,MIPSSpecialRegister s2) ->
     Stdlib.compare (mips_special_reg_to_string s1) (mips_special_reg_to_string s2)
  | (MIPSSpecialRegister _, _) -> -1
  | (_, MIPSSpecialRegister _) -> 1
  | (MIPSFloatingPointRegister i1,MIPSFloatingPointRegister i2) ->
     Stdlib.compare i1 i2
  | (MIPSFloatingPointRegister _,_) -> -1
  | (_, MIPSFloatingPointRegister _) -> 1
  | (FloatingPointRegister i1, FloatingPointRegister i2) -> Stdlib.compare i1 i2
  | (FloatingPointRegister _,_) -> -1
  | (_,FloatingPointRegister _) -> 1
  | (ControlRegister i1, ControlRegister i2) -> Stdlib.compare i1 i2
  | (ControlRegister _, _) -> -1
  | (_, ControlRegister _) -> 1
  | (DebugRegister i1, DebugRegister i2) -> Stdlib.compare i1 i2
  | (DebugRegister _, _) -> -1
  | (_, DebugRegister _) -> 1
  | (MmxRegister i1, MmxRegister i2) -> Stdlib.compare i1 i2
  | (MmxRegister _, _) -> -1
  | (_, MmxRegister _) -> 1
  | (XmmRegister i1, XmmRegister i2) -> Stdlib.compare i1 i2
  | (XmmRegister _, _) -> -1
  | (_, XmmRegister _) -> 1
  | (SegmentRegister s1, SegmentRegister s2) -> 
      Stdlib.compare (segment_to_string s1) (segment_to_string s2)
  | (SegmentRegister _, _) -> -1
  | (_, SegmentRegister _) -> 1
  | (DoubleRegister (c11,c12), DoubleRegister (c21,c22)) -> 
      Stdlib.compare 
	(cpureg_to_string c11, cpureg_to_string c12)
        (cpureg_to_string c21, cpureg_to_string c22)


let register_to_string register =
  match register with
  | CPURegister r -> cpureg_to_string r
  | SegmentRegister r -> segment_to_string r
  | ControlRegister i -> "CR" ^ (string_of_int i)
  | DebugRegister i -> "DR" ^ (string_of_int i)
  | DoubleRegister (r1,r2) -> (cpureg_to_string r1) ^ "_" ^ (cpureg_to_string r2)
  | FloatingPointRegister i -> "st(" ^ (string_of_int i) ^ ")"
  | MmxRegister i -> "mm(" ^ (string_of_int i) ^ ")"
  | XmmRegister i -> "xmm(" ^ (string_of_int i) ^ ")"
  | MIPSRegister r -> mipsreg_to_string r
  | MIPSSpecialRegister r -> mips_special_reg_to_string r
  | MIPSFloatingPointRegister i -> "$f" ^ (string_of_int i)
  | ARMRegister r -> armreg_to_string r
  | ARMSpecialRegister r -> arm_special_reg_to_string r
  | ARMExtensionRegister (s, i) -> arm_extension_reg_to_string s i


let extract_cpu_reg s =
  let len = String.length s in
  let rsub = String.sub s 4 (len - 5) in
  try
    cpureg_from_string rsub
  with
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR s ; STR " cannot be converted to cpu register: " ;
                        STR rsub ]))

let extract_mips_reg s =
  let len = String.length s in
  let rsub = String.sub s 5 (len - 6) in
  try
    mipsreg_from_string rsub
  with
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR s ; STR " cannot be converted to mips register: " ;
                        STR rsub ]))

let register_from_string (s:string) =
  if starts_with s "x86(" then
    CPURegister (extract_cpu_reg s)
  else if starts_with s "mips(" then
    MIPSRegister (extract_mips_reg s)
  else
    try
      register_from_string s
    with
    | BCH_failure p ->
       raise (BCH_failure
                (LBLOCK [ STR "register string conversion not supported for ";
                          STR s;
                          STR ": ";
                          p]))

let byte_reg_of_reg r = 
  match r with
  | Eax -> Al
  | Ecx -> Cl
  | Edx -> Dl
  | Ebx -> Bl
  | Esp -> Ah
  | Ebp -> Ch
  | Esi -> Dh
  | Edi -> Bh
  | Ax -> Al
  | Cx -> Cl
  | Dx -> Dl
  | Bx -> Bl
  | _ -> 
    begin
      ch_error_log#add "invalid argument" 
	(LBLOCK [ STR "byte_reg_of_reg: " ; STR (cpureg_to_string r) ; 
		  STR " has no corresponding byte register"]);
      raise (Invalid_argument "byte_reg_of_reg")
    end

let word_reg_of_reg r =
  match r with
  | Eax -> Ax
  | Ecx -> Cx
  | Edx -> Dx
  | Ebx -> Bx
  | Esp -> Sp
  | Ebp -> Bp
  | Esi -> Si
  | Edi -> Di
  | _ -> 
    begin
      ch_error_log#add "invalid argument" 
	(LBLOCK [ STR "word_reg_of_reg: " ; STR (cpureg_to_string r) ; 
		  STR " has no corresponding word register"]);
      raise (Invalid_argument "word_reg_of_reg")
    end

let sized_reg_of_reg r size = 
  match size with 
    1 -> byte_reg_of_reg r
  | 2 -> word_reg_of_reg r
  | 4 -> r
  | _ -> 
    begin
      ch_error_log#add "invalid argument" 
	(LBLOCK [ STR "sized_reg_of_reg: " ; STR (cpureg_to_string r) ; 
		  STR " invalid width: " ; INT size ]) ;
      raise (Invalid_argument "sized_reg_of_reg")
    end


let registers_affected_by r =
  match r with
  | Eax -> [ Al ; Ah ; Ax ]
  | Ecx -> [ Cl ; Ch ; Cx ]
  | Edx -> [ Dl ; Dh ; Dx ]
  | Ebx -> [ Bl ; Bh ; Bx ]
  | Esp -> [ Sp ]
  | Ebp -> [ Bp ]
  | Esi -> [ Si ]
  | Edi -> [ Di ]
  | Al | Ah  -> [ Eax ; Ax ]
  | Cl | Ch  -> [ Ecx ; Cx ]
  | Bl | Bh  -> [ Ebx ; Bx ]
  | Dl | Dh  -> [ Edx ; Dx ]
  | Ax -> [ Al ; Ah ; Eax ]
  | Cx -> [ Cl ; Ch ; Ecx ]
  | Dx -> [ Dl ; Dh ; Edx ]
  | Bx -> [ Bl ; Bh ; Ebx ]
  | _ -> []


let registers_zeroed_by r =
  match r with
  | Eax -> [ Eax ; Al ; Ah ; Ax ]
  | Ecx -> [ Ecx ; Cl ; Ch ; Cx ]
  | Edx -> [ Edx ; Dl ; Dh ; Dx ]
  | Ebx -> [ Ebx ; Bl ; Bh ; Bx ]
  | Ax  -> [ Ax ; Ah ; Al ]
  | Cx  -> [ Cx ; Ch ; Cl ]
  | Dx  -> [ Dx ; Dh ; Dl ]
  | Bx  -> [ Bx ; Bh ; Bl ]
  | _ -> [ r ]

let index_to_register (index:int) =
  match index with
  | 0 -> Eax
  | 1 -> Ecx
  | 2 -> Edx
  | 3 -> Ebx
  | 4 -> Esp
  | 5 -> Ebp
  | 6 -> Esi
  | 7 -> Edi
  | _ -> raise (Invalid_argument ("index_to_register with " ^ (string_of_int index)))

let index_to_word_register (index:int) =
  match index with
  | 0 -> Ax
  | 1 -> Cx
  | 2 -> Dx
  | 3 -> Bx
  | 4 -> Sp
  | 5 -> Bp
  | 6 -> Si
  | 7 -> Di
  | _ -> raise (Invalid_argument ("index_to_word_register with " ^ (string_of_int index)))

let index_to_byte_register (index:int) =
  match index with
  | 0 -> Al
  | 1 -> Cl
  | 2 -> Dl
  | 3 -> Bl
  | 4 -> Ah
  | 5 -> Ch
  | 6 -> Dh
  | 7 -> Bh
  | _ -> raise (Invalid_argument ("index_to_byte_register with " ^ (string_of_int index)))
