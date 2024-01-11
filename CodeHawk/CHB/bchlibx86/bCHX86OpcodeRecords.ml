(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* =============================================================================
   The implementation in this file is based on the documents:

   Intel 64 and IA-32 Architectures Software Developer's Manual, September 2010
   Volume 2A: Instruction Set Reference, A-M
   Volume 2B: Instruction Set Reference, N-Z
   ============================================================================= *)

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHCPURegisters
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHX86Opcodes


class type ['a]  opcode_formatter_int =
object
  method ops: string -> operand_int list -> 'a
  method no_ops: string -> 'a
end

let pop_suffix  (pop:bool) =
  if pop then "p" else ""

let npop_suffix (pop:int) =
  if pop = 0 then "" else if pop = 1 then "p" else "pp"

let fp_infix (fp:bool) =
  if fp then "" else "i"

let cpe_infix  (cpe:bool) =
  if cpe then "" else "n"

let unordered_infix (unordered:bool) =
  if unordered then "u" else ""

let scalar_infix (scalar:bool) =
  if scalar then "s" else "p"             (* scalar or packed *)

let single_infix (single:bool) =
  if single then "s" else "d"   (* single or double precision *)

let is_dup (modifier:string) =
  match modifier with "dup" | "hdup" | "ldup" -> true | _ -> false

let truncate_infix (truncate:bool) =
  if truncate then "t" else ""

let signed_saturation_infix (ss:bool) =
  if ss then "s" else ""

let unsigned_saturation_infix (us:bool) =
  if us then "us" else ""

let get_float_type (scalar:bool) (single:bool) =
  let frep = if scalar then FScalar else FPacked in
  let fkind = if single then FFloat else FDouble in
  TFloat (fkind, frep, [])


type 'a opcode_record_t = {
  docref: string;
  mnemonic: string;
  operands: operand_int list;
  flags_set: eflag_t list;
  flags_used: eflag_t list;
  group_name: string;
  long_name: string;
  intel_asm: 'a;
  att_asm: 'a
}


let get_record (opc:opcode_t) =
  match opc with
  (* AAA             ---- ASCII Adjust after addition                ---- 37 *)
  | AAA -> {
    docref      = "2A, 3-16";
    mnemonic    = "aaa";
    operands    = [ax_r RW];
    flags_set   = [OFlag; SFlag; ZFlag; CFlag; PFlag];
    flags_used  = [];
    group_name  = "binary coded decimal";
    long_name   = "ASCII_Adjust_After_Addition";
    intel_asm   = (fun f -> f#no_ops "aaa");
    att_asm     = (fun f -> f#no_ops "aaa")
   }

  (* AAD             ---- ASCII Adjust AX before diviion             ---- D5 0A
     AAD imm8        ---- ASCII Adjust AX before division            ---- D5 ib
   *)
  | AAD op -> {
    docref      = "2A, 3-18";
    mnemonic    = "aad";
    operands    = [ax_r RW; op];
    flags_set   = [OFlag; SFlag; ZFlag; CFlag; PFlag];
    flags_used  = [];
    group_name  = "binary coded decimal";
    long_name   = "ASCII_Adjust_Before_Division";
    intel_asm   = (fun f -> f#ops "aad" [op]);
    att_asm     = (fun f -> f#ops "aad" [op])
   }

  (* AAM             ---- ASCII Adjust AX after multiply             ---- D4 0A
     AAM imm8        ---- ASCII Adjust AX after multiply             ---- D4 ib
   *)
  | AAM op -> {
    docref      = "2A, 3-20";
    mnemonic    = "aam";
    operands    = [ax_r RW; op];
    flags_set   = [OFlag; SFlag; ZFlag; CFlag; PFlag];
    flags_used  = [];
    group_name  = "binary coded decimal";
    long_name   = "ASCII_Adjust_Before_Division";
    intel_asm   = (fun f -> f#ops "aam" [op]);
    att_asm     = (fun f -> f#ops "aam" [op])
   }

  (* AAS             ---- ASCII Adjust AL after subtraction          ---- 3F *)
  | AAS -> {
    docref      = "2A, 3-22";
    mnemonic    = "aas";
    operands    = [ax_r RW];
    flags_set   = [OFlag; SFlag; ZFlag; CFlag; PFlag];
    flags_used  = [];
    group_name  = "binary coded decimal";
    long_name   = "ASCII_Adjust_Before_Division";
    intel_asm   = (fun f -> f#no_ops "aas");
    att_asm     = (fun f -> f#no_ops "aas")
   }

  (* ADC r/m8,r8     ---- Add with carry byte register to r/m8       ---- 10/r
     ADC r/m32,r32   ---- Add with carry r32 to r/m32                ---- 11/r
     ADC r8,r/m8     ---- Add with carry r/m8 to byte register       ---- 12/r
     ADC r32,r/m32   ---- Add with carry r/m32 to r32                ---- 13/r
     ADC AL,imm8     ---- Add with carry imm8 to AL                  ---- 14/ib
     ADC AX, imm16   ---- Add with carry imm16 to AX                 ---- 15/iw
     ADC EAX,imm32   ---- Add with carry imm32 to EAX                ---- 15 id
     ADC r/m8,imm8   ---- Add with carry imm8 to r/m8                ---- 80/2 ib
     ADC r/m32,imm32 ---- Add with CF imm32 to r/m32                 ---- 81/2 id
     ADC r/m32,imm8  ---- Add with CF sign extended imm8 into r/m32  ---- 83/2 ib
  *)
  | AddCarry (op1,op2) -> {
    docref       = "2A, 3-27";
    mnemonic     = "adc";
    operands     = [op1; op2];
    flags_set    = [OFlag; SFlag; ZFlag; CFlag; PFlag];
    flags_used   = [CFlag];
    group_name   = "integer arithmetic";
    long_name    = "AddCarry";
    intel_asm    = (fun f -> f#ops "adc" [op1; op2]);
    att_asm      = (fun f -> f#ops "adc" [op2; op1]);
 }

  (* ADD r/m8,r8     ---- Add r8 to r/m8                              ---- 00/r
     ADD r/m32,r32   ---- Add r32 to r/m32                            ---- 01/r
     ADD r8,r/m8     ---- Add r/m8 to r8                              ---- 02/r
     ADD r32,r/m32   ---- Add r/m32 to r32                            ---- 03/r
     ADD AL,imm8     ---- Add imm8 to AL                              ---- 04 ib
     ADD EAX,imm32   ---- Add imm32 to EAX                            ---- 05 id
     ADD r/m8,imm8   ---- Add imm8 to r/m8                            ---- 80/0 ib
     ADD r/m32,imm32 ---- Add imm32 to r/m32                          ---- 81/0 id
     ADD r/m32,imm8  ---- Add sign-extended imm8 to r/m32             ---- 83/0 ib
  *)
  | Add (op1,op2) -> {
    docref       = "2A, 3-31";
    mnemonic     = "add";
    operands     = [op1; op2];
    flags_set    = [OFlag; SFlag; ZFlag; CFlag; PFlag];
    flags_used   = [];
    group_name   = "integer arithmetic";
    long_name    = "Add";
    intel_asm    = (fun f -> f#ops "add" [op1; op2]);
    att_asm      = (fun f -> f#ops "add" [op2; op1]);
 }

   (* AESDEC xmm1,xmm2/m128 --- Perform one round of an AES decryption flow
      using the Equivalent Inverse Cipher operating on a 128-bit data (state)
      from xmm1 with a 128-bit round key from xmm2/m128       ---- 66 0F 38 DE/r
   *)
  | AESDecrypt (op1,op2) -> {
    docref       = "2A, 3-54";
    mnemonic     = "aesdec";
    operands     = [op1; op2];
    flags_set    = [];
    flags_used   = [];
    group_name   = "encryption";
    long_name    = "AESDecrypt";
    intel_asm    = (fun f -> f#ops "aesdec" [op1; op2]);
    att_asm      = (fun f -> f#ops "aesdec" [op2; op1]);
 }

  (* AESDECLAST xmm1,xmm2/m128 --- Perform the last round of an AES decryption
      flow using the Equivalent Inverse Cipher, operaing on a 128-bit data
      (state) from xmm1 with a 128-bit round key from xmm2/m128---- 66 0F 38 DF/r
  *)
  | AESDecryptLast (op1,op2) -> {
    docref       = "2A, 3-57";
    mnemonic     = "aesdeclast";
    operands     = [op1; op2];
    flags_set    = [];
    flags_used   = [];
    group_name   = "encryption";
    long_name    = "AESDecryptLast";
    intel_asm    = (fun f -> f#ops "aesdeclast" [op1; op2]);
    att_asm      = (fun f -> f#ops "aesdeclast" [op2; op1]);
 }

  (* AESENC xmm1,xmm2/m128 --- Perform one round of an AES encryption flow,
     operating on a 128-bit data (state) from xmm1 with a 128-bit round key
     from xmm2/m128                                           ---- 66 0F 38 DC/r
  *)
  | AESEncrypt (op1,op2) -> {
    docref       = "2A, 3-60";
    mnemonic     = "aesenc";
    operands     = [op1; op2];
    flags_set    = [];
    flags_used   = [];
    group_name   = "encryption";
    long_name    = "AESEncrypt";
    intel_asm    = (fun f -> f#ops "aesenc" [op1; op2]);
    att_asm      = (fun f -> f#ops "aesenc" [op2; op1])
 }

  (* AESENCLAST xmm1,xmm2/m128 --- Perform the last round of an AES encryption
     flow, operating on a 128-bit data (state) from xmm1 with a 128-bit
     round key from xmm2/m128                                 ---- 66 0F 38 DD/r
  *)
  | AESEncryptLast (op1,op2) -> {
    docref       = "2A, 3-63";
    mnemonic     = "aesenclast";
    operands     = [op1; op2];
    flags_set    = [];
    flags_used   = [];
    group_name   = "encryption";
    long_name    = "AESEncryptLast";
    intel_asm    = (fun f -> f#ops "aesenclast" [op1; op2]);
    att_asm      = (fun f -> f#ops "aesenclast" [op2; op1])}

  (* AESIMC xmm1,xmm2/m128 --- Perform the InvMixColumn transformation on a
	   128-bit round key from xmm2/m128 and store the result in xmm1
                                                              ---- 66 0F 38 DB/r
  *)
  | AESInvMix (op1,op2) -> {
    docref       = "2A, 3-66";
    mnemonic     = "aesimc";
    operands     = [op1; op2];
    flags_set    = [];
    flags_used   = [];
    group_name   = "encryption";
    long_name    = "AESInvMixColumn";
    intel_asm    = (fun f -> f#ops "aesimc" [op1; op2]);
    att_asm      = (fun f -> f#ops "aesimc" [op2; op1])}

  (* AESKEYGENASSIST xmm1, xmm2/m128,imm8 --- Assist in AES round key generation
     using an 8-bit Round Constant (RCON) specified in the immediate byte,
     operating on 128 bits of data specified in xmm2/m128 and store the result
     in xmm1                                                  ---- 66 0F 3A DF/r
  *)
  | AESKeyGenAssist (op1,op2,op3) -> {
    docref       = "2A, 3-68";
    mnemonic     = "aeskeygenassist";
    operands     = [op1; op2];
    flags_set    = [];
    flags_used   = [];
    group_name   = "encryption";
    long_name    = "AESKeyGenAssist";
    intel_asm    = (fun f -> f#ops "aeskeygenassist" [op1; op2; op3]);
    att_asm      = (fun f -> f#ops "aeskeygenassist" [op3; op2; op1])} (* check *)

  (* ARPL r/m16,r16 --- Adjust RPL of r/m16 to not less than RPL of r16 --- 63
                        Adjusted Requested Privilege Level of Selector
     The RPL field is located in bits 0 and 1 of each operand
   *)
  | Arpl (op1,op2) -> {
    docref     = "2A, 3-82";
    mnemonic   = "arpl";
    operands   = [op1; op2];
    flags_set  = [ZFlag];
    flags_used = [];
    group_name = "misc";
    long_name  = "AdjustRPLField";
    intel_asm  = (fun f -> f#ops "arpl" [op1; op2]);
    att_asm    = (fun f -> f#ops "arpl" [op2; op1])}

  (* BSF r32,r/m32 --- Bit scan forward on r/m32                  --- 0F BC/r *)
  | BitScanForward (op1,op2) -> {
    docref       = "2A, 3-100";
    mnemonic     = "bsf";
    operands     = [op1; op2];
    flags_set    = [ZFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "BitScanForward";
    intel_asm    = (fun f -> f#ops "bsf" [op1; op2]);
    att_asm      = (fun f -> f#ops "bsf" [op2; op1])}

  (* BSR r32,r/m32 --- Bit scan reverse on r/m32                  --- 0F BD/r *)
  | BitScanReverse (op1,op2) -> {
    docref       = "2A, 3-103";
    mnemonic     = "bsr";
    operands     = [op1; op2];
    flags_set    = [ZFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "BitScanReverse";
    intel_asm    = (fun f -> f#ops "bsr" [op1; op2]);
    att_asm      = (fun f -> f#ops "bsr" [op2; op1])}

  (* INT 3 ------- Interrupt 3: trap to debugger                      ---- CC *)
  | BreakPoint -> {
    docref       = "2A, 3-533";
    mnemonic     = "int";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "BreakPoint";
    intel_asm    = (fun f -> f#no_ops "int 3");
    att_asm      = (fun f -> f#no_ops "int 3")}

  (* BSWAP r32 --- Reverses the byte order of a 32 bit register  --- 0F C8+rd *)
  | BSwap op -> {
    docref       = "2A, 3-106";
    mnemonic     = "bswap";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "ByteSwap";
    intel_asm    = (fun f -> f#ops "bswap" [op]);
    att_asm      = (fun f -> f#ops "bswap" [op])}

  (* BT  r/m32,imm8 --- Store selected bit in CF flag           ---- 0F BA/4 ib
     BT  r/m32,r32 ---- Store selected bit in CF flag           ---- 0F A3/r
  *)
  | BitTest (op1,op2) -> {
    docref       = "2A, 3-108";
    mnemonic     = "bt";
    operands     = [op1; op2];
    flags_set    = [CFlag; OFlag; SFlag; PFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "BitTest";
    intel_asm    = (fun f -> f#ops "bt" [op1; op2]);
    att_asm      = (fun f -> f#ops "bt" [op2; op1])}

   (* BTC r/m32,imm8 --- Store selected bit in CF flag and complement
                                                                ---- 0F BA/7 ib
      BTC r/m32,r32 --- Store selected bit in CF flag and complement
                                                                ---- 0F BB/r
  *)
  | BitTestComplement (op1,op2) -> {
    docref       = "2A, 3-111";
    mnemonic     = "btc";
    operands     = [op1; op2];
    flags_set    = [CFlag; OFlag; SFlag; PFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "BitTestComplement";
    intel_asm    = (fun f -> f#ops "btc" [op1; op2]);
    att_asm      = (fun f -> f#ops "btc" [op2; op1])}

  (* BTR r/m32,imm8 --- Store selected bit in CF flag and clear  ---- 0F BA/6 ib
     BTR r/m32,r32  --- Store selected bit in CF flag and clear  ---- 0F B3/r
  *)
  | BitTestReset (op1,op2) -> {
    docref       = "2A, 3-114";
    mnemonic     = "btr";
    operands     = [op1; op2];
    flags_set    = [CFlag; OFlag; SFlag; PFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "BitTestReset";
    intel_asm    = (fun f -> f#ops "btr" [op1; op2]);
    att_asm      = (fun f -> f#ops "btr" [op2; op1])}

  (* BTS r/m32,imm8 --- Store selected bit in CF flag and set    ---- 0F BA/5 ib
     BTS r/m32,r32  --- Store selected bit in CF flag and set    ---- 0F AB/r
  *)
  | BitTestAndSet (op1,op2) -> {
    docref       = "2A, 3-117";
    mnemonic     = "bts";
    operands     = [op1; op2];
    flags_set    = [CFlag; OFlag; SFlag; PFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "BitTestAndSet";
    intel_asm    = (fun f -> f#ops "bts" [op1; op2]);
    att_asm      = (fun f -> f#ops "bts" [op2; op1])}

  (* CLC  --- Clear Carry Flag                                        ---- F8 *)
  | ClearCF -> {
    docref       = "2A, 3-141";
    mnemonic     = "clc";
    operands     = [];
    flags_set    = [CFlag];
    flags_used   = [];
    group_name   = "cc operation";
    long_name    = "ClearCarryFlag";
    intel_asm    = (fun f -> f#no_ops "clc");
    att_asm      = (fun f -> f#no_ops "clc")}

  (* CLD  --- Clear Direction Flag                                    ---- FC *)
  | ClearDF -> {
    docref       = "2A, 3-142";
    mnemonic     = "cld";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "misc";
    long_name    = "ClearDirectionFlag";
    intel_asm    = (fun f -> f#no_ops "cld");
    att_asm      = (fun f -> f#no_ops "cld")}

  (* CLD  --- Clear Interrupt Flag                                    ---- FA *)
  | ClearInterruptFlag -> {
    docref       = "2A, 3-145";
    mnemonic     = "cli";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "misc";
    long_name    = "ClearInterruptFlag";
    intel_asm    = (fun f -> f#no_ops "cli");
    att_asm      = (fun f -> f#no_ops "cli")}

  (* CLTS ---- Clear TS flag in CR0                                 ---- 0F 06 *)
  | ClearTaskSwitchedFlag -> {
    docref       = "2A, 3-148";
    mnemonic     = "clts";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "misc";
    long_name    = "ClearTaskSwitchedFlag";
    intel_asm    = (fun f -> f#no_ops "clts");
    att_asm      = (fun f -> f#no_ops "clts")}

  (* CMOVO r32,r/m32   --- Move if overflow (OF=1)                   ---- 0F 40/r
     CMOVNO r32,r/m32  --- Move if not overflow (OF=0)               ---- 0F 41/r
     CMOVC r32,r/m32   --- Move if carry (CF=1)                      ---- 0F 42/r
     CMOVNC r32,r/m32  --- Move if not carry (CF=0)                  ---- 0F 43/r
     CMOVZ r32,r/m32   --- Move if zero (ZF=1)                       ---- 0F 44/r
     CMOVNZ r32,r/m32  --- Move if not zero (ZF=0)                   ---- 0F 45/r
     CMOVBE r32,r/m32  --- Move if below or equal (CF=1 or ZF=1)     ---- 0F 46/r
     CMOVA r32,r/m32   --- Move if above (CF=0 and ZF=0)             ---- 0F 47/r
     CMOVS r32,r/m32   --- Move if sign (SF=1)                       ---- 0F 48/r
     CMOVNS r32,r/m32  --- Move if not sign (SF=0)                   ---- 0F 49/r
     CMOVPE r32,r/m32  --- Move if parity even (PF=1)                ---- 0F 4A/r
     CMOVPO r32,r/m32  --- Move if parity odd (PF=0)                 ---- 0F 4B/r
     CMOVL r32,r/m32   --- Move if less (SF != OF)                   ---- 0F 4C/r
     CMOVGE r32,r/m32  --- Move if greater or equal (SF=OF)          ---- 0F 4D/r
     CMOVLE r32,r/m32  --- Move if less or equal (ZF=1 or SF!=OF)    ---- 0F 4E/r
     CMOVG r32,r/m32   --- Move if greater (ZF=0 and SF=OF)          ---- 0F 4F/r
*)
  | CMovcc (cc,width,op1,op2) ->
    let name = "cmov" ^ (condition_code_to_suffix_string cc) in
    { docref      = "2A, 3-151";
      mnemonic    = name;
      operands    = [op1; op2];
      flags_set   = [];
      flags_used  = flags_used_by_condition cc;
      group_name  = "move";
      long_name   = "ConditionalMove" ^ (condition_code_to_name cc);
      intel_asm   = (fun f -> f#ops name [op1; op2]);
      att_asm     = (fun f -> f#ops name [op2; op1])}

  (* CMP r/m8,r8     ---- Compare r8 with r/m8                       ---- 38/r
     CMP r/m32,r32   ---- Compare r32 with r/m32                     ---- 39/r
     CMP r8,r/m8     ---- Compare r/m8 with r8                       ---- 3A/r
     CMP r32,r/m32   ---- Compare r/m32 with r32                     ---- 3B/r
     CMP AL,imm8     ---- Compare imm8 with AL                       ---- 3C ib
     CMP AX, imm16   ---- Compare imm16 with AX                      ---- 3D iw
     CMP EAX,imm32   ---- Compare imm32 with EAX                     ---- 3D id
     CMP r/m8,imm8   ---- Compare imm8 with r/m8                     ---- 80/7 ib
     CMP r/m32,imm32 ---- compare imm32 with r/m32                   ---- 81/7 id
     CMP r/m32,imm8  ---- Compare sign-extended imm8 with r/m32      ---- 83/7 ib
  *)
  | Cmp (op1,op2) -> {
    docref       = "2A, 3-158";
    mnemonic     = "cmp";
    operands     = [op1; op2];
    flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
    flags_used   = [];
    group_name   = "test";
    long_name    = "Compare";
    intel_asm    = (fun f -> f#ops "cmp" [op1; op2]);
    att_asm      = (fun f -> f#ops "cmp" [op2; op1])}

  (* CMPXCHG r/m8,r8 --- Compare AL with r/m8. If equal, ZF is
                         set and r8 is loaded into r/m8. Else       ---- 0F A6/r
                         clear ZF and load r/m8 into AL             ---- 0F B0/r
     CMPXCHG r/m32,r32 --- Compare EAX with r/m32. If equal, SF is
                           set and r32 is loaded into r/m32. Else   ---- 0F A7/r
                           clear ZF and load r/m32 into EAX         ---- 0F B1/r
  *)
  | CmpExchange (width,op1,op2) ->
    let src = register_op (sized_reg_of_reg Eax width) width RD in
    {	docref       = "2A, 3-185";
	mnemonic     = "cmpxch";
	operands     = [op1; op2; src];
	flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
	flags_used   = [];
	group_name   = "move";
	long_name    = "CompareExchange";
	intel_asm    = (fun f -> f#ops "cmpxch" [op1; op2]);
	att_asm      = (fun f -> f#ops "cmpxch" [op2; op1])}

  (* CMPXCHG8B m64 --- Compare EDX:EAX with m64. If equal, set ZF and
                       load ECX:EBX into m64. Else, clear ZF and load
                       m64 into EDX:EAX.                            ---- 0F C7/1
  *)
  | CmpExchange8B (op,opdst,opsrc) -> {
    docref           = "2A 3-155";
    mnemonic         = "cmpxchg8b";
    operands         = [op; opdst; opsrc];
    flags_set        = [ZFlag];
    flags_used       = [];
    group_name       = "move";
    long_name        = "CompareExchange8B";
    intel_asm        = (fun f -> f#ops "cmpxchg8b" [op]);
    att_asm          = (fun f -> f#ops "cmpxchg8b" [op])}

  (* CMPS m8,m8 ---- compare byte at DS:[ESI] with byte at ES:[EDI]     ---- A6
     CMPS m32,m32 -- compare dword at DS:[ESI] with dword at ES:[EDI]   ---- A7
  *)
  | Cmps (width,op1,op2) ->
    let name = "cmps" ^ (width_suffix_string width) in
    { docref       = "2A, 3-171";
      mnemonic     = name;
      operands     = [op1; op2; esi_r RW; edi_r RW];
      flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
      flags_used   = [DFlag];
      group_name   = "string operation";
      long_name    = "CompareStrings";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}

  (* CMC ---- Complement CF flag                                      ---- F5 *)
  | ComplementCF -> {
    docref       = "2A, 3-150";
    mnemonic     = "cmc";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "cc operation";
    long_name    = "ComplementCarryFlag";
    intel_asm    = (fun f -> f#no_ops "cmc");
    att_asm      = (fun f -> f#no_ops "cmc")}

  (* CWD ---           DX:AX <- sign-extend of AX                       ---- 99
     CDQ ---           EDX:EAX <- sign-extend of EAX                    ---- 99
  *)
  | ConvertLongToDouble (op1,op2) ->
    let name = if op1#size = 2 then "cwd" else "cdq" in {
      docref       = "2A, 3-301";
      mnemonic     = name;
      operands     = [op1; op2];
      flags_set    = [];
      flags_used   = [];
      group_name   = "move";
      long_name    = "ConvertWordToDoubleword";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}

  (* CBW  (16 bits) -- AX      <- sign-extend of AL                     ---- 98
     CWDE (32 bits) -- EAX     <- sign-extend of AX                     ---- 98
	*)
  | ConvertWordToDoubleword (op1,op2) ->
    let name = if op1#size = 2 then "cwb" else "cwde" in {
      docref       = "2A, 3-139";
      mnemonic     = name;
      operands     = [op1; op2];
      flags_set    = [];
      flags_used   = [];
      group_name   = "move";
      long_name    = "ConvertWordToDoubleword";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}

  (* TZCNT  r/m32,r32 ---- Count the number of trailing zero bits ---- F3 0F BC/r
  *)
  | CountTrailingZeroBits (op1, op2) -> {
    docref       = "2B, 4-713";
    mnemonic     = "tzcnt";
    operands     = [op1; op2];
    flags_set    = [CFlag; OFlag; SFlag; PFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "CountTrailingZeroBits";
    intel_asm    = (fun f -> f#ops "tzcnt" [op1; op2]);
    att_asm      = (fun f -> f#ops "tzcnt" [op2; op1])}

  (* CPUID  --- Returns processor identification and feature
                information to the EAX, EBX, ECX and EDX
                registers, as determined by input entered in EAX
                (in some cases, ECX, as well)                         ---- 0F A2
   *)
  | Cpuid -> {
    docref       = "2A, 3-197";
    mnemonic     = "cpuid";
    operands     = [eax_r RW; ebx_r WR; ecx_r WR; edx_r WR];
    flags_set    = [];
    flags_used   = [];
    group_name   = "misc";
    long_name    = "CpuIdentification";
    intel_asm    = (fun f -> f#no_ops "cpuid");
    att_asm      = (fun f -> f#no_ops "cpuid")}

  (* DAA --- Decimal Adjust AL after addition                         ---- 27 *)
  | DAA -> {
    docref       = "2A, 3-232";
    mnemonic     = "daa";
    operands     = [al_r RW];
    flags_set    = [CFlag; OFlag; ZFlag; SFlag; PFlag];
    flags_used   = [];
    group_name   = "binary coded decimal";
    long_name    = "Decimal_Adjust_After_Addition";
    intel_asm    = (fun f -> f#no_ops "daa");
    att_asm      = (fun f -> f#no_ops "daa")}

  (* DAS   --- Decimal Adjust AL after subtraction                    ---- 2F *)
  | DAS -> {
    docref       = "2A, 3-234";
    mnemonic     = "das";
    operands     = [al_r RW];
    flags_set    = [CFlag; OFlag; ZFlag; SFlag; PFlag];
    flags_used   = [];
    group_name   = "binary coded decimal";
    long_name    = "Decimal_Adjust_After_Subtraction";
    intel_asm    = (fun f -> f#no_ops "das");
    att_asm      = (fun f -> f#no_ops "das")}

  (* DEC r32   ---- Decrement r32 by 1                                ---- 48+rd
     DEC r/m8  ---- Decrement r/m8 by 1                               ---- FE/1
     DEC r/m32 ---- Decrement r/m doubleword by 1                     ---- FF/1
  *)
  | Decrement op -> {
    docref       = "2A, 3-307";
    mnemonic     = "dec";
    operands     = [op];
    flags_set    = [OFlag; SFlag; ZFlag; PFlag];    (* note: CFlag is not set *)
    flags_used   = [];
    group_name   = "integer arithmetic";
    long_name    = "Decrement";
    intel_asm    = (fun f -> f#ops "dec" [op]);
    att_asm      = (fun f -> f#ops "dec" [op])}

  (* CALL rel32 --- Call near, relative, displacement relative to
		                next instruction                      ---- E8 cd
  *)
  | DirectCall op -> {
    docref       = "2A, 3-120";
    mnemonic     = "call";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "DirectCall";
    intel_asm    = (fun f -> f#ops "call" [op]);
    att_asm      = (fun f -> f#ops "call" [op])}

  (* JMP rel32 --- Jump near relative, RIP = RIP + 32bit disp         ---- E9 cd
     JMP ptr 16:32  --- Jump far, absolute address given in operand   ---- EA cp
     JMP rel8  --- Jump near, RIP=RIP+8bit disp sign-extended         ---- EB cb
  *)
  | DirectJmp op -> {
    docref       = "2A, 3-572";
    mnemonic     = "jmp";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "DirectJump";
    intel_asm    = (fun f -> f#ops "jmp" [op]);
    att_asm      = (fun f -> f#ops "jmp" [op])}

  (* LOOP rel8 --- Decrement count; jump short if count is not equal to 0
                                                                   ---- E2 cb  *)
  | DirectLoop op -> {
    docref       = "2A, 3-622";
    mnemonic     = "loop";
    operands     = [op; ecx_r RD];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "Loop";
    intel_asm    = (fun f -> f#ops "loop" [op]);
    att_asm      = (fun f -> f#ops "loop" [op])}

  (* DIV r/m8  --- Unsigned divide:  AL,AH <- AX / r/m8             ---- F6/6 ib
     DIV r/m32 --- Unsigned divide EDX:EAX by r/m32 with
                            result stored in EAX <- quotient,
                            EDX <- remainder                        ---- F7/6
  *)
  | Div (width,quot,rem,dividend,divisor) ->
    { docref       = "2A, 3-310";
      mnemonic     = "div";
      operands     = [quot; rem; dividend; divisor];
      flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];(* flags are undefined *)
      flags_used   = [];
      group_name   = "integer arithmetic";
      long_name    = "UnsignedDivide";
      intel_asm    = (fun f -> f#ops "div" [divisor]);
      att_asm      = (fun f -> f#ops "div" [divisor])}

  (* 0F 77 --- EMMS --- set the x87 FPU tag word to empty *)
  | EmptyMmx -> {
    docref       = "2A, 3-334";
    mnemonic     = "emms";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "mmx";
    long_name    = "EmptyMmx";
    intel_asm    = (fun f -> f#no_ops "emms");
    att_asm      = (fun f -> f#no_ops "emms")}

  (* FADD ST(0),ST(i) -- Add st(0) to st(i) and store result in st(0)  ---- D8 C0+i
     FADD ST(i),ST(0) -- Add st(i) to st(0) and store result in st(i)  ---- DC C0+i
     FADD m32fp     ---- Add m32fp to st(0) and store result in st(0)  ---- D8/0
     FIADD m32int    --- Add m32int to st(0) and store result in st(0) ---- DA/0
     FADD m64fp      --- Add m64fp to ST(0) and store result in ST(0)  ---- DC/0
     FIADD m16int    --- Add m16int to st(0) and store result in st(0) ---- DE/0
     FADDP ST(i),ST(0) - Add st(0) to st(i), store result in st(i)
                                       and pop the register stack      ---- DE C0+i

     pop  : floating point stack is popped after operation
     fp   : source operand is a floating point number (no need for conversion)
     width: width of the source operand
  *)
  | Fadd (pop,fp,width,dst,src) ->
     let name =
       "f" ^ (if fp then "" else "i") ^ "add" ^ (if pop then "p" else "") in
    { docref       = "2A, 3-347";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "AddFP";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* FCLEX  --- Clear floating point exception flags after checking for
                pending unmasked floating point exceptions          ---- 9B DB E2
		 FNCLEX --- clear floating point exception flags without checking
                pending  unmasked floating point exceptions            ---- DB E2

		 cpe : check for pending unmasked floating point exceptions
  *)
  | Fclex cpe ->
    let name = "f" ^ (cpe_infix cpe) ^ "clex" in
    { docref       = "2A, 3-358";
      mnemonic     = name;
      operands     = [];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "ClearFPExceptions";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}


  (* FCOM ST(i) --- Compare ST(0) with ST(i)                          ---- D8 D0+i
     FCOMP ST(i) -- Compare ST(0) with ST(i) and pop register stack   ---- D8 D8+i
     FCOM m32fp --- Compare ST(0) with m32fp                          ---- D8/2
     FCOMP m32fp -- Compare ST(0) with m32fp and pop register stack   ---- D8/3
     FCOM m64fp --- Compare ST(0) with m64fp                          ---- DC/2
     FCOMP m64fp -- Compare st(0) with m64fp  and pop register stack  ---- DC/3
     FCOMPP
     ---- Compare ST(0) with ST(1) and pop register stack twice       ---- DE D9

     pop  : number of times floating point stack is popped
     fp   : source operand is a floating point number (no need for conversion)
     width: width of the source operand
  *)
  | Fcom (pop,fp,width,src) ->
    let name = "f" ^ (fp_infix fp) ^ "com" ^ (npop_suffix pop) in
    { docref       = "2A, 3-362";
      mnemonic     = name;
      operands     = [fpu_register_op 0 RD; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "CompareFP";
      intel_asm    = (fun f -> f#ops name [src]);
      att_asm      = (fun f -> f#ops name [src])}

  (* FUCOMI ST(0),ST(i)
     --- Compare ST(0) with ST(i), check for ordered value,
         set EFlags, check for                                      ---- DB E8+i
     FCOMI ST(0),ST(i)
     --- Compare ST(0) with ST(i) and set EFlags                    ---- DB F0+i
     FUCOMIP ST(0),ST(i)
     --- Compare ST(0) with ST(i), check for ordered values,
         set EFlags, and pop register stack                         ---- DF E8+i
     FCOMIP ST(0),ST(i)
     --- Compare ST(0) with ST(i), set EFlags, and pop
         register stack                                             ---- DF F0+i

     pop       : floating point stack is popped after operation
     unordered : QNaNs do not raise an exception, but set result to unordered
  *)
  | Fcomi (pop,unordered,src) ->
    let name = "f" ^ (unordered_infix unordered) ^ "comi" ^ (pop_suffix pop) in
    { docref       = "2A, 3-366";
      mnemonic     = name;
      operands     = [fpu_register_op 0 RD; src];
      flags_set    = [ZFlag; PFlag; CFlag];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "CompareFPSetFlags";
      intel_asm    = (fun f -> f#ops name [src]);
      att_asm      = (fun f -> f#ops name [src])}

  (* FDIV ST(0),ST(i)
     --- Divide ST(0) by ST(i) and store result in ST(0)            ---- D8 F0+i
     FDIV  ST(i),ST(0)
     --- Divide ST(i) by ST(0) and store result in ST(i)            ---- DC F8+i
     FDIV m32fp
     --- Divide ST(0) by m32fp and store result in ST(0)            ---- D8/6
     FICOM m32int
     --- Compare ST(0) with m32int                                  ---- DA/2
     FICOMP m32int
     --- Compare ST(0) with m32int and pop stack register           ---- DA/3
     FIDIV m32int
     --- Divide ST(0) by m32int and store result in ST(0)           ---- DA/6
     FDIV m64fp
     --- Divide st(0) by m64fp and store result in st(0)            ---- DC/6
     FICOM m16int    ---- Compare ST(0) with m16int                 ---- DE/2
     FICOMP m16int
     --- Compare ST(0) with m16int and pop stack register           ---- DE/3
     FIDIV m16int
     --- Divide ST(0) by m16int and store result in ST(0)           ---- DE/6
     FDIVP ST(i),ST(0)
     --- Divide ST(i) by ST(0), store the result in
         ST(i) and pop register stack                               ---- DE F8+i

     pop   : floating point stack is popped after operation
     fp    : source operand is a floating point number (no need for conversion)
     width : width of the source operand
  *)
  | Fdiv (pop,fp,width,dst,src) ->
     let name =
       "f" ^ (if fp then "" else "i") ^ "add" ^ (if pop then "p" else "") in
    { docref       = "2A, 3-373";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "DivideFP";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* FDIVR ST(i),ST(0)
     --- Divide ST(i) by ST(0) and store result in ST(0)            ---- D8 F8+i
     FDIVR ST(i),ST(0)
     --- Divide ST(0) by ST(i) and store result in ST(i)            ---- DC F0+1
     FDIVR m32fp
     ---- Divide m32fp by ST(0) and store result in ST(0)           ---- D8/7
     FIDIVR m32int
     --- Divide m32int by ST(0) and store result in ST(0)           ---- DA/7
     FDIVR m64fp
     --- Divide m64fp by ST(0) and store result in ST(0)            ---- DC/7
     FIDVR m16int
     --- Divide m16int by ST(0) and store result  in ST(0)          ---- DE/7
     FDIVRP ST(i),ST(0)
     --- Divide ST(0) by ST(i), store the result in
         ST(i) and pop register stack                               ---- DE F0+i

     pop   : floating point stack is popped after operation
     fp    : source operand is a floating point number (no need for conversion)
     width : width of the source operand
  *)
  | Fdivr (pop,fp,width,dst,src) ->
     let name =
       "f" ^ (if fp then "" else "i") ^ "div" ^ (if pop then "p" else "") in
    { docref       = "2A, 3-377";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "ReverseDivideFP";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* FINIT
     --- Initialize FPU after checking for pending unmasked
         floating point exceptions                                  ---- 9B DB E3
     FNINIT
     --- Initialize FPU without checking for pending unmasked
         floating point exceptions                                  ---- DB E3

     cpe : check for pending unmasked floating point exceptions
  *)
  | Finit cpe ->
    let name = "f" ^ (cpe_infix cpe) ^ "init" in
    { docref       = "2A, 3-389";
      mnemonic     = name;
      operands     = [];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "InitializeFP";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}


  (* FMUL ST(0),ST(i)
     --- Multiply ST(0) by ST(i) and store result in ST(0)           --- D8 C8+i
     FMUL ST(i),ST(0)
     --- Multiply ST(i) by ST(0) and store result in ST(i)          ---- DC C8+i
     FMUL m32f
     ---- Multiply ST(0) by m32fp and store result in ST(0)         ---- D8/1
     FIMUL m32int
     ---- Multiply ST(0) by m32int adn store result in ST(0)        ---- DA/1
     FMUL m64fp
     --- Multiply st(0) by m64fp and store result in st(0)          ---- DC/1
     FIMUL m16int
     --- Multiiply ST(0) by m16int and store result in ST(0)         --- DE/1
     FMULP ST(i),ST(0)
     --- Multiply ST(i) by ST(0) and store result
         in ST(i) and pop the register stack                        ---- DE C8+i

     pop   : floating point stack is popped
     fp    : source operand is a floating point number (no need for conversion)
     width : width of the source operand
  *)
  | Fmul (pop,fp,width,dst,src) ->
     let name =
       "f" ^ (if fp then "" else "i") ^ "mul" ^ (if pop then "p" else "") in
    { docref       = "2A, 3-408";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "MultiplyFP";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (*  FSUB ST(0),ST(i)
      --- Subtract ST(i) from ST(0) and store result in ST(0)     ---- D8 E0+i
      FSUB ST(i),ST(0)
      ---- Subtract ST(0) from ST(i) and store result in ST(i)    ---- DC E8+i
      FSUB m32fp
      ---- Subtract m32fp from ST(0) and store result in ST(0)    ---- D8/4
      FISUB m32int
      ---- Subtract m32int from ST(0) and store result in ST(0)   ---- DA/4
      FSUB m64fp
      ---- Subtract m64fp from st(0) and store result in st(0)
                                                                  ---- DC/4
      FISUB m16int
      ---- Subtract m16int from ST(0) and store result int ST(0)  ---- DE/4
      FSUBP ST(i),ST(0)
      ---- Subtract ST(0) from ST(i), store result in
           ST(i) and pop register stack                           ---- DE E8+i

      pop   : floating point stack is popped after operation
      fp    : source operand is a floating point number (no need for conversion)
      width : width of source operand
  *)
  | Fsub (pop,fp,width,dst,src) ->
     let name =
       "f" ^ (if fp then "" else "i") ^ "sub" ^ (if pop then "p" else "") in
    { docref       = "2A, 3-455";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "SubtractFP";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

   (* FSUBR ST(0),ST(i)
      --- Subtract ST(0) from ST(i) and store result in ST(0)        ---- D8 E8+i
      FSUBR ST(i),ST(0)
      --- Subtrach ST(i) from ST(0) and store result in ST(i)        ---- DC E0+i
      FSUBR m32fp
      ---- Subtract ST(0) from m32fp and store result in ST(0)       ---- D8/5
      FISUBR m32int
      --- Subtract ST(0) from m32int and store result in ST(0)       ---- DA/5
      FSUBR m64fp
      --- Subtract st(0) from m64fp and store result in st(0)        ---- DC/5
      FISUBR m16int
      --- Subtract st(0) from m16int and store result  in st(0)      ---- DE/5
      FSUBRP ST(i),ST(0)
      --- Subtract ST(i) from ST(0), store result in
          ST (i) and pop the register stack                          ---- DE E0+i

      pop   : floating point stack is popped after operation
      fp    : source operand is a floating point number (no need for conversion)
      width : width of the source operand
   *)

  | Fsubr (pop,fp,width,dst,src) ->
     let name =
       "f" ^ (if fp then "" else "i") ^ "subr" ^ (if pop then "p" else "") in
    { docref       = "2A, 3-459";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "ReverseSubtractFP";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* FUCOMPP ---- Compare ST(0) with ST(1) and pop register twice    ---- DA E9
     FUCOM ST(i),ST(0) ---- Unordered comparison of ST(0) with ST(i) ---- DD E0+i
     FUCOMP ST(i),ST(0) ---- Unordered comparison of ST(0) with ST(i)
                             and pop register stack                  ---- DD E8+i

     pop  : number of times floating point stack is popped
  *)

  | Fucom (pop,src) ->
     let name =
       "fucom" ^ (if pop = 0 then "" else if pop = 1 then "p" else "pp") in
    { docref       = "2A, 3-465";
      mnemonic     = name;
      operands     = [fpu_register_op 0 RD; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "UnorderedCompareFP";
      intel_asm    = (fun f -> f#ops name [src]);
      att_asm      = (fun f -> f#ops name [src])}

  (* FXCH ---- Exchange the contents of ST(0) and ST(i)          ---- D9 C8+i *)
  | Fxch src -> {
    docref       = "2A, 3-470";
    mnemonic     = "fxch";
    operands     = [fpu_register_op 0 RW; src];
    flags_set    = [];
    flags_used   = [];
    group_name   = "floating point";
    long_name    = "FPExchange";
    intel_asm    = (fun f -> f#ops "fxch" [src]);
    att_asm      = (fun f -> f#ops "fxch" [src])}

  (* CVTPI2PS xmm,mm/m64
     --- Convert two signed doubleword integers from mm/m64
         to two sinle-prec floating-point values in xmm             ---- 0F 2A/r
     CVTTPS2PI mm,xmm/m64
     --- Convert two single-prec floating-point values from
         xmm/m64 to two signed doubleword integers in mm
         using truncation   		                            ---- 0F 2C/r
     CVTPS2PI mm,xmm/m64
     --- Convert two packed single-prec floating-point values
         from xmm/m64 to two packed signed doublewords in mm        ---- 0F 2D/r
     CVTPS2PD xmm1,xmm2/m64
     --- Convert two packed single-prec floating-point values
         in xmm2/m64 to two packed double-prec floating-point
         values in xmm1                                             ---- 0F 5A/r
     CVTDQ2PS xmm1,xmm2/m128
     --- Convert four packed signed doubleword integers from
         xmm2/m128 to four packed single-prec floating-point
         values in xmm1                                             ---- 0F 5B/r


     CVTPI2PD xmm,mm/m64
     --- Convert two packed signed doubleword integers from
         mm/m64 to two packed double-prec floating-point
         values in xmm                                           ---- 66 0F 2A/r
     CVTTPD2PI mm,xmm/m128
     --- Convert two packed double-prec floating-point
         values from xmm/m128 to two packed signed doubleword
         integers in mm using truncation		         ---- 66 0F 2C/r
     CVTPD2PI mm,xmm/m128
     --- Convert two packed double-prec floating-point
         values from xmm/m128 to two packed signed doubleword
         integers in mm                                          ---- 66 0F 2D/r
     CVTPD2PS xmm1,xmm2/m128
     --- Convert two packed double-prec floating-point
         values in xmm2/m128 to two packed single-prec
         floating-point values in xmm1                           ---- 66 0F 5A/r
     CVTPS2DQ xmm1,xmm2/m128
     --- Convert four packed single-prec floating-point
         values from xmm2/m128 to four packed signed
         doubleword integers in xmm1                             ---- 66 0F 5B/r
     CVTTPD2DQ xmm1,xmm2/m128
     --- Convert two packed double-prec floating-point
         values from xmm2/m128 to two packed signed
         doubleword integers in xmm1 using truncation            ---- 66 0F E6/r

     CVTSI2SD xmm,r/m32
     ---  Convert one signed doubleword integer from r/m32
          to one double-precision floating-point value           ---- F2 0F 2A/r
     CVTTSD2SI r32,xmm/m64
     --- Convert one double-precision floating-point value
         from xmm/m64 to one signed doubleword integer in r32
         using truncation                                        ---- F2 0F 2C/r
     CVTSD2SI r32,xmm/m64
     --- Convert one double-prec floating-point value from
         xmm/m64 to one signed doubleword integer r32            ---- F2 0F 2D/r
     CVTSD2SS xmm1,xmm2/m64
     --- Convert one double-precision floating-point value
         in xmm2/m64 to one single-precision floating-point
         value in xmm1                                           ---- F2 0F 5A/r
     CVTPD2DQ xmm1,xmm2/m128
     --- Convert two packed double-prec floating-point
         values from xmm2/m128 to two packed signed
         doubleword integers in xmm1                             ---- F2 0F E6/r

     CVTSI2SS xmm,r/m32
     --- Convert one signed doubleword integer from r/m32
         to one single-precision floating-point value            ---- F3 0F 2A/r
     CVTTSS2SI r32,xmm/m32
     ---- Convert one single-prec floating-point value from
          xmm/m32 to one signed doubleword integer in r32
          using truncation                                       ---- F3 0F 2C/r
     CVTSS2SI r32,xmm/m32
     --- Convert one single-precision floating-point value
         from xmm/m32 to one signed doubleword integer in r32    ---- F3 0F 2D/r
     CVTSS2SD xmm1,xmm2/m32
     --- Convert one single-precision floating-point value
         in xmm2/m32 to one double-precision floating-point
         value in xmm1                                           ---- F3 0F 5A/r
     CVTTPS2DQ xmm1,xmm2/m128
     --- Convert four single-prec floating-point values
         from xmm2/m128 to four signed doubleword integers
         in xmm1 using truncation                                ---- F3 0F 5B/r
     CVTDQ2PD xmm1,xmm2/m128
     --- Convert two packed signed doubleword integers
         from xmm2/m128 to two packed double-prec
         floating-point values in xmm1                           ---- F3 0F E6/r


     truncate : destination is truncated
     srctype,dsttype : "dq" : two packed signed doubleword integers
                       "pd" : packed double precision floating point values
                       "ps" : packed single precision floating point values
                       "sd" : scalar double precision floating point value
                       "si" : signed doubleword integer
                       "ss" : scalar single precision floating point value
  *)

  | FConvert (truncate,srctype,dsttype,dst,src) ->
    let name = "cvt" ^ (truncate_infix truncate) ^ srctype ^ "2" ^ dsttype in
    { docref       = "2A";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    =
        "FConvert:" ^ (truncate_infix truncate) ^ srctype ^ "2" ^ dsttype;
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* FLD          --- Push ST(i) onto the FPU register stack          ---- D9 C0+i
     FLD m32fp    --- push mf32p onto the FPU register stack          ---- D9/0
     FILD m32int  --- Push m32int onto the FPU register stack         ---- DB/0
     FLD m80fp    --- Push m80fp onto the FPU register stack          ---- DB/5
     FLD m64fp    --- Push m64fp onto FPU register stack              ---- DD/0
     FILD  m16int --- Push m16int onto FPU register stack             ---- DF/0
     FILD  m64int --- Push m64int onto FPU register stack             ---- DF/5

     fp   : source operand is a floating point number (no conversion needed)
     width: width of the source operand, to be extended to 80-bit
               double-extended precision
  *)
  | FLoad (fp,width,src) ->
    let name = "f" ^ (fp_infix fp) ^ "ld" in
    {	docref       = "2A, 3-398";
	mnemonic     = name;
	operands     = [fpu_register_op 0 WR; src];
	flags_set    = [];
	flags_used   = [];
	group_name   = "floating point";
	long_name    = "LoadFP";
	intel_asm    = (fun f -> f#ops name [src]);
	att_asm      = (fun f -> f#ops name [src])}

  (* FLD1 ---- Push +1.0 onto the FPU register stack                 ---- D9 E8
     FLDL2T -- Push log_2 10 onto the FPU register stack             ---- D9 E9
     FLDL2E -- Push log_2 e onto the FPU register stack              ---- D9 EA
     FLDPI --- Push pi onto the FPU register stack                   ---- D9 EB
     FLDLG2 -- Push log_10 2 onto the FPU register stack             ---- D9 EC
     FLDLN2 -- Push log_e 2 onto the FPU register stack              ---- D9 ED
     FLDZ ---- Push +0.0 onto the FPU register stack                 ---- D9 EE
  *)
  | FLoadConstant (suffix,descr) ->
    let name = "fld" ^ suffix in
    {	docref       = "2A, 3-401";
	mnemonic     = name;
	operands     = [fpu_register_op 0 WR];
	flags_set    = [];
	flags_used   = [];
	group_name   = "floating point";
	long_name    = "LoadFPConstant";
	intel_asm    = (fun f -> f#no_ops name);
	att_asm      = (fun f -> f#no_ops name)}

  (* FLDENV m14/28byte
     --- Load FPU environment from m15byte or m28byte                 ---- D9/4
     FLDCW m2byte      --- Load FPU control word from m2byte          ---- D9/5
   *)
  | FLoadState (state,width,src) ->
    let name = "fld" ^ state in
    { docref       = "2A, 3-403, 3-405";
      mnemonic     = name;
      operands     = [src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "LoadFPStatus";
      intel_asm    = (fun f -> f#ops name [src]);
      att_asm      = (fun f -> f#ops name [src])}

  (* FCHS  ---- Complement sign of st(0)                               ---- D9 E0
     FABS  ---- Replace st(0) with its absolute value                  ---- D9 E1
     FTST  ---- Compare ST(0) with 0.0                                 ---- D9 E4
     FXAM  ---- Examines the contents of ST(0) register                ---- D9 E5
     F2XM1  --- Replace ST(0) with 2^(st(0))-1                         ---- D9 F0
     FYL2X  --- Replace ST(1) with (ST(1) * log2ST(0)) and pop the
                register stack                                         ---- D9 F1
     FPTAN  --- Replace ST(0) with its approximate tangent and push 1
                onto the FPU stack                                     ---- D9 F2
     FPATAN --- Replace ST(1) with arctan(ST(1)/ST(0)) and pop the
                register stack                                         ---- D9 F3
     FPREM1 --- Replace ST(0) with the IEEE remainder obtained from
                dividing ST(0) by ST(1).                               ---- D9 F5
     FDECSTP -- Decrement TOP field in FPU status word                 ---- D9 F6
     FINCSTP -- Increment the TOP field of the FPU status register     ---- D9 F7
     FYL2XP1 -- Replace ST(1) with ST(1) * log2(ST(0) + 1.0) and pop
                the register stack                                     ---- D9 F9
     FSQRT  --- Replace ST(0) with its square root                     ---- D9 FA
     FSINCOS -- Compute the sine and cosine of ST(0); replace ST(0)
                with the approximate sine, and push the approximate
                cosine onto the register stack                         ---- D9 FB
     FRNDINT -- Round ST(0) to an integer                              ---- D9 FC
     FSIN   --- Replace ST(0) with its sine                            ---- D9 FE
     FCOS   --- Replace ST(0) with its cosine                          ---- D9 FF
  *)
  | FStackOp (name,descr) -> {
    docref       = "";
    mnemonic     = name;
    operands     = [fpu_register_op 0 RW];
    flags_set    = [];
    flags_used   = [];
    group_name   = "floating point";
    long_name    = "FStackOperation:" ^ name;
    intel_asm    = (fun f -> f#no_ops name);
    att_asm      = (fun f -> f#no_ops name)}

    (* FST m32fp    --- Copy st(0) to m32fp                           ---- D9/2
       FSTP mf32p   --- Copy st(0) to m32fp and pop register stack    ---- D9/3
       FIST m32int  --- Store ST(0) in m32 int                        ---- DB/2
       FISTP m32int --- Store st(0) in m32int and pop register stack  ---- DB/3
       FSTP m80fp   --- Copy ST(0) to m80fp and pop register stack    ---- DB/7
       FST  m64fp   --- Copy ST(0) to m64fp                           ---- DD/2
       FSTP m64fp   --- Copy ST(0) to m64fp and pop register          ---- DD/3
       FST ST(i)    --- Copy ST(0) to ST(i)                           ---- DD D0+i
       FSTP ST(i)   --- Copy ST(0) to ST(i) and pop register stack    ---- DD D8+i
       FIST m16int  --- Store ST(0) in m16int                         ---- DF/2
       FISTP m16int --- Store ST(0) in m16 and pop register stack     ---- DF/3
       FISTP m64int --- Store st(0) in m64int and pop register stack  ---- DF/7

       pop   : pop floating point stack after operation
       fp    : number is stored in destination in floating point format
       width : width of destination operand
    *)
  | FStore (pop,fp,width,dst) ->
    let name = "f" ^ (fp_infix fp) ^ "st" ^ (pop_suffix pop) in
    { docref       = "2A, 3-391, 3-443";
      mnemonic     = name;
      operands     = [dst; fpu_register_op 0 RD];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "StoreFP";
      intel_asm    = (fun f -> f#ops name [dst]);
      att_asm      = (fun f -> f#ops name [dst])}

  (* FBSTP m80bcd --- Store ST(0) in M80bcd and pop ST(0)           ---- DF/6 *)
  | Fbstp dst -> {
    docref       = "2A, 3-353";
    mnemonic     = "fbst";
    operands     = [dst; fpu_register_op 0 RD];
    flags_set    = [];
    flags_used   = [];
    group_name   = "floating point";
    long_name    = "Store bcd integer";
    intel_asm    = (fun f -> f#ops "fbst" [dst]);
    att_asm      = (fun f -> f#ops "fbst" [dst])}

  (* FRSTOR m94/108byte --- Load FPU state from m94byte or m108byte  ---- DD/4 *)
  | FRestoreState src -> {
    docref     = "2A 3-325";
    mnemonic   = "frstor";
    operands   = [src];
    flags_set  = [];
    flags_used = [];
    group_name = "floating point";
    long_name  = "RestoreFPUState";
    intel_asm  = (fun f -> f#ops "frstor" [src] );
    att_asm    = (fun f -> f#ops "frstor" [src] )}

  (* FXRSTOR m512byte
     --- Restore the x87 FPU, MMX, XMM, and MXCSR register
         state from m512byte.                                     ---- 0F AE/1 *)
  | FXRestore src -> {
    docref      = "2A 3-360";
    mnemonic    = "fxrstor";
    operands    = [src];
    flags_set   = [];
    flags_used  = [];
    group_name  = "floating point";
    long_name   = "FXRestore";
    intel_asm   = (fun f -> f#ops "fxrstor" [src]);
    att_asm     = (fun f -> f#ops "fxrstor" [src])}

  (* FSAVE m94/108byte --- Store FPU state to m94byte or m108byte
                           after checking for pending unmasked
                           floating-point exceptions. Then
                           re-initialize the FPU                    ---- 9B DD/6

     FNSAVE m94/108byte -- Store FPU environment to m94byte or m108byte
                           without checking for pending unmasked
                           floating- point exceptions. Then
                           re-initialize the FPU                     ---- DD/6 *)
  | FSaveState (chex,dst) ->
    let name = if chex then "fsave" else "fnsave" in
    { docref     = "2A 3-327";
      mnemonic   = name;
      operands   = [dst];
      flags_set  = [];
      flags_used = [];
      group_name = "floating point";
      long_name  = "SaveFPUState";
      intel_asm  = (fun f -> f#ops name [dst]);
      att_asm    = (fun f -> f#ops name [dst])}

  (* FXSAVE m512byte --- Save the x87 FPU, MMX, XMM, and MXCSR register
                         state to m512byte.                        --- 0F AE/0 *)
  | FXSave dst -> {
    docref       = "2A 3-363";
    mnemonic     = "fxsave";
    operands     = [dst];
    flags_set    = [];
    flags_used   = [];
    group_name   = "floating point";
    long_name    = "FXSave";
    intel_asm    = (fun f -> f#ops "fxsave" [dst]);
    att_asm      = (fun f -> f#ops "fxsave" [dst])}

  (*  FSTENV m14/28byte
      --- Store FPU environment to m14byte or m28byte
          after checking for pending unmasked floating-point
          exceptions                                                ---- 9B D9/6
      FSTCW m2byte
      --- Store FPU control word to m2byte after checking
          for pending unmasked floating point exceptions            ---- 9B D9/7
      FSTSW m2 byte
      --- Store FPU status word to m2byte after checking
          for pending unmasked floating point exceptions            ---- 9B DD/7
      FWTSW AX
      --- Store FPU status word in AX register after checking
          for pending unmasked floating point exceptions 	    ---- 9B DF E0
      FNSTENV m14/28byte
      --- Store FPU environment to m14byte or m28byte
          without checking for pending unmasked floating point
          exceptions                                                 ---- D9/6
      FNSTCW m2byte
      --- Store FPU control word to m2byte without checking
          for pending unmasked floating point exceptions             ---- D9/7
      FNSTW m2byte
      --- Store FPU status word at m2byte without checking for
          pending unmasked floating point exceptions                 ---- DD/7
      FNSTW AX
      ---- Store FPU status word in AX without checking for
      pending unmasked floating point exceptions                     ---- DF E0

      state: state to be stored in dst
      cpe  : check for pending floating point exceptions
      width: width of destination operand
  *)
  | FStoreState (state,cpe, width, dst) ->
    let name = "f" ^ (cpe_infix cpe) ^ "st" ^ state in
    { docref       = "2A, 3-446, 3-452";
      mnemonic     = name;
      operands     = [dst];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "StoreFPState";
      intel_asm    = (fun f -> f#ops name [dst]);
      att_asm      = (fun f -> f#ops name [dst])}

  (* CMPPD xmm1,xmm2/m128,imm8
     --- Compare packed double-precision
         floating-point values in xmm2/m128 and
         xmm1 using imm8 as comparison predicate                 ---- 66 0F C2/r

     CMPSD xmm1,xmm2/m64,imm8
     --- Compare low double-prec floating-point value
         in xmm2/m64 and xmm1 using imm8 as comparison
         predicate                                               ---- F2 0F C2/r
     CMPSS xmm1,xmm2/m32, imm8
     --- Compare low single-precision floating-point
         value in xmm2/m32 and xmm1 using imm8 as
         comparison predicate                                    ---- F3 0F C2/r

     scalar : scalar or packed floating point value
     single : single or double precision
     predicate: first 3 bits contain condition code
  *)
  | FXmmCompare (scalar,single,dst,src,predicate) ->
    let name = "cmp" ^ (scalar_infix scalar) ^ (single_infix single) in
    { docref       = "2A";
      mnemonic     = name;
      operands     = [dst; src; predicate];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "FCompare";
      intel_asm    = (fun f -> f#ops name [dst; src; predicate]);
      att_asm      = (fun f -> f#ops name [src; predicate; dst])}

  (* MOVUPS xmm1,xmm2/m128
     --- Move packed single precision floating-point values
         from xmm2/m128 to xmm1                                     ---- 0F 10/r
     MOVUPS xmm2/m128,xmm1
     --- Move packed single precision floating-point values
         from xmm1 to xmm2/m128                                     ---- 0F 11/r
     MOVHLPS xmm1,xmm2
     --- Move two packed single-precision floating-point values
         from high quadword of xmm2 to low quadword of xmm1         ---- 0F 12/r
     MOVLPS m64,xmm
     --- Move two packed single-prec floating-point values
         from low quadword of xmm to m64                            ---- 0F 13/r
     MOVLHPS xmm1,xmm2
     --- Move two packed single-prec floating-point value
         from low quadword of xmm2 to high quadword of xmm1         ---- 0F 16/r
     MOVHPS xmm,m64
     --- Move two packed single-prec floating-point values
         from m64 to high quadword of xmm                           ---- 0F 16/r
     MOVHPS m64,xmm
     --- Move two packed single-prec floating-point values
         from high quadword of xmm to m64                           ---- 0F 17/r
     MOVAPS xmm1,xmm2/m128
     --- Move packed single precision floating-point values
         from xmm2/m128 to xmm1                                     ---- 0F 28/r
     MOVAPS xmm2/m128,xmm1
     --- Move packed single precision floating-point values
         from xmm1 to xmm2/m128                                     ---- 0F 29/r
     MOVNTPS m128,xmm
     --- Move packed single-prec floating-point values from
         xmm to m128 using non-temporal hint                        ---- 0F 2B/r


     MOVUPD xmm1,xmm2/m128
     --- Move packed double-prec floating-point values
         from xmm2/m128 to xmm1                                   ---- 66 0F 10/r
     MOVUPD xmm2/m128,xmm1
     --- Move double-prec floating-point value values
         from xmm1 to xmm2/m128                                   ---- 66 0F 11/r
     MOVLPD xmm,m64
     --- Move double-prec floating-point value from
         m64 to low quadword of xmm                               ---- 66 0F 12/r
     MOVLPD m64,xmm
     --- Move double-prec floating-point value from
         low quadword of xmm to m64                               ---- 66 0F 13/r
     MOVHPD xmm,m64
     --- Move double-prec floating-point value from
         m64 to high quadword of xmm                              ---- 66 0F 16/r
     MOVHPD m64,xmm
     --- Move double-prec floating-point value from
         high quadword of xmm to m64                              ---- 66 0F 17/r
     MOVAPD xmm1,xmm2/m128
     --- Move packed double precision floating
         point values from xmm2/m128 to xmm1                      ---- 66 0F 28/r
     MOVAPD xmm2,xmm1/m128
     --- Move packed double precision floating
         point values from xmm1 to xmm2/m128                      ---- 66 0F 29/r
     MOVNTPD m128,xmm
     --- Move packed double-prec floating-point values
         from xmm to m128 using non-temporal hint                 ---- 66 0F 2B/r

     MOVSD xmm1,xmm2/m64
     --- Move scalar double-prec floating-point value
         from xmm2/m64 to xmm1 register                           ---- F2 OF 10/r
     MOVSD xmm2/m64,xmm1
     --- Move scalar double-prec floating-point value
         from xmm1 register to xmm2/m64                           ---- F2 0F 11/r
     MOVDDUP xmm1,xmm2/m64
     --- Move one double-prec floating-point value from
         the lower 64-bit xmm2/m64 to xmm1 and duplicate          ---- F2 0F 12/r

     MOVSS xmm1,xmm2/m32
     --- Move scalar single-precision floating-point
         value from xmm2/m32 to xmm1 register                     ---- F3 0F 10/r
     MOVSS xmm2/m32,xmm1
     --- Move scalar single-precision floating-point
         value from xmm1 register to xmm2/m32                     ---- F3 0F 11/r
     MOVSLDUP xmm1,xmm2/m128
     --- Move two single-prec floating-point values
         from the lower 32-bit of each qword in
         xmm2/m128 to xmm1 and duplicate each 32-bit
         operand to the higher 32-bits of each qword              ---- F3 0F 12/r
     MOVSHDUP xmm1,xmm2/m128
     --- Move two single-prec floating-point values
         from the higher 32-bits of each qword in
         xmm2/m128 to xmm1 and duplicat each 32-bit
         operand to the lower 32-bits of each qword               ---- F3 0F 16/r

    modifier: "a"   : aligned
              "u"   : unaligned
              "hl"  : high to low
              "lh"  : low to high
              "h"   : high in dst
              "l"   : low in dst
              "nt"  : non-temporal hint
              "dup","hdup","ldup" : duplicate
    scalar : scalar or packed
    single : single or double precision
  *)
  | FXmmMove (modifier,scalar,single,dst,src) ->
    let name = if is_dup modifier then
	"mov" ^ (single_infix single) ^ modifier
      else
	"mov" ^ modifier ^ (scalar_infix scalar) ^ (single_infix single) in
    { docref       = "2A";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "FXmmMove:" ^ modifier;
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}


  (*
     UNPCKLPS xmm1,xmm2/m128
     --- Unpacks and Interleaves single-precision
         floating-point values from low quadwords
         of xmm1 and xmm2/mem into xmm                              ---- 0F 14/r
     UCOMISS xmm1,xmm2/m32
     --- Compare lower single-precision floating-point
         value in xmm1 register with lower single-precision
         floating-point value in xmm2/m32                           ---- 0F 2E/r
     COMISS xmm1,xmm2/m32
     ---  Compare low single-precision floating-point values
          in xmm1 and xmm2/mem32 and set the EFLAGS flags
          accordingly.                                              ---- 0F 2F/r
     RSQRTPS xmm1,xmm2/m128
     --- Computes the reciprocals of the square roots of
         the packed single-prec floating point values in
         xmm2/m128                                                  ---- 0F 52/r
     RCPPS xmm1,xmm2/m128
     --- Computes the reciprocals of the packed single-prec
         floating-point values in xmm2/m128                         ---- 0F 53/r
     ANDPS xmm1,xmm2/m128
     --- Bitwise logical AND of xmm2/m128 and xmm1                  ---- 0F 54/r
     ANDNPS xmm1,xmm2/m128
     --- Bitwise logical AND NOT of xmm2/m128 and xmm1              ---- 0F 55/r
     ORPS xmm1,xmm2/m128
     --- Bitwise or of xmm2/m128 and xmm1                           ---- 0F 56/r
     XORPS xmm1,xmm2/m128
     --- Bitwise exclusive-or of xmm2/m128 and xmm1                 ---- 0F 57/r
     ADDPS xmm1,xmm2/m128
     --- Add packed single-precision floating point
         values from xmm2/m128 to xmm1                              ---- 0F 58/r
     SUBPS xmm1,xmm2/m128
     --- Subtract packed single-prec floating-point
         values in xmm2/m128 from xmm1                              ---- 0F 5C/r
     MINPS xmm1,xmm2/m128
     --- Return the minimum single-prec floating-point
         values in xmm2/m128                                        ---- 0F 5D/r
     DIVPS xmm1,xmm2/m128
     --- Divide packed single-prec floating-point values
         in xmm1 by packed single-prec floating-point
         values in xmm2/m128                                        ---- 0F 5E/r
     MAXPS xmm1,xmm2/m128
     --- Return the maximum single-prec floating-point
         values between xmm2/m128 and xmm1                          ---- 0F 5F/r

     UNPCKLPD xmm1,xmm2/m128
     --- Unpacks and Interleaves double-precision
         floating-point values from low quadwords
         of xmm1 and xmm2/m128.                                   --- 66 0F 14/r
     UNPCKHPD xmm1,xmm2/m128
     --- Unpacks and Interleaves double-precision
         floating-point values from high quadwords
         of xmm1 and xmm2/m128.                                   --- 66 0F 15/r
     UCOMISD xmm1,xmm2/m128
     --- Compares (unordered) the low double-prec
         floating-point values in xmm1 and xmm2/m64
         and set EFLAGS                                          ---- 66 0F 2E/r
     COMISD xmm1,xmm2/m128
     --- Compares low double-prec floating-point
         values in xmm1 and xmm2/m64 and set EFLAGS              ---- 66 0F 2F/r
     ANDPD xmm1,xmm2/m128
     --- Bitwise logical AND of xmm2/m128 and xmm1               ---- 66 0F 54/r
     ANDNPD xmm1,xmm2/m128
     --- Bitwise logical AND NOT of xmm2/m128 and xmm1           ---- 66 0F 55/r
     ORPD xmm1,xmm2/m128
     --- Bitwise OR of xmm2/m128 and xmm1                        ---- 66 0F 56/r
     XORPD xmm1,xmm2/m128
     --- Bitwise exclusive OR of xmm2/m128 and xmm1              ---- 66 0F 57/r
     ADDPD xmm1,xmm2/m128
     --- Add packed double-precision floating point values
         from xmm2/m128 to xmm1                                  ---- 66 0F 58/r
     MULPD xmm1,xmm2/m128
     --- Multiply packed double-prec floating-point
         values in xmm2/m128 by xmm1                             ---- 66 0F 59/r
     SUBPD xmm1,xmm2/m128
     --- Subtract packed double-prec floating-point
         values in xmm2/m128 from xmm1                           ---- 66 0F 5C/r
     MINPD xmm1,xmm2/m128
     --- Return the minimum double-prec floating-point
         values between xmm2/m128 and xmm1                       ---- 66 0F 5D/r
     DIVPD xmm1,xmm2/m128
     --- Divide packed double-prec floating-point values
         in xmm1 by packed double-prec floating-point
         values in xmm2/m128                            	 ---- 66 0F 5E/r
     MAXPD xmm1,xmm2/m128
     --- Return the maximum double-prec floating-point
         values between xmm2/m128 and xmm1                       ---- 66 0F 5F/r
     HADDPD xmm1,xmm2/m128
     --- Horizontal add packed double-prec
         floating-point values from xmm2/m128 to xmm1            ---- 66 0F 7C/r
     HSUBPD xmm1,xmm2/m128
     --- Horizontal subtract packed double-prec
         floating-point values from xmm2/m128 to xmm1            ---- 66 0F 7D/r
     ADDSUBPD xmm1,xmm2/m128
     --- add/subtract double-precision floating-point
         values from xmm2/m128 to xmm1                           ---- 66 0F D0/r


     COMISS xmm1,xmm2/m32
     --- Compare low single-prec floating-point values
         in xmm1 and xmm2/m32 and set the EFLAGS                 ---- F2 0F 2F/r
     SQRTSD xmm1,xmm2/m64
     --- Computes the square root of the low double-prec
         floating-point value in xmm2/m64                        ---- F2 0F 51/r
     ADDSD xmm1,xmm2/m64
     --- Add the low double-precision floating-point
     value from xmm2/m64 to xmm1                                 ---- F2 0F 58/r
     MULSD xmm1,xmm2/m64
     --- Multiply the low double-precision floating-point
         value in xmm2/m64 by low double-precision
         floating-point value in xmm1                            ---- F2 0F 59/r
     SUBSD xmm1,xmm2/m64
     --- Subtract the low double-precision
         floating-point value in xmm2/m64 from xmm1              ---- F2 0F 5C/r
     MINSD xmm1,xmm2/m64
     --- Return the minimum scalar double-prec floating-point
         value between xmm2/m64 and xmm1                         ---- F2 0F 5D/r
     DIVSD xmm1,xmm2/m64
     --- Divide low double-precision floating-point value
         in xmm1 by low double-precision floating-point
         value in xmm2.m64                                       ---- F2 0F 5E/r
     MAXSD xmm1,xmm2/m64
     --- Return the maximum scalar double-prec floating-point
         value between xmm2/m64 and xmm1                         ---- F2 0F 5F/r

     HADDPS xmm1,xmm2/m128
     --- Horizontal add packed single-prec
         floating-point values from xmm2/m128 to xmm1            ---- F2 0F 7C/r
     HSUBPS xmm1,xmm2/m128
     --- Horizontal subtract packed single-prec
         floating-point values from xmm2/m128 to xmm1            ---- F2 0F 7D/r

     ADDSUBPS xmm1,xmm2/m128
     --- Add/subtract single-precision floating-point
         values from xmm2/m128 to xmm1                           ---- F2 0F D0/r

     RSQRTSS xmm1,xmm2/m32
     --- Computes the reciprocals of the square root of the
         low single-prec floating-point value in xmm2/m32        ---- F3 0F 52/r
     RCPSS xmm1,xmm2/m32
     --- Computes the reciprocals of the scalar single-prec
         floating-point values in xmm2/m32                       ---- F3 0F 53/r
     ADDSS xmm1,xmm2/m32
     --- Add the low single-precision floating-point
         value from xmm2/m32 to xmm1                             ---- F3 0F 58/r
     MULSS xmm1,xmm2/m32
     --- Multiply the low single-precision floating-point
         value in xmm2/m32 by the low single-precision
         floating-point value in xmm1                            ---- F3 0F 59/r
     SUBSS xmm1,xmm2/m32
     --- Subtract the lower single-precision floating-point
         value in xmm2/m32 from xmm1                             ---- F3 0F 5C/r
     MINSS xmm1,xmm2/m32
     --- Return the minimum scalar single-precision
         floating-point value between xmm2/m32 and xmm1          ---- F3 0F 5D/r
     DIVSS xmm1,xmm2/m32
     --- Divide low single-precision floating-point value
         in xmm1 by low single-precision floating-point value
         in xmm2/m32                                             ---- F3 0F 5E/r
     MAXSS xmm1,xmm2/m32
     --- Return the maximum scalar single-precision
         floating-point value between xmm2/m32 and xmm1          ---- F3 0F 5F/r

     opname : base name of operation
		 scalar : scalar (S) or packed (P)
		 single : single (S) or double precision (D)
  *)
  | FXmmOp (opname,scalar,single,dst,src) ->
    let name = opname ^ (scalar_infix scalar) ^ (single_infix single) in
    { docref       = "2A,2B";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = (match opname with "comi" | "ucomi" ->
	[CFlag; ZFlag; SFlag; OFlag; PFlag; DFlag] | _ -> []) ;
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "FXmmOp:" ^ opname;
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* SHUFPS xmm1,xmm2/m128,imm8
     --- Shuffle packed single precision
         floating-point values selected by imm8 from
         xmm1 and xmm2/m128 to xmm1                            ---- 0F C6/r ib
     SHUFPD xmm1,xmm2/m128,imm
     --- Shuffle packed double-prec floating-point
         values selected by imm8 from xmm1 and
         xmm2/m128 to xmm1                                     ---- 66 0F C6/r ib
  *)
  | FXmmOpEx (opname,scalar,single,dst,src,extop) ->
    let name = opname ^ (scalar_infix scalar) ^ (single_infix single) in
    { docref       = "2A, 2B";
      mnemonic     = name;
      operands     = [dst; src; extop];
      flags_set    = [];
      flags_used   = [];
      group_name   = "floating point";
      long_name    = "FXmmOp:" ^ opname;
      intel_asm    = (fun f -> f#ops name [dst; src; extop]);
      att_asm      = (fun f -> f#ops name [src; extop; dst])}

  (* CLFLUSH m8 --- Flushes cache line containing m8             ---- 0F AE/7 *)
  | FlushCacheLine op -> {
    docref       = "2A, 3-143";
    mnemonic     = "clflush";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "misc";
    long_name    = "FlushCacheLine";
    intel_asm    = (fun f -> f#ops "clflush" [op]);
    att_asm      = (fun f -> f#ops "clflush" [op])}

  (* HLT --- Halt; Stops instruction execution and places the
             processor in a HALT state                               ---- F4 *)
  | Halt -> {
    docref       = "2A, 3-501";
    mnemonic     = "hlt";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "Halt";
    intel_asm    = (fun f -> f#no_ops "hlt");
    att_asm      = (fun f -> f#no_ops "hlt")}

  (* IDIV r/m8  --- Signed divide:  AL,AH <- AX / r/m8               ---- F6/7
     IDIV r/m32 --- Signed divide (EAX,EDX) <- EDX:EAX / r/m32       ---- F7/7
  *)
  | IDiv (width,quot,rem,dividend,divisor) ->
    { docref       = "2A, 3-511";
      mnemonic     = "idiv";
      operands     = [quot; rem; dividend; divisor];
      flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag]; (* flags are undefined *)
      flags_used   = [];
      group_name   = "integer arithmetic";
      long_name    = "SignedDivide";
      intel_asm    = (fun f -> f#ops "idiv" [divisor]);
      att_asm      = (fun f -> f#ops "idiv" [divisor])}

  (* IMUL r16,r/m16      --- r16 <- r/m16 * imm16                   ---- 69/r iw
     IMUL r32,r/m32      --- r32 <- r/m32 * imm32                   ---- 69/r id
     IMUL r16,r/m16,imm8 --- r16 <- r/m16 * sign-extended imm8      ---- 6B/r ib
     IMUL r32,r/m32,imm8 --- r32 <- r/m32 * sign-extended imm8      ---- 6B/r ib
     IMUL r16,r/m16      --- r16 <- r16 * r/m16                     ---- 0F AF/r
     IMUL r32,r/m32      --- r32 <- r32 * r/m32                     ---- 0F AF/r
     IMUL r/m8           --- Signed multiply AX <- AL * r/m8        ---- F6/5
     IMUL r/m32          --- Signed multiply EDX:EAX <- EAX * r/m32 ---- F7/5
*)
  | IMul (width,op1,op2,op3) -> {
    docref       = "2A, 3-515";
    mnemonic     = "imul";
    operands     = [op1; op2; op3];
    flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag]; (* SF,ZF,PF are undefined *)
    flags_used   = [];
    group_name   = "integer arithmetic";
    long_name    = "SignedMultiply";
    intel_asm    = (fun f -> f#ops "imul" [op1; op2; op3]);
    att_asm      = (fun f -> f#ops "imul" [op2; op3; op1])}

  (* INC r32   ---- Increment r32 by 1                                ---- 40+rd
     INC r/m8  ---- Increment r/m8 by 1                               ---- FE/0
     INC r/m32 ---- Increment r/m doubleword by 1                     ---- FF/0
  *)
  | Increment op -> {
    docref       = "2A, 3-522";
    mnemonic     = "inc";
    operands     = [op];
    flags_set    = [OFlag; SFlag; ZFlag; PFlag];    (* note: CFlag is not set *)
    flags_used   = [];
    group_name   = "integer arithmetic";
    long_name    = "Increment";
    intel_asm    = (fun f -> f#ops "inc" [op]);
    att_asm      = (fun f -> f#ops "inc" [op])}

  (* CALL r/m32 ---
     --- Call near, absolute indirect, address given in r/m32       ---- FF/2 *)
  | IndirectCall op -> {
    docref       = "2A, 3-120";
    mnemonic     = "call*";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "IndirectCall";
    intel_asm    = (fun f -> f#ops "call*" [op]);
    att_asm      = (fun f -> f#ops "call*" [op])}

  (* JMP r/m32
     --- Jump near, absolute indirect, address given in r/m32       ---- FF/4 *)
  | IndirectJmp op -> {
    docref       = "2A, 3-572";
    mnemonic     = "jmp*";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "IndirectJump";
    intel_asm    = (fun f -> f#ops "jmp*" [op]);
    att_asm      = (fun f -> f#ops "jmp*" [op])}

  (* IN AL,imm8 --- Input byte from imm8 I/O port address into AL      ---- E4 ib
     IN AX,imm8 --- Input word from imm8 I/O port address into AX      ---- E5 in
     IN EAX,imm8 -- Input dword from imm8 I/O port address into EAX    ---- E5 ib

     IN AL,DX   --- Input byte from I/O port in DX into AL             ---- EC
     IN AX,DX   --- Input word from I/O port in DX into AX             ---- ED
     IN EAX,DX  --- Input doubleword from I/O port in DX into EAX      ---- ED *)
  | InputFromPort (width,dest,port) -> {
    docref        = "2A, 3-398";
    mnemonic      = "in";
    operands      = [dest; port];
    flags_set     = [];
    flags_used    = [];
    group_name    = "I/O";
    long_name     = "InputFromPort";
    intel_asm     = (fun f -> f#ops "in" [dest; port]);
    att_asm       = (fun f -> f#ops "in" [port; dest])}

  (* INSB
     --- Input byte from I/O port specified in DX into memory         ---- 6C
         location ES:(E)DI
     INSD
     --- Input doubleword from I/O port specified in DX into memory   ---- 6D
	 location ES:(E)DI
   *)
  | InputStringFromPort (width,op) ->
    let name = "ins" ^ (width_suffix_string width) in
    { docref       = "2A, 3-525";
      mnemonic     = name;
      operands     = [op; edi_r RW; dx_r RD];
      flags_set    = [];
      flags_used   = [];
      group_name   = "I/O";
      long_name    = "InputStringFromPort";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}

  (* IRET ---- Interrupt return                                       ---- CF *)
  | InterruptReturn opsize_override ->
    let name = if opsize_override then "iret" else "iretd" in
    {	docref       = "2A, 3-553";
	mnemonic     = name;
	operands     = [];
	flags_set    = [CFlag; ZFlag; SFlag; OFlag; PFlag; DFlag];
                                                      (* potentially restored *)
	flags_used   = [];
	group_name   = "control flow";
	long_name    = "InterruptReturn";
	intel_asm    = (fun f -> f#no_ops name);
	att_asm      = (fun f -> f#no_ops name)}

  | InvalidateTLBEntries op -> {
      docref       = "2A, 3-533";
      mnemonic     = "invlpg";
      operands     = [op];
      flags_set    = [];
      flags_used   = [];
      group_name   = "kernelmode";
      long_name    = "InvalidateTLBEntries";
      intel_asm    = (fun f -> f#ops "invlpg" [op]);
      att_asm      = (fun f -> f#ops "invlpg" [op])}

  | InvalidatePCID (op1, op2) -> {
      docref       = "2A, 3-535";
      mnemonic     = "invpcid";
      operands     = [op1; op2];
      flags_set    = [];
      flags_used   = [];
      group_name   = "kernelmode";
      long_name    = "InvalidatePCID";
      intel_asm    = (fun f -> f#ops "invpcid" [op1; op2]);
      att_asm      = (fun f -> f#ops "invpcid" [op1; op2])}

  (* JO  rel8 --- Jump short if overflow       (OF=1)                ---- 70
     JNO rel8 --- Jump short if not overflow   (OF=0)                ---- 71
     JB  rel8 --- Jump short if below          (CF=1)                ---- 72
     JNC rel8 --- Jump short if not carry      (CF=0)                ---- 73
     JZ  rel8 --- Jump short if zero           (ZF=1)                ---- 74
     JNZ rel8 --- Jump short if not zero       (ZF=0)                ---- 75
     JBE rel8 --- Jump short if below or equal (CF=1 or ZF=1)        ---- 76
     JA  rel8 --- Jump short if above          (CF=0, ZF=0)          ---- 77
     JS  rel8 --- Jump short if sign           (SF=1)                ---- 78
     JNS rel8 --- Jump short if not sign       (SF=0)                ---- 79
     JP  rel8 --- Jump short if parity         (PF=1)                ---- 7A
     JPO rel8 --- Jump short if parity odd     (PF=0)                ---- 7B
     JL  rel8 --- Jump short if less           (SF!=OF)              ---- 7C
     JGE rel8 --- Jump short if greater or equal (SF=OF)             ---- 7D
     JLE rel8 --- Jump short if less or equal  (ZF=1 or SF!=OF)      ---- 7E
     JG  rel8 --- Jump short if greater        (ZF=0, SF=OF)         ---- 7F

     JO  rel32 --- Jump near if overflow (OF=1)                ---- 0F 80 cd
     JNO rel32 --- Jump near if not overflow (OF=0)            ---- 0F 81 cd
     JC  rel32 --- Jump near if carry (CF=1)                   ---- 0F 82 cd
     JNC rel32 --- Jump near if not carry (CF=0)               ---- 0F 83 cd
     JZ  rel32 --- Jump near if zero (ZF=1)                    ---- 0F 84 cd
     JNZ rel32 --- Jump near if not zero (ZF=0)                ---- 0F 85 cd
     JBE rel32 --- Jump near if below or equal (CF=1 or ZF=1)  ---- 0F 86 cd
     JA  rel32 --- Jump near if above (CF=0, ZF=0)             ---- OF 87 cd
     JS  rel32 --- Jump near if sign (SF=1)                    ---- 0F 88 cd
     JNS rel32 --- Jump near if not sign (SF=0)                ---- 0F 89 cd
     JPE rel32 --- Jump near if parity even (PF=1)             ---- 0F 8A cd
     JPO rel32 --- Jump near if parity odd (PF=0)              ---- 0F 8B cd
     JL  rel32 --- Jump near if less (SF!=OF)                  ---- 0F 8C cd
     JGE rel32 --- Jump near if greater or equal (SF=OF)       ---- 0F 8D cd
     JLE rel32 --- Jump near if less or equal (ZF=1 or SF!=OF) ---- 0F 8E cd
     JG  rel32 --- Jump near if greater (ZF=0, SF=OF)          ---- 0F 8F cd *)
  | Jcc (cc,op) ->
    let name = "j" ^ (condition_code_to_suffix_string cc) in
    { docref       = "2A, 3-564";
      mnemonic     = name;
      operands     = [op];
      flags_set    = [];
      flags_used   = flags_used_by_condition cc;
      group_name   = "control flow";
      long_name    = "ConditionalJump" ^ (condition_code_to_name cc);
      intel_asm    = (fun f -> f#ops name [op]);
      att_asm      = (fun f -> f#ops name [op])}

  (* JECXZ rel8 --- Jump short if ECX register is 0                ---- E3 cb *)
  | Jecxz op -> {
    docref       = "2A, 3-564";
    mnemonic     = "jecxz";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "ConditionalJumpEcx";
    intel_asm    = (fun f -> f#ops "jecxz" [op]);
    att_asm      = (fun f -> f#ops "jecxz" [op])}

  (* LEA r32,m --------- Store effective address for m in r32       ---- 8D/r *)
  | Lea (dst,src) -> {
    docref       = "2A, 3-601";
    mnemonic     = "lea";
    operands     = [dst; src];
    flags_set    = [];
    flags_used   = [];
    group_name   = "move";
    long_name    = "LoadEffectiveAddress";
    intel_asm    = (fun f -> f#ops "lea" [dst; src]);
    att_asm      = (fun f -> f#ops "lea" [src; dst])}

  (* ENTER --- Save EBP and allocate stack frame                      ---- C8 *)
  | Enter (size,nesting) -> {
      docref     = "2A, 3-336";
      mnemonic   = "enter";
      operands   = [size; nesting];
      flags_set  = [];
      flags_used = [];
      group_name = "control flow";
      long_name  = "Enter";
      intel_asm  = (fun f -> f#ops "enter" [size; nesting]);
      att_asm    = (fun f -> f#ops "enter" [size; nesting])}

  (* LEAVE --- Set ESP to EBP, then pop EBP                          ---- C9 *)
  | Leave -> {
    docref       = "2A, 3-604";
    mnemonic     = "leave";
    operands     = [esp_r WR; ebp_r WR];
    flags_set    = [];
    flags_used   = [];
    group_name   = "control flow";
    long_name    = "Leave";
    intel_asm    = (fun f -> f#no_ops "leave");
    att_asm      = (fun f -> f#no_ops "leave")}

  (* SYSCALL --- Linux System Call with index in Eax              ---  CD 80 *)
  | LinuxSystemCall op -> {
      docref     = "?";
      mnemonic   = "syscall";
      operands   = [op];
      flags_set  = [];
      flags_used = [];
      group_name = "misc";
      long_name  = "LinuxSystemCall";
      intel_asm  = (fun f -> f#ops "syscall" [op]);
      att_asm    = (fun f -> f#ops "syscall" [op])}

  (* LDS/LES/LFS/LGS/LSS --- Load Far Pointer *)
  | LoadFarPointer (op1, op2, op3) ->
     let mnem =
       match op1#get_segment_register with
       | StackSegment -> "ss"
       | DataSegment -> "ds"
       | ExtraSegment -> "es"
       | FSegment -> "fs"
       | GSegment -> "gs"
       | CodeSegment ->
          raise
            (BCH_failure
               (LBLOCK [STR "Unexpected segment in LoadFarPointer"])) in
     {
       docref = "2A, 3-587";
       mnemonic = mnem;
       operands = [op1; op2; op3];
       flags_set = [];
       flags_used = [];
       group_name = "misc";
       long_name = "LoadFarPointer";
       intel_asm = (fun f -> f#ops mnem [op2; op3]);
       att_asm = (fun f -> f#ops mnem [op3; op2])
    }

  (* LAHF ---- Load AH <- Eflags(SF:ZF:0:AF:0:PF:1:CF)                ---- 9F *)
  | LoadFlags -> {
    docref       = "2A, 3-583";
    mnemonic     = "lahf";
    operands     = [ah_r WR];
    flags_set    = [];
    flags_used   = [SFlag; CFlag];
    group_name   = "misc";
    long_name    = "LoadFlags";
    intel_asm    = (fun f -> f#no_ops "lahf");
    att_asm      = (fun f -> f#no_ops "lahf")}

 (* LGDT --- Load Global Descriptor Table Register                --- 0F 01/2 *)
 | LoadGDTR op -> {
     docref     = "2A, 3-599";
     mnemonic   = "lgdt";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "LoadGDTR";
     intel_asm  = (fun f -> f#ops "lgdt" [op]);
     att_asm    = (fun f -> f#ops "lgdt" [op])}

 (* LIDT --- Load Interrupr Descriptor Table Register             --- 0F 01/2 *)
 | LoadIDTR op -> {
     docref     = "2A, 3-599";
     mnemonic   = "lidt";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "LoadIDTR";
     intel_asm  = (fun f -> f#ops "lidt" [op]);
     att_asm    = (fun f -> f#ops "lidt" [op])}

 (* LLDT --- Load Local Descriptor Table Register                 --- 0F 00/2 *)
 | LoadLDTR op -> {
     docref     = "2A, 3-602";
     mnemonic   = "lldt";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "LoadLDTR";
     intel_asm  = (fun f -> f#ops "lldt" [op]);
     att_asm    = (fun f -> f#ops "lldt" [op])}

 (* LTR --- Load Task Register                                    --- 0F 00/3 *)
 | LoadTaskRegister op -> {
     docref     = "2A, 3-620";
     mnemonic   = "ltr";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "LoadTaskRegister";
     intel_asm  = (fun f -> f#ops "ltr" [op]);
     att_asm    = (fun f -> f#ops "ltr" [op])}

  (* LODSB --- Load byte at address DS:[ESI] into AL                   ---- AC
     LODSW --- Load word at address DS:[ESI] into AX                   ---- AD
     LODSD --- Load dword at address DS:[ESI] into EAX                 ---- AD
  *)
 | Lods (width, op) ->
    let name = "lods" ^ (width_suffix_string width) in
    let dst = try register_op (sized_reg_of_reg Eax width) width WR with _ ->
      raise (BCH_failure (LBLOCK [STR "Error in lods operand size: "; INT width])) in
    { docref       = "2A, 3-618";
      mnemonic     = name;
      operands     = [dst; op; esi_r RW ];
      flags_set    = [];
      flags_used   = [DFlag];
      group_name   = "string operation";
      long_name    = "LoadString";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}

  (* AND r/m8,r8   ---- r/m8 AND r8                                  ---- 20/r
     AND r/m32,r32 ---- r/m32 AND r32                                ---- 21/r
     AND r8,r/m8   ---- r8 AND r/m8                                  ---- 22/r
     AND r32,r/m32 ---- r32 AND r/m32                                ---- 23/r
     AND AL,imm8   ---- AL AND imm8                                  ---- 24 ib
     AND EAX,imm32 ---- EAX AND imm32                                ---- 25 ib
     AND r/m8,imm8 ---- r/m8 AND r8                                  ---- 80/4 ib
     AND r/m32,imm32 -- r/m32 AND r32                                ---- 81/4 id
     AND r/m32,imm8 --- r/m32 AND imm8 (sign-extended)               ---- 83/4 ib
  *)
  | LogicalAnd (dst,src) -> {
    docref       = "2A, 3-71";
    mnemonic     = "and";
    operands     = [dst; src];
    flags_set    = [OFlag; CFlag; SFlag; ZFlag; PFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "LogicalAnd";
    intel_asm    = (fun f -> f#ops "and" [dst; src]);
    att_asm      = (fun f -> f#ops "and" [src; dst])}

  (* OR r/m8,r8   ----- r/m8 OR r8                                    ---- 08/r
     OR r/m32,r32 ----- r/m32 OR r32                                  ---- 09/r
     OR r8,r/m8   ----- r8 OR r/m8                                    ---- 0A/r
     OR r32,r/m32 ----- r32 OR r/m32                                  ---- 0B/r
     OR AL,imm8   ----- AL or imm8                                    ---- 0C ib
     OR EAX,imm32 ----- EAX or imm32                                  ---- 0D id
     OR r/m8,imm8 ----- r/m8 OR r8                                    ---- 80/1 ib
     OR  r/m32,imm32 ---- r/m32 OR r32                                ---- 81/1 id
     OR  r/m32,imm8  ---- r/m32 or imm8 (sign-extended)               ---- 83/1 ib
  *)
  | LogicalOr (op1,op2) -> {
    docref       = "2A, 4-15";
    mnemonic     = "or";
    operands     = [op1; op2];
    flags_set    = [OFlag; CFlag; SFlag; ZFlag; PFlag];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "LogicalOr";
    intel_asm    = (fun f -> f#ops "or" [op1; op2]);
    att_asm      = (fun f -> f#ops "or" [op2; op1])}

  (* MFENCE --- Memory Fence                                     --- 0F AE F0 *)
  | MemoryFence -> {
    docref       = "2B, 4-22";
    mnemonic     = "mfence";
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "misc";
    long_name    = "MemoryFence";
    intel_asm    = (fun f -> f#no_ops "mfence");
    att_asm      = (fun f -> f#no_ops "mfence")}

  (* FEMMS    ---- Clear MMX state                         --- 0F 0E
     VMCPUID  ---- Illegal opcode used by virtual machines --- 0F C7 C8 01 00 *)
  | MiscOp name -> {
    docref       = "";
    mnemonic     = name;
    operands     = [];
    flags_set    = [];
    flags_used   = [];
    group_name   = "misc";
    long_name    = name;
    intel_asm    = (fun f -> f#no_ops name);
    att_asm      = (fun f -> f#no_ops name)}

  (* MOV r/m8,r8   ------ Move r8 to r/m8                            ---- 88/r
     MOV r/m32,r32 ------ Move r32 to r/m32                          ---- 89/r
     MOV r8,r/m8   ------ Move r/m8 to r8                            ---- 8A/r
     MOV r32,r/m32 ------ Move r/m32 to r32                          ---- 8B/r
     MOV r/m16,SREG ----  Move segment register to r/m16             ---- 8C/r
     MOV AL,moffs8  ----  Move byte at (seg:offset) to AL            ---- A0
     MOV EAX,moffs32 ---- Move doubleword at (seg:offset) to EAX     ---- A1
     MOV moffs8,AL   ---- Move AL to seg:offset                      ---- A2
     MOV moffs32,EAX ---- Mov EAX to (seg:offset)                    ---- A3
     MOV r8,imm8    ----- Move imm8 to r8                            ---- B0+rb
     MOV r32,imm32  ----- Move imm32 to r32                          ---- B8+rb
     MOV r/m8,imm8  ----  Move imm8 to r/m8                          ---- C6/0
     MOV r/m32,imm32 ---- Move imm32 to r/m32                        ---- C7/0
  *)
  | Mov (width,dst,src) -> {
    docref       = "2A, 3-667";
    mnemonic     = "mov";
    operands     = [dst; src];
    flags_set    = [];
    flags_used   = [];
    group_name   = "move";
    long_name    = "Move";
    intel_asm    = (fun f -> f#ops "mov" [dst; src]);
    att_asm      = (fun f -> f#ops "mov" [src; dst])}

  (* MOVD mm,r/m32 --- Move doubleword from r/m32 to mm            ---- 0F 6E/r
     MOVQ mm,mm/m64 -- Move quadword from mm/m64 to mm             ---- 0F 6F/r
     MOVD r/m32,mm --- Move doubleword from mm to r/m32            ---- 0F 7E/r
     MOVQ mm/m64,mm -- Move quadword from mm to mm/m64             ---- 0F 7F/r
     MOVD xmm,r/m32 -- Move doubleword from r/m32 to xmm           ---- 66 0F 6E/r
     MOVD r/m32,xmm -- Move doubleword from from xmm to r/m32      ---- 66 0F 7E/r
     MOVQ xmm1,xmm2/m64 --- Move quadword from xmm2/m64 to xmm1    ---- F3 0F 7E/r
     MOVQ xmm2/m64,xmm1 --- Move quadword from xmm1 to xmm2/mem64  ---- 66 0F D6/r
   *)
  | Movdw (width,op1,op2) ->
    let name = if width = 4 then "movd" else "movq" in
    {	docref       = "2A, 3-689";
	mnemonic     = name;
	operands     = [op1; op2];
	flags_set    = [];
	flags_used   = [];
	group_name   = "move";
	long_name    = "MoveDoubleword";
	intel_asm    = (fun f -> f#ops name [op1; op2]);
	att_asm      = (fun f -> f#ops name [op2; op1])}

  (* MOVDQA xmm1,xmm2/m128
     --- Move aligned double quadword from xmm2/m128 to xmm1     ---- 66 0F 6F/r
     MOVDQA xmm2/m128,xmm1
     --- Move aligned double quadword from xmm1 to xmm2/m128     ---- 66 0F 7F/r
     MOVDQU xmm1,xmm2/m128
     --- Move unaligned double quadword from xmm2/m128 to xmm1   ---- F3 0F 6F/r
     MOVDQU xmm2/m128,xmm1
     --- Move unaligned double quadword from xmm1 to xmm2/m128   ---- F3 0F 7F/r
  *)
  | Movdq (aligned,dst,src) ->
    let name = "movdq" ^ (if aligned then "a" else "u") in
    { docref       = "2A, 3-696";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "move";
      long_name    = "MoveDoubleQuadWord";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* MOVNTI m32,r32
     --- Move doubleword from r32 to m32 using non-temporal hint     ---- 0F C3/r
     MOVNTQ m64,mm
     --- Move quadword from mm to m64 using non-temporal hint        ---- 0F E7/r
     MOVNTDQA xmm1,m128
     --- Move double quadword from m128 to xmm using
         non-temporal hint                                     ---- 66 0F 38 2A/r
     MOVNTDQ m128,xmm
     --- Move double quadword from xmm to m128 using
         non-temporal hint                                        ---- 66 0F E7/r
  *)
  | Movnt (aligned,width,dst,src) ->
    let name = "movnt" ^ (match width with 4 -> "i" | 8 -> "q" | _ -> "dq") ^
      (if aligned then "a" else "") in
  { docref       = "2A, 3-724";
    mnemonic     = name;
    operands     = [dst; src];
    flags_set    = [];
    flags_used   = [];
    group_name   = "move";
    long_name    = "MoveNontemporalHint";
    intel_asm    = (fun f -> f#ops name [dst; src]);
    att_asm      = (fun f -> f#ops name [src; dst])}

  (* MOVS m8,m8    ----- move byte from address DS:[ESI] to ES:[EDI]     ---- A4
     MOVS m32,m32  ----- move dword from address DS:[ESI] to ES:[EDI]    ---- A5
  *)
  | Movs (width,dst,src,srcptr,dstptr) ->
    let name = "movs" ^ (width_suffix_string width) in
  { docref       = "2A, 3-746";
    mnemonic     = "movs";
    operands     = [dst; src; srcptr; dstptr];
    flags_set    = [];
    flags_used   = [];
    group_name   = "string operation";
    long_name    = "MoveString";
    intel_asm    = (fun f -> f#no_ops name);
    att_asm      = (fun f -> f#no_ops name)}

  (* MOVSX r32,r/m8 --- Move byte to doubleword with sign extension  ---- 0F BE
     MOVSX r32,r/m16 -- Move word to doubleword with sign extension  ---- 0F BF
  *)
  | Movsx (width,dst,src) -> {
    docref       = "2A, 3-763";
    mnemonic     = "movsx";
    operands     = [dst; src];
    flags_set    = [];
    flags_used   = [];
    group_name   = "move";
    long_name    = "MoveSignExtend";
    intel_asm    = (fun f -> f#ops "movsx" [dst; src]);
    att_asm      = (fun f -> f#ops "movsx" [src; dst])}

  (* MOVZX r32,r/m8 --- Move byte to doubleword with zero extension ---- 0F B6
     MOVZX r32,r/m16 -- Move word to doubleword with zero extension ---- 0F B7
  *)
  | Movzx (width,dst,src) -> {
    docref       = "2A, 3-772";
    mnemonic     = "movzx";
    operands     = [dst; src];
    flags_set    = [];
    flags_used   = [];
    group_name   = "move";
    long_name    = "MoveZeroExtend";
    intel_asm    = (fun f -> f#ops "movzx" [dst; src]);
    att_asm      = (fun f -> f#ops "movzx" [src; dst])}

  (* MUL r/m8  ---- Unsigned multiply: AX <- AL * r/m8               ---- F6/4
     MUL r/m32 ---- Unsigned multiply EDX:EAX <- EAX * r/m32         ---- F7/4
  *)
  | Mul (width,dst,src,op) ->
    {	docref       = "2A, 3-778";
	mnemonic     = "mul";
	operands     = [dst; src; op];
	flags_set    = [OFlag; CFlag; SFlag; ZFlag; PFlag];
                                                   (* SFlag, ZFlag, PFlag undefined *)
	flags_used   = [];
	group_name   = "integer arithmetic";
	long_name    = "UnsignedMultiply";
	intel_asm    = (fun f -> f#ops "mul" [op]);
	att_asm      = (fun f -> f#ops "mul" [op])}
  (* NOP (2 bytes)  -- 66 90
   * NOP (3 bytes)  -- 0F 1F 00
   * NOP (4 bytes)  -- 0F 1F 40 00
   * NOP (5 bytes)  -- 0F 1F 44 00 00
   * NOP (6 bytes)  -- 66 0F 1F 44 00 00
   * NOP (7 bytes)  -- 0F 1F 80 00 00 00 00
   * NOP (8 bytes)  -- 0F 1F 84 00 00 00 00 00
   * NOP (9 bytes)  -- 66 0F 1F 84 00 00 00 00 00
   *)
  | MultiByteNop width ->
     let name = "nop  (" ^ (string_of_int width) ^ " bytes)"    in
     {
      docref     = "?";
      mnemonic   = "nop";
      operands   = [];
      flags_set  = [];
      flags_used = [];
      group_name = "misc";
      long_name  = "MultiByteNop";
      intel_asm  = (fun f -> f#no_ops name);
      att_asm    = (fun f -> f#no_ops name) }

  (* NOT r/m8  --- Reverse each bit of r/m8                          ---- F6/2
     NOT r/m32 --- One's complement negate r/m32                     ---- F7/2
  *)
  | OnesComplementNegate op -> {
    docref       = "2A, 4-13";
    mnemonic     = "not";
    operands     = [op];
    flags_set    = [];
    flags_used   = [];
    group_name   = "bit operation";
    long_name    = "OnesComplementNegate";
    intel_asm    = (fun f -> f#ops "not" [op]);
    att_asm      = (fun f -> f#ops "not" [op])}

  (* OUTSB
     --- Output byte from memory location specified in
         DS:(E)SI or RSI to I/O port specified in DX                   ---- 6E
     OUTSD
     --- Output doubleword from memory location specified in
         DE:(E)SI or RSI to I/O port specified in DX                   ---- 6F
  *)
  | OutputStringToPort (width,op) ->
    let name = "outs" ^ (width_suffix_string width) in
    { docref       = "2A, 3-525";
      mnemonic     = name;
      operands     = [op; esi_r RW; dx_r RD];
      flags_set    = [];
      flags_used   = [];
      group_name   = "I/O";
      long_name    = "OutputStringToPort";
      intel_asm    = (fun f -> f#no_ops name);
      att_asm      = (fun f -> f#no_ops name)}

  (* OUT imm8,AL ---- Output byte in AL to I/O port address imm8           E6 ib
     OUT imm8,AX ---- Output word in AX to I/O port address imm8           E7 ib
     OUT imm8,EAX --- Output doubleword in EAX to I/O port address imm8    E7 ib

     OUT DX,AL   ---- Output byte in AL to I/O port address in DX          EE
     OUT DX,AX   ---- Output word in AX to I/O port address in DX          EF
     OUT DX,EAX  ---- Output doubleword in EAX to I/O port address in DX   EF *)

  | OutputToPort (width,port,src) -> {
    docref       = "2B 4-17";
    mnemonic     = "out";
    operands     = [port; src];
    flags_set    = [];
    flags_used   = [];
    group_name   = "I/O";
    long_name    = "OutputToPort";
    intel_asm    = (fun f -> f#ops "out" [port; src]);
    att_asm      = (fun f -> f#ops "out" [src; port])}


  (* PADDQ mm1,mm2/m64 --- Add quadword integer mm2/m64 to mm1      ---- 0F D4/r
     PADDUSB mm1,mm2/m64
     --- Add packed unsigned byte integers from mm/m64
         and mm and saturate the results                            ---- 0F DC/r
     PADDUSW mm1,mm2/m64
     --- Add packed unsigned word integers from mm/m64
         and mm and saturate the results                            ---- 0F DD/r
     PADDSB mm,m64
     --- Add packed signed byte integers from mm/m64
         and mm and saturate the result                             ---- 0F EC/r
     PADDSW mm,m64
     --- Add packed signed word integers from mm/m64
         and mm and saturate the result                             ---- 0F ED/r
     PADDB mm,mm/m64
     --- Add packed byte integers from mm/m64 and mm                ---- 0F FC/r
     PADDW mm,mm/m64
     --- Add packed word integers from mm/m64 and mm                ---- 0F FD/r
     PADDD mm,mm/m64
     --- Add packed doubleword integers from mm/m64 and mm          ---- 0F FE/r

     PADDQ xmm1,xmm2/m128
     --- Add packed quadword integers xmm2/m128 to xmm1          ---- 66 0F D4/r
     PADDUSB xmm1,xmm1/m128
     --- Add packed unsigned byte integers from xmm2/m128
         and xmm1 and saturate the results                       ---- 66 0F DC/r
     PADDUSW xmm1,xmm1/m128
     --- Add packed unsigned word integers from xmm2/m128
     and xmm1 and saturate the results                           ---- 66 0F DD/r
     PADDSB xmm1,xmm1/m128
     --- Add packed signed byte integers from xmm2/m128
         and xmm1 and saturate the results                       ---- 66 0F EC/r
     PADDSW xmm1,xmm1/m128
     --- Add packed signed word integers from xmm2/m128
         and xmm1 and saturate the results                       ---- 66 0F ED/r
     PADDB xmm1,xmm2/m128
     ---  Add packed byte integers from xmm2/m128 and xmm1 -      --- 66 0F FC/r
     PADDW xmm1,xmm2/m128
     ---  Add packed word integers from xmm2/m128 and xmm1       ---- 66 0F FD/r
     PADDD xmm1,xmm2/m128
     ---  Add packed doubleword integers from xmm2/m128 and xmm1 ---- 66 0F FE/r

     ss: signed saturation
     us: unsigned saturation
     width: width of packed entries
  *)
  | PackedAdd (ss,us,width,dst,src) ->
     let name =
       "padd" ^ (signed_saturation_infix ss) ^ (unsigned_saturation_infix us) ^
      (width_suffix_string width) in
    { docref       = "2B";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "packed integer";
      long_name    = "PackedAdd";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* PCMPGTB mm1,mm2/m64
     --- Compare packed signed byte integers in mm1 and mm2/m64
         for greater than and store result in mm1                  ---- 0F 64/r
     PCMPGTW mm1,mm2/m64
     --- Compare packed signed word integers in mm1 and mm2/m64
     for greater than and store result in mm1                      ---- 0F 65/r
     PCMPGTD mm1,mm2/m64
     --- Compare packed signed doubleword integers in mm1 and
         mm2/m64 and store result in mm1                           ---- 0f 66/r
     PCMPEQB mm,mm/m64
     --- Compare packed bytes in mm/m64 and mm for equality        ---- 0F 74/r
     PCMPEQW mm,mm/m64
     --- Compare packed words in mm/m64 and mm for equality        ---- 0F 75/r
     PCMPEQD mm,mm/m64
     --- Compare packed doublewords in mm/m64 and mm for equality  ---- 0F 76/r

     PCMPEQQ xmm1,xmm2/m128
     --- Compare packed qwords in xmm2/m128 and xmm1
         for equality                                        ---- 66 0F 38 29/r
     PCMPGTQ xmm1,xmm2/m128
     --- Compare packed qwords in xmm2/m128 and
         xmm1 for greater than                               ---- 66 0F 38 37/r

     PCMPGTB xmm1,xmm2/m128
     --- Compare packed signed byte integers in xmm1 and
         xmm2/m128 for greater than and store the result
         in xmm1                                                ---- 66 0F 64/r
     PCMPGTW xmm1,xmm2/m128
     --- Compare packed signed word integers in xmm1 and
         xmm2/m128 for greater than and store the result
         in xmm1                                                ---- 66 0F 65/r
     PCMPGTD xmm1,xmm2/m128
     --- Compare packed signed doubleword integers in
         xmm1 and xmm2/m128 for greater than and store
         the result in xmm1                                     ---- 66 0F 66/r
     PCMPEQB xmm1,xmm2/m128
     --- Compare packed bytes in xmm2/m128 and xmm1
         for equality                                           ---- 66 0F 74/r
     PCMPEQW xmm1,xmm2/m128
     --- Compare packed words in xmm2/m128 and xmm1
         for equality                                           ---- 66 0F 75/r
     PCMPEQD xmm1,xmm2/m128
     --- Compare packed doublewords in xmm2/m128 and xmm1
         for equality                                           ---- 66 0F 76/r

     pred : predicate to be used for comparison (eq or gt)
     width: width of the packed entries
  *)
  | PackedCompare (pred,width,dst,src) ->
    let name = "pcmp" ^ pred ^ (width_suffix_string width) in
    { docref       = "2B, 4-88";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "packed integer";
      long_name    = "PackedCompare" ^ pred;
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* PCMPESTRI xmm1, xmm2/m128, imm8 (op1:reg, op2:rm)  ---- 66 0F 3A 61/r imm8
     Perform a packed comparison of string data with explicit lengths, generating
     an index, and storing the result in ECX.

     PCMPESTRM xmm1, xmm2/m128, imm8 (op1:reg, op2:rm)  ---- 66 0F 3A 60/r imm8
     Perform a packed comparison of string data with explicit lengths, generating
     a mask, and storing the result in XMM0

     PCMPISTRI xmm1, xmm2/m128, imm8 (op1:reg, op2:rm)  ---- 66 0F 3A 63/r imm8
     Perform a packed comparison of string data with implicit lengths, generating
     an index, and storing the result in ECX.

     PCMPISTRM xmm1, xmm2/m128, imm8 (op1:reg, op2:rm)  ---- 66 0F 3A 62/r imm8
     Perform a packed comparison of string data with implicit lengths, generating
     a mask, and storing the result in XMM0.

     explicit : true: explicit length; false: implicit length
     index    : true: result is an index saved in ecx
                false: result is a mask saved in xmm0
  *)
  | PackedCompareString (explicit,index,op1,op2,controlbyte) ->
    let echar = if explicit then "e" else "i" in
    let ichar = if index then "i" else "m" in
    let ename = if explicit then "explicit" else "implicit" in
    let iname = if index then "index" else "mask" in
    let name = "pcmp" ^ echar ^ "str" ^ ichar in
    let dstop = if index then ecx_r WR else xmm_register_op 0 WR in
    let srcops = if explicit then [eax_r RD; edx_r RD] else [] in
    { docref = "2B, 4-94";
      mnemonic = name;
      operands = [op1; op2; controlbyte; dstop] @ srcops;
      flags_set = [CFlag; SFlag; ZFlag; PFlag; OFlag];
      flags_used = [];
      group_name = "packed string";
      long_name = "PackedCompareString_" ^ ename ^ "_" ^ iname;
      intel_asm = (fun f -> f#ops name [op1; op2; controlbyte]);
      att_asm = (fun f -> f#ops name [op1; op2; controlbyte])}

  (* PACKSSWB mm1,mm2/m64
     --- Converts 4 packed signed word integers from
         mm1 and from mm2/m64 into 8 packed signed byte
         integers in mm1 using signed saturation.                      --- 0F 63

     PACKUSWB mm,mm/m64
     --- Converts 4 signed word integers from mm
         and 4 signed word integers from mm/m64 into
         8 unsigned byte integers in mm using unsigned
         saturation.                                                  ---- 0F 67

     PACKSSDW mm1,mm2/m64
     --- Converts 2 packed signed doubleword integers
         from mm1 and from mm2/m64 into 4 packed signed
         word integers in mm1 using signed saturation.                ---- 0F 6B

     PACKSSWB xmm1,xmm2/m128
     --- Converts 8 packed signed word integers
         from xmm1 and from xxm2/m128 into 16 packed
         signed byte integers in xxm1 using signed
         saturation.                                             ---- 66 0F 63/r

     PACKUSWB xmm1,xmm2/m128
     --- Converts 8 signed word integers from xmm1
         and 8 signed word integers from xmm2/m128
         into 16 unsigned byte integers
         in xmm1 using unsigned saturation                       ---- 66 0F 67/r

     PACKSSDW xmm1,xmm2/m128
     --- Converts 4 packed signed doubleword integers
         from xmm1 and from xxm2/m128 into 8 packed
         signed word integers in xxm1 using signed
         saturation                                              ---- 66 0f 6B/r

  *)
  | PackedConvert (ty,dst,src) -> {
    docref         = "page 120";
    mnemonic       = "pack" ^ ty;
    operands       = [dst; src];
    flags_set      = [];
    flags_used     = [];
    group_name     = "packed integer";
    long_name      = "PackedConvert";
    intel_asm      = (fun f -> f#ops ("pack" ^ ty) [dst; src]);
    att_asm        = (fun f -> f#ops ("pack" ^ ty) [src; dst])}

  (*  PEXTRW reg,mm,imm8
      --- Extract the word specified by imm8 from mm and
          move it to reg, bits 15-0                              ---- 0F C5/r ib
      PEXTRB reg/m8,xmm2,imm8
      --- Extract a byte integer value from xmm2 at
          the source byte offset specified by imm8
          into reg or m8                                      ---- 66 0F 3A 14/r
      PEXTRD r/m32,xmm2,imm8
      --- Extract a dword integer value from xmm2 at
          the source dword offset specified by imm8
          into r/m32                                           ---- 66 0F 3A 16/r
      PEXTRW reg,xmm,imm8
      ---- Extract the word specified by imm8 from xmm and
           move it to reg bits 15-0                            ---- 66 0F C5/r ib
  *)
  | PackedExtract (width,dst,src,selector) ->
    let name = "pextr" ^ (width_suffix_string width)  in
    { docref       = "2B, 4-114";
      mnemonic     = name;
      operands     = [dst; src; selector];
      flags_set    = [];
      flags_used   = [];
      group_name   = "packed integer";
      long_name    = "PackedExtract";
      intel_asm    = (fun f -> f#ops name [dst; src; selector]);
      att_asm      = (fun f -> f#ops name [src; selector; dst])}

  (* PALIGNR mm1,mm2/m64,imm8
     --- Concatenate destination and source
         operands, extract byte-aligned result
         shifted to the right by imm8 into mm1                    ---- 0F 3A 0F
     PALIGNR xmm1,xmm2/m128,imm8
     --- Concatenate destination and source operands,
         extract byte-aligned result shifted to the
         right by constant value imm8 into xmm1                ---- 66 0F 3A 0F
  *)
  | PackedAlignRight (dst,src,shift) -> {
    docref       = "2B, 4-62";
    mnemonic    = "palignr";
    operands     = [dst; src; shift];
    flags_set    = [];
    flags_used   = [];
    group_name   = "packed integer";
    long_name    = "PackedAlignRight";
    intel_asm    = (fun f -> f#ops "palignr" [dst; src; shift]);
    att_asm      = (fun f -> f#ops "palignr" [src; shift; dst])}

  (* PINSRW mm,r32/m16,imm8
     --- Insert the low word from r32 or
         from m16 into mm at the word position
         specified by imm8                                       ---- 0F C4/r ib
     PINSRB xmm1,r/m32,imm8
     --- Insert a byte integer value from r/m32
         into xmm1 at the destination element
         specified by imm 8                                ---- 66 0F 3A 20/r ib
     PINSRD xmm1,r/m32,imm8
     --- Insert a dword integer value from r/m32
         into xmm1 at the destination element
         specified by imm 8                                ---- 66 0F 3A 22/r ib
     PINSRW mm,r32/m16,imm8
     --- Insert the low word from r32 or from m16
         into mm at the word position specified by imm8       ---- 66 0F C4/r ib
  *)
  | PackedInsert (width,dst,src,extop) ->
    let name = "pinsr" ^ (width_suffix_string width) in
    { docref       = "2B, 4-137";
      mnemonic     = name;
      operands     = [dst; src; extop];
      flags_set    = [];
      flags_used   = [];
      group_name   = "packed integer";
      long_name    = "PackedInsert";
      intel_asm    = (fun f -> f#ops name [dst; src; extop]);
      att_asm      = (fun f -> f#ops name [src; extop; dst])}

  (* ROUNDSD xmm1, xmm2/m64, imm8
     ---  Round the low packed double precision
          floating-point value in xmm2/m64 and
          place the result in xmm1. The rounding
          mode is determined by imm8.                      ---- 66 0F 3A 0B/r ib
  *)
  | PackedRoundScalarDouble (dst, src, roundingmode) ->
    { docref       = "2B, 4-326";
      mnemonic     = "roundsd";
      operands     = [dst; src; roundingmode];
      flags_set    = [];
      flags_used   = [];
      group_name   = "packed integer";
      long_name    = "PackedRoundScalarDouble";
      intel_asm    = (fun f -> f#ops "roundsd" [dst; src; roundingmode]);
      att_asm      = (fun f -> f#ops "roundsd" [src; roundingmode; dst])}


  (* PSHUFB mm1,mm2/m64
     --- Shuffle bytes in mm1 according to contents of mm2/m64   ---- 0F 38 00/r
     PSHUFW mm1,mm2/m64,imm8
     --- Shuffle the words in mm2/m64 based on the encoding
         in imm8 and store the result in mm1                     ---- 0F 70/r ib
     PSHUFB xmm1,xmm2/m128
     --- Shuffle bytes in xmm1 according to contents
         of xmm2/m128                                         ---- 66 0F 38 00/r
     PSHUFD xmm1,xmm2/m128,imm8
     --- Shuffle the doubleword in xmm2/m128 based on
         the encoding in imm8 and store the result in xmm1    ---- 66 0F 70/r ib
     PSHUFLW xmm1,xmm2/m128,imm8
     --- Shuffle the low words in xmm2/m128 based on
         the encoding in imm8 and store the result in xmm1    ---- F2 0F 70/r ib
     PSHUFHW xmm1,xmm2/m128,imm8
     --- Shuffle the high words in xmm2/m128 based on
         the encoding in imm8 and store the result in xmm1    ---- F3 0F 70/r ib
  *)
  | PackedShuffle (suffix,dst,src,optEncoding) ->
    let name = "pshuf" ^ suffix in
    let ops = match optEncoding with
      | Some encoding -> [dst; src; encoding] | _ -> [dst; src] in
    { docref       = "2B, 4-246";
      mnemonic     = name;
      operands     = ops;
      flags_set    = [];
      flags_used   = [];
      group_name   = "packed integer";
      long_name    = "PackedShuffle";
      intel_asm    = (fun f -> f#ops name ops);
      att_asm      = (fun f -> f#ops name (match optEncoding with
	Some encoding -> [src; encoding; dst] | _ -> [src; dst]))}

  (* PMULHRSW mm1,mm2/m64
     --- Multiply 16-bit signed words, scale and round
         signed doublewords, pack high 16 bits to mm1            ---- 0F 38 0B/r
     PMULLW mm,mm/m64
     --- Multiply packed signed word integers in mm1 and mm2/m64,
         store the low 16 bits in mm1                            ---- 0F D5/r
     PMULHUW mm1,mm2/m64
     --- Multiply the packed unsigned word integers in
         mm1 and mm2/m64 and store high 16 bits in mm1           ---- 0F E4/r
     PMULHW mm1,mm2/m64
     --- Multiply the packed signed word integers in
         mm1 and mm2/m64 and store high 16 bits in mm1           ---- 0F E5/r
     PMULUDQ mm1,mm2/m64
     --- Multiply unsigned doubleword integer in mm1 by
         unsigned doubleword integer in mm2/m64, and store
	 the quadword result in mm1                              ---- 0F F4/r
     PMULHRSW xmm1,xmm2/m128
     --- Multiply 16-signed words, scale and round
         signed doublewords, pack high 16 bits in xmm1        ---- 66 0F 38 0B/r
     PMULDQ xmm1,xmm2/m128
     --- Multiply packed signed dword integers in
         xmm1 and xmm2/m128                                   ---- 66 0F 38 28/r
     PMULLD xmm1,xmm2/m128
     --- Multiply packed dword signed integers in xmm1
         and xmm2/m128 and store the low 32 bits of
         each in xmm1                                         ---- 66 0F 38 40/r
     PMULLW xmm1,xmm2/m128
     --- Multiply packed signed word integers in xmm1 and
         xmm2/m128 and store low 16 bits in xmm1                 ---- 66 0F D5/r
     PMULHUW xmm1,xmm2/m128
     --- Multiply packed unsigned word integers in xmm1
         and xmm2/m128 and store the high 16 bits in xmm1        ---- 66 0F E4/r
     PMULHW xmm1,xmm2/m128
     --- Multiply packed signed word integers in xmm1
         and xmm2/m128 and store the high 16 bits in xmm1        ---- 66 0F E5/r
     PMULUDQ xmm1,xmm2/m128
     --- Multiply packed unsigned doubleword integers in
         xmm1 by packed unsigned doubleword integers in
         xmm2/m128 and store quadword result in xmm1             ---- 66 0F F4/r
  *)
  | PackedMultiply (suffix,dst,src) ->
    let name = "pmul" ^ suffix in
    { docref       = "2B, 4-197";
      mnemonic     = name;
      operands     = [dst; src];
      flags_set    = [];
      flags_used   = [];
      group_name   = "packed integer";
      long_name    = "PackedMultiply";
      intel_asm    = (fun f -> f#ops name [dst; src]);
      att_asm      = (fun f -> f#ops name [src; dst])}

  (* PABSB mm1,mm2/m64
     --- Compute absolute value of byte mm2/m64
         and store unsigned result in mm1                        ---- 0F 38 1C/r
     PABSW mm1,mm2/m64
     --- Compute absolute value of 16-bit integers
         in mm2/m64 and store unsigned result in mm1             ---- 0F 38 1D/r
     PABSD mm1,mm2/m64
     --- Compute absolute value of 32-bit integers
         in mm2/m64 and store unsigned result in mm1             ---- 0F 38 1E/r
     PAND mm1,mm2/m64
     --- Bitwise and of mm2/m64 and mm1                          ---- 0F DB/r
     PANDN mm1,mm2/m64
     --- Bitwise and not of mm2/m64 and mm1                      ---- 0F DF/r
     PAVGB mm1,mm2/m64
     --- Average packed unsigned byte integers from mm2/m64
         and mm1 with rounding                                   ---- 0F E0/r
     PAVGW mm1,mm2/m64
     --- Average packed unsigned word integers from mm2/m64
         and mm1 with rounding                                   ---- 0F E3/r
     POR mm,mm/m64
     --- Bitwise OR of mm/m64 and mm                             ---- 0F EB/r
     PMAX mm1,mm2/m64
     --- Compare signed word integers in mm2/m64 and
         mm1 and return maximum values                           ---- 0F EE/r
     PXOR mm1,mm2/m64
     --- Bitwise XOR of mm1 and mm2/m64                          ---- 0F EF/r
     PMADDWD mm,mm/m64
     --- Multiply the packed words in mm by the packed
         words in mm/m64, add adjacent doubleword
         and store in mm                                         ---- 0F 5F/r
     PSADBW mm1,mm2/m64
     --- Computes the absolute differences of the
         packed unsigned byte integers from mm2/m64
         and mm1; differences are then summed to produce
         an unsigned word integer result                          ---- 0F 6F/r

     PABSB xmm1,xmm2/m128
     --- Compute absolute value of bytes in xmm2/m128
         and store unsigned result in xmm1                    ---- 66 0F 38 1C/r
     PABSW xmm1,xmm2/m128
     --- Compute absolute value of 16-bit integers in
         xmm2/m128 and store unsigned result in xmm1          ---- 66 0F 38 1D/r
     PABSD xmm1,xmm2/m128
     --- Compute absolute value of 32-bit integers in
         xmm2/m128 and store unsigned result in xmm1          ---- 66 0F 38 1E/r
     MOVMSKPD reg,xmm
     --- Extract 2-bit sign mask from xmm and store in
         reg. The upper bits of r32 are filled with zeros        ---- 66 0F 50/r

     PMOVMSKB reg,xmm
     --- Move a byte mask of xmm to reg. The upper
         bits of r32 or r64 are zeroed                           ---- 66 0F D7/r
     PAND xmm1,xmm2/m128
     --- Bitwise AND of xmm2/m128 and xmm1                       ---- 66 0F DB/r
     PANDN xmm1,xmm2/m128
     --- Bitwise AND NOT of xmm2/m128 and xmm1                   ---- 66 0F DF/r
     PAVGB xmm1,xmm2/m128
     --- Average packed unsigned byte integers from
         xmm2/m128 and xmm1 with rounding                        ---- 66 0F E0/r
     PAVGW xmm1,xmm2/m128
     --- Average packed unsigned word integers from
         xmm2/m128 and xmm1 with rounding                        ---- 66 0F E3/r
     POR xmm1,xmm2/m128
     ----- Bitwise OR of xmm1/m128 and xmm1                      ---- 66 0F EB/r
     PMAX xmm1,xmm2/m128
     ---- Compare signed word integers in xmm2/m128 and
          xmm1 and return maximum values.                        ---- 66 0F EE/r
     PXOR xmm1,xmm2/m128
     ---- Bitwise XOR of xmm2/m128 and xmm1                      ---- 66 0F EF/r
*)
 | PackedOp (opname,width,dst,src) ->
   let name = "p" ^ opname ^ (width_suffix_string width) in
   { docref       = "2B";
     mnemonic     = name;
     operands     = [dst; src];
     flags_set    = [];
     flags_used   = [];
     group_name   = "packed integer";
     long_name    = "Packed:" ^ opname;
     intel_asm    = (fun f -> f#ops name [dst; src]);
     att_asm      = (fun f -> f#ops name [src; dst])}

  (* PSRLW mm,imm8
     --- Shift words in mm right imm8 while shifting in 0s       ---- 0F 71/2 ib
     PSRAW mm,imm8
     --- Shift words in mm right by imm8 while shifting in sign
         bits                                                    ---- 0F 71/4 ib
     PSLLW mm,imm8
     --- Shift words in mm left imm8 while shifting in 0s        ---- 0F 71/6 ib
     PSRLD mm,imm8
     --- Shift doublewords in mm right by imm8 while shifting
         in 0s                                                   ---- 0F 72/2 ib
     PSRAD mm,imm8
     --- Shift doublewords in mm right by imm8 while shifting
         in sb                                                   ---- 0F 72/4 ib
     PSLLD mm,imm8
     --- Shift doublewords in mm left by imm8 while shifting
         in 0s                                                   ---- 0F 72/6 ib
     PSRLQ mm,imm8
     --- Shift mm right by imm8 while shifting in 0s             ---- 0F 73/2 ib
     PSLLQ mm,imm8
     --- Shift quadword in mm left by imm8 while shifting
         in 0s                                                   ---- 0F 73/6 ib

     PSRLW mm,mm/m64
     --- Shift words in mm right by mm/m64                          ---- 0F D1/r
     PSRLD mm,mm/m64
     --- Shift doublewords in mm right by mm/m64                    ---- 0F D2/r
     PSRLQ mm,mm/m64
     --- Shift mm right by mm/m64                                   ---- 0F D3/r
     PSRAW mm1,mm2/m64
     --- Shift words in mm right by mm/mm64                         ---- 0F E1/r
     PSRAD mm1,mm2/m64
     --- Shift doublewords in mm right by mm/mm64                   ---- 0F E2/r
     PSLLW mm,mm/m64
     --- Shift words in mm left by mm/m64                           ---- 0F F1/r
     PSLLD mm,mm/m64
     --- Shift doublewords in mm left by mm/m64                     ---- 0F F2/r
     PSLLQ mm,mm/m64
     --- Shift qword in mm left by mm/m64                           ---- 0F F3/r

     PSRLW xmm1,imm8
     --- Shift words in xmm1 right by imm8		      ---- 66 0F 71/2 ib
     PSRAW xmm1,imm8
     --- Shift words in xmm1 right by imm8                    ---- 66 0F 71/4 ib
     PSLLW xmm1,imm8
     --- Shift words in xmm1 left by imm8                     ---- 66 0F 71/6 ib
     PSRLD xmm1,imm8
     --- Shift doublewords in xmm1 right by imm8              ---- 66 0F 72/2 ib
     PSRAD xmm1,imm8
     --- Shift doublewords in xmm1 right by imm8              ---- 66 0F 72/4 ib
     PSLLD xmm1,imm8
     --- Shift doublewords in xmm1 left by imm8               ---- 66 0F 72/6 ib
     PSRLQ xmm1,imm8
     --- Shift doublewords in xmm1 right by imm8              ---- 66 0F 73/2 ib
     PSRLDQ xmm1,imm8
     --- Shift xmm1 right by imm8 while shifting in 0s        ---- 66 0F 73/3 ib
     PSLLQ  xmm1,imm8
     --- Shift quadword in xmm left by imm8 while shifting
         in 0s                                                ---- 66 0F 73/6 ib
     PSLLDQ xmm1,imm8
     --- Shift xmm1 left by imm8 while shifting in 0s         ---- 66 0F 73/7 ib
     PSRLW xmm1,xmm2/m128
     --- Shift words in xmm1 right by xmm2/m128               ---- 66 0F D1/r
     PSRLD xmm1,xmm2/m128
     --- Shift doublewords right by xmm2/m128                 ---- 66 0F D2/r
     PSRLQ xmm1,xmm2/m128
     --- Shift quadwords right by xmm2/m128                   ---- 66 0F D3/r
     PSRAW xmm1,xmm2/m128
     --- Shift words in xmm1 right by xmm2/m128               ---- 66 0F E1/r
     PSRAD xmm1,xmm2/m128
     --- Shift doublewords in xmm1 right by xmm2/m128         ---- 66 0F E2/r
     PSLLW xmm1,xmm2/m128
     --- Shift words in xmm1 left by xmm2/m128                ---- 66 0F F1/r
     PSLLD xmm1,xmm2/m128
     --- Shift doublewords in xmm1 left by xmm1/m128          ---- 66 0F F2/r
     PSLLQ xmm1,xmm2/m128
     --- Shift quadwords in xmm1 left by xmm1/m128            ---- 66 0F F3/r

     dir : direction and type of shift:
           "ll" : left logical
           "rl" : right logical
           "ra"; right arithmetic
     width: width of packed entries
  *)
 | PackedShift (dir,width,dst,src) ->
   let name = "ps" ^ dir ^ (width_suffix_string width) in
   { docref       = "2B, 4-268";
     mnemonic     = name;
     operands     = [dst; src];
     flags_set    = [];
     flags_used   = [];
     group_name   = "packed integer";
     long_name    = "PackedShift" ^ dir;
     intel_asm    = (fun f -> f#ops name [dst; src]);
     att_asm      = (fun f -> f#ops name [src; dst])}

  (* PSUBUSB mm,mm/m64
     --- Subtract unsigned packed bytes in mm/m64 from
         unsigned packed bytes in mm and saturate results         ---- 0F D8/r
     PSUBUSW mm,mm/m64
     --- Subtract unsigned packed bytes in mm/m64 from
         unsigned packed bytes in mm and saturate results         ---- 0F D9/r
     PSUBSB mm,mm/m64
     --- Subtract signed packed bytes in mm/m64 from signed
         packed bytes in mm and saturate results                  ---- 0F E8/r
     PSUBSW mm,mm/m64
     --- Subtract signed packed words in mm/m64 from signed
         packed bytes in mm and saturate results                  ---- 0F E9/r
     PSUBB mm,mm/m64
     --- Subtract packed byte integers in mm/m64 from
         packed byte integers in mm                               ---- 0F F8/r
     PSUBW mm,mm/m64
     --- Subtract packed word integers in mm/m64 from
         packed word integers in mm                               ---- 0F F9/r
     PSUBD mm,mm/m64
     --- Subtract packed doubleword integers in mm/m64 from
         packed doubleword integers in mm                         ---- 0F FA/r
     PSUBQ mm,mm/m64
     --- Subtract quadword integer in mm from mm2/m64             ---- 0F FB/r

     PSUBUSB xmm1,xmm2/m128
     --- Subtract packed unsigned byte integers in
         xmm2/m128 from packed unsigned integers in
         xmm1 and saturate results                               ---- 66 0F D8/r
     PSUBUSW xmm1,xmm2/m128
     --- Subtract packed unsigned word integers in
         xmm2/m128 from packed unsigned integers in
         xmm1 and saturate results                               ---- 66 0F D9/r
     PSUBSB xmm1,xmm2/m128
     --- Subtract packed signed byte integers in xmm2/m128
         from packed signed byte integers in xmm1 and
         saturate results                                        ---- 66 0F E8/r
     PSUBSB xmm1,xmm2/m128
     --- Subtract packed signed word integers in xmm2/m128
         from packed signed word integers in xmm1 and
         saturate results                                        ---- 66 0F E9/r
     PSUBB xmm1, xmm2/m128
     --- Subtract packed byte integers in xmm2/m128
         from packed byte integers in xmm1                       ---- 66 0F F8/r
     PSUBW xmm1, xmm2/m128
     --- Subtract packed word integers in xmm2/m128
         from packed word integers in xmm1                       ---- 66 0F F9/r
     PSUBD xmm1, xmm2/m128
     --- Subtract packed doubleword integers in xmm2/m128
         from packed doubleword integers in xmm1                 ---- 66 0F FA/r
     PSUBQ xmm1,xmm2/m128
     --- Subtract packed quadword integers in xmm2/m128
         from packed quadword integers in xmm1                   ---- 66 0F FB/r

     ss: signed saturation
     us: unsigned saturation
     width: width of packed entries
  *)
 | PackedSubtract (ss,us,width,dst,src) ->
    let name =
      "psub" ^ (signed_saturation_infix ss) ^ (unsigned_saturation_infix us) ^
     (width_suffix_string width) in
   { docref       = "2B, 4-296";
     mnemonic     = name;
     operands     = [dst; src];
     flags_set    = [];
     flags_used   = [];
     group_name   = "packed integer";
     long_name    = "PackedSubtract";
     intel_asm    = (fun f -> f#ops name [dst; src]);
     att_asm      = (fun f -> f#ops name [src; dst])}

  (* PUNPCKLBW mm,mm/m32
     --- Interleave low-order doublewords from mm and mm/m32
         into mm                                                    ---- 0F 60/r
     PUNPCKLWD mm,mm/m32
     --- Interleave low-order doublewords from mm and mm/m32
     into mm                                                        ---- 0F 61/r
     PUNPCKLDQ mm,mm/m32
     --- Interleave low-order doublewords from mm and mm/m32
         into mm                                                    ---- 0F 62/r
     PUNPCKHBW mm,mm/m64
     --- Unpack and interleave high-order bytes from mm and
         mm/m64 into mm                                             ---- 0F 68/r
     PUNCHKHWD mm,mm/m64
     --- Unpack and interleave high-order words from mm and
         mm/m64 into mm                                             ---- 0F 69/r
     PUNCHKHDQ mm,mm/m64
     --- Unpack and interleave high-order doublewords from
         mm and mm/m64 into mm                                      ---- 0F 6A/r

     PUNPCKLBW xmm1,xmm2/m128
     --- Interleave low-order bytes from xmm1 and
         xmm2/m128 into xmm1                                     ---- 66 0F 60/r
     PUNPCKLWD xmm1,xmm2/m128
     --- Interleave low-order words from xmm1 and
         xmm2/m128 into xmm1                                     ---- 66 0F 61/r
     PUNPCKLDQ xmm1,xmm2/m128
     --- Interleave low-order doublewords from xmm1
         and xmm2/m128 into xmm1                                 ---- 66 0F 62/r
     PUNPCKHBW xmm1,xmm1/m128
     --- Unpack and interleave high-order bytes
         from xmm1 and xmm2/m128 into xmm1                       ---- 66 0F 68/r
     PUNPCKHWD xmm1,xmm1/m128
     --- Unpack and interleave high-order words
         from xmm1 and xmm2/m128 into xmm1                       ---- 66 0F 69/r
     PUNPCKHDQ xmm1,xmm1/m128
     --- Unpack and interleave high-order doublewords
         from xmm1 and xmm2/m128 into xmm1                       ---- 66 0F 6A/r
     PUNPCKHQDQ xmm1,xmm1/m128
     --- Unpack and interleave high-order bytes
         from xmm1 and xmm2/m128 into xmm1                       ---- 66 0F 6D/r
  *)
 | Unpack (hilo,width,dst,src) ->
    let name =
      "punpck"
      ^ hilo
      ^ (match width with
         | 1 -> "bw"
         | 2 -> "wd"
         | 4 -> "dq"
         | _ -> "qdq") in
   { docref       = "2B, 4-307";
     mnemonic     = name;
     operands     = [dst; src];
     flags_set    = [];
     flags_used   = [];
     group_name   = "packed integer";
     long_name    = "Unpack";
     intel_asm    = (fun f -> f#ops name [dst; src]);
     att_asm      = (fun f -> f#ops name [src; dst])}

  (* POP ES ---- Pop Extra segment register                          ---- 07
     POP SS  --- Pop stack segment regiter                           ---- 17
     POP DS  --- Pop data segment register                           ---- 1F
     POP FS  --- Pop FS                                              ---- 0F A1
     POP GS  --- Pop GS                                              ---- 0F A9
     POP r32 --- Pop top of stack into r32; increment stack pointer  ---- 58+rd
     POP r/m32 - Pop top of stack into m32, increment stack pointer  ---- 8F/0
  *)
 | Pop (_,op) -> {
   docref       = "2A, 4-220";
   mnemonic     = "pop";
   operands     = [op; esp_r RW; esp_deref RD];
   flags_set    = [];
   flags_used   = [];
   group_name   = "move";
   long_name    = "Pop";
   intel_asm    = (fun f -> f#ops "pop" [op]);
   att_asm      = (fun f -> f#ops "pop" [op])}

  (* POPF  ---- Pop top of stack into EFLAGS                          ---- 9D *)
 | PopFlags -> {
   docref       = "2A, 4-232";
   mnemonic     = "popf";
   operands     = [esp_r RW ; esp_deref RD];
   (* restored from the stack *)
   flags_set    = [CFlag; ZFlag; SFlag; OFlag; PFlag];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "PopFlags";
   intel_asm    = (fun f -> f#no_ops "popf");
   att_asm      = (fun f -> f#no_ops "popf")}

  (* POPA --- Pop EDI, ESI, EBP, EBX, EDX, ECX, and EAX                --- 61 *)
 | PopRegisters -> {
   docref       = "page 1285";
   mnemonic     = "popa";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "move";
   long_name    = "PopRegisters";
   intel_asm    = (fun f -> f#no_ops "popa");
   att_asm      = (fun f -> f#no_ops "popa")}

  (* PREFETCHNTA m8
     --- move data from m8 closer to the processor using NTA hint   ---- 0F 18/0
     PREFETCHT0 m8
     --- move data from m8 closer to the processor using T0 hint    ---- 0F 18/1
     PREFETCHT1 m8
     --- move data from m8 closer to the processor using T1 hint    ---- 0F 18/2
     PREFETCHT2 m8
     --- move data from m8 closer to the processor using T2 hint    ---- 0F 18/3
  *)
 | Prefetch (suffix,op) ->
   let name = "prefetch" ^ suffix in
   { docref       = "2A, 4-239";
     mnemonic     = name;
     operands     = [op];
     flags_set    = [];
     flags_used   = [];
     group_name   = "misc";
     long_name    = "PrefetchDataIntoCaches";
     intel_asm    = (fun f -> f#ops name [op]);
     att_asm      = (fun f -> f#ops name [op])}

  (* PUSH ES --- Push Extra segment register                         ---- 06
     PUSH CS --- Push Code segment register                          ---- 0E
     PUSH SS --- Push stack segment register                         ---- 16
     PUSH DS --- Push data segment register                          ---- 1E
     PUSH FS --- Push FS                                             ---- 0F A0
     PUSH GS --- Push GS                                             ---- 0F A8
     PUSH r32 -- Push r32                                            ---- 50+rd
     PUSH imm32 - Push sign-extended imm32                           ---- 68
     PUSH imm8 -- Push sign-extended imm8                            ---- 6A
     PUSH r/m32 - Push r/m32                                         ---- FF/6
  *)
 | Push (size,op) -> {
   docref       = "2A, 4-319";
   mnemonic     = "push";
   operands     = [op; esp_deref ~with_offset:(-(size)) WR; esp_r RW];
   flags_set    = [];
   flags_used   = [];
   group_name   = "move";
   long_name    = "Push";
   intel_asm    = (fun f -> f#ops "push" [op]);
   att_asm      = (fun f -> f#ops "push" [op])}

  (* PUSHA --- Push EAX, ECX, EDX, EBX, original ESP, EBP, ESI, and EDI. --- 60 *)

 | PushRegisters -> {
   docref       = "pg 1372";
   mnemonic     = "pusha";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "move";
   long_name    = "PushRegisters";
   intel_asm    = (fun f -> f#no_ops "pusha");
   att_asm      = (fun f -> f#no_ops "pusha")}


 (*  PUSHF ---- Push EFLAGS                                           ---- 9C *)
 | PushFlags -> {
   docref       = "2A, 4-327";
   mnemonic     = "pushf";
   operands     = [esp_deref ~with_offset:(-4) WR; esp_r RW];
   flags_set    = [];
   flags_used   = [CFlag; ZFlag; OFlag; SFlag; PFlag; DFlag];
   group_name   = "misc";
   long_name    = "PushFlags";
   intel_asm    = (fun f -> f#no_ops "pushf");
   att_asm      = (fun f -> f#no_ops "pushf")}

  (* RCL r/m8,imm8 ---- Rotate 9 bits (CF,r/m8) left imm8 times      ---- C0/2 ib
     RCL r/m32,imm8 --- Rotate 33 bits (CF,r/m32) left imm8 times    ---- C1/2 ib
     RCL r/m8,1    ---- Rotate 9 bits (CF,r/m8) left once            ---- D0/2
     RCL r/m32,1   ---- Rotate 33 bits (CF,r/m32) left once          ---- D1/2
     RCL r/m8,CL   ---- Rotate 9 bits (CF,r/m8) left CL times        ---- D2/2
     RCL r/m32, CL ---- Rotate 33 bits (CF,r/m32) left CL times      ---- D3/3
  *)
 | Rcl (op1,op2) -> {
   docref       = "2A, 4-333";
   mnemonic     = "rcl";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag];
   flags_used   = [CFlag];
   group_name   = "bit operation";
   long_name    = "RotateCarryLeft";
   intel_asm    = (fun f -> f#ops "rcl" [op1; op2]);
   att_asm      = (fun f -> f#ops "rcl" [op2; op1])}

  (* RCR r/m8,imm8 ---- Rotate 9 bits (CF,r/m8) right imm8 times     ---- C0/3 ib
     RCR r/m32,imm8 --- Rotate 33 bits (CF,r/m32) right imm8 times   ---- C1/3 ib
     RCR r/m8,1    ---- Rotate 9 bits (CF,r/m8) right once           ---- D0/3
     RCR r/m32,1   ---- Rotate 33 bits (CF,r/m32) right once         ---- D1/3
     RCR r/m8,CL   ---- Rotate 9 bits (CF,r/m8) right CL times       ---- D2/3
     RCR r/m32, CL ---- Rotate 33 bits (CF,r/m32) right CL times     ---- D3/3
  *)
 | Rcr (op1,op2) -> {
   docref       = "2A, 4-333";
   mnemonic     = "rcr";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag];
   flags_used   = [CFlag];
   group_name   = "bit operation";
   long_name    = "RotateCarryRight";
   intel_asm    = (fun f -> f#ops "rcr" [op1; op2]);
   att_asm      = (fun f -> f#ops "rcr" [op2; op1])}

  (* REPE CMPS m8
     --- Find nonmatching bytes in ES:[EDI] and DS:[ESI]              ---- F3 A6
     REPE CMPS m32 m32
     --- Find nonmatching doublewords in ES:[EDI] and DS:[ESI]        ---- F3 A7
   *)
 | RepECmps (width,src1,src2) -> {
   docref       = "2A, 4-359";
   mnemonic     = "repe cmps";
   operands     = [ecx_r RW; edi_r RW; esi_r RW; src1; src2 ];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [DFlag; ZFlag];
   group_name   = "string operation";
   long_name    = "RepCompareWhileEqual";
   intel_asm    = (fun f -> f#no_ops "repe cmps");
   att_asm      = (fun f -> f#no_ops "repe cmps")}

  (* REPE SCAS m8  --- Find non-AL byte starting at ES:[EDI]          ---- F3 AE
     REPE SCAS m32 --- Find non-EAX doubleword starting at ES:[EDI]   ---- F3 AF
  *)
 | RepEScas (width,op) ->
    let src =
      if width = 1 then
        al_r WR
      else if width = 2 then
        ax_r WR
      else eax_r WR in
   { docref       = "2A, 4-359";
     mnemonic     = "repe scas";
     operands     = [ecx_r RW; edi_r RW; op; src ];
     flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
     flags_used   = [DFlag; ZFlag];
     group_name   = "string operation";
     long_name    = "RepScanWhileEqual";
     intel_asm    = (fun f -> f#no_ops "repe scas");
     att_asm      = (fun f -> f#no_ops "repe scas")}

  (* REP INS m8,DX
     --- Input ECX bytes from port DX into ES:[EDI]                   ---- F3 6C
   * REP INS m32,DX
   --- Input ECX doublewords from port DX into ES:[EDI]               ---- F3 6D
   *)
 | RepIns (width,dst) -> {
   docref       = "2A, 4-359";
   mnemonic     = "rep ins";
   operands     = [dst; ecx_r RW; edi_r RW; dx_r RD];
   flags_set    = [];
   flags_used   = [DFlag];
   group_name   = "string operation";
   long_name    = "RepInputData";
   intel_asm    = (fun f -> f#no_ops "rep ins");
   att_asm      = (fun f -> f#no_ops "rep ins")}

  (* REP LODS m8  --- Load ECX bytes from DS:[ESI] into AL            ---- F3 AC
   * REP LODS m32 --- Load ECX doublewords from DS:[ESI] into EAX     ---- F3 AD
   *)
 | RepLods (width,src) ->
    let dst =
      if width = 1 then
        al_r WR
      else if width = 2
      then ax_r WR
      else eax_r WR in
   { docref       = "2A, 4-359";
     mnemonic     = "rep lods";
     operands     = [dst; src; ecx_r RW; esi_r RW];
     flags_set    = [];
     flags_used   = [DFlag];
     group_name   = "string operation";
     long_name    = "RepLoad";
     intel_asm    = (fun f -> f#no_ops "rep lods");
     att_asm      = (fun f -> f#no_ops "rep lods")}

  (* REP MOVS m8  m8
     --- Move ECX bytes from DS:[ESI] to ES:[EDI]                     ---- F3 A4
     REP MOVS m32 m32
     --- Move ECX double words from DS:[ESI] to ES:[EDI]              ---- F3 A5
  *)
 | RepMovs (width,dst,src) -> {
   docref       = "2A, 4-359";
   mnemonic     = "rep movs";
   operands     = [dst; ecx_r RW; edi_r RW; esi_r RW; src ];
   flags_set    = [];
   flags_used   = [DFlag];
   group_name   = "string operation";
   long_name    = "RepMove";
   intel_asm    = (fun f -> f#no_ops "rep movs");
   att_asm      = (fun f -> f#no_ops "rep movs")}

  (* REPNE MOVS m8  m8
     --- Move ECX bytes from DS:[ESI] to ES:[EDI]                     ---- F2 A4
     REPNE MOVS m32 m32
     --- Move ECX double words from DS:[ESI] to ES:[EDI]              ---- F2 A5
  *)
 | RepNeMovs (width,dst,src) -> {
   docref       = "not documented";
   mnemonic     = "repne movs";
   operands     = [dst; ecx_r RW; edi_r RW; esi_r RW; src ];
   flags_set    = [];
   flags_used   = [DFlag];
   group_name   = "string operation";
   long_name    = "RepNeMove";
   intel_asm    = (fun f -> f#no_ops "repne movs");
   att_asm      = (fun f -> f#no_ops "repne movs")}

  (* REPNE CMPS m8
     --- Find matching bytes in ES:[EDI] and DS:[ESI]                 ---- F2 A6
     REPNE CMPS m32
     --- Find matching doublewords in ES:[EDI] and DS:[EDI]           ---- F2 A7
  *)
 | RepNeCmps (width,src1,src2) -> {
   docref       = "2A, 4-359";
   mnemonic     = "repne cmps";
   operands     = [ecx_r RW; edi_r RW; esi_r RW; src1; src2 ];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [DFlag; ZFlag];
   group_name   = "string operation";
   long_name    = "RepCompareWhileNotEqual";
   intel_asm    = (fun f -> f#no_ops "repne cmps");
   att_asm      = (fun f -> f#no_ops "repne cmps")}

  (* REPNE SCAS m8 --- Find AL starting at ES:[EDI]                   ---- F2 AE
     REPNE SCAS m32 -- Find EAX starting at ES:[EDI]                  ---- F2 AF
   *)
 | RepNeScas (width,dst) ->
    let src =
      if width = 1 then
        al_r WR
      else if width = 2
      then ax_r WR
      else
        eax_r WR in
   { docref       = "2A, 4-359";
     mnemonic     = "repne scas";
     operands     = [ecx_r RW; edi_r RW; dst; src ];
     flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
     flags_used   = [DFlag; ZFlag];
     group_name   = "string operation";
     long_name    = "RepScanWhileNotEqual";
     intel_asm    = (fun f -> f#no_ops "repne scas");
     att_asm      = (fun f -> f#no_ops "repne scas")}

  (* REP OUTS m8,DX
     --- Input ECX bytes from DS:[ESI] to port DX                     ---- F3 6E
   * REP OUTS m32,DX
   --- Input ECX doublewords from DS:[ESI] to port DX                 ---- F3 6F
   *)
 | RepOuts (width,op) -> {
   docref       = "2A, 4-359";
   mnemonic     = "rep outs";
   operands     = [op; ecx_r RW; esi_r RW; dx_r RD];
   flags_set    = [];
   flags_used   = [DFlag];
   group_name   = "string operation";
   long_name    = "RepOutputData";
   intel_asm    = (fun f -> f#no_ops "rep outs");
   att_asm      = (fun f -> f#no_ops "rep outs")}

  (* REP STOS m8  --- Fill ECX bytes at ES:[EDI] with AL              ---- F3 AA
     REP STOS m32 --- Fill ECX doublewords at ES:[EDI] with EAX       ---- F3 AB
  *)
 | RepStos (width,op) ->
    let src =
      if width = 1 then
        al_r WR
      else if width = 2
      then ax_r WR
      else
        eax_r WR in
   { docref       = "2A, 4-359";
     mnemonic     = "rep stos";
     operands     = [op; ecx_r RW; edi_r RW; src];
     flags_set    = [];
     flags_used   = [DFlag];
     group_name   = "string operation";
     long_name    = "RepStore";
     intel_asm    = (fun f -> f#no_ops "rep stos");
     att_asm      = (fun f -> f#no_ops "rep stos")}

  (* REPNE STOS m8  --- Fill ECX bytes at ES:[EDI] with AL             ---- F2 AA
     REPNE STOS m32 --- Fill ECX doublewords at ES:[EDI] with EAX      ---- F2 AB
  *)
 | RepNeStos (width,op) ->
    let src =
      if width = 1 then
        al_r WR
      else if width = 2 then
        ax_r WR
      else
        eax_r WR in
   { docref       = "not documented";
     mnemonic     = "repne stos";
     operands     = [op; ecx_r RW; edi_r RW; src];
     flags_set    = [];
     flags_used   = [DFlag];
     group_name   = "string operation";
     long_name    = "RepStore";
     intel_asm    = (fun f -> f#no_ops "repne stos");
     att_asm      = (fun f -> f#no_ops "repne stos")}

  (* RET imm16
     --- Near return to calling procedure and pop imm16
         bytes from the stack                                        ---- C2 iw
     RET ------- Near return to calling procedure                    ---- C3
     BND RET ---                                                     ---- F2 C3
  *)
 | Ret optAdj ->
    let asm =
      match optAdj with Some i -> "ret " ^ (string_of_int i) | _ -> "ret" in
   { docref       = "2A, 4-364";
     mnemonic     = "ret";
     operands     = [];
     flags_set    = [];
     flags_used   = [];
     group_name   = "control flow";
     long_name    = "Return";
     intel_asm    = (fun f -> f#no_ops asm);
     att_asm      = (fun f -> f#no_ops asm)}

 | BndRet optAdj ->
    let asm =
      match optAdj with
      | Some i -> "bnd ret " ^ (string_of_int i)
      | _ -> "bnd ret" in
   { docref       = "";
     mnemonic     = "bnd ret";
     operands     = [];
     flags_set    = [];
     flags_used   = [];
     group_name   = "control flow";
     long_name    = "BndReturn";
     intel_asm    = (fun f -> f#no_ops asm);
     att_asm      = (fun f -> f#no_ops asm)}


 | RepzRet -> {
   docref       = "";
   mnemonic     = "repz ret";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "control flow";
   long_name    = "RepReturn";
   intel_asm    = (fun f -> f#no_ops "repz ret");
   att_asm      = (fun f -> f#no_ops "repz ret")}

  (* ROL r/m8,imm8 ---- Rotate 8 bits r/m8 left imm8 times           ---- C0/0 ib
     ROL r/m32,imm8 --- Rotate 32 bits r/m32 left imm8 times         ---- C1/0 ib
     ROL r/m8,1    ---- Rotate 8 bits r/m8 left, once                ---- D0/0
     ROL r/m32,1   ---- Rotate 32 bits left once                     ---- D1/0
     ROL r/m8,CL   ---- Rotate 8 bits r/m8 left CL times             ---- D2/0
     ROL r/m32, CL ---- Rotate 32 bits rm32 left CL times            ---- D3/0
  *)
 | Rol (op1,op2) -> {
   docref       = "2A, 4-333";
   mnemonic     = "rol";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "RotateLeft";
   intel_asm    = (fun f -> f#ops "rol" [op1; op2]);
   att_asm      = (fun f -> f#ops "rol" [op2; op1])}

  (* ROR r/m8,imm8  --- Rotate 8 bits r/m8 right imm8 times          ---- C0/1 in
     ROR r/m32,imm8 --- Rotate 32 bits r/m32 right imm8 times        ---- C1/1 ib
     ROR r/m8,1    ---- Rotate 8 bits r/m8 right, once               ---- D0/1
     ROR r/m32,1   ---- Rotate 32 bits right once                    ---- D1/1
     ROR r/m8,CL   ---- Rotate 8 bits r/m8 right CL times            ---- D2/1
     ROR r/m32, CL ---- Rotate 32 bits r/m32 right CL times          ---- D3/1
  *)
 | Ror (op1,op2) -> {
   docref       = "2A, 4-333";
   mnemonic     = "ror";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "RotateRight";
   intel_asm    = (fun f -> f#ops "ror" [op1; op2]);
   att_asm      = (fun f -> f#ops "ror" [op2; op1])}

  (* SAR r/m8,imm8 ---- Signed divide r/m8 by 2, imm8 times          ---- C0/7 ib
     SAR r/m32,imm8 --- Signed divide r/m32 by 2 imm8 times          ---- C1/7 ib
     SAR r/m8,1    ---- Signed divide r/m8 by 2, once                ---- D0/7
     SAR r/m32,1   ---- Signed divide r/m32 by 2, once               ---- D1/7
     SAR r/m8,CL   ---- Signed divide r/m8 by 2, CL times            ---- D2/7
     SAR r/m32, CL ---- Signed divide r/m32 by 2, CL times           ---- D3/7
  *)
 | Sar (op1,op2) -> {
   docref       = "2A, 4-399";
   mnemonic     = "sar";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "ShiftArithmeticRight";
   intel_asm    = (fun f -> f#ops "sar" [op1; op2]);
   att_asm      = (fun f -> f#ops "sar" [op2; op1])}

  (* SCASB
     --- Compare AL with byte at ES:[EDI] and set status flags           ---- AE
     SCASD
     --- Compare EAX with doubleword at ES:[EDI] and set status flags    ---- AF
  *)
 | Scas (width,op) ->
   let name = "scas" ^ (width_suffix_string width) in
   let src =
     if width = 1 then al_r RD else if width = 2 then ax_r RD else eax_r RD in
   { docref       = "2A, 4-411";
     mnemonic     = name;
     operands     = [op; src];
     flags_set    = [CFlag; ZFlag; OFlag; SFlag; PFlag];
     flags_used   = [DFlag];
     group_name   = "string operation";
     long_name    = "ScanString";
     intel_asm    = (fun f -> f#no_ops name);
     att_asm      = (fun f -> f#no_ops name)}

 (* SETALC     ---- Set Al on carry (undocumented)                    ---- D6 *)
 | SetALC ->
   { docref       = "undocumented";
     mnemonic     = "setalc";
     operands     = [al_r WR];
     flags_set    = [];
     flags_used   = [CFlag];
     group_name   = "undocumented";
     long_name    = "SetAlOnCarry";
     intel_asm    = (fun f -> f#no_ops "setalc");
     att_asm      = (fun f -> f#no_ops "setalc")}

  (* SETO r/m8  ---- Set byte if overflow (OF=1)                     ---- 0F 90
     SETNO r/m8 ---- Set byte if not overflow (OF=0)                 ---- 0F 91
     SETC r/m8  ---- Set byte if carry (CF=1)                        ---- 0F 92
     SETNC r/m8 ---- Set byte if not carry (CF=0)                    ---- 0F 93
     SETZ r/m8  ---- Set byte if zero (ZF=1)                         ---- 0F 94
     SETNZ r/m8 ---- Set byte if not zero (ZF=0)                     ---- 0F 95
     SETBE r/m8 ---- Set byte if below or equal (CF=1 or ZF=1)       ---- 0F 96
     SETA r/m8  ---- Set byte if above (CF=0 and ZF=0)               ---- 0F 97
     SETS r/m8  ---- Set byte if sign (SF=1)                         ---- 0F 98
     SETNS r/m8 ---- Set byte if not sign (SF=0)                     ---- 0F 99
     SETPE r/m8 ---- Set byte if parity even (PF=1)                  ---- 0F 9A
     SETPO r/m8 ---- Set byte if parity odd (PF=0)                   ---- 0F 9B
     SETL r/m8  ---- Set byte if less (SF != OF)                     ---- 0F 9C
     SETGE r/m8 ---- Set byte if greater or equal (SF=OF)            ---- 0F 9D
     SETLE r/m8 ---- Set byte if less or equal (ZF=1 or SF!=OF)      ---- 0F 9E
     SETG r/m8  ---- Set byte if greater (ZF=0,SF=OF)                ---- 0F 9F
   *)
 | Setcc (cc,op) ->
   let name = "set" ^ (condition_code_to_suffix_string cc) in
   { docref       = "2A, 4-416";
     mnemonic     = name;
     operands     = [op];
     flags_set    = [];
     flags_used   = [CFlag; ZFlag; OFlag; SFlag; PFlag];
     group_name   = "bit operation";
     long_name    = "SetOnCondition";
     intel_asm    = (fun f -> f#ops name [op]);
     att_asm      = (fun f -> f#ops name [op])}

 (* STC  --- Set Carry Flag                                           ---- F9 *)
 | SetCF -> {
   docref       = "2A, 4-460";
   mnemonic     = "stc";
   operands     = [];
   flags_set    = [CFlag];
   flags_used   = [];
   group_name   = "cc operation";
   long_name    = "SetCarryFlag";
   intel_asm    = (fun f -> f#no_ops "stc");
   att_asm      = (fun f -> f#no_ops "stc")}

 (* STD  --- Set Direction Flag                                       ---- FD *)
 | SetDF -> {
   docref       = "2A, 4-461";
   mnemonic     = "std";
   operands     = [];
   flags_set    = [DFlag];
   flags_used   = [];
   group_name   = "cc operation";
   long_name    = "SetDirectionFlag";
   intel_asm    = (fun f -> f#no_ops "std");
   att_asm      = (fun f -> f#no_ops "std")}

 (* STI  --- Set Interrupt Flag                                       ---- FB *)
 | SetInterruptFlag -> {
   docref       = "2A, 4-462";
   mnemonic     = "sti";
   operands     = [];
   flags_set    = [IFlag];
   flags_used   = [];
   group_name   = "cc operation";
   long_name    = "SetInterruptFlag";
   intel_asm    = (fun f -> f#no_ops "sti");
   att_asm      = (fun f -> f#no_ops "sti")}

  (* SHL r/m8,imm8 ---- Multiply r/m8 by 2 imm8 times                ---- C0/4 ib
     SHL r/m32,imm8 --- Multiply r/m32 by 2 imm8 times               ---- C1/4 ib
     SHL r/m8,1    ---- Multiply r/m8 by 2, once                     ---- D0/4
     SAL r/m8,1    ---- Multiply r/m8 by 2, once                     ---- D0/6
     -- (not documented)
     SHL r/m32,1   ---- Multiply r/m32 by 2, once                    ---- D1/4
     SAL r/m32,1   ---- Multiply r/m32 by 2, once                    ---- D1/6
     -- (not documented)
     SHL r/m8,CL   ---- Multiply r/m8 by 2, CL times                 ---- D2/4
     SHL r/m8,CL   ---- Multiply r/m8 by 2, CL times                 ---- D2/6
     -- (not documented)
     SHL r/m32, CL ---- Multiply r/m32 by 2, CL times                ---- D3/4
     SHL r/m32, CL ---- Multiply r/m32 by 2, CL times                ---- D3/6
     -- (not documented)
  *)
 | Shl (op1,op2) -> {
   docref       = "2A, 4-399";
   mnemonic     = "shl";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "ShiftLeft";
   intel_asm    = (fun f -> f#ops "shl" [op1; op2]);
   att_asm      = (fun f -> f#ops "shl" [op2; op1])}

 (* SHLD r/m32,r32,imm8
    --- Shift r/m32 to left imm8 places while
        shifting bits from r32 in from the right                   ---- 0F A4/r
    SHLD r/m32,r32,CL
    --- Shift r/m32 to left CL places while
        while shifting bits from r32 in from the right             ---- 0F A5/r
  *)
 | Shld (op1,op2,op3) -> {
   docref       = "2A, 4-425";
   mnemonic     = "shld";
   operands     = [op1; op2; op3];
   flags_set    = [SFlag; CFlag; OFlag; PFlag; ZFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "ShiftLeftDoublePrecision";
   intel_asm    = (fun f -> f#ops "shld" [op1; op2; op3]);
   att_asm      = (fun f -> f#ops "shld" [op3; op2; op1])}

  (* SHR r/m8,imm8  --- Unsigned divide r/m8 by 2, imm8 times         ---- C0/5 ib
     SHR r/m32,imm8 --- Unsigned divide r/m32 by 2 imm8 times         ---- C1/5 ib
     SHR r/m8,1     --- Unsigned divide r/m8 by 2, once               ---- D0/5
     SHR r/m32,1   ---- Unsigned divide r/m32 by 2, once              ---- D1/5
     SHR r/m8,CL   ---- Unsigned divide r/m8 by 2, CL times           ---- D2/5
     SHR r/m32, CL ---- Unsigned divide r/m32 by 2, CL times          ---- D3/5
  *)
 | Shr (op1,op2) -> {
   docref       = "2A, 4-399";
   mnemonic     = "shr";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "ShiftRight";
   intel_asm    = (fun f -> f#ops "shr" [op1; op2]);
   att_asm      = (fun f -> f#ops "shr" [op2; op1])}

 (* SHRD r/m32,r32,imm8
    --- Shift r/m32 to right imm8 places while
        shifting bits from r32 in from the left                      ---- 0F AC/r
    SHRD r/m32,r32,CL
    --- Shift r/m32 to right CL places while
        shifting bits from r32 in from the left                      ---- 0F AD/r
  *)
 | Shrd (op1,op2,op3) -> {
   docref       = "2A, 4-429";
   mnemonic     = "shrd";
   operands     = [op1; op2; op3];
   flags_set    = [SFlag; CFlag; OFlag; PFlag; ZFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "ShiftRightDoublePrecision";
   intel_asm    = (fun f -> f#ops "shrd" [op1; op2; op3]);
   att_asm      = (fun f -> f#ops "shrd" [op3; op2; op1])}

 (* SAHF  --- Store AH into Flags                                     ---- 9E *)
 | StoreFlags -> {
   docref       = "2A, 4-397";
   mnemonic     = "sahf";
   operands     = [ah_r RD];
   flags_set    = [SFlag; ZFlag; PFlag; CFlag];   (* restored from AH *)
   flags_used   = [];
   group_name   = "misc";
   long_name    = "StoreFlags";
   intel_asm    = (fun f -> f#no_ops "sahf");
   att_asm      = (fun f -> f#no_ops "sahf")}

 (* SGDT --- Store Global Descriptor Table Register               --- 0F 01/0 *)
 | StoreGDTR op -> {
     docref     = "2B, 4-617";
     mnemonic   = "sgdt";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "StoreGDTR";
     intel_asm  = (fun f -> f#ops "sgdt" [op]);
     att_asm    = (fun f -> f#ops "sgdt" [op])}

 (* SIDT --- Store Local Descriptor Table Register                --- 0F 00/0 *)
 | StoreLDTR op -> {
     docref     = "2B, 4-645";
     mnemonic   = "sldt";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "StoreLDTR";
     intel_asm  = (fun f -> f#ops "sldt" [op]);
     att_asm    = (fun f -> f#ops "sldt" [op])}

 (* SLDT --- Store Interrupt Descriptor Table Register            --- 0F 01/1 *)
 | StoreIDTR op -> {
     docref     = "2A, 4-440";
     mnemonic   = "sidt";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "StoreIDTR";
     intel_asm  = (fun f -> f#ops "sidt" [op]);
     att_asm    = (fun f -> f#ops "sidt" [op])}

 (* STR --- Store Task Register                                   --- 0F 00/1 *)
 | StoreTaskRegister op -> {
     docref     = "2B, 4-668";
     mnemonic   = "str";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "StoreTaskRegister";
     intel_asm  = (fun f -> f#ops "str" [op]);
     att_asm    = (fun f -> f#ops "str" [op])}

  (* STOS m8  --- Store AL  at address ES:EDI                            ---- AA
     STOS m32 --- Store EAX at address ES:EDI                            ---- AB
  *)
 | Stos (width, dst,src,opedi,opdf) ->
   let name = "stos" ^ (width_suffix_string width) in
   (*  let src = if width = 1 then al_r RD else if width = 2 then ax_r RD else eax_r RD in *)
   { docref       = "2A, 4-467";
     mnemonic     = "stos";
     operands     = [dst; src; opedi; opdf];
     flags_set    = [];
     flags_used   = [DFlag];
     group_name   = "string operation";
     long_name    = "StoreString";
     intel_asm    = (fun f -> f#no_ops name);
     att_asm      = (fun f -> f#no_ops name)}

  (* SUB r/m8,r8   ---- Subtract r8 from r/m8                        ---- 28/r
     SUB r/m32,r32 ---- Subtract r32 from r/m32                      ---- 29/r
     SUB r8,r/m8   ---- Subtract r/m8 from r8                        ---- 2A/r
     SUB r32,r/m32 ---- Subtract r/m32 from r32                      ---- 2B/r
     SUB AL,imm8   ---- Subtract imm8 from AL                        ---- 2C ib
     SUB EAX,imm32 ---- Subtract imm32 from EAX                      ---- 2D id
     SUB r/m8,imm8 ---- Subtract imm8 from r/m8                      ---- 80/5 ib
     SUB r/m32,imm32 -- Subtract imm32 from r/m32                    ---- 81/5 id
     SUB r/m32,imm8 --- Subtract sign-extended imm8 from r/m32       ---- 83/5 ib
   *)
 | Sub (op1,op2) -> {
   docref       = "2A, 4-474";
   mnemonic     = "sub";
   operands     = [op1; op2];
   flags_set    = [SFlag; ZFlag; OFlag; SFlag; PFlag];
   flags_used   = [];
   group_name   = "integer arithmetic";
   long_name    = "Subtract";
   intel_asm    = (fun f -> f#ops "sub" [op1; op2]);
   att_asm      = (fun f -> f#ops "sub" [op2; op1])}

  (* SBB r/m8,r8   ---- Subtract with borrow r8 from r/m8            ---- 18/r
     SBB r/m32,r32 ---- Subtract with borrow r32 from r/m32          ---- 19/r
     SBB r8,r/m8   ---- Subtract with borrow r/m8 from r8            ---- 1A/r
     SBB r32,r/m32 ---- Subtract with borrow r/m32 from r32          ---- 1B/r
     SBB AL, imm8  ---- Subtract with borrow imm8 from AL            ---- 1C ib
     SBB EAX, imm32 --- Subtract with borrow imm32 from EAX          ---- 1D id
     SBB r/m8,imm8 ---- Subtract with borrow imm8 from r/m8          ---- 80/3 ib
     SBB r/m32,imm32 -- Subtract with borrow imm32 from r/m32        ---- 81/3 id
     SBB r/m32,imm8
     --- Subtract with borrow sign-extended imm8 from r/m32          ---- 83/3 ib
   *)
 | SubBorrow (op1,op2) -> {
   docref       = "2A, 4-407";
   mnemonic     = "sbb";
   operands     = [op1; op2];
   flags_set    = [SFlag; ZFlag; OFlag; PFlag; CFlag];
   flags_used   = [CFlag];
   group_name   = "integer arithmetic";
   long_name    = "SubBorrow";
   intel_asm    = (fun f -> f#ops "sbb" [op1; op2]);
   att_asm      = (fun f -> f#ops "sbb" [op2; op1])}

 (* SYSCALL --- Fast System Call                                      ---- 0F 05
                 Fast call to privilege level 0 system procedures.*)
 | SysCall -> {
   docref       = "2A, 4-404";
   mnemonic     = "syscall";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "kernelmode";
   long_name    = "SysCall";
   intel_asm    = (fun f -> f#no_ops "syscall");
   att_asm      = (fun f -> f#no_ops "syscall")}

 (* SYSENTER --- Fast System Call                                     ---- 0F 34
                 Fast call to privilege level 0 system procedures.*)
 | SysEnter -> {
   docref       = "2A, 4-406";
   mnemonic     = "sysenter";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "kernelmode";
   long_name    = "SysEnter";
   intel_asm    = (fun f -> f#no_ops "sysenter");
   att_asm      = (fun f -> f#no_ops "sysenter")}

 (* SYSEXIT --- Fast return from fast system call                   --- 0F 35 *)
 | SysExit -> {
   docref       = "2A, 4-409";
   mnemonic     = "sysexit";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "kernelmode";
   long_name    = "SysExit";
   intel_asm    = (fun f -> f#no_ops "syscall");
   att_asm      = (fun f -> f#no_ops "syscall")}

 (* SYSRET --- Return to compatibility mode from fast system call    --- 0F 07 *)
 | SysReturn -> {
   docref       = "2A, 4-412";
   mnemonic     = "sysret";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "kernelmode";
   long_name    = "SysReturn";
   intel_asm    = (fun f -> f#no_ops "sysret");
   att_asm      = (fun f -> f#no_ops "syscall")}

 (* XLAT --- Table Lookup Translation
             Set AL to memory byte DS:[(E)BX + unsigned AL].          --- D7  *)
 | TableLookupTranslation -> {
   docref        = "2B 4-577";
   mnemonic      = "xlat";
   operands      = [];
   flags_set     = [];
   flags_used    = [];
   group_name    = "move";
   long_name     = "TableLookupTranslation";
   intel_asm     = (fun f -> f#no_ops "xlat");
   att_asm       = (fun f -> f#no_ops "xlat")}

 (* ENDBR32
    --- Terminate an Indirect Branch in 32-bit and
        compatbility mode                                    --- F3 0F 1E FB  *)
 | TerminateBranch32 -> {
   docref       = "2A, 3-345";
   mnemonic     = "endbr32";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "TerminateBranch32";
   intel_asm    = (fun f -> f#no_ops "endbr32");
   att_asm      = (fun f -> f#no_ops "endbr32")}

 (* TEST r/m8,r8
    --- AND r8 with r/m8, set SF,ZF,PF according to result             ---- 84/r
    TEST r/m32,r32
    --- AND r32 with r/m32, set SF,ZF,PF according to result           ---- 85/r
    TEST AL,imm8
    ---- AND imm8 with AL, set SF,ZF,PF according to result            ---- A8 ib
    TEST EAX,imm32
    --- AND imm32 with EAX, set SF,ZF,PF according to result           ---- A9 ib
    TEST r/m8,imm8
    --- AND imm8 with r/m8, set SF,ZF,PF according to result         ---- F6/0 ib
    TEST r/m32
    ---- AND imm32 with r/m32, set SF,ZF,PF according to result       --- F7/0 id
  *)
 | Test (op1,op2) -> {
   docref       = "2A, 4-504";
   mnemonic     = "test";
   operands     = [op1; op2];
   flags_set    = [SFlag; ZFlag; OFlag; PFlag; CFlag];
   flags_used   = [];
   group_name   = "test";
   long_name    = "Test";
   intel_asm    = (fun f -> f#ops "test" [op1; op2]);
   att_asm      = (fun f -> f#ops "test" [op2; op1])}

 (* TPAUSE --- Timed Pause                                     --- 66 0F AE/6 *)
 | TimedPause op -> {
     docref     = "2B, 4-711";
     mnemonic   = "tpause";
     operands   = [op];
     flags_set  = [];
     flags_used = [];
     group_name = "misc";
     long_name  = "StoreGDTR";
     intel_asm  = (fun f -> f#ops "tpause" [op]);
     att_asm    = (fun f -> f#ops "tpause" [op])}

 (* NEG r/m8  --- Two's complement negate r/m8                         ---- F6/3
    NEG r/m32 --- Two's complement negate r/m 32                       ---- F7/3
  *)
 | TwosComplementNegate op -> {
   docref       = "2A, 4-8";
   mnemonic     = "neg";
   operands     = [op];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "TwosComplementNegate";
   intel_asm    = (fun f -> f#ops "neg" [op]);
   att_asm      = (fun f -> f#ops "neg" [op])}

 (* UD0 --- Undefined instruction                               ---- 0F FF/r *)
 | UndefinedInstruction0 (op1, op2) -> {
   docref       = "2B, 4-719";
   mnemonic     = "ud0";
   operands     = [op1; op2];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "UndefinedInstruction0";
   intel_asm    = (fun f -> f#ops "ud0" [op1; op2]);
   att_asm      = (fun f -> f#ops "ud0" [op1; op2])}

 (* UD1 --- Undefined instruction                                ---- 0F B9/r *)
 | UndefinedInstruction1 (op1, op2) -> {
   docref       = "2B, 4-719";
   mnemonic     = "ud1";
   operands     = [op1; op2];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "UndefinedInstruction0";
   intel_asm    = (fun f -> f#ops "ud1" [op1; op2]);
   att_asm      = (fun f -> f#ops "ud1" [op1; op2])}

 (* UD2 --- Undefined instruction                                 ---- 0F 0B *)
 | UndefinedInstruction2 -> {
   docref       = "2B, 4-513";
   mnemonic     = "ud2";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "UndefinedInstruction2";
   intel_asm    = (fun f -> f#no_ops "ud2");
   att_asm      = (fun f -> f#no_ops "ud2")}

 (* WBINVD --- Write Back and Invalidate Cache                      --- 0F 09 *)
 | WriteBackInvalidateCache -> {
   docref       = "2D, 6-3";
   mnemonic     = "wbinvd";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "kernelmode";
   long_name    = "WriteBackInvalidateCache";
   intel_asm    = (fun f -> f#no_ops "wbinvd");
   att_asm      = (fun f -> f#no_ops "wbinvd")}

 (* XADD r/m8,r8   --- exchange r8 and r/m8; load sum into r/m8     ---- 0F C0/r
    XADD r/m32,r32 --- exchange r32 and r/m32; load sum into r/m32  ---- 0F C1/r
  *)
 | XAdd (op1,op2) -> {
   docref       = "2B, 4-535";
   mnemonic     = "xadd";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [];
   group_name   = "integer arithmetic";
   long_name    = "ExchangeAdd";
   intel_asm    = (fun f -> f#ops "xadd" [op1; op2]);
   att_asm      = (fun f -> f#ops "xadd" [op2; op1])}

 (* XCHG r/m8,r8  ----- Exchange r8 with byte from r/m8             ---- 86/r
    XCHG r/m32,r32 ---- Exchange r32 with doubleword from r/m32     ---- 87/r
    XCHG r32, EAX  ---- Exchange EAX with r32                       ---- 90+rd
  *)
 | Xchg (op1,op2) -> {
   docref       = "2B, 4-538";
   mnemonic     = "xchg";
   operands     = [op1; op2];
   flags_set    = [];
   flags_used   = [];
   group_name   = "move";
   long_name    = "Exchange";
   intel_asm    = (fun f -> f#ops "xchg" [op1; op2]);
   att_asm      = (fun f -> f#ops "xchg" [op2; op1])}


 (* XOR r/m8,r8     ---- r/m8 xor r8                                ---- 30/r
    XOR r/m32,r32   ---- r/m32 xor r32                              ---- 31/r
    XOR r8,r/m8     ---- r8 xor r/m8                                ---- 32/r
    XOR r32,r/m32   ---- r32 xor r/m32                              ---- 33/r
    XOR AL,imm8     ---- AL XOR imm8                                ---- 34 ib
    XOR EAX,imm32   ---- EAX XOR imm32                              ---- 35 id
    XOR r/m8,imm8   -----r/m8 XOR r8                                ---- 80/6 ib
    XOR r/m32,imm32 ---- r/m32 XOR r32                              ---- 81/6 id
    XOR r/m32,imm8  ---- r/m32 XOR imm8 (sign-extended)             ---- 83/6 ib
  *)
 | Xor (op1,op2) -> {
   docref       = "2B, 4-546";
   mnemonic     = "xor";
   operands     = [op1; op2];
   flags_set    = [CFlag; OFlag; SFlag; ZFlag; PFlag];
   flags_used   = [];
   group_name   = "bit operation";
   long_name    = "ExclusiveOr";
   intel_asm    = (fun f -> f#ops "xor" [op1; op2]);
   att_asm      = (fun f -> f#ops "xor" [op2; op1])}

 | XStoreRng -> {
   docref       = "";
   mnemonic     = "xstore-rng";
   operands     =
     [es_edi WR; ds_esi RD; edi_r WR; esi_r WR; eax_r RW; ecx_r RW; ebx_r RW];
   flags_set    = [];
   flags_used   = [];
   group_name   = "encryption";
   long_name    = "XStoreRng";
   intel_asm    = (fun f -> f#no_ops "xstore-rng");
   att_asm      = (fun f -> f#no_ops "xstore-rng")}

 | XCrypt suffix ->
   let name = "crypt" ^ suffix in
   { docref       = "";
     mnemonic     = name;
     operands     =
       [es_edi WR; ds_esi RD; edi_r WR; esi_r WR; eax_r RW; ecx_r RW; ebx_r RW];
     flags_set    = [];
     flags_used   = [];
     group_name   = "encryption";
     long_name    = "XCrypt";
     intel_asm    = (fun f -> f#no_ops name);
     att_asm      = (fun f -> f#no_ops name)}

 (* XGETBV
    --- Reads an extended control register specified by
        ECX into EDX:EAX                                        ---- 0F 01 D0 *)
 | XGetBV -> {
   docref       = "2B, 4-451";
   mnemonic     = "xgetbv";
   operands     = [ecx_r RD; double_register_op Edx Eax 8 WR];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "GetValueExtendedControlRegister";
   intel_asm    = (fun f -> f#no_ops "xgetbv");
   att_asm      = (fun f -> f#no_ops "xgetbv")}

 | XRestore op -> {
   docref       = "2D, 6-45";
   mnemonic     = "xrstor";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "XRestore";
   intel_asm    = (fun f -> f#ops "xrstor" [op]);
   att_asm      = (fun f -> f#ops "xrstor" [op])}

 | XRestoreSupervisor op -> {
   docref       = "2D, 6-50";
   mnemonic     = "xrstors";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "XRestoreSupervisor";
   intel_asm    = (fun f -> f#ops "xrstors" [op]);
   att_asm      = (fun f -> f#ops "xrstors" [op])}

 | XSave op -> {
   docref       = "2D, 6-54";
   mnemonic     = "xsave";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "XSave";
   intel_asm    = (fun f -> f#ops "xsave" [op]);
   att_asm      = (fun f -> f#ops "xsave" [op])}

 | XSaveSupervisor op -> {
   docref       = "2D, 6-63";
   mnemonic     = "xsaves";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "XSaveSupervisor";
   intel_asm    = (fun f -> f#ops "xsaves" [op]);
   att_asm      = (fun f -> f#ops "xsaves" [op])}

 (* RDMSR --- Read Model Specific Register into EDX:EAX            ---- 0F 32 *)
 | ReadModelSpecificRegister -> {
   docref       = "2B, 4-537";
   mnemonic     = "rdmsr";
   operands     = [ecx_r RD; double_register_op Edx Eax 8 WR];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "ReadModelSpecificRegister";
   intel_asm    = (fun f -> f#no_ops "rdmsr");
   att_asm      = (fun f -> f#no_ops "rdmsr")}

 (* RDPMC --- Read Model Specific Register into EDX:EAX            ---- 0F 33 *)
 | ReadPerformanceMonitoringCounters -> {
   docref       = "2B, 4-542";
   mnemonic     = "rdpmc";
   operands     = [ecx_r RD; double_register_op Edx Eax 8 WR];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "ReadPerformanceMonitoringCounters";
   intel_asm    = (fun f -> f#no_ops "rdpmc");
   att_asm      = (fun f -> f#no_ops "rdpmc")}

 (* RDTSC --- Read Time Stamp Counter into EDX:EAX                 ---- 0F 31 *)
 | ReadTimeStampCounter -> {
   docref       = "2B, 4-355";
   mnemonic     = "rdtsc";
   operands     = [ecx_r RD; double_register_op Edx Eax 8 WR];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "ReadTimeStampCounter";
   intel_asm    = (fun f -> f#no_ops "rdtsc");
   att_asm      = (fun f -> f#no_ops "rdtsc")}

 (* Randomize the operand; new instruction added in 2012         ---- 0F C7/6 *)
 | RdRandomize op -> {
   docref       = "";
   mnemonic     = "rdrand";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "Randomize";
   intel_asm    = (fun f -> f#ops "rdrand" [op]);
   att_asm      = (fun f -> f#ops "rdrand" [op])}

 (* Read a 32-bit NIST SP800-90B & C compliant random value      ---- 0F C7/7 *)
 | ReadSeed op -> {
   docref       = "";
   mnemonic     = "rdseed";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "ReadSeed";
   intel_asm    = (fun f -> f#ops "rdseed" [op]);
   att_asm      = (fun f -> f#ops "rdseed" [op])}

 (* SERIALIZE --- Serialize Instruction Execution                --- 0F 01 E8 *)
 | SerializeExecution -> {
   docref       = "2B, 4-610";
   mnemonic     = "serialize";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "SerializeExecution";
   intel_asm    = (fun f -> f#no_ops "serialize");
   att_asm      = (fun f -> f#no_ops "serialize")}

 | Ldmxcsr op -> {
   docref       = "2A, 3-592";
   mnemonic     = "ldmxcsr";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "LoadMxcsrRegister";
   intel_asm    = (fun f -> f#ops "ldmxcsr" [op]);
   att_asm      = (fun f -> f#ops "ldmxcsr" [op])}

 | Stmxcsr op -> {
   docref       = "2B, 4-465";
   mnemonic     = "stmxcsr";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "StoreMxcsrRegister";
   intel_asm    = (fun f -> f#ops "stmxcsr" [op]);
   att_asm      = (fun f -> f#ops "stmxcsr" [op])}

 | Pause -> {
   docref       = "2B, 4-71";
   mnemonic     = "pause";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "Pause";
   intel_asm    = (fun f -> f#no_ops "pause");
   att_asm      = (fun f -> f#no_ops "pause")}

 | VZeroAll -> {
   docref       = "2B";
   mnemonic     = "vzeroall";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "avx";
   long_name    = "VZeroAll";
   intel_asm    = (fun f -> f#no_ops "vzeroall");
   att_asm      = (fun f -> f#no_ops "vzeroall")}

 | VMovdq (aligned,dst,src) ->
   let name = "vmovdq" ^ (if aligned then "a" else "u") in
   { docref       = "2A";
     mnemonic     = name;
     operands     = [dst; src];
     flags_set    = [];
     flags_used   = [];
     group_name   = "avx";
     long_name    = "VMoveAVX";
     intel_asm    = (fun f -> f#ops name [dst; src]);
     att_asm      = (fun f -> f#ops name [src; dst])}

 | VPackedOp (opname,width,dst,src1,src2) ->
   let name = "vp" ^ opname ^ (width_suffix_string width) in
   { docref       = "2B";
     mnemonic     = name;
     operands     = [dst; src1; src2];
     flags_set    = [];
     flags_used   = [];
     group_name   = "packed integer";
     long_name    = "Packed:" ^ opname;
     intel_asm    = (fun f -> f#ops name [dst; src1; src2]);
     att_asm      = (fun f -> f#ops name [src1; src2; dst])}


 | VPackedAdd (ss,us,width,dst,src1,src2) ->
    let name =
      "vpadd"
      ^ (signed_saturation_infix ss)
      ^ (unsigned_saturation_infix us)
      ^ (width_suffix_string width) in
   { docref       = "2B";
     mnemonic     = name;
     operands     = [dst; src1; src2];
     flags_set    = [];
     flags_used   = [];
     group_name   = "avx";
     long_name    = "VPackedAdd";
     intel_asm    = (fun f -> f#ops name [dst; src1; src2]);
     att_asm      = (fun f -> f#ops name [src1; src2; dst])}

 | VPackedAlignRight (dst,src1,src2,shift) -> {
   docref       = "2B, 4-62";
   mnemonic    = "vpalignr";
   operands     = [dst; src1; src2; shift];
   flags_set    = [];
   flags_used   = [];
   group_name   = "avx";
   long_name    = "VPackedAlignRight";
   intel_asm    = (fun f -> f#ops "vpalignr" [dst; src1; src2; shift]);
   att_asm      = (fun f -> f#ops "vpalignr" [src1; src2; shift; dst])}

 | VPackedShift (dir,width,dst,src1,src2) ->
   let name = "vps" ^ dir ^ (width_suffix_string width) in
   { docref       = "";
     mnemonic     = name;
     operands     = [dst; src1; src2];
     flags_set    = [];
     flags_used   = [];
     group_name   = "avx";
     long_name    = "VPackedShift" ^ dir;
     intel_asm    = (fun f -> f#ops name [dst; src1; src2]);
     att_asm      = (fun f -> f#ops name [src1; src2; dst])}

 | VPackedShuffle (suffix,dst,src,optEncoding) ->
   let name = "vpshuf" ^ suffix in
   let ops = match optEncoding with
     | Some encoding -> [dst; src; encoding] | _ -> [dst; src] in
   { docref       = "";
     mnemonic     = name;
     operands     = ops;
     flags_set    = [];
     flags_used   = [];
     group_name   = "avx";
     long_name    = "VPackedShuffle";
     intel_asm    = (fun f -> f#ops name ops);
     att_asm      = (fun f -> f#ops name (match optEncoding with
       Some encoding -> [src; encoding; dst] | _ -> [src; dst]))}

 (* WAIT  --- Check pending unmasked floating point exceptions        ---- 9B *)
 | Wait -> {
   docref       = "2A, 4-529";
   mnemonic     = "wait";
   operands     = [];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "Wait";
   intel_asm    = (fun f -> f#no_ops "wait");
   att_asm      = (fun f -> f#no_ops "wait")}

 (* WRMSR --- Write Model Specific Register from EDX:EAX           ---- 0F 32 *)
 | WriteModelSpecificRegister -> {
   docref       = "2B, 4-537";
   mnemonic     = "rdmsr";
   operands     = [ecx_r RD; double_register_op Edx Eax 8 RD];
   flags_set    = [];
   flags_used   = [];
   group_name   = "misc";
   long_name    = "WriteModelSpecificRegister";
   intel_asm    = (fun f -> f#no_ops "wrmsr");
   att_asm      = (fun f -> f#no_ops "wrmsr")}

 | JumpTableEntry op -> {
   docref       = "";
   mnemonic     = "jt entry";
   operands     = [op];
   flags_set    = [];
   flags_used   = [];
   group_name   = "control flow";
   long_name    = "JumpTableEntry";
   intel_asm    = (fun f -> f#ops "jt entry" [op]);
   att_asm      = (fun f -> f#ops "jt entry" [op])}

 (* meta instructions *)

 | OpInvalid
 | Unknown
 | InconsistentInstr _
 | NotCode _ ->
   let name = match opc with
     | Unknown ->
        "unknown" | InconsistentInstr s -> "inconsistent:" ^ s | _ -> "meta" in
   { docref       = "";
     mnemonic     = name;
     operands     = [];
     flags_set    = [];
     flags_used   = [];
     group_name   = "Meta";
     long_name    = name;
     intel_asm    = (fun f -> f#no_ops name);
     att_asm      = (fun f -> f#no_ops name)}

 | CfNop (len,desc) ->
   let desc = "cfnop(" ^ (string_of_int len) ^ "," ^ desc ^ ")" in
   { docref       = "";
     mnemonic     = "cfnop";
     operands     = [];
     flags_set    = [];
     flags_used   = [];
     group_name   = "Meta";
     long_name    = "cfnop";
     intel_asm    = (fun f -> f#no_ops desc);
     att_asm      = (fun f -> f#no_ops desc)}

 | CfJmp (op,len,desc) ->
   let desc = "cfjmp(" ^ (string_of_int len) ^ "," ^ desc ^ ")" in
   { docref       = "";
     mnemonic     = "cfjmp";
     operands     = [];
     flags_set    = [];
     flags_used   = [];
     group_name   = "Meta";
     long_name    = "cfjmp";
     intel_asm    = (fun f -> f#ops desc [op]);
     att_asm      = (fun f -> f#ops desc [op])}


class string_formatter_t: [string] opcode_formatter_int =
object
  method ops s operands =
    let (_,result) = List.fold_left
      (fun (isfirst,a) op -> if isfirst
	then (false,s ^ " " ^ op#toString)
	else
	  (false, a ^ ", " ^ op#toString)) (true,s) operands in
    result

  method no_ops s = s
end


let string_formatter = new string_formatter_t

let get_operands (opc:opcode_t) = (get_record opc).operands

let get_flags_set (opc:opcode_t) = (get_record opc).flags_set

let get_flags_used (opc:opcode_t) = (get_record opc).flags_used

let get_opcode_name  (opc:opcode_t) = (get_record opc).mnemonic

let get_opcode_long_name (opc:opcode_t) = (get_record opc).long_name

let get_opcode_group (opc:opcode_t) = (get_record opc).group_name


let is_conditional_instruction (opc:opcode_t) =
  let cflags = (get_record opc).flags_used in
  let is_condition_flag f = match f with DFlag | IFlag -> false | _ -> true in
  match List.filter is_condition_flag cflags with [] -> false | _ -> true


let opcode_to_string (opc:opcode_t) =
  let default () = (get_record opc).intel_asm string_formatter in
  default ()


let write_xml_opcode (node:xml_element_int) (opc:opcode_t) (floc:floc_int) =
  let default () =
    let opr = get_record opc in
    let set = node#setAttribute in
    let osnode = xmlElement "ops" in
    begin
      osnode#appendChildren (List.map (fun op ->
	let onode = xmlElement "op" in
	begin op#write_xml onode floc; onode end) opr.operands);
      node#appendChildren [osnode];
      set "mnem" opr.mnemonic;
    end in
  default ()
