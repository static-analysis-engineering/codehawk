(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma

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
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHFunctionApi
open BCHFunctionData
open BCHFunctionSummary
open BCHLibTypes
open BCHSystemInfo

(* bchlibmips32 *)
open BCHMIPSAssemblyInstruction
open BCHMIPSTypes
open BCHMIPSOpcodeRecords

(* --------------------------------------------------------------------------------
 * Note:
 * It is assumed that all instructions are at 4-byte boundaries. Address indices
 * are obtained by dividing the actual address by 4. Unlike x86 there are no
 * instructions in the instruction array at unaligned addresses.
 * -------------------------------------------------------------------------------- *)


let numArrays = 1000
let arrayLength = 100000

let mips_instructions =
  ref (Array.make 1 (make_mips_assembly_instruction wordzero OpInvalid ""))

let mips_instructions = 
  Array.make numArrays (Array.make 1 (make_mips_assembly_instruction wordzero OpInvalid ""))

let initialize_mips_instructions len =
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [ STR "Initialize " ; INT len ; STR " instructions" ]) in
  let remaining = ref len in
  let index = ref 0 in
  begin
    while !remaining > 0 && !index < numArrays do
      mips_instructions.(!index) <-
        Array.make arrayLength (make_mips_assembly_instruction wordzero OpInvalid "");
      remaining := !remaining - arrayLength ;
      index := !index + 1 
    done ;
    if !remaining > 0 then
      raise (BCH_failure
               (LBLOCK [STR "Not sufficient array space to store all instruction bytes"]));
  end

let get_indices (index:int) = (index/arrayLength, index mod arrayLength)

let set_instruction (index:int) (instruction:mips_assembly_instruction_int) =
  try
    let (i,j) = get_indices index in
    mips_instructions.(i).(j) <- instruction
  with
  | Invalid_argument s ->
     raise (Invalid_argument ("set_instruction: " ^ s))

let initialize_instruction_segment (endindex:int) =
  for index = 0 to (endindex - 1) do
    set_instruction index (make_mips_assembly_instruction wordzero OpInvalid "")
  done

let get_instruction (index:int) =
  let (i,j) = get_indices index in
  try
    mips_instructions.(i).(j)
  with
  | Invalid_argument s ->
     raise (
         Invalid_argument
           ("get_instruction: "
            ^ s
            ^ " ("
            ^ (string_of_int i)
            ^ ", "
            ^ (string_of_int j)
            ^ ")"))

let fold_instructions (f:'a -> mips_assembly_instruction_int -> 'a) (init:'a) =
  Array.fold_left (fun a arr ->
    Array.fold_left (fun a1 opc -> f a1 opc) a arr) init mips_instructions

let iter_instructions (f: mips_assembly_instruction_int -> unit) =
  Array.iter (fun arr -> Array.iter f arr) mips_instructions

let iteri_instructions (f: int -> mips_assembly_instruction_int -> unit) =
  Array.iteri (fun i arr -> 
    let k = i * arrayLength in
    Array.iteri (fun j instr -> f (k+j) instr) arr) mips_instructions

class mips_assembly_instructions_t
        (len:int) (code_base:doubleword_int):mips_assembly_instructions_int =
object (self)

  val codeBase = code_base
  val codeEnd = code_base#add_int len
  val length = len

  method is_code_address (va: doubleword_int) =
    codeBase#le va && va#lt codeEnd

  method set (index:int) (instruction:mips_assembly_instruction_int) =
    try
      set_instruction index instruction
    with
      Invalid_argument _ ->
	raise (BCH_failure 
		 (LBLOCK [ STR "set: Instruction index out of range: " ;
                           INT index ;
			   STR " (length is " ; INT length ; STR ")"]))

  method set_not_code (datablocks:data_block_int list) =
    List.iter self#set_not_code_block datablocks

  method private set_not_code_block (db:data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    let startindex = (startaddr#subtract codeBase)#to_int / 4 in
    let startinstr =
      make_mips_assembly_instruction startaddr (NotCode (Some (DataBlock db))) "" in
    let endindex = (endaddr#subtract codeBase)#to_int / 4 in
    begin
      self#set startindex startinstr ;
      for i = startindex + 1  to endindex - 1 do
        let iaddr = codeBase#add_int i in
        self#set i (make_mips_assembly_instruction iaddr (NotCode None) "")
      done
    end

  method length = length

  method at_index (index:int) =
    try
      let instr = get_instruction index in
      if instr#get_address#equal wordzero then
	let newInstr =
          make_mips_assembly_instruction (codeBase#add_int index) NoOperation "" in
	begin set_instruction index newInstr ; newInstr end
      else
	instr
    with
    | Invalid_argument s ->
       raise (BCH_failure
		(LBLOCK [ STR "at_index: Instruction index out of range: ";
                          INT index ;
                          STR ": ";
                          STR s;
			  STR " (length is ";
                          INT length ; STR ")"]))

  (* assume all instructions are aligned on 4-byte boundaries *)
  method at_address (va:doubleword_int) =
    try
      let index = ((va#subtract codeBase)#to_int / 4) in
      self#at_index index
    with
    | BCH_failure p ->
       raise (BCH_failure
                (LBLOCK [STR "Error in assembly-instructions:at-address: ";
                         va#toPretty;
                         STR " with codeBase: ";
                         codeBase#toPretty;
                         STR ": ";
                         p ]))

  method get_code_addresses_rev ?(low=codeBase) ?(high=wordmax) () =
    let low = if low#lt codeBase then codeBase else low in
    let high = 
      if (codeBase#add_int length)#lt high then codeBase#add_int (length-1) else high in
    let high = if high#lt low then low else high in
    let low = (low#subtract codeBase)#to_int / 4 in
    let high = (high#subtract codeBase)#to_int / 4 in
    let addresses = ref [] in
    begin
      for i = low to high do
	addresses := (codeBase#add_int (i*4)) :: !addresses
      done ;
      !addresses
    end

  method get_num_instructions =
    List.length (self#get_code_addresses_rev ())

  method get_num_unknown_instructions =
    List.fold_left
      (fun acc a ->
        match (self#at_address a)#get_opcode with
        | OpInvalid -> acc + 1
        | _ -> acc) 0 (self#get_code_addresses_rev ())

  method iteri (f:int -> mips_assembly_instruction_int -> unit) =
    iteri_instructions
      (fun i instr -> if i < len / 4 then f i instr else ())

  method itera (f:doubleword_int -> mips_assembly_instruction_int -> unit) =
    self#iteri (fun i instr -> f (codeBase#add_int (i*4)) instr)

  method write_xml (node:xml_element_int) =
    let bnode = ref (xmlElement "b") in
    self#itera
      (fun va instr ->
        let _ =
          if instr#is_block_entry then
            begin
              bnode := xmlElement "b" ;
              (!bnode)#setAttribute "ba" va#to_hex_string ;
              node#appendChildren [ !bnode ]
            end in
        let inode = xmlElement "i" in
        begin
          instr#write_xml inode;
          (!bnode)#appendChildren [ inode ]
        end)

  method toString ?(filter = fun _ -> true) () =
    let stringList = ref [] in
    let firstNew = ref true in
    let add_function_names va =
      if functions_data#is_function_entry_point va && functions_data#has_function_name va then
	let names = (functions_data#get_function va)#get_names in
	let fLine = match names with
	  | [] -> ""
	  | [ name ] -> "\nfunction: " ^ name ^ "\n" ^
	    (functions_data#get_function va)#get_function_name
	  | _ -> "\nfunctions:\n" ^ 
	    (String.concat "\n" (List.map (fun n -> "    " ^ n) names)) ^ "\n" ^
	    (functions_data#get_function va)#get_function_name in
	let line = "\n" ^ (string_repeat "~" 80) ^ fLine ^ "\n" ^
	  (string_repeat "~" 80) in
	stringList := line :: !stringList in      
    begin
      self#itera
        (fun va instr ->
          if filter instr then
            let statusString = Bytes.make 4 ' ' in
            let _ =
              if functions_data#is_function_entry_point va then
                  Bytes.set statusString 0 'F' in
            let _ =
              if instr#is_block_entry then
                Bytes.set statusString 2 'B' in
            let _ =
              if instr#is_delay_slot then
                Bytes.set statusString 2 'D' in
            let instrbytes = instr#get_instruction_bytes in
            let spacedstring = byte_string_to_spaced_string instrbytes in
            let len = String.length spacedstring in
            let bytestring =
              if len <= 16 then
                let s = Bytes.make 16 ' ' in
                begin
                  Bytes.blit (Bytes.of_string spacedstring) 0 s 0 len ;
                  Bytes.to_string s
                end
              else
                spacedstring ^ "\n" ^ (String.make 24 ' ') in
            match instr#get_opcode with
            | NotCode None -> ()
            | NotCode (Some (DataBlock db)) ->
               stringList := db#toString :: !stringList
            | OpInvalid ->
               let line = (Bytes.to_string statusString) ^ va#to_hex_string ^ "  "
                          ^ bytestring ^ "  "  ^ "**invalid**" in
               stringList := line ::  !stringList
                        
            | _ ->
	       let _ =
                 if !firstNew then 
		   begin stringList := "\n" :: !stringList ; firstNew := false end in
               let _ = add_function_names va in
               let line = (Bytes.to_string statusString) ^ va#to_hex_string ^ "  "
                          ^ bytestring ^ "  " ^ instr#toString in
               stringList := line :: !stringList
          else
            firstNew := true) ;
      String.concat "\n" (List.rev !stringList)
    end
         
  method toPretty = STR "assembly instructions"
    
end

let mips_assembly_instructions = ref (new mips_assembly_instructions_t 1 wordzero)

let initialize_mips_assembly_instructions 
      (length:int)    (* in bytes *)
      (codebase:doubleword_int) =
  let instrcount = length / 4 in
  begin
    chlog#add
      "disassembly"
      (LBLOCK [ STR "Initialize " ; INT instrcount ; STR " instructions: " ;
                codebase#toPretty ; STR " - " ; (codebase#add_int length)#toPretty ]) ;
    initialize_instruction_segment instrcount ;
    mips_assembly_instructions := new mips_assembly_instructions_t length codebase ;
  end
 
