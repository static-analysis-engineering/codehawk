(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHFunctionApi
open BCHFunctionData
open BCHFunctionSummary
open BCHLibTypes
open BCHSystemInfo

(* bchlibx86 *)
open BCHAssemblyInstruction
open BCHLibx86Types
open BCHX86OpcodeRecords
open BCHX86Opcodes


let numArrays = 1000
let arrayLength = 100000

let instructions = ref (Array.make 1 (make_assembly_instruction wordzero OpInvalid ""))

let instructions = 
  Array.make numArrays (Array.make 1 (make_assembly_instruction wordzero OpInvalid ""))

let initialize_instructions len =
  let remaining = ref len in
  let index = ref 0 in
  begin
    while !remaining > 0 && !index < numArrays do
      instructions.(!index) <-
        Array.make arrayLength (make_assembly_instruction wordzero OpInvalid "");
      remaining := !remaining - arrayLength ;
      index := !index + 1 
    done ;
    if !remaining > 0 then
      raise (BCH_failure
               (LBLOCK [ STR "Not sufficient array space to store all instruction bytes"]))
  end

let get_indices (index:int) = (index/arrayLength, index mod arrayLength)

let set_instruction (index:int) (instruction:assembly_instruction_int) =
  let (i,j) = get_indices index in
  instructions.(i).(j) <- instruction

let initialize_instruction_segment (start:int) (endindex:int) =
  for index = start to (endindex - 1) do
    set_instruction index (make_assembly_instruction wordzero OpInvalid "")
  done

let get_instruction (index:int) =	
  let (i,j) = get_indices index in instructions.(i).(j)

let fold_instructions (f:'a -> assembly_instruction_int -> 'a) (init:'a) =
  Array.fold_left (fun a arr ->
    Array.fold_left (fun a1 opc -> f a1 opc) a arr) init instructions

let iter_instructions (f: assembly_instruction_int -> unit) =
  Array.iter (fun arr ->	Array.iter f arr) instructions

let iteri_instructions (f: int -> assembly_instruction_int -> unit) =
  Array.iteri (fun i arr -> 
    let k = i * arrayLength in
    Array.iteri (fun j instr -> f (k+j) instr) arr) instructions

class assembly_instructions_t
        (len:int) (code_base:doubleword_int):assembly_instructions_int =
object (self)

  val codeBase = code_base
  val codeEnd = code_base#add_int len
  val length = len

  method set (index:int) (instruction:assembly_instruction_int) =
    try
      set_instruction index instruction
    with
      Invalid_argument _ ->
	raise (BCH_failure 
		 (LBLOCK [ STR "Instruction index out of range: " ; INT index ;
			   STR " (length is " ; INT length ; STR ")"]))

  method set_not_code (data_blocks:data_block_int list) = 
    List.iter self#set_not_code_block data_blocks

  method set_jumptables (jumptables:jumptable_int list) =
    List.iter self#set_jumptable jumptables

  method private set_not_code_block (data_block:data_block_int) =
    let startAddress = data_block#get_start_address in
    let endAddress = data_block#get_end_address in
    if startAddress#lt codeBase then
      chlog#add "not code" 
	(LBLOCK [ STR "Ignoring data block " ; STR data_block#toString ; 
		  STR "; start address is less than start of code" ]) 
    else if codeEnd#le endAddress then
      chlog#add "not code" 
	(LBLOCK [ STR "Ignoring data block " ; STR data_block#toString ;
		  STR "; end address is beyond end of code section "])
    else
      let _ = chlog#add "not code" 
	(LBLOCK [ STR "start: " ; startAddress#toPretty ; STR "; end: " ;
		  endAddress#toPretty ]) in
      let startIndex = (startAddress#subtract codeBase)#to_int in
      let startInstr = make_assembly_instruction startAddress 
	(NotCode (Some (DataBlock data_block))) "" in
      let endIndex = (endAddress#subtract codeBase)#to_int in
      begin
	set_instruction startIndex startInstr ;
	for i = startIndex + 1 to endIndex - 1 do
	  set_instruction i (make_assembly_instruction (codeBase#add_int i) (NotCode None) "")
	done
      end

  method private set_jumptable (jumptable:jumptable_int) =
    let startAddress = jumptable#get_start_address in
    let endAddress = jumptable#get_end_address in
    if codeBase#le startAddress && endAddress#le codeEnd then
      let _ = chlog#add "not code" 
	(LBLOCK [ STR "start: " ; startAddress#toPretty ; STR "; end: " ; 
		  endAddress#toPretty ; STR "; jump table" ]) in
      let startIndex = (startAddress#subtract codeBase)#to_int in
      let startInstr = make_assembly_instruction startAddress 
	(NotCode (Some (JumpTable jumptable))) "" in
      let endIndex = (endAddress#subtract codeBase)#to_int in
      begin
	set_instruction startIndex startInstr ;
	for i = startIndex + 1 to endIndex - 1 do
	  set_instruction i (make_assembly_instruction (codeBase#add_int i) (NotCode None) "")
	done
      end

  method length = length

  method is_in_code_range (address:doubleword_int) = 
    codeBase#le address && address#lt codeEnd

  method at_index (index:int) =
    try
      let instr = get_instruction index in
      if instr#get_address#equal wordzero then
	let newInstr = make_assembly_instruction (codeBase#add_int index) OpInvalid "" in
	begin set_instruction index newInstr ; newInstr end
      else
	instr
    with
      Invalid_argument _ ->
	raise (BCH_failure
		 (LBLOCK [ STR "Instruction index out of range: " ; INT index ;
			   STR " (length is " ; INT length ; STR ")"]))

  method at_address (va:doubleword_int) =
    try
      let index = (va#subtract codeBase)#to_int in self#at_index index
    with
    | Invalid_argument s ->
       raise (BCH_failure (LBLOCK [ STR "Error in assembly-instructions:at-address: " ;
                                    va#toPretty ]))

  method get_code_addresses_rev ?(low=codeBase) ?(high=wordmax) () =
    let low = if low#lt codeBase then codeBase else low in
    let high = 
      if (codeBase#add_int length)#lt high then
        codeBase#add_int (length-1)
      else
        high in
    let high = if high#lt low then low else high in
    let low = (low#subtract codeBase)#to_int in
    let high = (high#subtract codeBase)#to_int in
    let addresses = ref [] in
    begin
      for i = low to high do
	if (get_instruction i)#is_valid_instruction then
	  addresses := (codeBase#add_int i) :: !addresses
      done ;
      !addresses
    end

  method get_next_valid_instruction_address (va:doubleword_int) =
    let index = (va#subtract codeBase)#to_int in
    let rec loop i =
      if i >= len then
	raise (BCH_failure
		 (LBLOCK [ STR "There is no valid instruction after " ;
                           va#toPretty]))
      else
	match (self#at_index i)#get_opcode with 
	| OpInvalid -> loop (i+1) 
	| _ -> i in
    codeBase#add_int (loop (index+1))

  method get_jumptable (addr:doubleword_int) =
    let index = (addr#subtract codeBase)#to_int in
    let rec loop i =
      if i < 0 || i >= len then
	None
      else
	match (self#at_index i)#get_opcode with
	| NotCode None -> loop (i-1)
	| NotCode (Some (JumpTable jt)) -> Some jt
	| _ -> None in
    loop index

  method get_num_instructions = 
    (List.length (self#get_code_addresses_rev ()) ) - self#get_nop_count

  method get_num_unknown_instructions =
    let num = ref 0 in
    let _ = iter_instructions
      (fun opc -> if opc#is_unknown then
	  if List.mem opc#get_instruction_bytes [ "ffff" ] then () else num := !num + 1
	else ()) in
    !num

  method private get_nop_count =
    let num = ref 0 in
    let _ = iter_instructions (fun opc -> if opc#is_nop then num := !num + 1) in
    !num

  method get_data_blocks =
    let blocks = ref [] in
    let _ = self#iteri (fun _ instr -> match instr#get_opcode with 
	NotCode (Some (DataBlock b)) -> blocks := b :: !blocks
      | _ -> ()) in
    !blocks

  method get_opcode_stats =
    let stats = Hashtbl.create 53 in
    let add s = 
      if Hashtbl.mem stats s then 
	Hashtbl.replace stats s ((Hashtbl.find stats s) + 1) 
      else
	Hashtbl.add stats s 1 in
    begin
      iter_instructions (fun instr ->
	match instr#get_opcode with
	  OpInvalid | BreakPoint | NotCode _ ->  ()
	| opc -> add (get_opcode_long_name opc)) ;
      Hashtbl.fold (fun k v a -> (k,v)::a) stats []
    end

  method get_opcode_group_stats =
    let stats = Hashtbl.create 53 in
    let add s = 
      if Hashtbl.mem stats s then
	Hashtbl.replace stats s ((Hashtbl.find stats s) + 1) 
      else
	Hashtbl.add stats s 1 in
    begin
      iter_instructions (fun instr ->
	match instr#get_opcode with
	  OpInvalid | BreakPoint | NotCode _ -> ()
	| opc -> add (get_opcode_group opc)) ;
      Hashtbl.fold (fun k v a -> (k,v)::a) stats []
    end

  method iteri (f:int -> assembly_instruction_int -> unit) = iteri_instructions f

  method itera (f:doubleword_int -> assembly_instruction_int -> unit) =
    self#iteri (fun i instr -> f (codeBase#add_int i) instr) 

  method is_code_address (va:doubleword_int) =
    codeBase#le va && va#lt codeEnd && (self#at_address va)#is_valid_instruction

  method has_next_valid_instruction (va:doubleword_int) =
    let index = (va#subtract codeBase)#to_int in
    let rec loop i =
	if i >= len || (self#at_index i)#is_not_code then false else 
	  match (self#at_index i)#get_opcode with 
	  | OpInvalid -> loop (i+1) | _ -> true in
    loop (index+1)

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
      self#itera (fun va instruction ->
	if filter instruction then
	  let statusString = Bytes.make 4 ' ' in
	  let _ = if functions_data#is_function_entry_point va then
                    (* statusString.[0] <- 'F' in *)
                    Bytes.set statusString 0 'F' in
	  let _ = if instruction#is_block_entry then
                    (* statusString.[2] <- 'B' in *)
                    Bytes.set statusString 2 'B' in
	  let instructionBytes = instruction#get_instruction_bytes in
	  let spacedString = byte_string_to_spaced_string instructionBytes in
	  let len = String.length spacedString in
	  let byteString =  if len <= 30 then
	      let s = Bytes.make 30 ' ' in
	      begin
                Bytes.blit (Bytes.of_string spacedString) 0 s 0 len ;
                Bytes.to_string s
              end
	    else
	      spacedString ^ "\n" ^ (String.make 38 ' ') in
	  match instruction#get_opcode with
	  | OpInvalid | NotCode None -> ()
	  | NotCode (Some b) -> stringList := (not_code_to_string b) :: !stringList
	  | Ret _ | BndRet _ ->
	    let _ = add_function_names va in
	    let line = (Bytes.to_string statusString) ^ va#to_hex_string
                       ^ "  " ^ byteString ^ "  " ^ instruction#toString ^ "\n" in 
	    stringList := line :: !stringList
	  | _ ->
	    let _ = if !firstNew then 
		begin stringList := "\n" :: !stringList ; firstNew := false end in
	    let _ = add_function_names va in
	    let line = (Bytes.to_string statusString) ^ va#to_hex_string
                       ^ "  " ^ byteString ^ "  " ^ instruction#toString  in
	    stringList := line :: !stringList
	else 
	  firstNew := true) ;
      String.concat "\n" (List.rev !stringList)
    end
      
  method toPretty = STR "assembly instructions"
    
end

let assembly_instructions = ref (new assembly_instructions_t 1 wordzero)

let initialize_assembly_instructions 
    (displacement:int)
    (end_section:int)
    (length:int)
    (code_base:doubleword_int)
    (jumptables:jumptable_int list)
    (data_blocks: data_block_int list) =
  let endCode = code_base#add_int length in
  let jumptablesInCode = List.filter 
    (fun j -> code_base#le j#get_start_address && j#get_end_address#le endCode) jumptables in
  begin
    chlog#add "initialization"
      (LBLOCK [ STR "Initialize instructions of section at displacement " ; 
		INT displacement ; STR " to " ; INT end_section ; STR " with " ;
		INT (List.length jumptables) ; STR " jumptables and " ; 
		INT (List.length data_blocks) ; STR " data blocks" ]) ;
    initialize_instruction_segment displacement end_section ;
    assembly_instructions := new assembly_instructions_t length code_base ;
    !assembly_instructions#set_jumptables jumptablesInCode ;
    !assembly_instructions#set_not_code data_blocks
  end
    
