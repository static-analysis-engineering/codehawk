(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023 Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionSummary
open BCHLibTypes
open BCHSystemInfo

(* bchlibpower32 *)
open BCHPowerAssemblyInstruction
open BCHPowerTypes

module TR = CHTraceResult


(* --------------------------------------------------------------------------------
 * Note:
 * It is assumed that all instructions are at 4-byte boundaries. Address indices
 * are obtained by dividing the actual address by 4. Unlike x86 there are no
 * instructions in the instruction array at unaligned addresses.
 * -------------------------------------------------------------------------------- *)


let numArrays = 10000
let arrayLength = 100000

let initialized_length = ref 0


let power_instructions =
  ref (Array.make 1 (make_power_assembly_instruction wordzero false OpInvalid ""))


let power_instructions = 
  Array.make
    numArrays
    (Array.make 1 (make_power_assembly_instruction wordzero false OpInvalid ""))


let initialize_power_instructions (len: int) =
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [STR "Initialize "; INT len; STR " bytes"]) in
  let remaining = ref len in
  let index = ref 0 in
  begin
    while !remaining > 0 && !index < numArrays do
      power_instructions.(!index) <-
        Array.make
          arrayLength (make_power_assembly_instruction wordzero false OpInvalid "");
      remaining := !remaining - arrayLength ;
      index := !index + 1 
    done ;
    initialized_length := len;
    if !remaining > 0 then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Not sufficient array space to store all instruction bytes"]))
  end


let get_indices (index:int) = (index/arrayLength, index mod arrayLength)


let set_instruction (index: int) (instruction: power_assembly_instruction_int) =
  try
    let (i,j) = get_indices index in
    power_instructions.(i).(j) <- instruction
  with
  | Invalid_argument s ->
     raise (Invalid_argument ("set_instruction: " ^ s))


let initialize_instruction_segment (endindex: int) =
  for index = 0 to (endindex - 1) do
    set_instruction index (make_power_assembly_instruction wordzero false OpInvalid "")
  done


let get_instruction (index: int): power_assembly_instruction_result =
  if index >= 0 && index <= !initialized_length then
    let (i,j) = get_indices index in
    Ok (power_instructions.(i).(j))
  else
    Error ["get_instruction:" ^ (string_of_int index)]


let fold_instructions (f: 'a -> power_assembly_instruction_int -> 'a) (init: 'a) =
  Array.fold_left (fun a arr ->
    Array.fold_left (fun a1 opc -> f a1 opc) a arr) init power_instructions


let iter_instructions (f: power_assembly_instruction_int -> unit) =
  Array.iter (fun arr -> Array.iter f arr) power_instructions


let iteri_instructions (f: int -> power_assembly_instruction_int -> unit) =
  Array.iteri (fun i arr -> 
    let k = i * arrayLength in
    Array.iteri (fun j instr -> f (k+j) instr) arr) power_instructions


class power_assembly_instructions_t
        (len: int)
        (codebase: doubleword_int): power_assembly_instructions_int =
object (self)

  val codeBase = codebase
  val codeEnd = codebase#add_int len
  val length = len

  method length = length

  (* Return the index that corresponds to the virtual address. If
     the virtual address is out-of-range, return None. *)
  method private indexresult (va: doubleword_int): int TR.traceresult =
    if codeBase#le va && va#lt codeEnd then
      va#subtract_to_int codeBase
    else
      Error ["index:"^ va#to_hex_string]

  method private at_index (index:int): power_assembly_instruction_result =
    TR.tmap
      ~msg:"at_index"
      (fun instr ->
        if instr#get_address#equal wordzero then
          let newInstr =
            make_power_assembly_instruction
              (codeBase#add_int index) true OpInvalid "" in
          begin
            set_instruction index newInstr;
            newInstr
          end
        else
          instr)
      (get_instruction index)

  method set_instruction
           (va: doubleword_int) (instr:power_assembly_instruction_int) =
    log_tfold
      (mk_tracelog_spec ~tag:"disassembly" ("set instruction:" ^ va#to_hex_string))
      ~ok:(fun index -> set_instruction index instr)
      ~error:(fun _ -> ())
      (self#indexresult va)

  method get_instruction (va:doubleword_int): power_assembly_instruction_result =
    TR.tbind
      ~msg:"assembly_instructions:get_instruction"
      self#at_index
      (self#indexresult va)

  method is_code_address (va: doubleword_int) =
    codeBase#le va && va#lt codeEnd

    (*
  method set (index: int) (instr: power_assembly_instruction_int) =
    try
      set_instruction index instr
    with
    | Invalid_argument _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "set: Instruction index out of range: ";
                 INT index;
                 STR " (length is ";
                 INT length;
                 STR ")"]))
     *)

  method set_not_code (datablocks: data_block_int list) =
    List.iter self#set_not_code_block datablocks

  method private set_not_code_block (db: data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    log_tfold
      (mk_tracelog_spec
         ~tag:"disassembly"
         ("set_not_code_block:startaddr:" ^ startaddr#to_hex_string))
      ~ok:(fun startindex ->
        log_tfold
          (mk_tracelog_spec
             ~tag:"disassembly"
             ("set_not_code_block:endaddr:" ^ endaddr#to_hex_string))
          ~ok: (fun endindex ->
            let startinstr =
              make_power_assembly_instruction
                startaddr true (NotCode (Some (DataBlock db))) "" in
            begin
              set_instruction startindex startinstr;
              for i = startindex + 1 to endindex - 1 do
                set_instruction
                  i
                  (make_power_assembly_instruction
                     (codeBase#add_int i) true (NotCode None) "")
              done;
              (if collect_diagnostics () then
                 ch_diagnostics_log#add
                   "not code (data block)"
                   (LBLOCK [startaddr#toPretty; STR " - "; endaddr#toPretty]))
            end)
          ~error:(fun _ -> ())
          (self#indexresult endaddr))
      ~error:(fun _ -> ())
      (self#indexresult startaddr)

   (*
  method private set_not_code_block (db: data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    let startindex = (TR.tget_ok (startaddr#subtract_to_int codeBase)) / 4 in
    let startinstr =
      make_power_assembly_instruction
        startaddr false (NotCode (Some (DataBlock db))) "" in
    let endindex = (TR.tget_ok (endaddr#subtract_to_int codeBase)) / 4 in
    begin
      self#set startindex startinstr ;
      for i = startindex + 1  to endindex - 1 do
        let iaddr = codeBase#add_int i in
        self#set i (make_power_assembly_instruction iaddr false (NotCode None) "")
      done
    end
    *)

    (*
  method at_index (index: int) =
    try
      let instr = get_instruction index in
      if instr#get_address#equal wordzero then
	let newInstr =
          make_power_assembly_instruction
            (codeBase#add_int index) false NoOperation "" in
	begin
          set_instruction index newInstr;
          newInstr
        end
      else
	instr
    with
    | Invalid_argument s ->
       raise
         (BCH_failure
	    (LBLOCK [
                 STR "at_index: Instruction index out of range: ";
                 INT index ;
                 STR ": ";
                 STR s;
		 STR " (length is ";
                 INT length ; STR ")"]))
     *)

  method get_next_valid_instruction_address
           (va: doubleword_int): doubleword_int TR.traceresult =
    TR.tbind
      ~msg:("get_next_valid_instruction_address:" ^ va#to_hex_string)
      (fun index ->
        let optnextindex =
          let rec loop i =
            if i >= self#length then
              None
            else
              match TR.to_option (self#at_index i) with
              | Some instr when instr#is_not_code -> None
              | Some instr ->
                 (match instr#get_opcode with
                  | OpInvalid -> loop (i + 1)
                  | _ -> Some i)
              | _ -> None in
          loop (index + 1) in
        (match optnextindex with
         | Some nextindex -> Ok (codeBase#add_int nextindex)
         | _ ->
            Error [
                "get_next_valid_instruction_address:not found:"
                ^ va#to_hex_string]))
      (self#indexresult va)

  method get_prev_valid_instruction_address
           (va: doubleword_int): doubleword_int TR.traceresult =
    TR.tbind
      ~msg:("get_previous_valid_instruction_address:" ^ va#to_hex_string)
      (fun index ->
        let optprevindex =
          let rec loop i =
            if i < 0 then
              None
            else
              match TR.to_option (self#at_index i) with
              | Some instr when instr#is_not_code -> None
              | Some instr ->
                 (match instr#get_opcode with
                  | OpInvalid -> loop (i - 1)
                  | _ -> Some i)
              | _ -> None in
          loop (index - 1) in
        (match optprevindex with
         | Some previndex -> Ok (codeBase#add_int previndex)
         | _ ->
            Error [
                "get_prev_valid_instruction_address:not found:"
                ^ va#to_hex_string]))
      (self#indexresult va)

  method has_next_valid_instruction (va: doubleword_int): bool =
    TR.to_bool
      (fun index ->
        let rec loop i =
          if i >= len then
            false
          else
            (match TR.to_option (self#at_index i) with
             | Some instr when instr#is_not_code -> false
             | Some instr ->
                (match instr#get_opcode with
                 | OpInvalid -> loop (i + 1)
                 | _ -> true)
             | _ -> false) in
        loop (index + 1))
      (self#indexresult va)

  method has_prev_valid_instruction (va: doubleword_int): bool =
    TR.to_bool
      (fun index ->
        let rec loop i =
          if i < 0 then
            false
          else
            (match TR.to_option (self#at_index i) with
             | Some instr when instr#is_not_code -> false
             | Some instr ->
                (match instr#get_opcode with
                 | OpInvalid -> loop (i - 1)
                 | _ -> true)
             | _ -> false) in
        loop (index - 1))
      (self#indexresult va)

  (* assume all instructions are aligned on 4-byte boundaries
  method at_address (va: doubleword_int) =
    try
      let index = (TR.tget_ok (va#subtract_to_int codeBase)) / 4 in
      self#at_index index
    with
    | BCH_failure p ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in assembly-instructions:at-address: ";
                 va#toPretty;
                 STR " with codeBase: ";
                 codeBase#toPretty;
                 STR ": ";
                 p]))
   *)

  method get_code_addresses_rev ?(low=codeBase) ?(high=wordmax) () =
    let low = if low#lt codeBase then codeBase else low in
    let high =
      if (codeBase#add_int length)#lt high then
        codeBase#add_int (length-1)
      else
        high in
    let high = if high#lt low then low else high in
    let addresses = ref [] in
    let _ =
      log_titer
        (mk_tracelog_spec
           ~tag:"disassembly"
           ("get_code_addresses_rev:low:" ^ low#to_hex_string))
        (fun lowindex ->
          log_titer
            (mk_tracelog_spec
               ~tag:"disassembly"
               ("get_code_addresses_rev:high:" ^ high#to_hex_string))
            (fun highindex ->
              begin
                for i = lowindex to highindex do
                  (match TR.to_option (get_instruction i) with
                   | Some instr ->
                      if instr#is_valid_instruction then
                        addresses := (codeBase#add_int i) :: !addresses
                   | _ -> ())
                done;
              end)
            (self#indexresult high))
        (self#indexresult low) in
    !addresses

  method get_num_instructions =
    (List.length (self#get_code_addresses_rev ()))

  method get_num_unknown_instructions =
    let n = ref 0 in
    let _ =
      self#iteri (fun _ instr ->
          match instr#get_opcode with
          | NotRecognized _ -> n := !n + 1
          | _ -> ()) in
    !n

  method iteri (f: int -> power_assembly_instruction_int -> unit) =
    iteri_instructions
      (fun i instr -> if i < len then f i instr else ())

  method itera (f: doubleword_int -> power_assembly_instruction_int -> unit) =
    self#iteri (fun i instr -> f (codeBase#add_int i) instr)

  method write_xml (node: xml_element_int) = ()

  method toString ?(filter = fun _ -> true) () =
    let lines = ref [] in
    let firstNew = ref true in
    let add_function_names va =
      if functions_data#is_function_entry_point va then
        if functions_data#has_function_name va then
          let names = (functions_data#get_function va)#get_names in
          let fLine = match names with
            | [] -> ""
            | [ name ] ->
               "\nfunction: " ^ name ^ "\n"
               ^ (functions_data#get_function va)#get_function_name
            | _ ->
               "\nfunctions:\n"
               ^ (String.concat "\n" (List.map (fun n -> "    " ^ n) names))
               ^ "\n"
               ^ (functions_data#get_function va)#get_function_name in
          let line = "\n" ^ (string_repeat "-" 80) ^ fLine ^ "\n"
                     ^ (string_repeat "-" 80) in
          lines := line :: !lines
        else
          lines := "\n" :: !lines in
    begin
      self#itera
        (fun va instr ->
          try
            if filter instr then
              match instr#get_opcode with
              | OpInvalid -> ()
              | NotCode None -> ()
              | _ ->
                 let statusString = Bytes.make 4 ' ' in
                 let _ =
                   if functions_data#is_function_entry_point va then
                     Bytes.set statusString 0 'F' in
                 let _ =
                   if instr#is_block_entry then
                     Bytes.set statusString 2 'B' in
                 let instrbytes = instr#get_instruction_bytes in
                 let spacedstring = byte_string_to_spaced_string instrbytes in
                 let len = String.length spacedstring in
                 let bytestring =
                   if len <= 16 then
                     let s = Bytes.make 16 ' ' in
                     begin
                       Bytes.blit (Bytes.of_string spacedstring) 0 s 0 len;
                       Bytes.to_string s
                     end
                   else
                     spacedstring ^ "\n" ^ (String.make 24 ' ') in
                 let _ =
                   if !firstNew then
                     begin
                       lines := "\n" :: !lines;
                       firstNew := false
                     end in
                 let _ = add_function_names va in
                 let addr = va#to_hex_string in
                 let line =
                   (Bytes.to_string statusString)
                   ^ addr
                   ^ "  "
                   ^ bytestring
                   ^ "  "
                   ^ instr#toString in
                 lines := line :: !lines
            else
              firstNew := true
          with
          | BCH_failure p ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Error in instruction: ";
                       va#toPretty;
                       STR ": ";
                       p])));
      String.concat "\n" (List.rev !lines)
    end

  method toPretty = STR (self#toString ())

end


let power_assembly_instructions = ref (new power_assembly_instructions_t 1 wordzero)


let initialize_power_assembly_instructions
      (length: int)    (* in bytes *)
      (codebase: doubleword_int) =
  begin
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "Initialize ";
           INT length;
           STR " bytes; ";
           codebase#toPretty;
           STR " - ";
           (codebase#add_int length)#toPretty]);
    power_assembly_instructions := new power_assembly_instructions_t length codebase
  end


let get_power_assembly_instruction (a: doubleword_int) =
  !power_assembly_instructions#get_instruction a


let set_power_assembly_instruction (instr: power_assembly_instruction_int) =
  !power_assembly_instructions#set_instruction instr#get_address instr


let get_next_valid_instruction_address
      (a: doubleword_int): doubleword_int traceresult =
  !power_assembly_instructions#get_next_valid_instruction_address a


let has_next_valid_instruction (a: doubleword_int) =
  !power_assembly_instructions#has_next_valid_instruction a
