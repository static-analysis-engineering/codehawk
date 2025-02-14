(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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
open BCHFunctionData
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSAssemblyInstruction
open BCHMIPSTypes

module TR = CHTraceResult

(* ---------------------------------------------------------------------------
 * Note:
 * It is assumed that all instructions are at 4-byte boundaries. Address indices
 * are obtained by dividing the actual address by 4. Unlike x86 there are no
 * instructions in the instruction array at unaligned addresses.
 * ---------------------------------------------------------------------------- *)


let numArrays = 1000
let arrayLength = 100000

let initialized_length = ref 0


let mips_instructions = 
  Array.make
    numArrays
    (Array.make 1 (make_mips_assembly_instruction wordzero OpInvalid ""))


let initialize_mips_instructions len =
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [STR "Initialize "; INT len; STR " instructions"]) in
  let remaining = ref len in
  let index = ref 0 in
  begin
    while !remaining > 0 && !index < numArrays do
      mips_instructions.(!index) <-
        Array.make
          arrayLength (make_mips_assembly_instruction wordzero OpInvalid "");
      remaining := !remaining - arrayLength;
      index := !index + 1 
    done;
    initialized_length := len;
    (if !remaining > 0 then
      raise
        (BCH_failure
           (LBLOCK [
                STR "Not sufficient array space to store all instruction bytes"])));
  end


let get_indices (index:int) = (index/arrayLength, index mod arrayLength)


(* Enter the instruction in the backing array at the given index. If the
   index is out-of-range of the initialized length of the backing array,
   log an error message (but don't fail).
 *)
let set_instruction (index: int) (instr: mips_assembly_instruction_int) =
  if index >= 0 && index <= !initialized_length then
    let (i, j) = get_indices index in
    mips_instructions.(i).(j) <- instr
  else
    ch_error_log#add
      "set_instruction:invalid address"
      (LBLOCK [INT index; STR ": "; instr#toPretty])


let initialize_instruction_segment (endindex:int) =
  for index = 0 to (endindex - 1) do
    set_instruction index (make_mips_assembly_instruction wordzero OpInvalid "")
  done


(* Return the instruction at the given index from the backing store; if
   the index is out-of-range, return an error. *)
let get_instruction (index: int): mips_assembly_instruction_result =
  if index >= 0 && index <= !initialized_length then
    let (i, j) = get_indices index in
    Ok (mips_instructions.(i).(j))
  else
    Error ["get_instruction:" ^ (string_of_int index)]


(*
let fold_instructions (f:'a -> mips_assembly_instruction_int -> 'a) (init:'a) =
  Array.fold_left (fun a arr ->
    Array.fold_left (fun a1 opc -> f a1 opc) a arr) init mips_instructions


let iter_instructions (f: mips_assembly_instruction_int -> unit) =
  Array.iter (fun arr -> Array.iter f arr) mips_instructions
 *)

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

  method length = length

  (* assume all instructions are aligned on 4-byte boundaries. *)
  method private indexresult (va: doubleword_int): int TR.traceresult =
    if codeBase#le va && va#le codeEnd then
      TR.tmap (fun i -> i / 4) (va#subtract_to_int codeBase)
    else
      Error [
          "index:"
          ^ va#to_hex_string
          ^ "; codeBase: "
          ^ codeBase#to_hex_string
          ^ "; codeEnd: "
          ^ codeEnd#to_hex_string]

  method private at_index (index: int): mips_assembly_instruction_result =
    TR.tbind
      (fun instr ->
        if instr#get_address#equal wordzero then
          let newInstr =
            make_mips_assembly_instruction
              (codeBase#add_int index) NoOperation "" in
          begin
            set_instruction index newInstr;
            Ok newInstr
          end
        else if instr#is_invalid then
          Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                 ^ "Instruction at address "
                 ^ instr#get_address#to_hex_string
                 ^ " is invalid"]
        else
          Ok instr)
      (get_instruction index)

  method set_instruction
           (va: doubleword_int) (instr: mips_assembly_instruction_int) =
    log_tfold
      (mk_tracelog_spec ~tag:"disassembly" ("set_instruction:" ^ va#to_hex_string))
      ~ok:(fun index -> set_instruction index instr)
      ~error:(fun _ -> ())
      (self#indexresult va)

  method get_instruction (va: doubleword_int): mips_assembly_instruction_result =
    TR.tbind
      ~msg:"assembly_instructions:get_instruction"
      self#at_index
      (self#indexresult va)

  method is_code_address (va: doubleword_int) =
    codeBase#le va && va#lt codeEnd

  method set_not_code (datablocks:data_block_int list) =
    List.iter self#set_not_code_block datablocks

  method private set_not_code_block (db:data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    TR.tfold
      ~ok:(fun startindex ->
        TR.tfold
          ~ok:(fun endindex ->
            let startinstr =
              make_mips_assembly_instruction
                startaddr (NotCode (Some (DataBlock db))) "" in
            begin
              set_instruction startindex startinstr;
              for i = startindex + 1 to endindex - 1 do
                let iaddr = codeBase#add_int (i * 4) in
                set_instruction
                  i
                  (make_mips_assembly_instruction iaddr (NotCode None) "")
              done;
              (if collect_diagnostics () then
                 ch_diagnostics_log#add
                   "not code (data block)"
                   (LBLOCK [startaddr#toPretty; STR " - "; endaddr#toPretty]))
            end)
          ~error:(fun e ->
            log_error_result
              ~tag:"disassembly" __FILE__ __LINE__
              (("endaddr: " ^ endaddr#to_hex_string) :: e))
          (self#indexresult endaddr))
      ~error:(fun e ->
        log_error_result
          ~tag:"disassembly" __FILE__ __LINE__
          (("startaddr: " ^ startaddr#to_hex_string) :: e))
      (self#indexresult startaddr)

  method get_code_addresses_rev ?(low=codeBase) ?(high=wordmax) () =
    let low = if low#lt codeBase then codeBase else low in
    let high = 
      if (codeBase#add_int length)#lt high then
        codeBase#add_int (length-1)
      else
        high in
    let high = if high#lt low then low else high in
    let low = (TR.tget_ok (low#subtract_to_int codeBase)) / 4 in
    let high = (TR.tget_ok (high#subtract_to_int codeBase)) / 4 in
    let addresses = ref [] in
    begin
      for i = low to high do
	addresses := (codeBase#add_int (i*4)) :: !addresses
      done;
      !addresses
    end

  method get_num_instructions =
    List.length (self#get_code_addresses_rev ())

  method get_num_unknown_instructions =
    let n = ref 0 in
    let _ =
      self#iteri (fun _ instr ->
          match instr#get_opcode with
          | NotRecognized _ -> n := !n + 1
          | OpInvalid -> n := !n + 1
          | _ -> ()) in
    !n

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
              bnode := xmlElement "b";
              (!bnode)#setAttribute "ba" va#to_hex_string;
              node#appendChildren [!bnode]
            end in
        let inode = xmlElement "i" in
        begin
          instr#write_xml inode;
          (!bnode)#appendChildren [inode]
        end)

  method toString ?(filter = fun _ -> true) () =
    let stringList = ref [] in
    let firstNew = ref true in
    let add_function_names va =
      if functions_data#is_function_entry_point va
         && functions_data#has_function_name va then
	let names = (functions_data#get_function va)#get_names in
	let fLine = match names with
	  | [] -> ""
	  | [name] ->
             "\nfunction: "
             ^ name
             ^ "\n"
             ^ (functions_data#get_function va)#get_function_name
	  | _ ->
             "\nfunctions:\n"
             ^ (String.concat "\n" (List.map (fun n -> "    " ^ n) names))
             ^ "\n"
             ^ (functions_data#get_function va)#get_function_name in
	let line =
          "\n" ^ (string_repeat "~" 80) ^ fLine ^ "\n" ^ (string_repeat "~" 80) in
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
              if len = 0 then
                "<empty>"
              else if len <= 16 then
                let s = Bytes.make 16 ' ' in
                begin
                  Bytes.blit (Bytes.of_string spacedstring) 0 s 0 len;
                  Bytes.to_string s
                end
              else
                spacedstring ^ "\n" ^ (String.make 24 ' ') in
            match instr#get_opcode with
            | NotCode None -> ()
            | NotCode (Some (DataBlock db)) ->
               stringList := db#toString :: !stringList
            | OpInvalid -> ()
            | _ ->
	       let _ =
                 if !firstNew then 
		   begin
                     stringList := "\n" :: !stringList;
                     firstNew := false
                   end in
               let _ = add_function_names va in
               let line =
                 (Bytes.to_string statusString)
                 ^ va#to_hex_string
                 ^ "  "
                 ^ bytestring
                 ^ "  "
                 ^ instr#toString in
               stringList := line :: !stringList
          else
            firstNew := true);
      String.concat "\n" (List.rev !stringList)
    end
         
  method toPretty = STR "assembly instructions"
    
end


let mips_assembly_instructions = ref (new mips_assembly_instructions_t 1 wordzero)


let get_mips_assembly_instruction
      (va: doubleword_int): mips_assembly_instruction_result =
  !mips_assembly_instructions#get_instruction va


let set_mips_assembly_instruction (instr: mips_assembly_instruction_int) =
  !mips_assembly_instructions#set_instruction instr#get_address instr


let initialize_mips_assembly_instructions 
      (length:int)    (* in bytes *)
      (codebase:doubleword_int) =
  let instrcount = length / 4 in
  begin
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "Initialize ";
           INT instrcount;
           STR " instructions: ";
           codebase#toPretty;
           STR " - ";
           (codebase#add_int length)#toPretty]);
    initialize_instruction_segment instrcount;
    mips_assembly_instructions :=
      new mips_assembly_instructions_t length codebase
  end
