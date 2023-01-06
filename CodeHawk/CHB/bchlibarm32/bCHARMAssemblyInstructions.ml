(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs, LLC

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
open BCHDataBlock
open BCHDoubleword
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionSummary
open BCHLibTypes
open BCHStreamWrapper
open BCHStrings
open BCHSystemInfo
open BCHSystemSettings

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMAssemblyInstruction
open BCHARMTypes
open BCHARMOpcodeRecords


module H = Hashtbl
module TR = CHTraceResult


let numArrays = 1000
let arrayLength = 100000

let initialized_length = ref 0

(*
let arm_instructions =
  ref (Array.make 1 (make_arm_assembly_instruction wordzero true OpInvalid ""))
 *)

let arm_instructions =
  Array.make
    numArrays
    (Array.make 1 (make_arm_assembly_instruction wordzero true OpInvalid ""))


let initialize_arm_instructions (len:int) =
  if len < numArrays * arrayLength then
    let _ =
      chlog#add
        "disassembly"
        (LBLOCK [STR "Initialize "; INT len; STR " instructions bytes"]) in
    let remaining = ref len in
    let index = ref 0 in
    begin
      while !remaining > 0 && !index < numArrays do
        arm_instructions.(!index) <-
          Array.make
            arrayLength
            (make_arm_assembly_instruction wordzero true OpInvalid "");
        remaining := !remaining - arrayLength;
        index := !index + 1
      done;
      initialized_length := len
    end
  else
    raise
      (BCH_failure
         (LBLOCK [
              STR "Not sufficient array space to store all instruction bytes. ";
              STR "Requested: ";
              INT len;
              STR "; maximum available: ";
              INT (numArrays * arrayLength)]))


let get_indices (index:int) = (index/arrayLength, index mod arrayLength)


(* Enter the instruction in the backing array at the given index. If the
   index is out-of-range of the initialized length of the backing array,
   log an error message (but don't fail).
 *)
let set_instruction (index:int) (instr:arm_assembly_instruction_int) =
  if index >= 0 && index <= !initialized_length then
    let (i,j) = get_indices index in
    arm_instructions.(i).(j) <- instr
  else
    ch_error_log#add
      "set_instruction:invalid address"
      (LBLOCK [INT index; STR ": "; instr#toPretty])


let initialize_instruction_segment (endindex:int) =
  for index = 0 to (endindex - 1) do
    set_instruction
      index (make_arm_assembly_instruction wordzero true OpInvalid "")
  done


(* Return the instruction at the given index from the backing store; if
   the index is out-of-range, return None. *)
let get_instruction (index:int): arm_assembly_instruction_result =
  if index >= 0 && index <= !initialized_length then
    let (i,j) = get_indices index in
    Ok (arm_instructions.(i).(j))
  else
    Error ["get_instruction:" ^ (string_of_int index)]


let fold_instructions (f:'a -> arm_assembly_instruction_int -> 'a) (init:'a) =
  Array.fold_left
    (fun a arr ->
      Array.fold_left (fun a1 opc -> f a1 opc) a arr) init arm_instructions


let iter_instructions (f:arm_assembly_instruction_int -> unit) =
  Array.iter (fun arr -> Array.iter f arr) arm_instructions


let iteri_instructions (f:int -> arm_assembly_instruction_int -> unit) =
  Array.iteri
    (fun i arr ->
      let k = i * arrayLength in
      Array.iteri (fun j instr -> f (k+j) instr) arr) arm_instructions


class arm_assembly_instructions_t
        (len:int) (code_base:doubleword_int):arm_assembly_instructions_int =
object (self)

  val codeBase = code_base
  val codeEnd = code_base#add_int len
  val length = len
  val aggregates = H.create 3

  method length = length

  (* Return the index that corresponds to the virtual address. If
     the virtual address is out-of-range, return None. *)
  method private indexresult (va: doubleword_int): int TR.traceresult =
    if codeBase#le va && va#lt codeEnd then
      va#subtract_to_int codeBase
    else
      Error ["index:"^ va#to_hex_string]

  method private at_index (index:int): arm_assembly_instruction_result =
    TR.tmap
      ~msg:"at_index"
      (fun instr ->
        if instr#get_address#equal wordzero then
          let newInstr =
            make_arm_assembly_instruction
              (codeBase#add_int index) true OpInvalid "" in
          begin
            set_instruction index newInstr;
            newInstr
          end
        else
          instr)
      (get_instruction index)

  method set_instruction
           (va: doubleword_int) (instr:arm_assembly_instruction_int) =
    log_tfold
      (mk_tracelog_spec ~tag:"disassembly" ("set instruction:" ^ va#to_hex_string))
      ~ok:(fun index -> set_instruction index instr)
      ~error:(fun _ -> ())
      (self#indexresult va)

  method get_instruction (va:doubleword_int): arm_assembly_instruction_result =
    TR.tbind
      ~msg:"assembly_instructions:get_instruction"
      self#at_index
      (self#indexresult va)

  method set_aggregate
           (va: doubleword_int) (agg: arm_instruction_aggregate_int) =
    begin
      log_tfold
        (mk_tracelog_spec ~tag:"disassembly" ("set aggregate:" ^ va#to_hex_string))
        ~ok:(fun index ->
          begin
            H.add aggregates index agg;
            agg#anchor#set_aggregate_anchor;
            agg#entry#set_aggregate_entry;
            agg#exitinstr#set_aggregate_exit;
            List.iter (fun instr -> instr#set_in_aggregate va) agg#instrs
          end)
        ~error:(fun _ -> ())
        (self#indexresult va);
      (match agg#kind with
       | ARMJumptable jt -> self#set_jumptable jt#to_jumptable
       | _ -> ())
    end

  method get_aggregate (va: doubleword_int): arm_instruction_aggregate_int =
    let index =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "get_aggregate:" ; va#toPretty]))
        (self#indexresult va) in
    if H.mem aggregates index then
      H.find aggregates index
    else
      raise (BCH_failure (LBLOCK [STR "No aggregate found at "; va#toPretty]))

  method has_aggregate (va: doubleword_int): bool =
    TR.to_bool (H.mem aggregates) (self#indexresult va)

  method set_not_code (data_blocks: data_block_int list) =
    List.iter self#set_not_code_block data_blocks

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
              make_arm_assembly_instruction
                startaddr true (NotCode (Some (DataBlock db))) "" in
            begin
              set_instruction startindex startinstr;
              for i = startindex + 1 to endindex - 1 do
                set_instruction
                  i
                  (make_arm_assembly_instruction
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

  (* method private set_jumptables (jumptables: jumptable_int list) =
    List.iter self#set_jumptable jumptables *)

  method private set_jumptable (jumptable: jumptable_int) =
    let saddr = jumptable#get_start_address in
    let eaddr = jumptable#get_end_address in
    log_titer
      (mk_tracelog_spec
         ~tag:"disassembly"
         ("set_jumptable:" ^ saddr#to_hex_string))
      (fun startindex ->
        log_titer
          (mk_tracelog_spec
             ~tag:"disassembly"
             ("set_jumptable:" ^ eaddr#to_hex_string))
          (fun endindex ->
            let startinstr =
              make_arm_assembly_instruction
                saddr true (NotCode (Some (JumpTable jumptable))) "" in
            begin
              set_instruction startindex startinstr;
              for i = startindex + 1 to endindex - 1 do
                set_instruction
                  i
                  (make_arm_assembly_instruction
                     (codeBase#add_int i) true (NotCode None) "")
              done;
              (if collect_diagnostics () then
                 ch_diagnostics_log#add
                   "not code (jump table)"
                   (LBLOCK [saddr#toPretty; STR " - "; eaddr#toPretty]))
            end)
          (self#indexresult eaddr))
      (self#indexresult saddr)

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

  method is_code_address (va:doubleword_int) =
    TR.to_bool
      (fun instr -> instr#is_valid_instruction) (self#get_instruction va)

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
      
  method iteri (f:int -> arm_assembly_instruction_int -> unit) =
    iteri_instructions
      (fun i instr -> if i < len then f i instr else ())

  method itera (f:doubleword_int -> arm_assembly_instruction_int -> unit) =
    self#iteri (fun i instr -> f (codeBase#add_int i) instr)

  method write_xml (node:xml_element_int) =
    let bnode = ref (xmlElement "b") in
    self#itera
      (fun va instr ->
        if instr#is_valid_instruction then
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
    let lines = ref [] in
    let firstNew = ref true in
    let not_code_to_string nc =
      match nc with
      | JumpTable jt ->
         let s =
           jt#toString
             ~is_function_entry_point:(fun _ -> false)
             ~get_opt_function_name:(fun _ -> None) in
         ("\n" ^ s ^ "\n")
      | DataBlock db ->
         let s = db#get_data_string in
         let ch = make_pushback_stream s in
         let len = String.length s in
         let addr = ref db#get_start_address in
         let contents = ref [] in
         try
           begin
             for i = 0 to ((len/4) - 1) do
               begin
                 contents := (!addr, ch#read_doubleword) :: !contents;
                 addr := !addr#add_int 4
               end
             done;
             ("\n" ^ (string_repeat "~" 80) ^ "\nData block (size: "
              ^ (string_of_int len) ^ " bytes)\n\n"
              ^ (String.concat
                   "\n"
                   (List.map
                      (fun (a, v) ->
                        let addr = a#to_hex_string in
                        match elf_header#get_string_at_address v with
                        | Some s ->
                           "  " ^ addr ^ "  " ^ v#to_hex_string
                           ^ ": \"" ^ s ^ "\""
                        | _ ->
                           "  " ^ addr ^ "  " ^ v#to_hex_string)
                      (List.rev !contents)))
              ^ "\n" ^ (string_repeat "=" 80) ^ "\n")
           end
         with
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [STR "Error in data block of length "; INT len])) in
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
              | NotCode (Some b) -> lines := (not_code_to_string b) :: !lines
              | _ ->
                 let statusString = Bytes.make 4 ' ' in
                 let _ =
                   if functions_data#is_function_entry_point va then
                     Bytes.set statusString 0 'F' in
                 let  _ =
                   if instr#is_block_entry then
                     Bytes.set statusString 2 'B' in
                 (* let _ =
                   if instr#is_aggregate then
                     Bytes.set statusString 2 'A' in
                 let _ =
                   if instr#is_subsumed then
                     Bytes.set statusString 2 'S' in  *)
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
                     begin lines := "\n" :: !lines ; firstNew := false end in
                 let _ = add_function_names va in
                 let addr = va#to_hex_string in
                 let line =
                   (Bytes.to_string statusString) ^ addr ^ "  "
                   ^ bytestring ^ "  " ^ instr#toString in
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
                       p]))
          | _ ->
             ch_error_log#add "unknown error in toString"
               (LBLOCK [
                    STR "Unknown error in instruction: ";
                    va#toPretty;
                    STR ": ";
                    STR instr#toString]));
      String.concat "\n" (List.rev !lines)
    end

end


let arm_assembly_instructions = ref (new arm_assembly_instructions_t 1 wordzero)


let get_arm_assembly_instruction (a: doubleword_int) =
  !arm_assembly_instructions#get_instruction a


let set_arm_assembly_instruction (instr: arm_assembly_instruction_int) =
  !arm_assembly_instructions#set_instruction instr#get_address instr


let get_next_valid_instruction_address
      (a: doubleword_int): doubleword_int traceresult =
  !arm_assembly_instructions#get_next_valid_instruction_address a


let has_next_valid_instruction (a: doubleword_int) =
  !arm_assembly_instructions#has_next_valid_instruction a


let initialize_arm_assembly_instructions
      (length:int)  (* in bytes *)
      (codebase:doubleword_int)
      (datablocks: data_block_int list) =
  begin
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "Initialize ";
           INT length;
           STR " bytes: ";
           codebase#toPretty;
           STR " - ";
           (codebase#add_int length)#toPretty]);
    if length <= !initialized_length then
      begin
        initialize_instruction_segment length;
        arm_assembly_instructions := new arm_assembly_instructions_t length codebase;
        !arm_assembly_instructions#set_not_code datablocks
      end
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Unable to initialize arm assembly instructions with length ";
                INT length;
                STR ". Initialized length is only ";
                INT !initialized_length]))
  end


let set_data_references (lst: doubleword_int list) =
  let lst = List.sort (fun d1 d2 -> d1#compare d2) lst in
  let rec get
            (l: doubleword_int list)
            (w: doubleword_int list)
            (blocks: data_block_int list) =
    match l with
    | [] ->
       (match w with
        | [] -> blocks
        | _ ->
           let lastaddr = List.hd w in
           let w = List.rev w in
           let firstaddr = List.hd w in
           (match !arm_assembly_instructions#get_instruction firstaddr with
            | Ok instr when instr#is_not_code -> blocks
            | _ ->
               let db =
                 TR.tget_ok (make_data_block firstaddr (lastaddr#add_int 4) "") in
               let datalen = (List.length w) * 4 in
               let datastring = elf_header#get_xsubstring firstaddr datalen in
               let _ = db#set_data_string datastring in
               db::blocks))

    | hd::tl ->
       (match w with
        | [] -> get tl [hd] blocks
        | whd::_ when (whd#add_int 4)#equal hd ->
           get tl (hd::w) blocks
        | _ ->
           let lastaddr = List.hd w in
           let w = List.rev w in
           let firstaddr = List.hd w in
           (match !arm_assembly_instructions#get_instruction firstaddr with
            | Ok instr when instr#is_not_code ->
                 get tl [hd] blocks
            | _ ->
               let db =
                 TR.tget_ok (make_data_block firstaddr (lastaddr#add_int 4) "") in
               let datalen = (List.length w) * 4 in
               let datastring = elf_header#get_xsubstring firstaddr datalen in
               let _ = db#set_data_string datastring in
               get tl [hd] (db::blocks))) in
  let datablocks = get lst [] [] in
  !arm_assembly_instructions#set_not_code datablocks


let set_aggregate (iaddr: doubleword_int) (agg: arm_instruction_aggregate_int) =
  !arm_assembly_instructions#set_aggregate iaddr agg


let has_aggregate (iaddr: doubleword_int): bool =
  !arm_assembly_instructions#has_aggregate iaddr


let get_aggregate (iaddr: doubleword_int): arm_instruction_aggregate_int =
  !arm_assembly_instructions#get_aggregate iaddr
