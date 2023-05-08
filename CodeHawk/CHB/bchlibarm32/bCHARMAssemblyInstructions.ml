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
open BCHARMCallSitesRecords
open BCHARMTypes
open BCHARMOpcodeRecords
open BCHDisassembleARMInstruction
open BCHDisassembleThumbInstruction


module H = Hashtbl
module TR = CHTraceResult


let numArrays = 1000
let arrayLength = 100000

let initialized_length = ref 0


let arm_instructions =
  Array.make
    numArrays
    (Array.make 1 (make_arm_assembly_instruction wordzero true OpInvalid ""))


let initialize_arm_section_instructions (startindex: int) (len: int): int =
  if len < numArrays * arrayLength then
    let _ =
      chlog#add
        "disassembly"
        (LBLOCK [STR "Initialize "; INT len; STR " instructions bytes"]) in
    let remaining = ref len in
    let index = ref startindex in
    begin
      while !remaining > 0 && !index < numArrays do
        let arraylen =
          if !remaining > arrayLength then arrayLength else !remaining in
        arm_instructions.(!index) <-
          Array.make
            arraylen
            (make_arm_assembly_instruction wordzero true OpInvalid "");
        remaining := !remaining - arraylen;
        index := !index + 1
      done;
      initialized_length := len;
      !index
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


class address_translator_t =
object (self)

  val mutable indices: (string * int * int * int) list = []
  val mutable allindices_rev: (int * int) list = []

  method initialize (sections: (string * int * int) list) =
    let (_, section_indices) =
      List.fold_left (fun (startindex, indices) (name, start, size) ->
          let newindex = initialize_arm_section_instructions startindex size in
          let newindices = (name, start, size, startindex) :: indices in
          let _ =
            pverbose [
                STR "initialized ";
                STR name;
                STR " at start address: ";
                (TR.tget_ok (int_to_doubleword start))#toPretty;
                STR " at index: ";
                INT startindex;
                STR " with size: ";
                INT size;
                STR "; new index: ";
                INT newindex;
                NL] in
          (newindex, newindices)) (0, []) sections in
    indices <- List.rev section_indices

  method get_indices (addr: doubleword_int): int * int =
    let index = addr#value in
    let (found, result) =
      List.fold_left (fun (fnd, r) (name, start, size, startindex) ->
          if fnd then
            (fnd, r)
          else if index >= start && index < start + size then
            let offset = index - start in
            (true,
             Some (startindex + (offset / arrayLength), offset mod arrayLength))
          else
            (false, r)) (false, None) indices in
    match (found, result) with
    | (true, Some (i, j)) -> (i, j)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Address: ";
                 addr#toPretty;
                 STR " could not be translated to backing array indices"]))

  method get_all_indices_rev: (int * int) list =
    if (List.length allindices_rev) > 0 then
      allindices_rev
    else
      let result = ref [] in
      begin
        List.iter (fun (_, _, size, startindex) ->
            for i = 0 to size - 1 do
              result :=
                (startindex + (i / arrayLength), i mod arrayLength) :: !result
            done) indices;
        allindices_rev <- !result;
        !result
      end

end


let address_translator = new address_translator_t


let initialize_arm_instructions
      (sections: (string * doubleword_int * doubleword_int) list) =
  address_translator#initialize
    (List.map (fun (name, start, size) -> (name, start#value, size#value)) sections)


let get_indices (addr: doubleword_int) = address_translator#get_indices addr


(* Enter the instruction in the backing array at the given index. If the
   index is out-of-range of the initialized length of the backing array,
   log an error message (but don't fail).
 *)
let set_instruction (addr: doubleword_int) (instr: arm_assembly_instruction_int) =
  try
    let (i, j) = get_indices addr in
    arm_instructions.(i).(j) <- instr
  with
  | BCH_failure p ->
     ch_error_log#add
       "set_instruction:invalid address"
       (LBLOCK [addr#toPretty; STR ": "; instr#toPretty])


let initialize_instruction_section (addr: doubleword_int) (xsize: doubleword_int) =
  let size = xsize#value in
  for i = 0 to size - 1 do
    set_instruction
      (addr#add_int i) (make_arm_assembly_instruction wordzero true OpInvalid "")
  done


let initialize_instruction_sections
      (sl: (string * doubleword_int * doubleword_int) list) =
  List.iter (fun (name, addr, size) ->
      begin
        chlog#add
          "disassembly:initialize"
          (LBLOCK [
               STR "section: ";
               STR name;
               STR "; startaddress: ";
               addr#toPretty;
               STR "; size: ";
               size#toPretty]);
        initialize_instruction_section addr size;
        pverbose [
            STR "initialized instructions for section "; STR name; NL]
      end) sl


(* Return the instruction at the given index from the backing store; if
   the index is out-of-range, return Error.
 *)
let get_instruction (addr: doubleword_int): arm_assembly_instruction_result =
  try
    let (i, j) = get_indices addr in
    Ok (arm_instructions.(i).(j))
  with
  | BCH_failure p ->
     Error ["get_instruction: " ^ addr#to_hex_string]


let get_all_instruction_addrs (): doubleword_int list =
  let result = ref [] in
  begin
    List.iter (fun (i, j) ->
        let instr = arm_instructions.(i).(j) in
        if instr#is_valid_instruction then
          result := instr#get_address :: !result)
      address_translator#get_all_indices_rev;
    !result
  end


let fold_instructions (f:'a -> arm_assembly_instruction_int -> 'a) (init:'a) =
  Array.fold_left
    (fun a arr ->
      Array.fold_left (fun a1 opc -> f a1 opc) a arr) init arm_instructions


let iter_instructions (f:arm_assembly_instruction_int -> unit) =
  Array.iter (fun arr -> Array.iter f arr) arm_instructions


class arm_assembly_instructions_t
        (sections: (string * doubleword_int * doubleword_int) list) =
object (self)

  val sections = sections
  val mutable codeaddrs: doubleword_int list = []
  val mutable codeaddrs_rev: doubleword_int list = []
  val aggregates = H.create 3

  method length =
    List.fold_left (fun acc (_, _, size) -> acc + size#value) 0 sections

  method set_instruction
           (va: doubleword_int) (instr: arm_assembly_instruction_int) =
    set_instruction va instr

  method get_instruction (va: doubleword_int): arm_assembly_instruction_result =
    get_instruction va

  method set_aggregate
           (va: doubleword_int) (agg: arm_instruction_aggregate_int) =
    begin
      H.add aggregates va#value agg;
      agg#anchor#set_aggregate_anchor;
      agg#entry#set_aggregate_entry;
      agg#exitinstr#set_aggregate_exit;
      List.iter (fun instr -> instr#set_in_aggregate va) agg#instrs;
      (match agg#kind with
       | ARMJumptable jt -> self#set_jumptable jt#to_jumptable
       | _ -> ())
    end

  method get_aggregate (va: doubleword_int): arm_instruction_aggregate_int =
    if H.mem aggregates va#value then
      H.find aggregates va#value
    else
      raise
        (BCH_failure (LBLOCK [STR "No aggregate found at "; va#toPretty]))

  method has_aggregate (va: doubleword_int): bool = H.mem aggregates va#value

  method set_not_code (data_blocks: data_block_int list) =
    let _ =
      pverbose [
          STR "set_not_code ... with ";
          INT (List.length data_blocks);
          STR " data blocks";
          NL] in
    List.iter self#set_not_code_block data_blocks

  method private set_not_code_block (db: data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    let len = endaddr#value - startaddr#value in
    let _ =
      pverbose [
          STR "set-not-code at "; startaddr#toPretty; STR " with length "; INT len; NL] in
    let startinstr =
      make_arm_assembly_instruction
        startaddr true (NotCode (Some (DataBlock db))) "" in
    begin
      set_instruction startaddr startinstr;
      for i = 1 to (len - 1) do
        let va = startaddr#add_int i in
        set_instruction
          va (make_arm_assembly_instruction va true (NotCode None) "")
      done
    end

  method private set_jumptable (jumptable: jumptable_int) =
    let saddr = jumptable#get_start_address in
    let eaddr = jumptable#get_end_address in
    let len = saddr#value - eaddr#value in
    let startinstr =
      make_arm_assembly_instruction
        saddr true (NotCode (Some (JumpTable jumptable))) "" in
    begin
      set_instruction saddr startinstr;
      for i = 1 to (len - 1) do
        let va = saddr#add_int i in
        set_instruction
          va (make_arm_assembly_instruction va true (NotCode None) "")
      done
    end

  method get_next_valid_instruction_address
           (va: doubleword_int): doubleword_int TR.traceresult =
    let rec loop i =
      let iaddr = va#add_int i in
      match TR.to_option (get_instruction iaddr) with
      | Some instr when instr#is_not_code -> None
      | Some instr ->
         (match instr#get_opcode with
          | OpInvalid -> loop (i + 1)
          | _ -> Some iaddr)
      | _ -> None in
    (match loop 1 with
     | Some iaddr -> Ok iaddr
     | _ ->
        Error [
            "get_next_valid_instruction_address:not found:"
            ^ va#to_hex_string])

  method get_prev_valid_instruction_address
           (va: doubleword_int): doubleword_int TR.traceresult =
    let ival = va#value in
    let rec loop i =
      if i > ival then
        None
      else
        let iaddr = TR.tget_ok (va#subtract_int i) in
        match TR.to_option (get_instruction iaddr) with
        | Some instr when instr#is_not_code -> None
        | Some instr ->
           (match instr#get_opcode with
            | OpInvalid -> loop (i + 1)
            | _ -> Some iaddr)
        | _ -> None in
    (match loop 1 with
     | Some iaddr -> Ok iaddr
     | _ ->
        Error [
            "get_prev_valid_instruction_address:not found:"
            ^ va#to_hex_string])

  method has_next_valid_instruction (va: doubleword_int): bool =
    let rec loop i =
      match TR.to_option (get_instruction (va#add_int i)) with
      | Some instr when instr#is_not_code -> false
      | Some instr ->
         (match instr#get_opcode with
          | OpInvalid -> loop (i + 1)
          | _ -> true)
      | _ -> false in
    loop 1

  method has_prev_valid_instruction (va: doubleword_int): bool =
    let ival = va#value in
    let rec loop i =
      if i <= ival then
        match TR.to_option (get_instruction (TR.tget_ok (va#subtract_int i))) with
        | Some instr when instr#is_not_code -> false
        | Some instr ->
           (match instr#get_opcode with
            | OpInvalid -> loop (i + 1)
            | _ -> true)
        | _ -> false
      else
        false in
    loop 1

  method is_code_address (va:doubleword_int) =
    TR.to_bool
      (fun instr -> instr#is_valid_instruction) (self#get_instruction va)

  method collect_callsites =
    self#itera (fun va instr ->
        match instr#get_opcode with
        | BranchLink (_, op)
          | BranchLinkExchange (_, op) when op#is_absolute_address ->
           let tgt = op#get_absolute_address in
           let preinstrs: arm_assembly_instruction_int list ref = ref [] in
           let postinstrs: arm_assembly_instruction_int list ref = ref [] in
           let thisinstr: arm_assembly_instruction_int ref = ref instr in
           let thisva: doubleword_int ref = ref va in
           let postinstr: arm_assembly_instruction_int option ref = ref None in
           begin
             while (not !thisinstr#is_block_entry)
                   && (self#has_prev_valid_instruction !thisva) do
               thisva :=
                 (TR.tget_ok (self#get_prev_valid_instruction_address !thisva));
               thisinstr := (TR.tget_ok (self#get_instruction !thisva));
               preinstrs := (!thisinstr :: !preinstrs)
             done;
             (if self#has_next_valid_instruction va then
                begin
                  thisva := TR.tget_ok (self#get_next_valid_instruction_address va);
                  thisinstr := (TR.tget_ok (self#get_instruction !thisva));
                  while (not !thisinstr#is_block_entry)
                        && (self#has_next_valid_instruction !thisva) do
                    postinstrs := (!thisinstr :: !postinstrs);
                    thisva :=
                      (TR.tget_ok (self#get_next_valid_instruction_address !thisva));
                    thisinstr := (TR.tget_ok (self#get_instruction !thisva))
                  done;
                  if !thisinstr#is_block_entry then
                    postinstr := Some !thisinstr
                end
              else
                ());
             match !postinstr with
             | Some instr ->
                arm_callsites_records#add_callsite
                  tgt va !preinstrs (List.rev !postinstrs) instr
             | _ -> ()
           end
        | _ -> ())

  method get_code_addresses_rev ?(low=wordzero) ?(high=wordmax) () =
    let high = if high#lt low then low else high in
    let addrs_rev =
      if List.length codeaddrs_rev > 0 then
        codeaddrs_rev
      else
        let addrs = get_all_instruction_addrs () in
        begin
          codeaddrs_rev <- List.rev addrs;
          codeaddrs <- addrs;
          codeaddrs_rev
        end in
    List.filter (fun a -> low#le a && a#le high) addrs_rev

  method get_num_instructions =
    (List.length (self#get_code_addresses_rev ()))

  method get_num_unknown_instructions =
    let n = ref 0 in
    let _ =
      self#itera (fun _ instr ->
          match instr#get_opcode with
          | NotRecognized _ -> n := !n + 1
          | _ -> ()) in
    !n

  method itera (f:doubleword_int -> arm_assembly_instruction_int -> unit) =
    iter_instructions (fun instr -> f instr#get_address instr)

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

  method toString
           ?(datarefs:((string * arm_assembly_instruction_int list) list) = [])
           ?(filter = fun _ -> true) () =
    let lines = ref [] in
    let firstNew = ref true in
    let datareftable = H.create (List.length datarefs) in
    let _ = List.iter (fun (a, refs) -> H.add datareftable a refs) datarefs in
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
         let (alignedaddr, prefix) = db#get_start_address#to_aligned ~up:true 4 in
         let addr = ref alignedaddr in
         let contents = ref [] in
         let make_stream (v: doubleword_int) =
           let bytestring = write_hex_bytes_to_bytestring v#to_fixed_length_hex_string_le in
           make_pushback_stream ~little_endian:true bytestring in
         let opcode_string (addr: doubleword_int) (v: doubleword_int) =
           try
             let cha = make_stream v in
             if system_info#is_thumb addr then
               let instrbytes = cha#read_ui16 in
               let opcode = disassemble_thumb_instruction cha addr instrbytes in
               let opcodetxt =
                 match opcode with
                 | NotRecognized _ -> "not-recognized"
                 | _ -> arm_opcode_to_string opcode in
               let xtra =
                 if cha#pos = 2 then
                   " ++ "
                 else
                   "" in
               "T:" ^ opcodetxt ^ xtra
             else
               let instrbytes = cha#read_doubleword in
               let opcode = disassemble_arm_instruction cha addr instrbytes in
               let opcodetxt =
                 match opcode with
                 | NotRecognized _ -> "not-recognized"
                 | _ -> arm_opcode_to_string opcode in
              "A:" ^ opcodetxt
           with
             _ -> " --error--" in

         let pprefix =
           if prefix > 0 then
             "  " ^ (fixed_length_string !addr#to_hex_string 10) ^ "  align\n"
           else
             "" in
         let _ =
           if prefix > 0 && (String.length s) >= prefix then ch#skip_bytes prefix in
         try
           begin
             for i = 0 to (((len - prefix)/4) - 1) do
               begin
                 contents := (!addr, ch#read_doubleword) :: !contents;
                 addr := !addr#add_int 4
               end
             done;
             ("\n" ^ (string_repeat "~" 80) ^ "\nData block (size: "
              ^ (string_of_int len) ^ " bytes)\n\n"
              ^ pprefix
              ^ (String.concat
                   "\n"
                   (List.map
                      (fun (a, v) ->
                        let addr = a#to_hex_string in
                        if H.mem datareftable addr then
                          let datarefs = H.find datareftable addr in
                          "  "
                          ^ (fixed_length_string addr 10)
                          ^ "  "
                          ^ (fixed_length_string v#to_hex_string 12)
                          ^ (String.concat
                               ", " (List.map (fun instr -> instr#toString) datarefs))
                        else
                          match elf_header#get_string_at_address v with
                          | Some s ->
                             "  "
                             ^ (fixed_length_string addr 10)
                             ^ "  "
                             ^ (fixed_length_string v#to_hex_string 12)
                             ^ ": \""
                             ^ s
                             ^ "\""
                          | _ ->
                             "  "
                             ^ (fixed_length_string addr 10)
                             ^ "  "
                             ^ (fixed_length_string v#to_hex_string 14)
                             ^ "  "
                             ^ (opcode_string a v))
                      (List.rev !contents)))
              ^ "\n" ^ (string_repeat "=" 80) ^ "\n")
           end
         with
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "Error in printing data block. ";
                      STR "Address: ";
                      db#get_start_address#toPretty;
                      STR "; Aligned address: ";
                      alignedaddr#toPretty;
                      STR "; Prefix: ";
                      INT prefix;
                      STR "; Length: ";
                      INT len])) in
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


let arm_assembly_instructions = ref (new arm_assembly_instructions_t [])


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
      (sections: (string * doubleword_int * doubleword_int) list)
      (datablocks: data_block_int list) =
  begin
    initialize_instruction_sections sections;
    arm_assembly_instructions := new arm_assembly_instructions_t sections;
    !arm_assembly_instructions#set_not_code datablocks;
    pverbose [STR "Finish initializing arm assembly instructions"; NL]
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
