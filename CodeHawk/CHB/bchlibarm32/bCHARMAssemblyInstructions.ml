(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2025  Aarno Labs, LLC

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
open CHPrettyUtil
open CHTraceResult
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHByteUtilities
open BCHDataBlock
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities

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

          (*
let x2p = XprToPretty.xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)
           *)
let numArrays = 1000
let arrayLength = 100000

let initialized_length = ref 0

let memorymap = BCHGlobalMemoryMap.global_memory_map


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
                STR (timing ());
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
      List.fold_left (fun (fnd, r) (_name, start, size, startindex) ->
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

  method get_range_indices
           (startaddr: doubleword_int)
           (endaddr: doubleword_int): (int * int) list =
    let (i_start, j_start) = self#get_indices startaddr in
    let (i_end, j_end) = self#get_indices endaddr in
    if i_start = i_end then
      List.init ((j_end - j_start) + 1) (fun k -> (i_start, j_start + k))
    else if (i_end - i_start) = 1 then
      let lst1 =
        List.init (arrayLength - j_start) (fun k -> (i_start, j_start + k)) in
      let lst2 = List.init (j_end + 1) (fun k -> (i_end, k)) in
      lst1 @ lst2
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Indices spanning more than two arrays not yet supported"]))

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
   log an error message (but don't fail).*)
let set_instruction (addr: doubleword_int) (instr: arm_assembly_instruction_int) =
  try
    let (i, j) = get_indices addr in
    arm_instructions.(i).(j) <- instr
  with
  | BCH_failure p ->
     ch_error_log#add
       "set_instruction:invalid address"
       (LBLOCK [addr#toPretty; STR ": "; instr#toPretty; STR ": "; p])


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
            STR (timing ());
            STR "initialized instructions for section ";
            STR name;
            NL]
      end) sl


(* Return the instruction at the given index from the backing store; if
   the index is out-of-range, return Error.*)
let get_instruction (addr: doubleword_int): arm_assembly_instruction_result =
  try
    let (i, j) = get_indices addr in
    Ok (arm_instructions.(i).(j))
  with
  | BCH_failure p ->
     Error [
         "get_instruction: "
         ^ addr#to_hex_string
         ^ ": "
         ^ (pretty_to_string p)]

(* Return the addresses of valid instructions in the given address range
   (inclusive) *)
let get_range_instruction_addrs
      (startaddr: doubleword_int) (endaddr: doubleword_int): doubleword_int list =
  let result = ref [] in
  begin
    List.iter (fun (i, j) ->
        try
          let instr = arm_instructions.(i).(j) in
          if instr#is_valid_instruction then
            result := instr#get_address :: !result
        with
        | Invalid_argument _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Index out of bound with (";
                     INT i;
                     STR ", ";
                     INT j;
                     STR ")"])))
      (address_translator#get_range_indices startaddr endaddr);
    List.rev !result
  end

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

(*
let fold_instructions (f:'a -> arm_assembly_instruction_int -> 'a) (init:'a) =
  Array.fold_left
    (fun a arr ->
      Array.fold_left (fun a1 opc -> f a1 opc) a arr) init arm_instructions
 *)

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

  method get_jumptables =
    H.fold (fun va agg acc ->
        match agg#kind with
        | ARMJumptable jt ->
           let xva = TR.tget_ok (int_to_doubleword va) in
           (xva, jt) :: acc
        | _ -> acc) aggregates []

  method set_not_code (data_blocks: data_block_int list) =
    List.iter self#set_not_code_block data_blocks

  method private set_not_code_block (db: data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    let len = endaddr#value - startaddr#value in
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
    let len = eaddr#value - saddr#value in
    if len > 0 then
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

    (* Note: If a va is not a valid instruction and not part of a non-code
       block (and doesn't have instruction bytes associated with it) in
       thumb mode, the reason may be that an instruction at va-2 was
       initially disassembled as an (ultimately invalid) 4-byte thumb
       instruction, leaving the last two bytes (which may be a valid 2 or
       start of 4-byte instruction un-disassembled. The quick fix is to
       simply add the datablock to the userdata, so it will be pre-assigned
       as non-code block, but this should eventually be fixed.
     *)
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

  method get_code_addresses ?(low=wordzero) ?(high=wordmax) () =
    (* let _ =
      pverbose [
          STR (timing ());
          STR "get_code_addrs_rev: ";
          low#toPretty; STR " - ";
          high#toPretty;
          STR " ...";
          NL] in *)
    let high = if high#lt low then low else high in
    if low#equal wordzero && high#equal wordmax then
      let addrs =
        if List.length codeaddrs > 0 then
          codeaddrs
        else
          let addrs = get_all_instruction_addrs () in
          begin
            codeaddrs <- addrs;
            codeaddrs
          end in
      addrs
    else
      get_range_instruction_addrs low high

  method get_num_instructions =
    (List.length (self#get_code_addresses ()))

  method get_num_unknown_instructions =
    let n = ref 0 in
    let _ =
      self#itera (fun _ instr ->
          match instr#get_opcode with
          | NotRecognized _ -> n := !n + 1
          | _ -> ()) in
    !n

  method itera (f:doubleword_int -> arm_assembly_instruction_int -> unit) =
    begin
      pverbose [STR (timing ()); STR "itera ..."; NL];
      iter_instructions (fun instr -> f instr#get_address instr);
      pverbose [STR (timing ()); STR "  itera: done"; NL]
    end

  method write_xml (node:xml_element_int) =
    let subnodes = ref [] in
    let bnode = ref (xmlElement "b") in
    begin
      self#itera
        (fun va instr ->
          if instr#is_valid_instruction then
            let _ =
              if instr#is_block_entry then
                begin
                  bnode := xmlElement "b";
                  (!bnode)#setAttribute "ba" va#to_hex_string;
                  (* node#appendChildren [!bnode] *)
                  subnodes := !bnode :: !subnodes
                end in
            let inode = xmlElement "i" in
            begin
              instr#write_xml inode;
              (!bnode)#appendChildren [inode]
            end);
      node#appendChildren (List.rev !subnodes)
    end

  method private not_code_to_string
                   (datarefstr: doubleword_int -> string) (nc: not_code_t): string =
    match nc with
    | JumpTable jt ->
         let s =
           jt#toString
             ~is_function_entry_point:(fun _ -> false)
             ~get_opt_function_name:(fun _ -> None) in
         ("\n" ^ s ^ "\n")
    | DataBlock db ->
       let s = db#get_data_string in
       let len = String.length s in
       let (alignedaddr, prefix) = db#get_start_address#to_aligned ~up:true 4 in
       try
         self#datablock_to_string datarefstr s alignedaddr prefix
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
                     INT len]))

  method private datablock_to_string
                   ?(disassemble=true)
                   (datarefstr: (doubleword_int -> string))
                   (s: string)
                   (startaddr: doubleword_int)
                   (prefix: int): string =
    let ch = make_pushback_stream s in
    let len = String.length s in
    let addr = ref startaddr in
    let contents = ref [] in
    let addrstr_end = ref wordzero in
    let pprefix =
      if prefix > 0 then
        "  " ^ (fixed_length_string !addr#to_hex_string 10) ^ "  align\n"
      else
        "" in
    let _ =
      if prefix > 0 && (String.length s) >= prefix then
        ch#skip_bytes prefix in
    for _i = 0 to (((len - prefix)/4) - 1) do
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
               let (strend, s) =
                 self#render_datablock_line
                   (datarefstr a) ~disassemble !addrstr_end a v in
               let _ = if strend != !addrstr_end then addrstr_end := strend in
               s)
             (List.rev !contents)))
     ^ "\n" ^ (string_repeat "=" 80) ^ "\n")

  method private render_gloc
                   (datarefstr: string)
                   (a: doubleword_int)
                   (v: doubleword_int): string =
    let fls = fixed_length_string in
    let vhex = v#to_hex_string in
    let vm1 (v: doubleword_int) = TR.to_option (v#subtract_int 1) in
    let get_fname (addr: doubleword_int) =
      if functions_data#has_function_name addr then
        let fndata = functions_data#get_function addr in
        ":" ^ fndata#get_function_name
      else
        "" in
    let get_string (v: doubleword_int) =
      match elf_header#get_string_at_address v with
      | Some s ->
         let len = String.length s in
         if len < 50 then
           ":\"" ^ s ^ "\""
         else
           ":\"" ^ (String.sub s 0 50) ^ "...\""
      | _ -> "" in
    let get_memory_offset (gloc: global_location_int) (offset: xpr_t) =
      let zeroloc = BCHLocation.make_location_by_address wordzero wordzero in
      TR.tfold
        ~ok:(fun memoffset ->
          "  (" ^ (BCHMemoryReference.memory_offset_to_string memoffset) ^ ")"
          ^ "")
        ~error:(fun e ->
          begin
            log_diagnostics_result __FILE__ __LINE__ e;
            ""
          end)
        (gloc#address_memory_offset ~tgtsize:(Some 4) zeroloc offset) in
    let addrprefix = "  " ^ (fls a#to_hex_string 10) in
    let p_value =
      if v#equal wordzero then
        "<0x0>"

      else if v#equal wordmax then
        "<0xffffffff>"

      else if functions_data#is_function_entry_point v then
        "FAddr:<" ^ vhex ^ (get_fname v) ^ ">"

      else if (Option.is_some (vm1 v))
              && functions_data#is_function_entry_point (Option.get (vm1 v)) then
        let fentry = Option.get (vm1 v) in
        "FAddr:<" ^ vhex ^ (get_fname fentry) ^ "(T)>"

      else if memorymap#has_location v then
        let gloc = memorymap#get_location v in
        "GVAddr:<" ^ vhex ^ ":" ^ gloc#name ^ ">"

      else if elf_header#is_code_address v then
        "Code:<" ^ vhex ^ (get_string v) ^ ">"

      else if elf_header#is_data_address v then
        "Data:<" ^ vhex ^ (get_string v) ^ ">"

      else
        vhex in

    match memorymap#containing_location a with
    | None -> ""     (* should not be reachable *)
    | Some gloc ->
       let xprv = num_constant_expr a#to_numerical in
       TR.tfold_default
         (fun offset ->
           let p_memoff = get_memory_offset gloc xprv in
           match offset with
           | XConst (IntConst n) when n#equal numerical_zero ->
              addrprefix ^ "\n"
              ^ addrprefix
              ^ "  Global variable:<"
              ^ gloc#name ^ ": "
              ^ (btype_to_string gloc#btype) ^ ">\n"
              ^ addrprefix
              ^ "    GV:<"
              ^ gloc#name ^ ":0  >: "
              ^ p_value
              ^ p_memoff
              ^ datarefstr
           | XConst (IntConst n) ->
              addrprefix
              ^ "    GV:<"
              ^ gloc#name ^ ":"
              ^ (fls n#toString 3) ^ ">: "
              ^ p_value
              ^ p_memoff
              ^ datarefstr
           | _ -> "")
         (addrprefix ^ "  GV:<" ^ gloc#name ^ ":?>:" ^ p_value)
         (gloc#address_offset xprv)

  method private render_datablock_line
                   ?(disassemble=true)
                   (datarefstr: string)
                   (addrstr_end: doubleword_int)
                   (a: doubleword_int)
                   (v: doubleword_int): (doubleword_int * string) =
    let vm1 (v: doubleword_int) = TR.to_option (v#subtract_int 1) in
    let get_fname (addr: doubleword_int) =
      if functions_data#has_function_name addr then
        let fndata = functions_data#get_function addr in
        ":" ^ fndata#get_function_name
      else
        "" in
    let render_string (s: string): string =
      let len = String.length s in
      if len <= 40 then
        s
      else
        (String.sub s 0 40) ^ "... (length: " ^ (string_of_int len) ^ ")" in
    let addrprefix = "  " ^ (fixed_length_string a#to_hex_string 10) in
    let vhex = v#to_hex_string in
    let fls = fixed_length_string in
    if a#lt addrstr_end then
      (addrstr_end,
       addrprefix ^ "  <String:<" ^ (fls v#to_hex_string 12) ^ "> ... (cont'd)")

    else if Option.is_some (memorymap#containing_location a) then
      (addrstr_end, self#render_gloc datarefstr a v)

    else if memorymap#has_elf_symbol v then
      let name = memorymap#get_elf_symbol v in
      let memline = addrprefix ^ "  Sym:<" ^ vhex ^ ":" ^ name ^ ">" ^ datarefstr in
      (addrstr_end, memline)

    else if v#equal wordzero then
      (addrstr_end, addrprefix ^ "  <0x0>")

    else if v#equal wordmax then
      (addrstr_end, addrprefix ^ "  <0xffffffff>")

    else if functions_data#is_function_entry_point v then
      let l = addrprefix ^ "  FAddr:<" ^ vhex ^ (get_fname v) ^ ">" ^ datarefstr in
      (addrstr_end, l)

    else if (Option.is_some (vm1 v))
            && functions_data#is_function_entry_point (Option.get (vm1 v)) then
      let fentry = Option.get (vm1 v) in
      let l =
        addrprefix
          ^ "  FAddr:<" ^ vhex ^ (get_fname fentry) ^ "(T)>" ^ datarefstr in
      (addrstr_end, l)

    else if memorymap#has_location v then
      let gloc = memorymap#get_location v in
      let l = addrprefix ^ "  GVAddr:<" ^ vhex ^ ":" ^ gloc#name ^ ">" ^ datarefstr in
      (addrstr_end, l)

    else if elf_header#is_code_address v then
      let s =
        match elf_header#get_string_at_address v with
        | Some s ->
           let len = String.length s in
           if len < 50 then
             ":\""  ^ s ^ "\""
           else
             ":\"" ^ (String.sub s 0 50) ^ "...\""
        | _ -> "" in
      let l = addrprefix ^ "  Code:<" ^ vhex ^ s ^ ">" ^ datarefstr in
      (addrstr_end, l)

    else if elf_header#is_data_address v then
      let s =
        match elf_header#get_string_at_address v with
        | Some s ->
           let len = String.length s in
           if len < 50 then
             ":\"" ^ s ^ "\""
           else
             ":\"" ^ (String.sub s 0 50) ^ "...\""
        | _ -> "" in
      let l = addrprefix ^ "  Data:<" ^ vhex ^ s ^ ">" ^ datarefstr in
      (addrstr_end, l)

    else if elf_header#is_uninitialized_data_address v then
      let l = addrprefix ^ "  Bss:<" ^ vhex ^ ">" ^ datarefstr in
      (addrstr_end, l)

    else if Option.is_some (elf_header#get_string_at_address a) then
      let s = Option.get (elf_header#get_string_at_address a) in
      let slen = String.length s in
      let slen = if slen > 40 then 40 else slen in
      let l =
        addrprefix ^ "  <String:<" ^ (fls vhex 12) ^ ">: \""
        ^ (render_string s) ^ "\""
        ^ datarefstr in
      (a#add_int slen, l)

    else if (String.length datarefstr) > 0 then
      let l = addrprefix ^ "  Value<" ^ vhex ^ ">" ^ datarefstr in
      (addrstr_end, l)

    else if disassemble then
      let p_opcode = self#db_opcode_to_string a v in
      let l = addrprefix ^ "  " ^ (fls vhex 14) ^ "  " ^ p_opcode in
      (addrstr_end, l)

    else
      (addrstr_end, addrprefix ^ "  " ^ (fls vhex 14))

  method private db_opcode_to_string
                   (addr: doubleword_int) (v: doubleword_int): string =
    let make_stream (v: doubleword_int) =
      let bytestring =
        write_hex_bytes_to_bytestring v#to_fixed_length_hex_string_le in
      make_pushback_stream ~little_endian:true bytestring in
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
      _ -> " --error"

  method toString
           ?(datarefs:((string * arm_assembly_instruction_int list) list) = [])
           ?(datasections:(string list) = [])
           ?(filter = fun _ -> true) () =
    let lines = ref [] in
    let firstNew = ref true in
    let datareftable = H.create (List.length datarefs) in
    let _ = List.iter (fun (a, refs) -> H.add datareftable a refs) datarefs in
    let datarefstr (a: doubleword_int): string =
      if H.mem datareftable a#to_hex_string then
        let datarefs = H.find datareftable a#to_hex_string in
        "  (refs: "
        ^ (String.concat
             ", " (List.map (fun instr -> instr#get_address#to_hex_string) datarefs))
        ^ ")"
      else
        "" in
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
              | NotCode (Some b) ->
                 lines := (self#not_code_to_string datarefstr b) :: !lines
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

      (if (List.length datasections) > 0 then
         let printsections =
           List.fold_left (fun acc (_, sh, _) ->
               if List.mem sh#get_section_name datasections
                  || List.mem sh#get_addr#to_hex_string datasections then
                 match BCHELFHeader.elf_header#get_containing_section sh#get_addr with
                 | Some sec -> (sh, sec) :: acc
                 | _ -> acc
               else
                 acc) [] BCHELFHeader.elf_header#get_sections in
         begin
           lines := "\n\n==== Data sections ====\n\n" :: !lines;
           List.iter (fun (sh, sec) ->
               let psection =
                    self#datablock_to_string
                      ~disassemble:false datarefstr sec#get_xstring sh#get_addr 0 in
               begin
                 lines :=
                   ("\n\nData section "
                    ^ sh#get_section_name
                    ^ " (" ^ sh#get_addr#to_hex_string ^ ")\n") :: !lines;
                 lines := psection :: !lines
               end) printsections;
           lines := "\n\n ==== End of Data sections ====\n\n" :: !lines
         end);

      String.concat "\n" (List.rev !lines);
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
    !arm_assembly_instructions#set_not_code datablocks
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


let get_arm_jumptables (): (doubleword_int * arm_jumptable_int) list =
  !arm_assembly_instructions#get_jumptables


let get_associated_test_instr
      (finfo: function_info_int)
      (ctxtiaddr: ctxt_iaddress_t)
    : (location_int * arm_assembly_instruction_int) option =
  if finfo#has_associated_cc_setter ctxtiaddr then
    let faddr = finfo#get_address in
    let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
    let testloc = BCHLocation.ctxt_string_to_location faddr testiaddr in
    let testaddr = testloc#i in
    TR.tfold
      ~ok:(fun testinstr -> Some (testloc, testinstr))
      ~error:(fun e ->
        begin
          log_error_result __FILE__ __LINE__ e;
          None
        end)
      (get_arm_assembly_instruction testaddr)
  else
    None
