(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2024  Aarno Labs LLC

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
open BCHFunctionData
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerAssemblyInstruction
open BCHPowerTypes

module TR = CHTraceResult


let numArrays = 10000
let arrayLength = 100000

let initialized_length = ref 0


let pwr_instructions =
  Array.make
    numArrays
    (Array.make 1 (make_pwr_assembly_instruction wordzero false OpInvalid ""))


let initialize_pwr_section_instructions (startindex: int) (len: int): int =
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
        pwr_instructions.(!index) <-
          Array.make
            arraylen
            (make_pwr_assembly_instruction wordzero true OpInvalid "");
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
          let newindex = initialize_pwr_section_instructions startindex size in
          let newindices = (name, start, size, startindex) :: indices in
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
           (startaddr: doubleword_int) (endaddr: doubleword_int): (int * int) list =
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
           (LBLOCK [STR "Indices spanning more than two arrays not yet supported"]))

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


let initialize_pwr_instructions
      (sections: (string * doubleword_int * doubleword_int) list) =
  address_translator#initialize
    (List.map (fun (name, start, size) -> (name, start#value, size#value)) sections)


let get_indices (addr: doubleword_int) = address_translator#get_indices addr


(* Enter the instruction in the backing array at the given index. If the
   index is out-of-range of the initialized length of the backing array,
   log an error message (but don't fail).
 *)
let set_instruction (addr: doubleword_int) (instr: pwr_assembly_instruction_int) =
  try
    let (i, j) = get_indices addr in
    pwr_instructions.(i).(j) <- instr
  with
  | BCH_failure p ->
     ch_error_log#add
       "set_instruction:invalid address"
       (LBLOCK [addr#toPretty; STR ": "; instr#toPretty; STR ": "; p])


let initialize_instruction_section (addr: doubleword_int) (xsize: doubleword_int) =
  let size = xsize#value in
  for i = 0 to size - 1 do
    set_instruction
      (addr#add_int i) (make_pwr_assembly_instruction wordzero true OpInvalid "")
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
      end) sl


(* Return the instruction at the given index from the backing store; if
   the index is out-of-range, return Error.*)
let get_instruction (addr: doubleword_int): pwr_assembly_instruction_result =
  try
    let (i, j) = get_indices addr in
    Ok (pwr_instructions.(i).(j))
  with
  | BCH_failure p ->
     Error [
         "get_instruction: "
         ^ addr#to_hex_string
         ^ "("
         ^ (pretty_to_string p)
         ^ ")"
       ]


(* Return the addresses of valid instructions in the given address range
   (inclusive) *)
let get_range_instruction_addrs
      (startaddr: doubleword_int) (endaddr: doubleword_int): doubleword_int list =
  let result = ref [] in
  begin
    List.iter (fun (i, j) ->
        try
          let instr = pwr_instructions.(i).(j) in
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
        let instr = pwr_instructions.(i).(j) in
        if instr#is_valid_instruction then
          result := instr#get_address :: !result)
      address_translator#get_all_indices_rev;
    !result
  end


let _fold_instructions (f: 'a -> pwr_assembly_instruction_int -> 'a) (init: 'a) =
  Array.fold_left (fun a arr ->
    Array.fold_left (fun a1 opc -> f a1 opc) a arr) init pwr_instructions


let iter_instructions (f: pwr_assembly_instruction_int -> unit) =
  Array.iter (fun arr -> Array.iter f arr) pwr_instructions


let _iteri_instructions (f: int -> pwr_assembly_instruction_int -> unit) =
  Array.iteri (fun i arr ->
    let k = i * arrayLength in
    Array.iteri (fun j instr -> f (k+j) instr) arr) pwr_instructions


class pwr_assembly_instructions_t
        (sections: (string * doubleword_int * doubleword_int) list):
        pwr_assembly_instructions_int =
object (self)

  val sections = sections
  val mutable codeaddrs: doubleword_int list = []
  val mutable codeaddrs_rev: doubleword_int list = []

  method length =
    List.fold_left (fun acc (_, _, size) -> acc + size#value) 0 sections

  method set_instruction
           (va: doubleword_int) (instr:pwr_assembly_instruction_int) =
    set_instruction va instr

  method get_instruction (va:doubleword_int): pwr_assembly_instruction_result =
    get_instruction  va

  method is_code_address (va:doubleword_int) =
    TR.to_bool
        (fun instr -> instr#is_valid_instruction) (self#get_instruction va)

  method set_not_code (datablocks: data_block_int list) =
    List.iter self#set_not_code_block datablocks

  method private set_not_code_block (db: data_block_int) =
    let startaddr = db#get_start_address in
    let endaddr = db#get_end_address in
    let len = endaddr#value - startaddr#value in
    let startinstr =
      make_pwr_assembly_instruction
        startaddr true (NotCode (Some (DataBlock db))) "" in
    begin
      set_instruction startaddr startinstr;
      for i = 1 to (len - 1) do
        let va = startaddr#add_int i in
        set_instruction
          va (make_pwr_assembly_instruction va true (NotCode None) "")
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

  method get_code_addresses ?(low=wordzero) ?(high=wordmax) () =
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
      try
        get_range_instruction_addrs low high
      with
      | BCH_failure p ->
         begin
           ch_error_log#add
             "get-code-addresses"
             (LBLOCK [
                  low#toPretty;
                  STR " - ";
                  high#toPretty;
                  STR ": ";
                  p]);
           []
         end

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

  method itera (f:doubleword_int -> pwr_assembly_instruction_int -> unit) =
    begin
      iter_instructions (fun instr -> f instr#get_address instr)
    end

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


let pwr_assembly_instructions = ref (new pwr_assembly_instructions_t [])


let initialize_pwr_assembly_instructions
      (sections: (string * doubleword_int * doubleword_int) list)
      (datablocks: data_block_int list) =
  begin
    initialize_instruction_sections sections;
    pwr_assembly_instructions := new pwr_assembly_instructions_t sections;
    !pwr_assembly_instructions#set_not_code datablocks
  end


let get_pwr_assembly_instruction (a: doubleword_int): pwr_assembly_instruction_result =
  !pwr_assembly_instructions#get_instruction a


let set_pwr_assembly_instruction (instr: pwr_assembly_instruction_int) =
  !pwr_assembly_instructions#set_instruction instr#get_address instr


let get_next_valid_instruction_address
      (a: doubleword_int): doubleword_int traceresult =
  !pwr_assembly_instructions#get_next_valid_instruction_address a


let has_next_valid_instruction (a: doubleword_int) =
  !pwr_assembly_instructions#has_next_valid_instruction a
