(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs LLC

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
open BCHBCTypes
open BCHByteUtilities
open BCHFloc
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHPreFileIO
open BCHSystemInfo
open BCHTypeConstraintStore

(* bchlibarm32 *)
open BCHARMAssemblyFunctions
open BCHARMDictionary
open BCHARMLoopStructure
open BCHARMTypes
open BCHFnARMDictionary
open BCHFnARMTypeConstraints

module H = Hashtbl

let bd = BCHDictionary.bdictionary
let bcd = BCHBCDictionary.bcdictionary
let mmap = BCHGlobalMemoryMap.global_memory_map


class fn_analysis_results_t (fn:arm_assembly_function_int) =
object (self)

  val faddr = fn#get_address
  val finfo = get_function_info fn#get_address
  val env = (get_function_info fn#get_address)#env
  val vard = (get_function_info fn#get_address)#env#varmgr#vard
  val id = mk_arm_opcode_dictionary
             fn#get_address (get_function_info fn#get_address)#env#varmgr#vard

  method private write_xml_instruction
                   (node:xml_element_int)
                   (ctxtiaddr:ctxt_iaddress_t)
                   (instr:arm_assembly_instruction_int) =
    let loc = ctxt_string_to_location faddr ctxtiaddr in
    let floc = get_floc loc in
    let espoffset = floc#get_stackpointer_offset "arm" in
    begin
      arm_dictionary#write_xml_arm_opcode node instr#get_opcode;
      id#write_xml_instr node instr floc;
      id#write_xml_sp_offset node espoffset;
      arm_dictionary#write_xml_arm_bytestring
        node (byte_string_to_printed_string instr#get_instruction_bytes)
    end

  method private write_xml_instructions (node:xml_element_int) =
    fn#itera
      (fun baddr block ->
        let bNode = xmlElement "bl" in
        begin
          block#itera
            (fun ctxtiaddr instr ->
              let iNode = xmlElement "i" in
              begin
                self#write_xml_instruction iNode ctxtiaddr instr;
                bNode#appendChildren [iNode];
                iNode#setAttribute "ia" ctxtiaddr
              end);
          node#appendChildren [bNode];
          bNode#setAttribute "ba" baddr
        end)

  method private write_xml_cfg_block
                   (node:xml_element_int) (b:arm_assembly_block_int) =
    let set = node#setAttribute in
    let blockloc = b#get_location in
    let looplevels = get_arm_loop_levels b#get_context_string in
    let llNode = xmlElement "loops" in
    begin
      llNode#appendChildren
        (List.map (fun a ->
             let lNode = xmlElement "lv" in   (* level *)
             begin
               lNode#setAttribute "a" a;
               lNode
             end) looplevels);
      (if system_info#is_trampoline_payload b#get_first_address then
         set "role" "trampoline_payload");
      (if system_info#is_trampoline_wrapper b#get_first_address then
         set "role" "trampoline_wrapper");
      (if b#has_conditional_returns
       then
         set
           "fnexits"
           (String.concat "," (List.map string_of_int b#exit_edges_indices)));
      set "ba" b#get_context_string;
      set "ea" (make_i_location blockloc b#get_last_address)#ci
    end

  method private write_xml_cfg (node:xml_element_int) =
    let _ = record_arm_loop_levels faddr in
    let nodes = ref [] in
    let edges = ref [] in
    let bbNode = xmlElement "blocks" in
    let eeNode = xmlElement "edges" in
    begin
      fn#itera
        (fun baddr block ->
          let bNode = xmlElement "bl" in
          begin
            chlog#add
              "cfg assembly block"
              (LBLOCK [
                   STR baddr;
                   STR ": successors: ";
                   pretty_print_list block#get_successors
                     (fun s -> STR s) "[" ", " "]"]);
            self#write_xml_cfg_block bNode block;
            List.iter (fun succ ->
                let eNode = xmlElement "e" in
                let seta tag a = eNode#setAttribute tag a in
                begin
                  seta "src" baddr;
                  seta "tgt" succ;
                  edges := eNode :: !edges
                end) block#get_successors;
            nodes := bNode :: !nodes
          end);
      bbNode#appendChildren (List.rev !nodes);
      eeNode#appendChildren (List.rev !edges);
      node#appendChildren [bbNode; eeNode]
    end

  method private write_xml_jumptables (node: xml_element_int) =
    let jumptables = fn#get_jumptables in
    node#appendChildren
      (List.map (fun (va, jt) ->
           let jtnode = xmlElement "jt" in
           begin
             jtnode#setAttribute "va" va#to_hex_string;
             jt#write_xml jtnode;
             jtnode
           end) jumptables)

    (*
  method private write_xml_btypes (node: xml_element_int) =
    let btypes = finfo#get_btype_table in
    node#appendChildren
      (List.map (fun (vix, bix, bixs) ->
           let btnode = xmlElement "bt" in
           begin
             btnode#setIntAttribute "vix" vix;
             btnode#setIntAttribute "bix" bix;
             btnode#setAttribute
               "bixs"
               (String.concat "," (List.map string_of_int bixs));
             btnode
           end) btypes)
     *)

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let cNode = xmlElement "cfg" in
    let jjNode = xmlElement "jump-tables" in
    let dNode = xmlElement "instr-dictionary" in
    let iiNode = xmlElement "instructions" in
    let sfNode = xmlElement "stackframe" in
    let grNode = xmlElement "global-references" in
    (* let bNode = xmlElement "btypes" in *)
    begin
      self#write_xml_cfg cNode;
      self#write_xml_jumptables jjNode;
      self#write_xml_instructions iiNode;
      finfo#stackframe#write_xml sfNode;
      mmap#write_xml_references faddr vard grNode;
      (* self#write_xml_btypes bNode; *)
      id#write_xml dNode;
      append [cNode; dNode; iiNode; jjNode; sfNode; grNode]
    end

  method write_xml_register_types
           (node: xml_element_int)
           (regtypes: (register_t * string * btype_t option) list) =
    let regnode = xmlElement "register-lhs-types" in
    begin
      List.iter (fun (reg, iaddr, optty) ->
          let inode = xmlElement "reglhs" in
          begin
            bd#write_xml_register inode reg;
            inode#setAttribute "iaddr" iaddr;
            (match optty with
             | Some ty -> bcd#write_xml_typ inode ty
             | _ -> ());
            regnode#appendChildren [inode]
          end) regtypes;
      node#appendChildren [regnode]
    end

  method write_xml_stack_types
           (node: xml_element_int)
           (stacktypes: (int * btype_t option) list) =
    let stacknode = xmlElement "stack-variable-types" in
    begin
      List.iter (fun (offset, optty) ->
          let inode = xmlElement "offset" in
          begin
            inode#setIntAttribute "off" offset;
            (match optty with
             | Some ty -> bcd#write_xml_typ inode ty
             | _ -> ());
            stacknode#appendChildren [inode]
          end) stacktypes;
      node#appendChildren [stacknode]
    end

  method save =
    let node = xmlElement "application-results" in
    begin
      self#write_xml node;
      node#setAttribute "a" faddr#to_hex_string;
      save_app_function_results_file faddr#to_hex_string node;
      save_vars faddr#to_hex_string vard
    end

end


class arm_analysis_results_t:arm_analysis_results_int =
object (self)

  val table = H.create 3
  val typeconstraintstore = mk_type_constraint_store ()

  method record_results ?(save=true) (fn:arm_assembly_function_int) =
    let fndata = new fn_analysis_results_t fn in
    let vard = (get_function_info fn#get_address)#env#varmgr#vard in
    let typeconstraints =
      mk_arm_fn_type_constraints typeconstraintstore fn in
    let node = xmlElement "application-results" in
    begin
      (if save then
         let faddr = fn#get_address#to_hex_string in
         begin
           fndata#write_xml node;
           typeconstraints#record_type_constraints;
           fndata#write_xml_register_types node
             (typeconstraintstore#resolve_reglhs_types faddr);
           fndata#write_xml_stack_types node
             (typeconstraintstore#resolve_local_stack_lhs_types faddr);
           node#setAttribute "a" faddr;
           save_app_function_results_file faddr node;
           save_vars faddr vard
         end );
           (* (if save then fndata#save); *)
      H.add table fn#get_address#to_hex_string fn;
      typeconstraints#record_type_constraints;
    end

  method write_xml (node:xml_element_int) =
    let ffnode = xmlElement "functions" in
    let _ =
      (* H.iter (fun faddr fn -> *)
      arm_assembly_functions#itera (fun faddr fn ->
          let fnode = xmlElement "fn" in
          let xfaddr = faddr#to_hex_string in
          begin
            fnode#setAttribute "fa" xfaddr;
            fnode#setAttribute "md5" fn#get_function_md5;
            fnode#setAttribute "rf" (if H.mem table xfaddr then "Y" else "N");
            ffnode#appendChildren [fnode]
          end) (* table *) in
    node#appendChildren [ffnode]

  method save =
    let node = xmlElement "application-results" in
    begin
      self#write_xml node;
      save_resultdata_file node
    end

end


let arm_analysis_results = new arm_analysis_results_t
