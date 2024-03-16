(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHSystemSettings

(* jchpre *)
open JCHApplication
open JCHAnnotationsPre
open JCHBCFunction
open JCHIFSystem
open JCHPreAPI

(* jchfeatures  *)
open JCHFeatureDictionary
open JCHFeaturesAPI
open JCHMethodExprs

module H = Hashtbl

(* -------------------------------------------------------------------------- *
 * Byte code is reconstructed into                                            *
 * - assignments,                                                             *
 * - calls                                                                    *
 * - exceptions,                                                              *
 * - control flow graph                                                       *
 * all of these components are stored, in dictionary form,                    *
 * in xml; the actual feature extraction is performed by the semantic code    *
 * search application geared towards different application domains (e.g.,     *
 * algorithms, databases, crypto, collections, etc.                           *
 * -------------------------------------------------------------------------- *)

let returnvalue_is_popped (_mInfo:method_info_int) (_pc:int) = false   (* TBD *)


let can_translate_to_chif (mInfo:method_info_int) =
  let arraystorecount =
    let n = ref 0 in
    let _ =
      mInfo#get_bytecode#get_code#iteri (fun _ opc ->
	  match opc with OpArrayStore _ -> n := !n + 1 | _ -> ()) in !n in
  let instrcount = mInfo#get_instruction_count in
  not (instrcount > 4000 && arraystorecount > 1000)


let write_xml_method_expr_features
      (node:xml_element_int)
      (d:feature_dictionary_int)
      (_cInfo:class_info_int)
      (mInfo:method_info_int) =
  let add (pc:int) (fxfeature:fxfeature_t) =
    let fnode = xmlElement "fx" in
    begin
      d#write_xml_fxfeature fnode fxfeature;
      fnode#setIntAttribute "pc" pc;
      node#appendChildren [fnode]
    end in
  if mInfo#has_bytecode && (can_translate_to_chif mInfo) then
    let _ = chif_system#create_method_stack_layout mInfo in
    try
      mInfo#get_bytecode#get_code#iteri
        (fun pc opc ->
          match opc with    (* --- collect assignments --- *)
          | OpStore _
            | OpPutStatic _
            | OpIInc _
            | OpArrayStore _
            | OpPutField _ ->
             (try
                add pc (get_assignment_expr mInfo pc)
              with
              | JCH_failure p ->
                 system_settings#log_error
                   (LBLOCK  [
                        mInfo#get_class_method_signature#toPretty;
                        STR " at pc = ";
                        INT pc;
                        STR ": ";
                        opcode_to_pretty opc;
                        STR ": ";
                        p]))
          (* --- collect calls --- *)
          | OpInvokeVirtual (_,ms)
            | OpInvokeSpecial (_,ms)
            | OpInvokeStatic (_,ms)
            | OpInvokeInterface (_,ms)
               when not ms#has_return_value ||
                      (returnvalue_is_popped mInfo pc) ->
             add pc (get_procedurecall mInfo pc)
          (* --- collect exceptions raised --- *)
          | OpThrow -> add pc (get_throwable mInfo pc)
          (* --- collect return expressions --- *)
          | OpReturn t when (not (t = Void)) ->
             add pc (get_returnexpr mInfo pc)
          | OpReturn Void -> add pc (FXReturn None)
          | _ ->
             (* --- collect branch conditions --- *)
             if is_conditional_jump mInfo pc  then
               add pc (get_branch_condition mInfo pc)
             else
               ())
    with
    | JCH_failure p ->
       raise
         (JCH_failure
            (LBLOCK [
                 mInfo#get_class_method_signature#toPretty; STR ": "; p]))


let write_xml_method_cfg (node:xml_element_int) (mInfo:method_info_int) =
  let (blocks,succ) = get_bc_function_basic_blocks mInfo in
  let looplevels = get_cfg_loop_levels  mInfo blocks succ in
  if (List.length succ) = 0 then () else
    let cfgnode = xmlElement "cfg" in
    let bbNode = xmlElement "blocks" in
    let eeNode = xmlElement "edges" in
    let setp node i1 i2 =
      node#setAttribute
        "p" (String.concat "," [string_of_int i1; string_of_int i2]) in
    begin
      bbNode#appendChildren
        (List.map (fun b ->
             let bNode = xmlElement "bb" in
             begin
               (if H.mem looplevels b#get_firstpc
                   && (List.length (H.find looplevels b#get_firstpc) > 0) then
                  let levels = H.find looplevels b#get_firstpc in
                  let llNode = xmlElement "loops" in
                  begin
                    llNode#appendChildren
                      (List.map (fun l ->
                           let lNode = xmlElement "lvl" in
                           begin
                             lNode#setIntAttribute "pc" l#getSeqNumber;
                             lNode
                           end) levels);
                    bNode#appendChildren [llNode]
                  end);
               setp bNode b#get_firstpc b#get_lastpc;
               bNode
             end) blocks);
      eeNode#appendChildren
        (List.map (fun (src,tgt) ->
             let eNode = xmlElement "e" in
             begin setp eNode src tgt; eNode end) succ);
      cfgnode#appendChildren [bbNode; eeNode];
      node#appendChildren [cfgnode]
    end


let write_xml_method_features
      (node:xml_element_int)
      (d:feature_dictionary_int)
      (cInfo:class_info_int)
      (mInfo:method_info_int) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let exceptions = mInfo#get_exceptions in
  let etable = mInfo#get_exception_table in
  let fnode = xmlElement "features" in
  begin
    (if (List.length exceptions) > 0 then
       let eeNode = xmlElement "exceptions" in
       begin
         eeNode#appendChildren
           (List.map (fun e ->
                let eNode = xmlElement "e" in
                begin
                  d#write_xml_class_name eNode e;
                  eNode
                end) exceptions);
         node#appendChildren [eeNode]
       end);
    (if (List.length etable) > 0  then
       let hhnode = xmlElement "handlers" in
       begin
         hhnode#appendChildren
           (List.map (fun h ->
                let hnode = xmlElement "h" in
                let seti = hnode#setIntAttribute in
                begin
                  seti "spc" h#h_start;
                  seti "epc" h#h_end;
                  seti "hpc" h#handler;
                  (match h#catch_type with
                   | Some cn -> d#write_xml_class_name hnode cn
                   | _ -> ());
                  hnode
                end) etable);
         node#appendChildren [hhnode]
       end);
    (try
       write_xml_method_expr_features fnode d cInfo mInfo;
     with
     | JCH_failure p ->
        begin
          system_settings#log_error
            (LBLOCK [
                 STR "Error in translating ";
                 mInfo#get_class_method_signature#toPretty;
                 STR ": ";
                 p]);
          sety "obsolete" true
        end);
    node#appendChildren [fnode];
    d#write_xml_method_signature node
      mInfo#get_class_method_signature#method_signature;
    (if mInfo#has_bytecode then
       begin
         write_xml_method_cfg node mInfo;
         seti "instrs" mInfo#get_instruction_count;
         seti "bytes" mInfo#get_byte_count
       end);
    set "name" mInfo#get_method_name;
    set "access" (access_to_string mInfo#get_visibility);
    sety "final"  mInfo#is_final;
    sety "abstract" mInfo#is_abstract;
    sety "static" mInfo#is_static;
    sety "native" mInfo#is_native;
  end


let write_xml_class_expr_features
      (node:xml_element_int) (cInfo:class_info_int) =
  let set = node#setAttribute in
  let d = mk_feature_dictionary () in
  let dnode = xmlElement "dictionary" in
  let mmnode = xmlElement "methods" in
  let methods = cInfo#get_methods_defined in
  let add_classnames tag cns =
    if (List.length cns) > 0 then
      let cnode = xmlElement tag in
      begin
        cnode#appendChildren
          (List.map (fun cn ->
               let cnnode = xmlElement "cn"  in
               begin
                 cnnode#setAttribute "name" cn#simple_name;
                 cnnode#setAttribute "pkg" cn#package_name;
                 cnnode
               end) cns);
        node#appendChildren [cnode]
      end in
  let add_methodnames tag mss =
    if (List.length mss) > 0 then
      let mnode = xmlElement tag in
      begin
        mnode#appendChildren
          (List.map (fun ms ->
               let msnode = xmlElement "ms" in
               begin
                 msnode#setAttribute "name" ms#name;
                 msnode#setAttribute "sig" ms#to_signature_string;
                 msnode
               end) mss);
        node#appendChildren [mnode]
      end in
  let mInfos =
    List.fold_left (fun acc ms ->
        try
          let jm = cInfo#get_method ms in
          if jm#is_concrete then
            (app#get_method jm#get_class_method_signature) :: acc
          else
            acc
        with
        | JCH_failure  _ -> acc) [] methods in
  begin
    (if cInfo#has_super_class then
       add_classnames "superclass" [cInfo#get_super_class]);
    add_classnames "interfaces" cInfo#get_interfaces;
    add_methodnames "native-methods" cInfo#get_native_methods_defined;
    node#appendChildren [dnode];
    mmnode#appendChildren
      (List.map (fun mInfo ->
           let mnode = xmlElement "method" in
           begin
             write_xml_method_features mnode d cInfo mInfo;
             mnode
           end) mInfos);
    node#appendChildren [mmnode];
    d#write_xml dnode ;
    set "name" cInfo#get_class_name#simple_name;
    set "package" cInfo#get_class_name#package_name;
    set "md5" cInfo#get_md5_digest
  end
