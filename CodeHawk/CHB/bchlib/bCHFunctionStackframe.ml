(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2025  Aarno Labs LLC

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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHTraceResult
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHLibTypes

module H = Hashtbl
module TR = CHTraceResult


let x2p = XprToPretty.xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)


let bcd = BCHBCDictionary.bcdictionary
let bd = BCHDictionary.bdictionary


let stackslot_rec_to_pretty (sslot: stackslot_rec_t): pretty_t =
  LBLOCK [
      STR "offset: "; INT sslot.sslot_offset; NL;
      STR "name  : "; STR sslot.sslot_name; NL;
      STR "type  : "; STR (btype_to_string sslot.sslot_btype); NL;
      (match sslot.sslot_size with
       | Some s -> LBLOCK [STR "size  : "; INT s; NL]
       | _ -> STR "");
      (match sslot.sslot_desc with
       | Some desc -> LBLOCK [STR "desc  : "; STR desc; NL]
       | _ -> STR "")
    ]


class stackslot_t (sslot: stackslot_rec_t): stackslot_int =
object (self)

  method sslot_rec = sslot

  method name = sslot.sslot_name

  method offset = sslot.sslot_offset

  method btype = sslot.sslot_btype

  method is_typed: bool = not (btype_equal self#btype t_unknown)

  method spill: register_t option = sslot.sslot_spill

  method is_spill: bool = Option.is_some self#spill

  method is_struct: bool =
    match resolve_type self#btype with
    | Ok (TComp _) -> true
    | _ -> false

  method is_array: bool =
    match resolve_type self#btype with
    | Ok (TArray _) -> true
    | _ -> false

  method size = sslot.sslot_size

  method desc = sslot.sslot_desc

  method contains_offset (offset: int) =
    let size = match self#size with
      | Some s -> s
      | _ -> 4 in
    offset >= self#offset && offset < self#offset + size

  method frame2object_offset_value (xpr: xpr_t) =
    match xpr with
    | XConst (IntConst n) ->
       let numoffset = mkNumerical self#offset in
       Ok (num_constant_expr (n#sub numoffset))
    | _ ->
       Error [
           __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
           ^ "Offset expression "
           ^ (x2s xpr)
           ^ " not yet handled"]

  method frame_offset_memory_offset
           ?(tgtsize=None)
           ?(tgtbtype=t_unknown)
           (xpr: xpr_t): memory_offset_t traceresult =
    TR.tbind
      (self#object_offset_memory_offset ~tgtsize ~tgtbtype)
      (self#frame2object_offset_value xpr)

  method object_offset_memory_offset
           ?(tgtsize=None)
           ?(tgtbtype=t_unknown)
           (xoffset: xpr_t): memory_offset_t traceresult =
    match xoffset with
    | XConst (IntConst n) when n#equal CHNumerical.numerical_zero ->
       Ok NoOffset
    | XConst (IntConst n) when not self#is_typed ->
       Ok (ConstantOffset (n, NoOffset))
    | _ ->
       let tgtbtype =
         if is_unknown_type tgtbtype then None else Some tgtbtype in
       if self#is_array then
         let btype = TR.tvalue (resolve_type self#btype) ~default:t_unknown in
         self#arrayvar_memory_offset ~tgtsize ~tgtbtype btype xoffset
       else if self#is_struct then
         let btype = TR.tvalue (resolve_type self#btype) ~default:t_unknown in
         self#structvar_memory_offset ~tgtsize ~tgtbtype btype xoffset
       else
         Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                ^ (btype_to_string self#btype)
                ^ " not yet handled"]

  method private arrayvar_memory_offset
                   ~(tgtsize: int option)
                   ~(tgtbtype: btype_t option)
                   (btype: btype_t)
                   (xoffset: xpr_t): memory_offset_t traceresult =
    let iszero x =
      match x with
      | XConst (IntConst n) -> n#equal CHNumerical.numerical_zero
      | _ -> false in
    match xoffset with
    | XConst (IntConst n) when
           n#equal CHNumerical.numerical_zero
           && Option.is_none tgtsize
           && Option.is_none tgtbtype ->
       Ok NoOffset
    | _ ->
       if is_array_type btype then
         let eltty = get_element_type btype in
         tbind
           (fun elsize ->
             let optindex = BCHXprUtil.get_array_index_offset xoffset elsize in
             match optindex with
             | None ->
                Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                       ^ "Unable to extract index from " ^ (x2s xoffset)]
             | Some (indexxpr, xrem) when
                    iszero xrem
                    && Option.is_none tgtsize
                    && Option.is_none tgtbtype ->
                Ok (ArrayIndexOffset (indexxpr, NoOffset))
             | Some (indexxpr, xrem) ->
                Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                       ^ "Unable to handle remainder "
                       ^ (x2s xrem)
                       ^ " with index expression "
                       ^ (x2s indexxpr)])
           (size_of_btype eltty)
       else
         Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                ^ "xoffset: " ^ (x2s xoffset)
                ^ "; btype: " ^ (btype_to_string btype)]

  method private structvar_memory_offset
                   ~(tgtsize: int option)
                   ~(tgtbtype: btype_t option)
                   (btype: btype_t)
                   (xoffset: xpr_t): memory_offset_t traceresult =
    match xoffset with
    | XConst (IntConst n) when
           n#equal CHNumerical.numerical_zero
           && Option.is_none tgtsize
           && Option.is_none tgtbtype ->
       Ok NoOffset
    | XConst (IntConst _) ->
       if is_struct_type btype then
         let compinfo = get_struct_type_compinfo btype in
         (self#get_field_memory_offset_at ~tgtsize ~tgtbtype compinfo xoffset)
       else
         Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                ^ "xoffset: " ^ (x2s xoffset)
                ^ "; btype: " ^ (btype_to_string btype)]
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "xoffset: " ^ (x2s xoffset)
              ^ "; btype: " ^ (btype_to_string btype)]

  method private get_field_memory_offset_at
                   ~(tgtsize: int option)
                   ~(tgtbtype: btype_t option)
                   (c: bcompinfo_t)
                   (xoffset: xpr_t): memory_offset_t traceresult =
    let is_void_tgtbtype =
      match tgtbtype with
      | Some (TVoid _) -> true
      | _ -> false in
    let pr_tgtsize =
      match tgtsize with
      | Some s -> string_of_int s
      | _ -> "?" in
    match xoffset with
    | XConst (IntConst n) ->
       let offset = n#toInt in
       let finfos = c.bcfields in
       let optfield_r =
         List.fold_left (fun acc_r finfo ->
             match acc_r with
             (* Error has been detected earlier *)
             | Error e -> Error e
             (* Result has already been determined *)
             | Ok (Some _) -> acc_r
             (* Still looking for a result *)
             | Ok _ ->
                match finfo.bfieldlayout with
                | None ->
                   Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                          ^ "No field layout for field " ^ finfo.bfname]
                | Some (foff, sz) ->
                   if offset < foff then
                     Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                            ^ "Skipped over field: "
                            ^ (string_of_int offset)]
                   else if offset >= (foff + sz) then
                     Ok None
                   else
                     let offset = offset - foff in
                     tbind
                       (fun fldtype ->
                         if offset = 0 && is_void_tgtbtype then
                           Ok (Some (FieldOffset
                                       ((finfo.bfname, finfo.bfckey), NoOffset)))
                         else if offset = 0
                                 && (is_scalar fldtype) then
                           Ok (Some (FieldOffset
                                       ((finfo.bfname, finfo.bfckey), NoOffset)))
                         else
                           Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                                  ^ "Field offset "
                                  ^ (x2s xoffset)
                                  ^ " not yet handled"])
                       (resolve_type finfo.bftype)) (Ok None) finfos in
       (match optfield_r with
        | Error e -> Error e
        | Ok (Some offset) -> Ok offset
        | Ok None ->
           Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                  ^ "Unable to find field at offset " ^ (string_of_int offset)])
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Unable to determine field for xoffset: " ^ (x2s xoffset)
              ^ " and tgtsize: " ^ pr_tgtsize ]

  method write_xml(node: xml_element_int) =
    begin
      node#setAttribute "name" self#name;
      node#setIntAttribute "offset" self#offset;
      (match self#size with
       | Some s -> node#setIntAttribute "size" s
       | _ -> ());
      (if is_known_type self#btype then
         node#setIntAttribute "tix" (bcd#index_typ self#btype));
      (if self#is_spill then
         node#setIntAttribute "srix" (bd#index_register (Option.get self#spill)));
      (match self#desc with
       | Some d -> node#setAttribute "desc" d
       | _ -> ());
    end

end


class stackframe_t
        (fndata: function_data_int)
        (varmgr: variable_manager_int):stackframe_int =
object (self)

  (* val saved_registers = H.create 3   (* reg -> saved_register_t *) *)
  val accesses = H.create 3      (* offset -> (iaddr, stack_access_t) list *)
  val stackslots =
    let slots = H.create 3 in    (* offset -> stackslot *)
    begin
      (match fndata#get_function_annotation with
       | Some fnannot ->
          List.iter (fun svintro ->
              let negoffset = -svintro.svi_offset in
              let ty = match svintro.svi_vartype with
                | Some ty -> ty
                | _ -> t_unknown in
              let size = TR.to_option (size_of_btype ty) in
              let sslot = {
                  sslot_offset = negoffset;
                  sslot_name = svintro.svi_name;
                  sslot_btype = ty;
                  sslot_spill = None;
                  sslot_desc = Some ("svintro");
                  sslot_size = size} in
              let stackslot = new stackslot_t sslot in
              let _ =
                chlog#add "stack slot added" (stackslot_rec_to_pretty sslot) in
              H.add slots negoffset stackslot) fnannot.stackvarintros
       | _ -> ());
      slots
    end

  method private vard = varmgr#vard

  method private xd = self#vard#xd

  method private add_access
                   (offset: int) (iaddr: ctxt_iaddress_t) (acc: stack_access_t) =
    let entry =
      if H.mem accesses offset then
        H.find accesses offset
      else
        [] in
    H.replace accesses offset ((iaddr, acc) :: entry)

  method containing_stackslot (offset: int): stackslot_int option =
    H.fold (fun _ sslot acc ->
        match acc with
        | Some _ -> acc
        | _ -> if sslot#contains_offset offset then Some sslot else None)
      stackslots None

  method add_stackslot
           ?(name = None)
           ?(btype = t_unknown)
           ?(spill = None)
           ?(size = None)
           ?(desc = None)
           (offset: int): stackslot_int traceresult =
    if offset >= 0 then
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Illegal offset for stack slot: "
             ^ (string_of_int offset)
             ^ ". Offset should be less than zero."]
    else if H.mem stackslots offset then
      begin
        log_error_result
          ~tag:"duplicate stack slot"
          ~msg:("Stack slot at offset "
                ^ (string_of_int offset)
                ^ "already exists")
          __FILE__ __LINE__ [];
        Ok (H.find stackslots offset)
      end
    else
      match self#containing_stackslot offset with
      | Some sslot ->
         let msg =
           "Stackslot at offset "
           ^ (string_of_int offset)
           ^ " overlaps with "
           ^ sslot#name
           ^ " ("
           ^ (string_of_int sslot#offset)
           ^ (match sslot#size with
              | Some s -> ", size: " ^ (string_of_int s)
              | _ -> "")
           ^ ")" in
         begin
           log_error_result
             ~tag:"overlapping stackslot"
             ~msg
             __FILE__ __LINE__ [];
           Error [msg]
         end
      | _ ->
         let sname =
           match name with
           | Some name -> name
           | _ -> "var_" ^ (string_of_int offset) in
         let ssrec = {
             sslot_name = sname;
             sslot_offset = offset;
             sslot_btype = btype;
             sslot_spill = spill;
             sslot_size = size;
             sslot_desc = desc
           } in
         let sslot = new stackslot_t ssrec in
         begin
           H.add stackslots offset sslot;
           chlog#add
             "stackframe:add stackslot"
             (LBLOCK [
                  INT offset;
                  STR ": ";
                  STR sslot#name]);
           Ok sslot
         end

  method add_register_spill
           ~(offset: int) (reg: register_t) (iaddr:ctxt_iaddress_t) =
    let spill = RegisterSpill (offset, reg) in
    begin
      (if H.mem stackslots offset then
        if (H.find stackslots offset)#is_spill then
          ()
        else
          raise (BCH_failure (LBLOCK [STR "Stackslot already taken"]))
      else
        let ssrec = {
            sslot_name = (register_to_string reg) ^ "_spill";
            sslot_offset = offset;
            sslot_btype = t_unknown;
            sslot_spill = Some reg;
            sslot_size = Some 4;
            sslot_desc = Some "register spill"
          } in
        let sslot = new stackslot_t ssrec in
        H.add stackslots offset sslot);
        self#add_access offset iaddr spill
    end

  method add_register_restore
           ~(offset: int) (reg: register_t) (iaddr: ctxt_iaddress_t) =
    let restore = RegisterRestore (offset, reg) in
    begin
      (if H.mem stackslots offset then
        if (H.find stackslots offset)#is_spill then
          ()
        else
          raise (BCH_failure (LBLOCK [STR "Stackslot already taken"]))
      else
        let ssrec = {
            sslot_name = (register_to_string reg) ^ "_spill";
            sslot_offset = offset;
            sslot_btype = t_unknown;
            sslot_spill = Some reg;
            sslot_size = Some 4;
            sslot_desc = Some "register_spill"
          } in
        let sslot = new stackslot_t ssrec in
        H.add stackslots offset sslot);
      self#add_access offset iaddr restore
    end

  method add_load
           ~(offset:int)
           ~(size:int option)
           ~(typ:btype_t option)
           (var: variable_t)
           (iaddr:ctxt_iaddress_t) =
    let ty = match typ with Some t -> t  | _ -> t_unknown in
    let load = StackLoad (var, offset, size, ty) in
    self#add_access offset iaddr load

  method add_store
           ~(offset:int)
           ~(size:int option)
           ~(typ:btype_t option)
           ~(xpr:xpr_t option)
           (var: variable_t)
           (iaddr:ctxt_iaddress_t) =
    let ty = match typ with Some t -> t | _ -> t_unknown in
    let store = StackStore (var, offset, size, ty, xpr) in
    self#add_access offset iaddr store

  method add_block_read
           ~(offset:int)
           ~(size:int option)
           ~(typ:btype_t option)
           (iaddr:ctxt_iaddress_t) =
    let ty = match typ with Some t -> t | _ -> t_unknown in
    let blread = StackBlockRead (offset, size, ty) in
    self#add_access offset iaddr blread

  method add_block_write
           ~(offset:int)
           ~(size:int option)
           ~(typ:btype_t option)
           ~(xpr:xpr_t option)
           (iaddr:ctxt_iaddress_t) =
    let ty = match typ with Some t -> t | _ -> t_unknown in
    let store = StackBlockWrite (offset, size, ty, xpr) in
    self#add_access offset iaddr store

  method private write_xml_stack_slots (node: xml_element_int) =
    let slotsnode = xmlElement "stack-slots" in
    begin
      H.iter (fun _ slot ->
          let slotnode = xmlElement "slot" in
          begin
            slot#write_xml slotnode;
            slotsnode#appendChildren [slotnode]
          end) stackslots;
      node#appendChildren [slotsnode]
    end

  method private write_xml_stack_accesses (node: xml_element_int) =
    let slist = ref [] in
    let _ = H.iter (fun offset l -> slist := (offset, l) :: !slist) accesses in
    List.iter (fun (offset, l) ->
        let offNode = xmlElement "offset" in
        begin
          offNode#setIntAttribute "n" offset;
          List.iter (fun (iaddr, sa) ->
              let saNode = xmlElement "sa" in
              begin
                self#vard#write_xml_stack_access saNode sa;
                saNode#setAttribute "addr" iaddr;
                offNode#appendChildren [saNode]
              end) l;
          node#appendChildren [offNode]
        end) !slist

  method write_xml (node: xml_element_int) =
    let append = node#appendChildren in
    (* let srNode = xmlElement "saved-registers" in *)
    let sNode = xmlElement "stack-slots" in
    let saNode = xmlElement "stack-accesses" in
    begin
      self#write_xml_stack_slots sNode;
      self#write_xml_stack_accesses saNode;
      append [sNode; saNode]
    end


end


let mk_function_stackframe = new stackframe_t
