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
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHTraceResult
open CHXmlDocument

(* xprlib *)
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


let bd = BCHDictionary.bdictionary


class saved_register_t (reg:register_t) =
object (_self:'a)

  val mutable save_address = None
  val restore_addresses = new StringCollections.set_t

  method compare (other:'a) = Stdlib.compare reg other#get_register

  method set_save_address (a:ctxt_iaddress_t) = save_address <- Some a
  method add_restore_address (a:ctxt_iaddress_t) = restore_addresses#add a

  method get_register = reg

  method get_save_address =
    match save_address with
      Some a -> a
    | _ ->
      let msg = (LBLOCK [ STR "saved_register.get_save_address " ;
			  STR (register_to_string reg) ]) in
      begin
	ch_error_log#add "invocation error" msg ;
	raise (Invocation_error
                 ("saved_register.get_save_address " ^ (register_to_string reg)))
      end

  method get_restore_addresses = restore_addresses#toList

  method has_save_address =
    match save_address with Some _ -> true | _ -> false

  method has_restore_addresses = not restore_addresses#isEmpty

  method is_save_or_restore_address (iaddr:ctxt_iaddress_t) =
    (match save_address with Some a -> a = iaddr | _ -> false) ||
      (List.mem iaddr restore_addresses#toList)

  method write_xml (node:xml_element_int) =
    begin
      bd#write_xml_register node reg ;
      (match save_address with
       | Some a -> node#setAttribute "save" a ;
       | _ -> ()) ;
      (if restore_addresses#isEmpty then () else
         node#setAttribute "restore" (String.concat ";" restore_addresses#toList))
    end

  method toPretty =
    let pSaved = match save_address with
      | Some a -> LBLOCK [ STR "saved: " ; STR a ]
      | _ -> STR "not saved" in
    let pRestored = match restore_addresses#toList with
      | [] -> STR "not restored"
      | l ->
         LBLOCK [
             STR "restored: ";
	     pretty_print_list l (fun a -> STR a) "[" ", " "]" ] in
    LBLOCK [
        STR (register_to_string reg);
        STR ". ";
        pSaved;
        STR "; ";
        pRestored]

end


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


let opt_size_to_string (optsize: int option): string =
  match optsize with
  | Some s -> (string_of_int s)
  | _ -> "?"


class stackslot_t (sslot: stackslot_rec_t): stackslot_int =
object

  method sslot_rec = sslot

  method name = sslot.sslot_name

  method offset = sslot.sslot_offset

  method btype = sslot.sslot_btype

  method size = sslot.sslot_size

  method desc = sslot.sslot_desc

  method contains_offset (_offset: int) = false

  method frame2object_offset_value (_xpr: xpr_t) = Error ["Not yet implemenented"]

  method frame_offset_memory_offset
           ?(tgtsize=None)
           ?(tgtbtype=t_unknown)
           (_xpr: xpr_t): memory_offset_t traceresult =
    Error ["Not yet implemented for btype: "
           ^ (btype_to_string tgtbtype)
           ^  " and size "
           ^ (opt_size_to_string tgtsize)]

  method object_offset_memory_offset
           ?(tgtsize=None)
           ?(tgtbtype=t_unknown)
           (_xpr: xpr_t): memory_offset_t traceresult =
    Error ["Not yet implemented: "
           ^ (btype_to_string tgtbtype)
           ^ " and size "
           ^ (opt_size_to_string tgtsize)]

  method write_xml(_node: xml_element_int) = ()

end


class stackframe_t
        (fndata: function_data_int)
        (varmgr: variable_manager_int):stackframe_int =
object (self)

  val saved_registers = H.create 3   (* reg -> saved_register_t *)
  val accesses = H.create 3      (* offset -> (iaddr, stack_access_t) list *)
  val stackslots =
    let slots = H.create 3 in    (* offset -> stackslot *)
    begin
      (match fndata#get_function_annotation with
       | Some fnannot ->
          List.iter (fun svintro ->
              let ty = match svintro.svi_vartype with
                | Some ty -> ty
                | _ -> t_unknown in
              let size = TR.to_option (size_of_btype ty) in
              let sslot = {
                  sslot_offset = svintro.svi_offset;
                  sslot_name = svintro.svi_name;
                  sslot_btype = ty;
                  sslot_desc = Some ("svintro");
                  sslot_size = size} in
              let stackslot = new stackslot_t sslot in
              let _ =
                chlog#add "stack slot added" (stackslot_rec_to_pretty sslot) in
              H.add slots svintro.svi_offset stackslot) fnannot.stackvarintros
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
           ?(size = None)
           ?(desc = None)
           (offset: int): stackslot_int traceresult =
    if offset <= 0 then
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Illegal offset for stack slot: "
             ^ (string_of_int offset)
             ^ ". Offset should be greater than zero."]
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
    let _ = self#add_access offset iaddr spill in
    let regstr = register_to_string reg in
    if H.mem saved_registers regstr then
      (H.find saved_registers regstr)#set_save_address iaddr
    else
      let savedreg = new saved_register_t reg in
      begin
        savedreg#set_save_address iaddr;
        H.add saved_registers regstr savedreg
      end

  method add_register_restore
           ~(offset: int) (reg: register_t) (iaddr: ctxt_iaddress_t) =
    let restore = RegisterRestore (offset, reg) in
    let _ = self#add_access offset iaddr restore in
    let regstr = register_to_string reg in
    if H.mem saved_registers regstr then
      (H.find saved_registers regstr)#add_restore_address iaddr
    else
      let savedreg = new saved_register_t reg in
      begin
        savedreg#add_restore_address iaddr;
        H.add saved_registers regstr savedreg
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

  method private write_xml_saved_registers (node:xml_element_int) =
    let savedregs = H.fold (fun _ v a -> v::a) saved_registers [] in
    node#appendChildren
      (List.map (fun s ->
           let n = xmlElement "sr" in
           begin
             s#write_xml n;
             n
           end) savedregs)

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
    let srNode = xmlElement "saved-registers" in
    let saNode = xmlElement "stack-accesses" in
    begin
      self#write_xml_saved_registers srNode;
      self#write_xml_stack_accesses saNode;
      append [srNode; saNode]
    end


end


let mk_function_stackframe = new stackframe_t
