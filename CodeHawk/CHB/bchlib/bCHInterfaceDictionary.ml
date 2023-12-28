(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
(* The interface dictionary is global to the system. *)

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHIndexTable
open CHPrettyUtil
open CHStringIndexTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypeUtil
open BCHDoubleword
open BCHDictionary
open BCHLibTypes
open BCHLocation
open BCHSumTypeSerializer
open BCHUtilities

module TR = CHTraceResult

let bcd = BCHBCDictionary.bcdictionary
let bd = BCHDictionary.bdictionary


let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [
        STR "Type ";
        STR name;
        STR " tag: ";
        STR tag;
        STR " not recognized. Accepted tags: ";
        pretty_print_list accepted (fun s -> STR s) "" ", " ""] in
  begin
    ch_error_log#add "serialization tag" msg;
    raise (BCH_failure msg)
  end


class interface_dictionary_t:interface_dictionary_int =
object (self)

  val parameter_location_detail_table =
    mk_index_table "parameter-location-detail-table"
  val parameter_location_table = mk_index_table "parameter-location-table"
  val parameter_location_list_table =
    mk_index_table "parameter-location-list-table"
  val role_table = mk_index_table "role-table"
  val roles_table = mk_index_table "roles-table"
  val fts_parameter_table = mk_index_table "fts-parameter-table"
  val fts_parameter_list_table = mk_index_table "fts-parameter-list-table"
  val bterm_table = mk_index_table "bterm-table"
  val gterm_table = mk_index_table "gterm-table"
  val fts_parameter_value_table = mk_index_table "parameter-value-table"
  val function_signature_table = mk_index_table "function-signature-table"
  val function_interface_table = mk_index_table "function-interface-table"
  val function_semantics_table = mk_index_table "function-semantics-table"
  val xxpredicate_table = mk_index_table "xxpredicate-table"
  val xxpredicate_list_table = mk_index_table "xxpredicate-list-table"
  val function_stub_table = mk_index_table "function-stub-table"
  val call_target_table = mk_index_table "call-target-table"
  val jump_target_table = mk_index_table "jump_target_table"
  val c_struct_constant_table = mk_index_table "c-struct-constant-table"
  val struct_field_value_table = mk_index_table "struct-field-value-table"

  val mutable tables = []

  initializer
    tables <- [
      parameter_location_detail_table;
      parameter_location_table;
      parameter_location_list_table;
      role_table;
      roles_table;
      fts_parameter_table;
      fts_parameter_list_table;
      bterm_table;
      gterm_table;
      fts_parameter_value_table;
      function_signature_table;
      function_interface_table;
      function_semantics_table;
      xxpredicate_table;
      xxpredicate_list_table;
      function_stub_table;
      call_target_table;
      jump_target_table;
      c_struct_constant_table;
      struct_field_value_table
    ]

  method reset =
    begin
      List.iter (fun t -> t#reset) tables
    end

  method index_parameter_location_detail (d: parameter_location_detail_t) =
    let index_extract (x: (int * int) option) =
      match x with
      | None -> [-1]
      | Some (start, size) -> [start; size] in
    let key =
      ([],
       [bcd#index_typ d.pld_type; d.pld_size] @ (index_extract d.pld_extract)) in
    parameter_location_detail_table#add key

  method get_parameter_location_detail (index: int): parameter_location_detail_t =
    let name = "parameter_location_detail" in
    let (_, args) = parameter_location_detail_table#retrieve index in
    let a = a name args in
    { pld_type = bcd#get_typ (a 0);
      pld_size = a 1;
      pld_extract = if (a 2) = (-1) then None else Some (a 2, a 3)
    }

  method index_parameter_location (p:parameter_location_t) =
    let idetail (d: parameter_location_detail_t) =
      self#index_parameter_location_detail d in
    let tags = [parameter_location_mcts#ts p] in
    let key = match p with
      | StackParameter (i, d) -> (tags, [i; idetail d])
      | RegisterParameter (r, d) -> (tags, [bd#index_register r; idetail d])
      | GlobalParameter (a, d) -> (tags, [bd#index_address a; idetail d])
      | UnknownParameterLocation d -> (tags, [idetail d]) in
    parameter_location_table#add key

  method get_parameter_location (index:int):parameter_location_t =
    let name = "parameter_location" in
    let (tags,args) = parameter_location_table#retrieve index in
    let gdetail (i: int) = self#get_parameter_location_detail i in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "s" -> StackParameter (a 0, gdetail (a 1))
    | "r" -> RegisterParameter (bd#get_register (a 0), gdetail (a 1))
    | "g" -> GlobalParameter (bd#get_address (a 0), gdetail (a 1))
    | "u" -> UnknownParameterLocation (gdetail (a 0))
    | s -> raise_tag_error name s parameter_location_mcts#tags

  method index_parameter_location_list (l: parameter_location_t list): int =
    let key = ([], List.map self#index_parameter_location l) in
    parameter_location_list_table#add key

  method get_parameter_location_list (index: int): parameter_location_t list =
    let (_, args) = parameter_location_list_table#retrieve index in
    List.map self#get_parameter_location args

  method index_role (r:(string * string)) =
    let key = ([], [bd#index_string (fst r); bd#index_string (snd r)]) in
    role_table#add key

  method get_role (index:int) =
    let (_, args) = role_table#retrieve index in
    let a = a "role" args in
    (bd#get_string (a 0), bd#get_string (a 1))

  method index_roles (l:(string * string) list) =
    roles_table#add ([],List.map self#index_role l)

  method get_roles (index:int) =
    let (_,args) = roles_table#retrieve index in
    List.map self#get_role args

  method index_fts_parameter (p:fts_parameter_t) =
    let iopt (i: int option) = match i with Some i -> i | _ -> (-1) in
    let tags = [
        arg_io_mfts#ts p.apar_io;
        formatstring_type_mfts#ts p.apar_fmt] in
    let args = [
        iopt p.apar_index;
        bd#index_string p.apar_name;
        bcd#index_typ p.apar_type;
        bd#index_string p.apar_desc;
        self#index_roles p.apar_roles;
        p.apar_size;
        self#index_parameter_location_list p.apar_location
      ] in
    fts_parameter_table#add (tags, args)

  method get_fts_parameter (index:int): fts_parameter_t =
    let getopt (index: int) = if index = (-1) then None else Some index in
    let (tags, args) = fts_parameter_table#retrieve index in
    let t = t "fts-parameter" tags in
    let a = a "fts-parameter" args in
    { apar_index = getopt (a 0);
      apar_name = bd#get_string (a 1);
      apar_type = bcd#get_typ (a 2);
      apar_desc = bd#get_string (a 3);
      apar_roles = self#get_roles (a 4);
      apar_io = arg_io_mfts#fs (t 0);
      apar_fmt = formatstring_type_mfts#fs (t 1);
      apar_size = a 5;
      apar_location = self#get_parameter_location_list (a 6) }

  method index_bterm (t:bterm_t) =
    let tags = [bterm_mcts#ts t] in
    let key = match t with
      | ArgValue p -> (tags, [self#index_fts_parameter p])
      | RunTimeValue -> (tags, [])
      | ReturnValue t -> (tags, [self#index_bterm t])
      | NamedConstant s -> (tags, [bd#index_string s])
      | NumConstant n -> (tags @ [n#toString], [])
      | ArgBufferSize t
        | IndexSize t
        | ByteSize t -> (tags, [self#index_bterm t])
      | ArgAddressedValue (t1,t2) ->
         (tags, [self#index_bterm t1; self#index_bterm t2])
      | ArgNullTerminatorPos t -> (tags, [self#index_bterm t])
      | ArgSizeOf t -> (tags, [bcd#index_typ t])
      | ArithmeticExpr (op,t1, t2) ->
         (tags @ [arithmetic_op_mfts#ts op],
          [self#index_bterm t1; self#index_bterm t2]) in
    bterm_table#add key

  method get_bterm (index:int) =
    let name = "bterm" in
    let (tags,args) = bterm_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "a" -> ArgValue (self#get_fts_parameter (a 0))
    | "rt" -> RunTimeValue
    | "r" -> ReturnValue (self#get_bterm (a 0))
    | "n" -> NamedConstant (bd#get_string (a 0))
    | "nt" -> ArgNullTerminatorPos (self#get_bterm (a 0))
    | "c" -> NumConstant (mkNumericalFromString (t 1))
    | "s" -> ArgBufferSize (self#get_bterm (a 0))
    | "i" -> IndexSize (self#get_bterm (a 0))
    | "b" -> ByteSize (self#get_bterm (a 0))
    | "aa" ->
       ArgAddressedValue (self#get_bterm (a 0), self#get_bterm (a 1))
    | "as" -> ArgSizeOf (bcd#get_typ (a 0))
    | "x" ->
       ArithmeticExpr
         (arithmetic_op_mfts#fs (t 1),
          self#get_bterm (a 0),
          self#get_bterm (a 1))
    | s -> raise_tag_error name s bterm_mcts#tags

  method index_gterm (t: gterm_t) =
    let tags = [gterm_mcts#ts t] in
    let tloc loc = [loc#f#to_hex_string; loc#ci] in
    let key = match t with
      | GConstant n -> (tags @ [n#toString], [])
      | GReturnValue loc -> (tags @ (tloc loc), [])
      | GSideeffectValue (loc, s) -> (tags @ (tloc loc), [bd#index_string s])
      | GArgValue (dw, aindex, offsets) ->
         (tags @ [dw#to_hex_string], aindex::offsets)
      | GUnknownValue -> (tags, [])
      | GArithmeticExpr (op, g1, g2) ->
         (tags @ [g_arithmetic_op_mfts#ts op],
          [self#index_gterm g1; self#index_gterm g2]) in
    gterm_table#add key

  method get_gterm (index: int): gterm_t =
    let name = "gterm" in
    let (tags, args) = gterm_table#retrieve index in
    let getdw (s: string) = TR.tget_ok (string_to_doubleword s) in
    let makeloc (faddr: string) (ci: string) =
      let dw = TR.tget_ok (string_to_doubleword faddr) in
      ctxt_string_to_location dw ci in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "c" -> GConstant (mkNumericalFromString (t 1))
    | "r" -> GReturnValue (makeloc (t 1) (t 2))
    | "s" -> GSideeffectValue (makeloc (t 1) (t 2), bd#get_string (a 0))
    | "a" -> GArgValue (getdw (t 1), (a 0), List.tl args)
    | "u" -> GUnknownValue
    | "x" ->
       GArithmeticExpr
         (g_arithmetic_op_mfts#fs (t 1),
          self#get_gterm (a 0),
          self#get_gterm (a 1))
    | s -> raise_tag_error name s gterm_mcts#tags

  method index_fts_parameter_value (r: (fts_parameter_t * bterm_t)) =
    let (p, t) = r in
    fts_parameter_value_table#add
      ([], [self#index_fts_parameter p; self#index_bterm t])

  method get_fts_parameter_value (index:int) =
    let (_, args) = fts_parameter_value_table#retrieve index in
    let a = a "parmeter-value" args in
    (self#get_fts_parameter (a 0), self#get_bterm (a 1))

  method index_fts_parameter_list (l: fts_parameter_t list) =
    fts_parameter_list_table#add ([], List.map self#index_fts_parameter l)

  method get_fts_parameter_list (index:int) =
    let (_, args) = fts_parameter_list_table#retrieve index in
    List.map self#get_fts_parameter args

  method index_function_signature (fs: function_signature_t) =
    let tags = [fs.fts_calling_convention] in
    let args = [
        self#index_fts_parameter_list fs.fts_parameters;
        if fs.fts_varargs then 1 else 0;
        (match fs.fts_va_list with
         | Some l -> self#index_fts_parameter_list l
         | _ -> (-1));
        bcd#index_typ fs.fts_returntype;
        self#index_roles fs.fts_rv_roles;
        (match fs.fts_stack_adjustment with Some n -> n | _ -> (-1))
      ] @ (List.map bd#index_register fs.fts_registers_preserved) in
    function_signature_table#add (tags, args)

  method get_function_signature (index: int): function_signature_t =
    let name = "function-signature" in
    let (tags, args) = function_signature_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    { fts_parameters = self#get_fts_parameter_list (a 0);
      fts_varargs = (a 1) = 1 ;
      fts_va_list =
        if (a 2) = (-1) then
          None
        else
          Some (self#get_fts_parameter_list (a 2));
      fts_returntype = bcd#get_typ (a 3);
      fts_rv_roles = self#get_roles (a 4);
      fts_stack_adjustment = if (a 5) = (-1) then None else Some (a 5);
      fts_calling_convention = t 0;
      fts_registers_preserved =
        (List.map bd#get_register (get_list_suffix args 6))
    }

  method index_function_interface (fintf: function_interface_t) =
    let tags = [] in
    let args = [
        bd#index_string fintf.fintf_name;
        (match fintf.fintf_jni_index with Some n -> n | _ -> (-1));
        (match fintf.fintf_syscall_index with Some n -> n | _ -> (-1));
        self#index_function_signature fintf.fintf_type_signature;
        self#index_parameter_location_list fintf.fintf_parameter_locations;
        (* only the most precise type is saved, or none if incompatible*)
        (let mtype = btype_meet fintf.fintf_returntypes in
         match mtype with
         | Some ty -> bcd#index_typ ty
         | _ -> -1);
        (match fintf.fintf_bctype with Some t -> bcd#index_typ t | _ -> (-1));
      ] in
    function_interface_table#add (tags, args)

  method get_function_interface (index: int): function_interface_t =
    let name = "function-interface" in
    let (tags, args) = function_interface_table#retrieve index in
    let a = a name args in
    { fintf_name = bd#get_string (a 0);
      fintf_jni_index = if (a 1) = (-1) then None else Some (a 1);
      fintf_syscall_index = if (a 2) = (-1) then None else Some (a 2);
      fintf_type_signature = self#get_function_signature (a 3);
      fintf_parameter_locations = self#get_parameter_location_list (a 4);
      fintf_returntypes = (if (a 5) = (-1) then [] else [bcd#get_typ (a 5)]);
      fintf_bctype = if (a 6) = (-1) then None else Some (bcd#get_typ (a 6))
    }

  method index_function_semantics (fsem: function_semantics_t) =
    let tags = [] in
    let args = [
        self#index_xxpredicate_list fsem.fsem_pre;
        self#index_xxpredicate_list fsem.fsem_post;
        self#index_xxpredicate_list fsem.fsem_errorpost;
        self#index_xxpredicate_list fsem.fsem_sideeffects;
        self#index_xxpredicate_list fsem.fsem_postrequests
      ] in
    function_semantics_table#add (tags, args)

  method get_function_semantics (index: int): function_semantics_t =
    let name = "function-semantics" in
    let (tags, args) = function_semantics_table#retrieve index in
    let a = a name args in
    { fsem_pre = self#get_xxpredicate_list (a 0);
      fsem_post = self#get_xxpredicate_list (a 1);
      fsem_errorpost = self#get_xxpredicate_list (a 2);
      fsem_sideeffects = self#get_xxpredicate_list (a 3);
      fsem_postrequests = self#get_xxpredicate_list (a 4);
      fsem_io_actions = [];
      fsem_desc = "id";
      fsem_throws = []
    }

  method index_xxpredicate (p: xxpredicate_t) =
    let ib b = if b then 1 else 0 in
    let it = self#index_bterm in
    let ity = bcd#index_typ in
    let tags = [xxpredicate_mcts#ts p] in
    let key = match p with
      | XXAllocationBase t -> (tags, [it t])
      | XXBlockWrite (ty, t1, t2) -> (tags, [ity ty; it t1; it t2])
      | XXBuffer (ty, t1, t2) -> (tags, [ity ty; it t1; it t2])
      | XXEnum (t, s, b) -> (tags, [it t; bd#index_string s; ib b])
      | XXFalse -> (tags, [])
      | XXFreed t -> (tags, [it t])
      | XXFunctional -> (tags, [])
      | XXFunctionPointer (ty, t) -> (tags, [ity ty; it t])
      | XXIncludes (t, c) -> (tags, [it t; self#index_c_struct_constant c])
      | XXInitialized t -> (tags, [it t])
      | XXInitializedRange (ty, t1, t2) -> (tags, [ity ty; it t1; it t2])
      | XXInputFormatString t -> (tags, [it t])
      | XXInvalidated t -> (tags, [it t])
      | XXModified t -> (tags, [it t])
      | XXNewMemory (t1, t2) -> (tags, [it t1; it t2])
      | XXStackAddress t -> (tags, [it t])
      | XXHeapAddress t -> (tags, [it t])
      | XXGlobalAddress t -> (tags, [it t])
      | XXNoOverlap (t1, t2) -> (tags, [it t1; it t2])
      | XXNotNull t -> (tags, [it t])
      | XXNull t -> (tags, [it t])
      | XXNotZero t -> (tags, [it t])
      | XXNonNegative t -> (tags, [it t])
      | XXNullTerminated t -> (tags, [it t])
      | XXOutputFormatString t -> (tags, [it t])
      | XXPositive t -> (tags, [it t])
      | XXRelationalExpr (op, t1, t2) ->
         (tags @ [relational_op_mfts#ts op], [it t1; it t2])
      | XXSetsErrno -> (tags, [])
      | XXStartsThread (t, tl) -> (tags, List.map it (t::tl))
      | XXTainted t -> (tags, [it t])
      | XXValidMem t -> (tags, [it t])
      | XXDisjunction pl -> (tags, [self#index_xxpredicate_list pl])
      | XXConditional (p1, p2) ->
         (tags, [self#index_xxpredicate p1; self#index_xxpredicate p2])
    in
    xxpredicate_table#add key

  method index_xxpredicate_list (l: xxpredicate_t list) =
    xxpredicate_list_table#add ([], List.map self#index_xxpredicate l)

  method get_xxpredicate_list (index: int) =
    let (_, args) = xxpredicate_list_table#retrieve index in
    List.map self#get_xxpredicate args

  method get_xxpredicate (index: int): xxpredicate_t =
    let name = "xxpredicate_t" in
    let (tags, args) = xxpredicate_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let gt = self#get_bterm in
    let gty = bcd#get_typ in
    match (t 0) with
    | "ab" -> XXAllocationBase (gt (a 0))
    | "bw" -> XXBlockWrite (gty (a 0), gt (a 1), gt (a 2))
    | "b" -> XXBuffer (gty (a 0), gt (a 1), gt (a 2))
    | "e" -> XXEnum (gt (a 0), bd#get_string (a 1), (a 2) = 1)
    | "f" -> XXFalse
    | "fr" -> XXFreed (gt (a 0))
    | "fn" -> XXFunctional
    | "fp" -> XXFunctionPointer (gty (a 0), gt (a 1))
    | "inc" -> XXIncludes (gt (a 0), self#get_c_struct_constant (a 1))
    | "i" -> XXInitialized (gt (a 0))
    | "ir" -> XXInitializedRange (gty (a 0), gt (a 1), gt (a 2))
    | "ifs" -> XXInputFormatString (gt (a 0))
    | "inv" -> XXInvalidated (gt (a 0))
    | "m" -> XXModified (gt (a 0))
    | "nm" -> XXNewMemory (gt (a 0), gt (a 1))
    | "sa" -> XXStackAddress (gt (a 0))
    | "ha" -> XXHeapAddress (gt (a 0))
    | "ga" -> XXGlobalAddress (gt (a 0))
    | "no" -> XXNoOverlap (gt (a 0), gt (a 1))
    | "nn" -> XXNotNull (gt (a 0))
    | "nu" -> XXNull (gt (a 0))
    | "nz" -> XXNotZero (gt (a 0))
    | "nng" -> XXNonNegative (gt (a 0))
    | "nt" -> XXNullTerminated (gt (a 0))
    | "ofs" -> XXOutputFormatString (gt (a 0))
    | "pos" -> XXPositive (gt (a 0))
    | "x" -> XXRelationalExpr (relational_op_mfts#fs (t 1), gt (a 0), gt (a 1))
    | "errno" -> XXSetsErrno
    | "st" -> XXStartsThread (gt (a 0), List.map gt (List.tl args))
    | "t" -> XXTainted (gt (a 0))
    | "v" -> XXValidMem (gt (a 0))
    | "dis" -> XXDisjunction (self#get_xxpredicate_list (a 0))
    | "con" -> XXConditional (self#get_xxpredicate (a 0), self#get_xxpredicate (a 1))
    | s -> raise_tag_error name s xxpredicate_mcts#tags

  method index_function_stub (fstub:function_stub_t) =
    let tags = [ function_stub_mcts#ts fstub ] in
    let key = match fstub with
      | SOFunction name -> (tags, [ bd#index_string name ])
      | LinuxSyscallFunction index -> (tags, [ index ])
      | DllFunction (lib,name) ->
         (tags, [ bd#index_string lib ; bd#index_string name ])
      | JniFunction index -> (tags, [ index ])
      | PckFunction (lib,pcks,name) ->
         let args = [ bd#index_string lib ; bd#index_string name ]
                    @ (List.map bd#index_string pcks) in
         (tags,args) in
    function_stub_table#add key

  method get_function_stub (index:int) =
    let name = "function_stub" in
    let (tags,args) = function_stub_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "so" -> SOFunction (bd#get_string (a 0))
    | "sc" -> LinuxSyscallFunction (a 0)
    | "dll" -> DllFunction (bd#get_string (a 0), bd#get_string (a 1))
    | "jni" -> JniFunction (a 0)
    | "pck" ->
       let packages = List.map bd#get_string (get_list_suffix args 2) in
       PckFunction (bd#get_string (a 0), packages, bd#get_string  (a 1))
    | s -> raise_tag_error name s function_stub_mcts#tags

  method index_call_target (c:call_target_t) =
    let tags = [call_target_mcts#ts c] in
    let key = match c with
      | StubTarget s -> (tags, [self#index_function_stub s])
      | StaticStubTarget (dw,s) ->
         (tags, [bd#index_address dw; self#index_function_stub s])
      | AppTarget dw -> (tags, [bd#index_address dw])
      | InlinedAppTarget (dw,s) ->
         (tags, [bd#index_address dw; bd#index_string s])
      | WrappedTarget (dw, fintf, ctgt, pars) ->
         let args = [
             bd#index_address dw;
             self#index_function_interface fintf;
             self#index_call_target ctgt
           ] @ (List.map self#index_fts_parameter_value pars) in
         (tags,args)
      | VirtualTarget fintf -> (tags, [self#index_function_interface fintf])
      | IndirectTarget (bopt, tgts) ->
         let args = List.map self#index_call_target tgts in
         let args =
           match bopt with
           | Some b -> (self#index_bterm b) :: args
           | _ -> (-1) :: args in
         (tags, args)
      | CallbackTableTarget (dw, offset) -> (tags, [bd#index_address dw; offset])
      | UnknownTarget -> (tags, []) in
    call_target_table#add key

  method get_call_target (index:int) =
    let name = "call_target" in
    let (tags,args) = call_target_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "stub" -> StubTarget (self#get_function_stub (a 0))
    | "sstub" ->
       StaticStubTarget (bd#get_address (a 0), self#get_function_stub (a 1))
    | "app" -> AppTarget (bd#get_address (a 0))
    | "inl" -> InlinedAppTarget (bd#get_address (a 0), bd#get_string (a 1))
    | "wrap" ->
       let pars =
         List.map self#get_fts_parameter_value (get_list_suffix args 3) in
       WrappedTarget
         (bd#get_address (a 0),
          self#get_function_interface (a 1),
          self#get_call_target (a 2),
          pars)
    | "v" -> VirtualTarget (self#get_function_interface (a 0))
    | "i" ->
       let tgts = List.map self#get_call_target (get_list_suffix args 1) in
       let bterm =
         let arg0 = a 0 in
         if arg0 = -1 then None else Some (self#get_bterm arg0) in
       IndirectTarget (bterm, tgts)
    | "cb" -> CallbackTableTarget (bd#get_address (a 0), (a 1))
    | "u" -> UnknownTarget
    | s -> raise_tag_error name s call_target_mcts#tags

  method index_c_struct_constant (c:c_struct_constant_t) =
    let tags = [ c_struct_constant_mcts#ts c ] in
    let key = match c with
      | FieldValues l ->  (tags,List.map self#index_struct_field_value l)
      | FieldConstant t -> (tags,[ self#index_bterm t ])
      | FieldString s -> (tags,[ bd#index_string s ])
      | FieldCallTarget t -> (tags, [ self#index_call_target t ]) in
    c_struct_constant_table#add key

  method get_c_struct_constant (index:int) =
    let name = "c_struct_constant" in
    let (tags,args) = c_struct_constant_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "v" -> FieldValues (List.map self#get_struct_field_value args)
    | "c" -> FieldConstant (self#get_bterm (a 0))
    | "s" -> FieldString (bd#get_string (a 0))
    | "t" -> FieldCallTarget (self#get_call_target (a 0))
    | s -> raise_tag_error name s c_struct_constant_mcts#tags

  method index_struct_field_value (v:(int * c_struct_constant_t)) =
    let (offset,c) = v in
    struct_field_value_table#add
      ([],[ offset ; self#index_c_struct_constant c ])

  method get_struct_field_value (index:int) =
    let (_,args) = struct_field_value_table#retrieve index in
    let a = a "struct_field_value" args in
    (a 0, self#get_c_struct_constant (a 1))

  method write_xml_parameter_location
           ?(tag="ploc") (node:xml_element_int) (p:parameter_location_t) =
    node#setIntAttribute tag (self#index_parameter_location p)

  method read_xml_parameter_location
           ?(tag="ploc") (node:xml_element_int):parameter_location_t =
    self#get_parameter_location (node#getIntAttribute tag)

  method write_xml_parameter_location_list
           ?(tag="plocs") (node: xml_element_int) (l: parameter_location_t list) =
    node#setIntAttribute tag (self#index_parameter_location_list l)

  method read_xml_parameter_location_list
           ?(tag="plocs") (node: xml_element_int): parameter_location_t list =
    self#get_parameter_location_list (node#getIntAttribute tag)

  method write_xml_fts_parameter
           ?(tag="ftsp") (node:xml_element_int) (p: fts_parameter_t) =
    node#setIntAttribute tag (self#index_fts_parameter p)

  method read_xml_fts_parameter
           ?(tag="ftsp") (node:xml_element_int): fts_parameter_t =
    self#get_fts_parameter (node#getIntAttribute tag)

  method write_xml_function_signature
           ?(tag="fsig") (node: xml_element_int) (fsig: function_signature_t) =
    node#setIntAttribute tag (self#index_function_signature fsig)

  method read_xml_function_signature
           ?(tag="fsig") (node: xml_element_int): function_signature_t =
    self#get_function_signature (node#getIntAttribute tag)

  method write_xml_function_semantics
           ?(tag="fsem") (node: xml_element_int) (fsem: function_semantics_t) =
    node#setIntAttribute tag (self#index_function_semantics fsem)

  method read_xml_function_semantics
           ?(tag="fsem") (node: xml_element_int): function_semantics_t =
    self#get_function_semantics (node#getIntAttribute tag)

  method write_xml_function_interface
           ?(tag="fintf") (node:xml_element_int) (fintf: function_interface_t) =
    node#setIntAttribute tag (self#index_function_interface fintf)

  method read_xml_function_interface
           ?(tag="fintf") (node:xml_element_int):function_interface_t =
    self#get_function_interface (node#getIntAttribute tag)

  method write_xml_xxpredicate
           ?(tag="xxpre") (node: xml_element_int) (p: xxpredicate_t) =
    node#setIntAttribute tag (self#index_xxpredicate p)

  method write_xml_xxpredicate_list
           ?(tag="xxprelst") (node: xml_element_int) (pl: xxpredicate_t list) =
    node#setIntAttribute tag (self#index_xxpredicate_list pl)

  method read_xml_xxpredicate
           ?(tag="xxpre") (node: xml_element_int): xxpredicate_t =
    self#get_xxpredicate (node#getIntAttribute tag)

  method write_xml_bterm ?(tag="ibt") (node:xml_element_int) (t:bterm_t) =
    node#setIntAttribute tag (self#index_bterm t)

  method read_xml_bterm ?(tag="ibt") (node:xml_element_int):bterm_t =
    self#get_bterm (node#getIntAttribute tag)

  method write_xml_gterm ?(tag="igt") (node: xml_element_int) (t: gterm_t) =
    node#setIntAttribute tag (self#index_gterm t)

  method read_xml_gterm ?(tag="igt") (node: xml_element_int): gterm_t =
    self#get_gterm (node#getIntAttribute tag)

  method write_xml_function_stub
           ?(tag="ifst") (node:xml_element_int) (s:function_stub_t) =
    node#setIntAttribute tag (self#index_function_stub s)

  method read_xml_function_stub
           ?(tag="ifst") (node:xml_element_int):function_stub_t =
    self#get_function_stub (node#getIntAttribute tag)

  method write_xml_call_target
           ?(tag="ictgt") (node:xml_element_int) (c:call_target_t) =
    node#setIntAttribute tag (self#index_call_target c)

  method read_xml_call_target
           ?(tag="ictgt") (node:xml_element_int):call_target_t =
    self#get_call_target (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    begin
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin t#write_xml tnode ; tnode end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end


let interface_dictionary = new interface_dictionary_t
