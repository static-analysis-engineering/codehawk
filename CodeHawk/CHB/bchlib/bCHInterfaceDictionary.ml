(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHIndexTable
open CHPrettyUtil
open CHStringIndexTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHDictionary
open BCHLibTypes
open BCHSumTypeSerializer
open BCHUtilities

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

  val parameter_location_table = mk_index_table "parameter-location-table"
  val role_table = mk_index_table "role-table"
  val roles_table = mk_index_table "roles-table"
  val fts_parameter_table = mk_index_table "fts-parameter-table"
  val fts_parameter_list_table = mk_index_table "fts-parameter-list-table"
  val bterm_table = mk_index_table "bterm-table"
  val fts_parameter_value_table = mk_index_table "parameter-value-table"
  val function_signature_table = mk_index_table "function-signature-table"
  val function_interface_table = mk_index_table "function-interface-table"
  val function_stub_table = mk_index_table "function-stub-table"
  val call_target_table = mk_index_table "call-target-table"
  val jump_target_table = mk_index_table "jump_target_table"
  val c_struct_constant_table = mk_index_table "c-struct-constant-table"
  val struct_field_value_table = mk_index_table "struct-field-value-table"

  val mutable tables = []

  initializer
    tables <- [
      parameter_location_table;
      role_table;
      roles_table;
      fts_parameter_table;
      fts_parameter_list_table;
      bterm_table;
      fts_parameter_value_table;
      function_signature_table;
      function_interface_table;
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

  method index_parameter_location (p:parameter_location_t) =
    let tags = [ parameter_location_mcts#ts p ] in
    let key = match p with
      | StackParameter i -> (tags, [ i ])
      | RegisterParameter r -> (tags, [ bd#index_register r])
      | GlobalParameter a -> (tags, [ bd#index_address a ])
      | UnknownParameterLocation -> (tags,[]) in
    parameter_location_table#add key

  method get_parameter_location (index:int):parameter_location_t =
    let name = "parameter_location" in
    let (tags,args) = parameter_location_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "s" -> StackParameter (a 0)
    | "r" -> RegisterParameter (bd#get_register (a 0))
    | "g" -> GlobalParameter (bd#get_address (a 0))
    | "u" -> UnknownParameterLocation
    | s -> raise_tag_error name s parameter_location_mcts#tags

  method index_role (r:(string * string)) =
    let key = ([],[ bd#index_string (fst r) ; bd#index_string (snd r) ]) in
    role_table#add key

  method get_role (index:int) =
    let (_,args) = role_table#retrieve index in
    let a = a "role" args in
    (bd#get_string (a 0), bd#get_string (a 1))

  method index_roles (l:(string * string) list) =
    roles_table#add ([],List.map self#index_role l)

  method get_roles (index:int) =
    let (_,args) = roles_table#retrieve index in
    List.map self#get_role args

  method index_fts_parameter (p:fts_parameter_t) =
    let tags = [
        arg_io_mfts#ts p.apar_io;
        formatstring_type_mfts#ts p.apar_fmt] in
    let args = [
        bd#index_string p.apar_name;
        bd#index_btype p.apar_type;
        bd#index_string p.apar_desc;
        self#index_roles p.apar_roles;
        p.apar_size;
        self#index_parameter_location p.apar_location ] in
    fts_parameter_table#add (tags,args)

  method get_fts_parameter (index:int): fts_parameter_t =
    let (tags, args) = fts_parameter_table#retrieve index in
    let t = t "fts-parameter" tags in
    let a = a "fts-parameter" args in
    { apar_name = bd#get_string (a 0);
      apar_type = bd#get_btype (a 1);
      apar_desc = bd#get_string (a 2);
      apar_roles = self#get_roles (a 3);
      apar_io = arg_io_mfts#fs (t 0);
      apar_fmt = formatstring_type_mfts#fs (t 1);
      apar_size = a 4;
      apar_location = self#get_parameter_location (a 5) }

  method index_bterm (t:bterm_t) =
    let tags = [ bterm_mcts#ts t ] in
    let key = match t with
      | ArgValue p -> (tags,[ self#index_fts_parameter p ])
      | RunTimeValue
        | ReturnValue -> (tags,[])
      | NamedConstant s -> (tags,[bd#index_string s])
      | NumConstant n -> (tags @ [n#toString], [])
      | ArgBufferSize t 
        | IndexSize t
        | ByteSize t -> (tags, [self#index_bterm t])
      | ArgAddressedValue (t1,t2) ->
         (tags, [self#index_bterm t1; self#index_bterm t2])
      | ArgNullTerminatorPos t -> (tags, [self#index_bterm t])
      | ArgSizeOf t -> (tags, [bd#index_btype t])
      | ArithmeticExpr (op,t1,t2) ->
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
    | "r" -> ReturnValue
    | "n" -> NamedConstant (bd#get_string (a 0))
    | "c" -> NumConstant (mkNumericalFromString (t 1))
    | "s" -> ArgBufferSize (self#get_bterm (a 0))
    | "i" -> IndexSize (self#get_bterm (a 0))
    | "b" -> ByteSize (self#get_bterm (a 0))
    | "aa" ->
       ArgAddressedValue (self#get_bterm (a 0), self#get_bterm (a 1))
    | "as" -> ArgSizeOf (bd#get_btype (a 0))
    | "x" ->
       ArithmeticExpr
         (arithmetic_op_mfts#fs (t 1),
          self#get_bterm (a 0),
          self#get_bterm (a 1))
    | s -> raise_tag_error name s bterm_mcts#tags

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
        if fs.fts_varargs  then 1 else 0;
        (match fs.fts_va_list with
         | Some l -> self#index_fts_parameter_list l
         | _ -> (-1));
        bd#index_btype fs.fts_returntype;
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
      fts_returntype = bd#get_btype (a 3);
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
        self#index_function_signature fintf.fintf_type_signature
      ] in
    function_interface_table#add (tags, args)

  method get_function_interface (index: int): function_interface_t =
    let name = "function-interface" in
    let (tags, args) = function_interface_table#retrieve index in
    let a = a name args in
    { fintf_name = bd#get_string (a 0);
      fintf_jni_index = if (a 1) = (-1) then None else Some (a 1);
      fintf_syscall_index = if (a 2) = (-1) then None else Some (a 2);
      fintf_type_signature = self#get_function_signature (a 3)
    }

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
    let tags = [ call_target_mcts#ts c ] in
    let key = match c with
      | StubTarget s -> (tags, [ self#index_function_stub s ])
      | StaticStubTarget (dw,s) ->
         (tags, [ bd#index_address dw ; self#index_function_stub s ])
      | AppTarget dw -> (tags, [ bd#index_address dw ])
      | InlinedAppTarget (dw,s) ->
         (tags, [ bd#index_address dw ; bd#index_string s ])
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

  method write_xml_function_interface
           ?(tag="fintf") (node:xml_element_int) (fintf: function_interface_t) =
    node#setIntAttribute tag (self#index_function_interface fintf)

  method read_xml_function_interface
           ?(tag="fintf") (node:xml_element_int):function_interface_t =
    self#get_function_interface (node#getIntAttribute tag)

  method write_xml_bterm ?(tag="ibt") (node:xml_element_int) (t:bterm_t) =
    node#setIntAttribute tag (self#index_bterm t)

  method read_xml_bterm ?(tag="ibt") (node:xml_element_int):bterm_t =
    self#get_bterm (node#getIntAttribute tag)

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
           (fun t -> let tnode = xmlElement t#get_name in
                     begin t#write_xml tnode ; tnode end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

  

end

let interface_dictionary = new interface_dictionary_t
