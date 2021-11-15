(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
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
open BCHLibTypes
open BCHSumTypeSerializer
open BCHUtilities

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


let mk_constantstring (s:string):constantstring =
  if has_control_characters s then
    (hex_string s, true, String.length s)
  else
    (s,false, String.length s)


class bdictionary_t:bdictionary_int =
object (self)

  val string_table = mk_string_index_table "string-table"
  val address_table = mk_index_table "address-table"
  val arm_extension_register_table = mk_index_table "arm-extension-register-table"
  val arm_extension_register_element_table =
    mk_index_table "arm-extension-register-element-table"
  val arm_extension_register_replicated_element_table =
    mk_index_table "arm-extension-register-replicated-element-table"
  val register_table = mk_index_table "register-table"
  val attributes_table = mk_index_table "attributes-table"
  val tname_table = mk_index_table "tname-table"
  val tname_list_table = mk_index_table "tname-list-table"
  val bfunarg_table = mk_index_table "bfunarg-table"
  val bfunargs_table = mk_index_table "bfunargs-table"
  val btype_table = mk_index_table "btype-table"
  val compinfo_table = mk_index_table "compinfo-table"
  val fieldinfo_table = mk_index_table "fieldinfo_table"
  val enuminfo_table = mk_index_table "enuminfo_table"
  val enumitem_table = mk_index_table "enumitem_table"
  val constant_table = mk_index_table "constant-table"
  val exp_table = mk_index_table "exp-table"

  val mutable tables = []
  val mutable stringtables = []

  initializer
    begin
      tables <- [
        address_table;
        attributes_table;
        arm_extension_register_table;
        arm_extension_register_element_table;
        arm_extension_register_replicated_element_table;
        register_table;
        tname_table;
        tname_list_table;
        bfunarg_table;
        bfunargs_table;
        btype_table;
        compinfo_table;
        fieldinfo_table;
        enuminfo_table;
        enumitem_table;
        constant_table;
        exp_table 
      ];
      stringtables <- [
          string_table
        ]
    end
  
  method reset =
    begin
      List.iter (fun t -> t#reset) stringtables ;
      List.iter (fun t -> t#reset) tables
    end

  method index_string (s:string):int = string_table#add s

  method get_string (index:int) = string_table#retrieve index

  method index_address (dw:doubleword_int) =
    address_table#add ([dw#to_hex_string],[])

  method index_address_string (s:string) =
    address_table#add ([s],[])

  method get_address (index:int) =
    let (tags,_) = address_table#retrieve index in
    let t  = t "address" tags in
    string_to_doubleword (t 0)

  method get_address_string (index:int) =
    let (tags,_) = address_table#retrieve index in
    let t = t "address" tags in
    (t 0)

  method index_arm_extension_register (r: arm_extension_register_t) =
    arm_extension_register_table#add
      ([arm_extension_reg_type_mfts#ts r.armxr_type], [r.armxr_index])

  method get_arm_extension_register (index: int) =
    let name = "arm_extension_register" in
    let (tags, args) = arm_extension_register_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    {armxr_type = arm_extension_reg_type_mfts#fs (t 1); armxr_index = a 0}

  method index_arm_extension_register_element
           (e: arm_extension_register_element_t) =
    arm_extension_register_element_table#add
      ([],
       [self#index_arm_extension_register e.armxr;
        e.armxr_elem_index;
        e.armxr_elem_size])

  method get_arm_extension_register_element (index: int) =
    let name = "arm_extension_register_element" in
    let (_, args) = arm_extension_register_element_table#retrieve index in
    let a = a name args in
    {armxr = self#get_arm_extension_register (a 0);
     armxr_elem_index = (a 1);
     armxr_elem_size = (a 2)}

  method index_arm_extension_register_replicated_element
           (e: arm_extension_register_replicated_element_t) =
    arm_extension_register_replicated_element_table#add
      ([],
       [self#index_arm_extension_register e.armxrr;
        e.armxrr_elem_size;
        e.armxrr_elem_count])

  method get_arm_extension_register_replicated_element (index: int) =
    let name = "arm_extension_register_replicated_element" in
    let (_, args) =
      arm_extension_register_replicated_element_table#retrieve index in
    let a = a name args in
    {armxrr = self#get_arm_extension_register (a 0);
     armxrr_elem_size = (a 1);
     armxrr_elem_count = (a 2)}

  method index_register (r:register_t) =
    let tags = [ register_mcts#ts r ] in
    let key = match r with
      | SegmentRegister s -> (tags @ [ segment_mfts#ts s ],[])
      | CPURegister r -> (tags @ [ cpureg_mfts#ts r ],[])
      | DoubleRegister (r1,r2) ->
         (tags @ [ cpureg_mfts#ts r1 ; cpureg_mfts#ts r2 ],[])
      | FloatingPointRegister i 
        | ControlRegister i
        | DebugRegister i
        | MmxRegister i
        | XmmRegister i -> (tags,[i])
      | MIPSRegister r ->  (tags @ [ mips_reg_mfts#ts r ],[])
      | MIPSSpecialRegister r -> (tags @ [mips_special_reg_mfts#ts r], [])
      | MIPSFloatingPointRegister i -> (tags, [i])
      | ARMRegister r -> (tags @ [arm_reg_mfts#ts r], [])
      | ARMSpecialRegister r -> (tags @ [arm_special_reg_mfts#ts r], [])
      | ARMExtensionRegister xr ->
         (tags, [self#index_arm_extension_register xr])
      | ARMExtensionRegisterElement xre ->
         (tags, [self#index_arm_extension_register_element xre])
      | ARMExtensionRegisterReplicatedElement xrre ->
         (tags, [self#index_arm_extension_register_replicated_element xrre]) in
    register_table#add key

  method get_register (index:int) =
    let name = register_mcts#name in
    let (tags,args) = register_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "s" -> SegmentRegister (segment_mfts#fs (t 1))
    | "c" -> CPURegister (cpureg_mfts#fs (t 1))
    | "d" -> DoubleRegister (cpureg_mfts#fs (t 1),cpureg_mfts#fs (t 2))
    | "f" -> FloatingPointRegister (a 0)
    | "ctr" -> ControlRegister (a 0)
    | "dbg" -> DebugRegister (a 0)
    | "m" -> MmxRegister (a 0)
    | "x" -> XmmRegister (a 0)
    | "p" -> MIPSRegister (mips_reg_mfts#fs (t 1))
    | "ps" -> MIPSSpecialRegister (mips_special_reg_mfts#fs (t 1))
    | "pfp" -> MIPSFloatingPointRegister (a 0)
    | "a" -> ARMRegister (arm_reg_mfts#fs (t 1))
    | "as" -> ARMSpecialRegister (arm_special_reg_mfts#fs (t 1))
    | "armx" -> ARMExtensionRegister (self#get_arm_extension_register (a 0))
    | "armxe" ->
       ARMExtensionRegisterElement (self#get_arm_extension_register_element (a 0))
    | "armxr" ->
       ARMExtensionRegisterReplicatedElement
         (self#get_arm_extension_register_replicated_element (a 0))
    | s -> raise_tag_error name s register_mcts#tags

  method index_attributes (attrs:attributes) =
    let key =
      ([],List.map (fun a -> match a with Attr s -> self#index_string s) attrs) in
    attributes_table#add key

  method get_attributes (index:int) =
    let (_,args) = attributes_table#retrieve index in
    List.map (fun i -> Attr (self#get_string i)) args

  method index_tname (n:tname_t) =
    let tags = [ tname_mcts#ts n ] in
    let key = match n with
      | SimpleName s -> (tags, [ self#index_string s ])
      | TemplatedName (tn,btypes) ->
         let args = (self#index_tname tn) :: (List.map self#index_btype btypes) in
         (tags,args) in
    tname_table#add key

  method get_tname (index:int) =
    let name = tname_mcts#name in
    let (tags,args) = tname_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "s" -> SimpleName (self#get_string (a 0))
    | "t" ->
       TemplatedName (self#get_tname (a 0),
                      List.map self#get_btype (get_list_suffix args 1))
    | s -> raise_tag_error name s tname_mcts#tags

  method index_tname_list (l:tname_t list) =
    tname_list_table#add ([], List.map self#index_tname l)

  method get_tname_list (index:int) =
    let (_,args) = tname_list_table#retrieve index in
    List.map self#get_tname  args

  method index_bfunarg (a:bfunarg_t) =
    let (name,ty) = a in
    bfunarg_table#add ([], [ self#index_string name ; self#index_btype ty ])

  method get_bfunarg (index:int) =
    let (_,args) = bfunarg_table#retrieve index in
    let a = a "bfunarg" args in
    (self#get_string (a 0), self#get_btype (a 1))

  method index_bfunargs (r:bfunarg_t list) =
    let r =
      List.mapi (fun i (name,typ) ->
          let name = if name = "" then "$par$" ^ (string_of_int (i+1)) else name in
          (name,typ)) r in
    bfunargs_table#add ([], List.map self#index_bfunarg r)

  method get_bfunargs (index:int):bfunarg_t list =
    let (_,args) = bfunargs_table#retrieve index in
    List.map self#get_bfunarg args

  method private index_opt_bfunargs (f:bfunarg_t list option) =
    match f with None -> (-1) | Some r -> self#index_bfunargs r

  method private get_opt_bfunargs (index:int):bfunarg_t list option =
    if index = (-1) then None else Some (self#get_bfunargs index)

  method index_btype (t:btype_t) =
    let tags = [btype_mcts#ts t] in
    let ia = self#index_attributes in
    let key = match t with
      | TVoid attrs -> (tags, [ia attrs])
      | TInt (ik, attrs) -> (tags @ [ikind_mfts#ts ik ], [ ia attrs])
      | TFloat (fk, frep, attrs) ->
         let tags = tags @ [fkind_mfts#ts fk; frepresentation_mfts#ts frep] in
         (tags,[ ia attrs ])
      | TPtr (tt,attrs) -> (tags, [self#index_btype tt; ia attrs])
      | TRef (tt,attrs) -> (tags, [self#index_btype tt; ia attrs])
      | THandle (s,attrs) -> (tags, [self#index_string s; ia attrs])
      | TArray (tt, optx, attrs) ->
         (tags, [self#index_btype tt; self#index_opt_exp optx; ia attrs])
      | TFun (tt, optargs, varargs, attrs) ->
         (tags,
          [self#index_btype tt;
           self#index_opt_bfunargs optargs;
           (if varargs then 1 else 0);
           ia attrs])
      | TNamed (s, attrs) -> (tags, [self#index_string s; ia attrs])
      | TComp (tn, tnlist, attrs)
        | TEnum (tn, tnlist, attrs)
        | TClass (tn, tnlist, attrs) ->
         (tags, [self#index_tname tn; self#index_tname_list tnlist; ia attrs])
      | TVarArg attrs -> (tags, [ia attrs])
      | TUnknown attrs -> (tags, [ia attrs]) in
    btype_table#add key

  method  get_btype (index:int) =
    let name = btype_mcts#name in
    let (tags, args) = btype_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    let ia = self#get_attributes in
    match (t 0) with
    | "void" -> TVoid (ia (a 0))
    | "int" -> TInt (ikind_mfts#fs (t 1), ia (a 0))
    | "float" ->
       TFloat (fkind_mfts#fs (t 1), frepresentation_mfts#fs (t 2), ia (a 0))
    | "ptr" -> TPtr (self#get_btype (a 0), ia (a 1))
    | "ref" -> TRef (self#get_btype (a 0), ia (a 1))
    | "handle" -> THandle (self#get_string (a 0), ia (a 1))
    | "array" ->
       TArray (self#get_btype (a 0), self#get_opt_exp  (a 1), ia (a 2))
    | "fun" ->
       TFun (self#get_btype  (a 0),
             self#get_opt_bfunargs (a 1), (a 2) = 1, ia (a 3))
    | "named" -> TNamed (self#get_string (a 0), ia (a 1))
    | "comp" ->
       TComp (self#get_tname (a 0), self#get_tname_list (a 1), ia (a 2))
    | "enum" ->
       TEnum (self#get_tname (a 0), self#get_tname_list (a 1), ia (a 2))
    | "class" ->
       TClass (self#get_tname (a 0), self#get_tname_list (a 1), ia (a 2))
    | "vararg" -> TVarArg (ia (a 0))
    | "u" -> TUnknown (ia (a 0))
    | s -> raise_tag_error name s btype_mcts#tags

  method index_compinfo (c:bcompinfo_t) =
    let args =
      (if c.bcstruct then 1 else 0)
      :: (List.map self#index_fieldinfo c.bcfields) in
    compinfo_table#add ([c.bcname ], args)

  method get_compinfo (index:int) =
    let (tags, args) = compinfo_table#retrieve index in
    let name = "compinfo" in
    let t = t name tags in
    let a = a name args in
    { bcstruct = (a 0) = 1;
      bcname = t 0;
      bcfields = List.map self#get_fieldinfo (List.tl args)
    }

  method index_fieldinfo (f:bfieldinfo_t) =
    let tags = [f.bfname] in
    let args = [self#index_btype f.bftype; f.bfoffset; f.bfsize] in
    let (tags,args) =
      match f.bfenum with
      | Some (name, flags) ->
         (tags @ [name], args @ [if flags then 1 else 0])
      | _ -> (tags,args) in
    fieldinfo_table#add (tags, args)

  method get_fieldinfo (index:int) =
    let (tags, args) = fieldinfo_table#retrieve index in
    let name = "fieldinfo" in
    let t = t name tags in
    let a = a name args in
    { bfname = t 0;
      bftype = self#get_btype (a 0);
      bfenum = if (List.length tags) = 2 then Some (t 1, (a 3) = 1) else None;
      bfoffset = a 1;
      bfsize = a 2
    }

  method index_enuminfo (e:benuminfo_t) =
    let tags = [e.bename; ikind_mfts#ts e.bekind] in
    let args = List.map self#index_enumitem e.beitems in
    enuminfo_table#add (tags, args)
         
  method get_enuminfo (index:int) =
    let (tags, args) = enuminfo_table#retrieve index in
    let name = "enuminfo" in
    let t = t name tags in
    { bename = t 0;
      beitems = List.map self#get_enumitem args;
      bekind = ikind_mfts#fs (t 1)
    }

  method index_enumitem (i:beitem_t) =
    enumitem_table#add ([fst i], [self#index_exp (snd i)])

  method get_enumitem (index:int) =
    let (tags, args) = enumitem_table#retrieve index in
    let name = "enumitem" in
    let t = t name tags in
    let a = a name args in
    (t 0, self#get_exp (a 0))

  method private index_opt_exp (x:exp option) =
    match x with Some e -> self#index_exp e | _ -> (-1)

  method private get_opt_exp (index:int) =
    if index = -1 then None else Some (self#get_exp index)

  method index_constant (c:constant):int =
    let tags = [ constant_mcts#ts c ] in
    let key = match c with
      | CInt64 (i64,ik, opts) ->
         (tags @ [Int64.to_string i64; ikind_mfts#ts ik], [])
      | CStr s -> (tags, [ self#index_string s ])
      | CWStr i64r -> (tags @ (List.map Int64.to_string i64r), [])
      | CChr c -> (tags, [ Char.code c ])
      | CReal (f,fk,opts) ->
         (tags @ [ string_of_float f; fkind_mfts#ts fk ;
           match opts with Some s -> s | _ -> "" ], [])
      | CEnum (exp,ename,iname) ->
         (tags @ [ename; iname], [ self#index_exp exp ]) in
    constant_table#add key

  method get_constant (index:int):constant =
    let name = constant_mcts#name in
    let (tags,args) = constant_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "int"| "c64" ->
       CInt64 (Int64.of_string (t 1), ikind_mfts#fs (t 2),None)
    | "str" | "s" -> CStr (self#get_string (a 0))
    | "wstr" | "ws" -> CWStr (List.map Int64.of_string (List.tl tags))
    | "chr" | "c" -> CChr (Char.chr (a 0))
    | "real" | "r" ->
       let t3 = if (List.length tags) > 3 then (t 3) else "" in
       CReal (float_of_string (t 1), fkind_mfts#fs (t 2),
              let s = t3 in if s = "" then None else Some s)
    | "enum" | "e" -> CEnum (self#get_exp (a 0), t 1, t 2)
    | s -> raise_tag_error name s constant_mcts#tags

  method index_exp (x:exp) =
    let tags = [ "const" ] in
    let key = match x with
      | Const c -> (tags,[ self#index_constant c ]) in
    exp_table#add key

  method get_exp (index:int) =
    let name = "exp" in
    let (tags,args) = exp_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "const" -> Const (self#get_constant (a 0))
    | s -> raise_tag_error name s [ "const" ]

  method write_xml_register ?(tag="ireg") (node:xml_element_int) (r:register_t) =
    node#setIntAttribute tag (self#index_register r)

  method read_xml_register ?(tag="ireg") (node:xml_element_int):register_t =
    self#get_register (node#getIntAttribute tag)

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_string s)

  method read_xml_string ?(tag="istr") (node:xml_element_int):string =
    self#get_string (node#getIntAttribute tag)

  method write_xml_btype ?(tag="ity") (node:xml_element_int) (t:btype_t) =
    node#setIntAttribute tag (self#index_btype t)

  method read_xml_btype ?(tag="ity") (node:xml_element_int):btype_t =
    self#get_btype (node#getIntAttribute tag)

  method write_xml_compinfo ?(tag="ici") (node:xml_element_int) (c:bcompinfo_t) =
    node#setIntAttribute tag (self#index_compinfo c)
    
  method read_xml_compinfo ?(tag="ici") (node:xml_element_int):bcompinfo_t =
    self#get_compinfo (node#getIntAttribute tag)

  method write_xml_enuminfo ?(tag="iei") (node:xml_element_int) (e:benuminfo_t) =
    node#setIntAttribute tag (self#index_enuminfo e)

  method read_xml_enuminfo ?(tag="iei") (node:xml_element_int):benuminfo_t =
    self#get_enuminfo (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    begin
      node#appendChildren
        (List.map
           (fun t -> let tnode = xmlElement t#get_name in
                     begin t#write_xml tnode ; tnode end) stringtables) ;
      node#appendChildren
        (List.map
           (fun t -> let tnode = xmlElement t#get_name in
                     begin t#write_xml tnode ; tnode end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      List.iter (fun t -> t#read_xml (getc t#get_name)) stringtables ;
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end

                                
let bdictionary = new bdictionary_t
