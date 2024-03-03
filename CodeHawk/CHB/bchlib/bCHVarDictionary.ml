(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHIndexTable
open CHLogger
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHLocation
open BCHSumTypeSerializer


let bcd = BCHBCDictionary.bcdictionary
let bd = BCHDictionary.bdictionary
let id = BCHInterfaceDictionary.interface_dictionary


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


class vardictionary_t
        (faddr: doubleword_int)
        (xd: xprdictionary_int):vardictionary_int =
object (self)

  val faddr = faddr
  val xd = xd
  val memory_base_table = mk_index_table "memory-base-table"
  val memory_offset_table = mk_index_table "memory-offset-table"
  val assembly_variable_denotation_table =
    mk_index_table "assembly-variable-denotation-table"
  val constant_value_variable_table =
    mk_index_table "constant-value-variable-table"
  val memory_access_table = mk_index_table "memory-access-table"
  val stack_access_table = mk_index_table "stack-access-table"

  val mutable tables = []

  initializer
    tables <- [
      memory_base_table;
      memory_offset_table;
      assembly_variable_denotation_table;
      constant_value_variable_table;
      stack_access_table
    ]

  method reset =
    begin
      List.iter (fun t -> t#reset) tables
    end

  method faddr = faddr

  method xd = xd

  method get_indexed_variables =
    List.map (fun (_,index) -> (index,self#get_assembly_variable_denotation index))
             assembly_variable_denotation_table#items

  method get_indexed_bases =
    List.map (fun (_,index) -> (index,self#get_memory_base index))
             memory_base_table#items

  method index_memory_base (b: memory_base_t) =
    let tags = [ memory_base_mcts#ts b ] in
    let key = match b with
      | BLocalStackFrame
        | BRealignedStackFrame
        | BAllocatedStackFrame
        | BGlobal -> (tags, [])
      | BaseVar v -> (tags, [xd#index_variable v])
      | BaseUnknown s -> (tags, [bd#index_string s]) in
    memory_base_table#add key

  method get_memory_base (index: int)  =
    let name = memory_base_mcts#name in
    let (tags,args) = memory_base_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "l" -> BLocalStackFrame
    | "r" -> BRealignedStackFrame
    | "a" -> BAllocatedStackFrame
    | "g" -> BGlobal
    | "v" -> BaseVar (xd#get_variable (a 0))
    | "u" -> BaseUnknown (bd#get_string (a 0))
    | s -> raise_tag_error name s memory_base_mcts#tags

  method index_memory_offset (o: memory_offset_t) =
    let tags = [ memory_offset_mcts#ts o ] in
    let key = match o with
      | NoOffset -> (tags,[])
      | ConstantOffset (n,m) ->
         (tags @ [n#toString],[self#index_memory_offset m])
      | FieldOffset ((fname, fkey), m) ->
         (tags @ [fname], [fkey; self#index_memory_offset m])
      | IndexOffset (v,i,m) ->
         (tags, [xd#index_variable v; i; self#index_memory_offset m])
      | UnknownOffset -> (tags,[]) in
    memory_offset_table#add key

  method get_memory_offset (index:int) =
    let name = memory_offset_mcts#name in
    let (tags,args) = memory_offset_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "n" -> NoOffset
    | "c" ->
       ConstantOffset (mkNumericalFromString (t 1), self#get_memory_offset (a 0))
    | "f" -> FieldOffset ((t 1, a 0), self#get_memory_offset (a 1))
    | "i" ->
       IndexOffset (xd#get_variable (a 0), a 1, self#get_memory_offset (a 2))
    | "u" -> UnknownOffset
    | s -> raise_tag_error name s memory_offset_mcts#tags

  method index_assembly_variable_denotation (v:assembly_variable_denotation_t) =
    let tags = [ assembly_variable_denotation_mcts#ts v ] in
    let key = match v with
      | MemoryVariable (i, s, o) -> (tags, [i; s; self#index_memory_offset o])
      | RegisterVariable r -> (tags, [bd#index_register r])
      | CPUFlagVariable f -> (tags,[bd#index_flag f])
      | AuxiliaryVariable a -> (tags, [self#index_constant_value_variable a]) in
    assembly_variable_denotation_table#add key

  method get_assembly_variable_denotation (index:int) =
    let name =  "assembly_variable_denotation" in
    let (tags,args) = assembly_variable_denotation_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "m" -> MemoryVariable (a 0, a 1, self#get_memory_offset (a 2))
    | "r" -> RegisterVariable (bd#get_register (a 0))
    | "f" -> CPUFlagVariable (bd#get_flag (a 0))
    | "a" -> AuxiliaryVariable (self#get_constant_value_variable (a 0))
    | s -> raise_tag_error name s assembly_variable_denotation_mcts#tags

  method index_constant_value_variable (cvv: constant_value_variable_t) =
    let tags = [constant_value_variable_mcts#ts cvv] in
    let key = match cvv with
      | InitialRegisterValue (r, level) -> (tags, [bd#index_register r; level])
      | InitialMemoryValue v -> (tags, [xd#index_variable v])
      | FrozenTestValue (v, a1, a2) ->
         (tags @ [a1; a2], [xd#index_variable v])
      | FunctionReturnValue a -> (tags @ [a], [])
      | SyscallErrorReturnValue a -> (tags @ [a], [])
      | AugmentationValue (v, a, desc, suffix, ty) ->
         (* Note: description should not include comma's or spaces *)
         (tags @ [a; desc; suffix], [xd#index_variable v; bcd#index_typ ty])
      | SSARegisterValue (r, a, optname, ty) ->
         let rname = ssa_register_value_name r self#faddr a in
         let ntags =
           match optname with
           | Some name -> tags @ [a; rname; name]
           | _ -> tags @ [a; rname] in
         (ntags, [bd#index_register r; bcd#index_typ ty])
      | FunctionPointer (s1, s2, a) ->
         (tags @ [a], [bd#index_string s1; bd#index_string s2])
      | CallTargetValue t -> (tags, [id#index_call_target t])
      | SideEffectValue  (a, name, isglobal) ->
         (tags @  [a ], [bd#index_string name; (if isglobal then 1 else 0)])
      | MemoryAddress (i, o) -> (tags, [i; self#index_memory_offset o])
      | BridgeVariable (a,i) -> (tags @ [a], [i])
      | FieldValue (sname,offset,fname) ->
         (tags, [ bd#index_string sname ; offset ; bd#index_string fname ])
      | SymbolicValue x ->  (tags, [xd#index_xpr x])
      | SignedSymbolicValue (x, s0, sx) -> (tags, [xd#index_xpr x; s0; sx])
      | Special s -> (tags, [bd#index_string s])
      | RuntimeConstant s -> (tags, [bd#index_string s])
      | ChifTemp -> (tags,[]) in
    constant_value_variable_table#add key

  method get_constant_value_variable (index:int) =
    let name = "constant_value_variable" in
    let (tags,args) = constant_value_variable_table#retrieve index in
    let t = t name tags in
    let a = a name args in
    match (t 0) with
    | "ir" -> InitialRegisterValue (bd#get_register (a 0), a 1)
    | "iv" -> InitialMemoryValue (xd#get_variable (a 0))
    | "ft" -> FrozenTestValue (xd#get_variable (a 0), t 1, t 2)
    | "fr" -> FunctionReturnValue (t 1)
    | "ev" -> SyscallErrorReturnValue (t 1)
    | "av" ->
       AugmentationValue (xd#get_variable (a 0), t 1, t 2, t 3, bcd#get_typ (a 1))
    | "ssa" ->
       let optname =
         match tags with
         | [_; _; _; name] -> Some name
         | _ -> None in
       SSARegisterValue (bd#get_register (a 0), t 1, optname, bcd#get_typ (a 1))
    | "fp" -> FunctionPointer (bd#get_string (a 0), bd#get_string (a 1), t 1)
    | "ct" -> CallTargetValue (id#get_call_target (a 0))
    | "se" -> SideEffectValue (t 1, bd#get_string (a 0), (a 1) = 1)
    | "ma" -> MemoryAddress ((a 0), self#get_memory_offset (a 1))
    | "bv" -> BridgeVariable (t 1, a 0)
    | "fv" -> FieldValue (bd#get_string (a 0), a 1, bd#get_string  (a 2))
    | "sv" -> SymbolicValue (xd#get_xpr (a 0))
    | "ssv" -> SignedSymbolicValue (xd#get_xpr (a 0), a 1, a 2)
    | "sp" -> Special (bd#get_string (a 0))
    | "rt" -> RuntimeConstant (bd#get_string (a 0))
    | "chiftemp" -> ChifTemp
    | s -> raise_tag_error name s constant_value_variable_mcts#tags

  method index_stack_access (sa: stack_access_t) =
    let oi (v: int option) = match v with Some i -> i | _ -> -1 in
    let ox (x: xpr_t option) =
      match x with Some xx -> self#xd#index_xpr xx | _ -> -1 in
    let tags = [stack_access_mcts#ts sa] in
    let key = match sa with
      | RegisterSpill (offset, reg) -> (tags, [offset; bd#index_register reg])
      | RegisterRestore (offset, reg) -> (tags, [offset; bd#index_register reg])
      | StackLoad (var, offset, optsize, ty) ->
         (tags, [self#xd#index_variable var; offset; oi optsize; bcd#index_typ ty])
      | StackStore (var, offset, optsize, ty, optxpr) ->
         (tags,
          [self#xd#index_variable var;
           offset;
           oi optsize;
           bcd#index_typ ty;
           ox optxpr])
      | StackBlockRead (offset, optsize, ty) ->
         (tags, [offset; oi optsize; bcd#index_typ ty])
      | StackBlockWrite (offset, optsize, ty, optxpr) ->
         (tags, [offset; oi optsize; bcd#index_typ ty; ox optxpr]) in
    stack_access_table#add key

  method write_xml_memory_offset
           ?(tag="imo") (node:xml_element_int) (o:memory_offset_t) =
    node#setIntAttribute tag (self#index_memory_offset o)

  method read_xml_memory_offset
           ?(tag="imo") (node:xml_element_int):memory_offset_t =
    self#get_memory_offset (node#getIntAttribute tag)

  method write_xml_memory_base
           ?(tag="imb") (node:xml_element_int) (m:memory_base_t) =
    node#setIntAttribute tag (self#index_memory_base m)

  method read_xml_memory_base
           ?(tag="imb") (node:xml_element_int):memory_base_t =
    self#get_memory_base (node#getIntAttribute tag)

  method write_xml_assembly_variable_denotation
           ?(tag="ivd")
           (node:xml_element_int)
           (v:assembly_variable_denotation_t) =
    node#setIntAttribute tag (self#index_assembly_variable_denotation v)

  method read_xml_assembly_variable_denotation
           ?(tag="ivd")
           (node:xml_element_int):assembly_variable_denotation_t =
    self#get_assembly_variable_denotation (node#getIntAttribute tag)

  method write_xml_stack_access
           ?(tag="isa") (node: xml_element_int) (sa: stack_access_t) =
    node#setIntAttribute tag (self#index_stack_access sa)

  method write_xml (node:xml_element_int) =
    let vnode = xmlElement "var-dictionary" in
    let xnode = xmlElement "xpr-dictionary" in
    begin
      vnode#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables);
      xd#write_xml xnode;
      vnode#appendChildren [xnode];
      node#appendChildren [vnode]
    end

  method read_xml (node:xml_element_int) =
    let vnode = node#getTaggedChild "var-dictionary" in
    let getc = vnode#getTaggedChild in
    begin
      xd#read_xml (getc "xpr-dictionary");
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end


let mk_vardictionary = new vardictionary_t
