(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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
(* A variable manager and variable dictionary are created per function. *)

(* chlib *)
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHTraceResult
open CHUtil
open CHXmlDocument

(* xprlib *)
open XprDictionary
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHDoubleword
open BCHFunctionStub
open BCHLibTypes
open BCHMemoryReference
open BCHVarDictionary

module H = Hashtbl
module TR = CHTraceResult

(*
let x2p = xpr_formatter#pr_expr
let x2s x = p2s (x2p x)
 *)

let p2s = CHPrettyUtil.pretty_to_string

class assembly_variable_t
        ~(memrefmgr:memory_reference_manager_int)
        ~(vard: vardictionary_int)
        ~(index:int)
        ~(denotation:assembly_variable_denotation_t):assembly_variable_int =
object (self:'a)
  method index = index

  method compare (other:'a) = Stdlib.compare self#index other#index

  method get_denotation = denotation

  method get_name  =
    let aux den = match den with
      | MemoryVariable (i, size, offset) ->
         let basename =
           let memref_r = memrefmgr#get_memory_reference i in
           TR.tfold
             ~ok:(fun memref -> memref#get_name)
             ~error:(fun erl ->
               let _ =
                 ch_error_log#add
                   "invalid memory reference"
                   (STR (String.concat "; " erl)) in
               "invalid_memref")
             memref_r in
         (match basename with
          | "var" -> stack_offset_to_name offset
          | "varr" -> realigned_stack_offset_to_name offset
          | "gv" -> global_offset_to_name size offset
          | _ ->
             (match offset with
              | NoOffset -> "__pderef_" ^ basename ^ "_"
              | _ -> basename ^ (memory_offset_to_string offset)))
      | RegisterVariable reg -> register_to_string reg
      | CPUFlagVariable flag -> flag_to_string flag
      | AuxiliaryVariable a ->
	match a with
	| InitialRegisterValue (r,level) -> (register_to_string r) ^ "_in" ^
	  (if level = 0 then "" else "_" ^ (string_of_int level))
	| InitialMemoryValue v -> v#getName#getBaseName ^ "_in"
	| FrozenTestValue (fv,taddr,jaddr) ->
	  fv#getName#getBaseName ^ "_val_" ^ taddr ^ "_amp_" ^ jaddr
	| FunctionPointer (fname,cname,address) ->
	  "fp_" ^ fname ^ "_" ^ cname ^ "_" ^ address
	| FunctionReturnValue address -> "rtn_" ^ address
        | TypeCastValue  (iaddr, name, _, reg) ->
           "typecast_" ^ name ^ "_" ^ iaddr ^ "_" ^ (register_to_string reg)
        | SyscallErrorReturnValue address -> "errval_" ^ address
	| CallTargetValue tgt ->
	  (match tgt with
	  | StubTarget fs -> "stub_" ^ (function_stub_to_string fs)
	  | StaticStubTarget (_dw, fs) ->
             "staticstub_" ^ (function_stub_to_string fs)
	  | AppTarget a -> "tgt_" ^ a#to_hex_string
	  | _ -> "tgt_qq_")
	| SideEffectValue (address,arg,_) -> "se_" ^ address ^ "_" ^ arg
	| FieldValue (sname,offset,fname) ->
	   sname ^ "." ^ fname ^ "_amp_" ^ (string_of_int offset)
        | SymbolicValue x -> "sv__" ^ (string_of_int (vard#xd#index_xpr x)) ^ "__sv"
        | SignedSymbolicValue (x, s0, sx) ->
           "ssv__"
           ^ (string_of_int (vard#xd#index_xpr x))
           ^ "_"
           ^ (string_of_int s0)
           ^ "_"
           ^ (string_of_int sx)
           ^ "_"
	| BridgeVariable (address, n) ->
	  "arg_" ^ (string_of_int n) ^ "_for_call_at_" ^ address
	| Special s -> "special_" ^ s
  	| RuntimeConstant s -> "rtc_" ^ s
	| ChifTemp -> "temp" in
    let name = aux denotation in
    if has_control_characters name then
      let newname = "__xx__" ^ (hex_string name) in
      begin
	chlog#add
          "convert name"
          (LBLOCK [
            STR "Convert variable name ";
            STR name;
            STR " to ";
            STR newname;
            NL]);
	newname
      end
    else
      name

  method private get_memref_type (index: int) (_size: int): btype_t option =
    memrefmgr#get_memory_reference_type index

  method private get_memref_field_type (size: int) (offset: memory_offset_t):
                   btype_t option =
    match offset with
    | FieldOffset ((fname, ckey), NoOffset) ->
       let compinfo = get_compinfo_by_key ckey in
       let finfo = get_compinfo_field compinfo fname in
       Some finfo.bftype
    | FieldOffset (_, (FieldOffset _ as suboffset)) ->
       self#get_memref_field_type size suboffset
    | _ -> None

  method get_type: btype_t option =
    let aux den = match den with
      | MemoryVariable (i, size, NoOffset) ->
         self#get_memref_type i size
      | MemoryVariable (_, size, (FieldOffset _ as offset)) ->
         self#get_memref_field_type size offset
      | MemoryVariable _ -> None
      | RegisterVariable _ -> None
      | CPUFlagVariable _ -> None
      | AuxiliaryVariable a ->
         match a with
         | InitialRegisterValue _ -> None
         | InitialMemoryValue _ -> None
         | FrozenTestValue _ -> None
         | FunctionPointer _ -> None
         | FunctionReturnValue _ -> None
         | TypeCastValue (_, _, ty, _) -> Some ty
         | SyscallErrorReturnValue _ -> None
         | CallTargetValue _ -> None
         | SideEffectValue _ -> None
         | FieldValue _ -> None
         | SymbolicValue _ -> None
         | SignedSymbolicValue _ -> None
         | BridgeVariable _ -> None
         | Special _ -> None
         | RuntimeConstant _ -> None
         | ChifTemp -> None in
    aux denotation

  method to_basevar_reference: memory_reference_int option =
    match denotation with
    | AuxiliaryVariable a ->
       (match a with
        | InitialRegisterValue (CPURegister Esp, 0)
          | InitialRegisterValue (MIPSRegister MRsp, 0)
          | InitialRegisterValue (ARMRegister ARSP, 0)
          | InitialRegisterValue (PowerGPRegister 1, 0) ->
          Some memrefmgr#mk_local_stack_reference
        | InitialRegisterValue (CPURegister Esp, 1)
          | InitialRegisterValue (MIPSRegister MRsp, 1)
          | InitialRegisterValue (ARMRegister ARSP, 1)
          | InitialRegisterValue (PowerGPRegister 1, 1) ->
           Some memrefmgr#mk_realigned_stack_reference
        | _ -> None)
    | _ -> None

  method is_function_pointer =
    match denotation with
    | AuxiliaryVariable (FunctionPointer _) -> true | _ -> false

  method is_calltarget_value =
    match denotation with
    | AuxiliaryVariable (CallTargetValue _) -> true | _ -> false

  method get_calltarget_value: call_target_t traceresult =
    match denotation with
    | AuxiliaryVariable (CallTargetValue tgt) -> Ok tgt
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable " ^ self#get_name ^ " is not a calltarget value"]

  method is_global_sideeffect =
    match denotation with
    | AuxiliaryVariable (SideEffectValue (_, _, isglobal)) -> isglobal
    | _ -> false

  method get_global_sideeffect_target_address: doubleword_result =
    match denotation with
    | AuxiliaryVariable (SideEffectValue (_, arg, true)) ->
       let addr_r = string_to_doubleword arg in
       tprop addr_r (__FILE__ ^ ":" ^ (string_of_int __LINE__))
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a global sideeffect value: "
              ^ self#get_name]

  method get_pointed_to_function_name: string traceresult =
    match denotation with
    | AuxiliaryVariable (FunctionPointer (name, _, _)) -> Ok name
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a function pointer: " ^ self#get_name]

  method is_frozen_test_value =
    match denotation with
    | AuxiliaryVariable (FrozenTestValue _) -> true
    | _ -> false

  method is_in_test_jump_range (a :ctxt_iaddress_t): bool traceresult =
    match denotation with
    | AuxiliaryVariable (FrozenTestValue (_, taddr, jaddr)) ->
       Ok (taddr < a && a <= jaddr)
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a frozen test value: " ^ a ^ ", " ^ self#get_name]

  method get_frozen_variable:
           (variable_t * ctxt_iaddress_t * ctxt_iaddress_t) traceresult =
    match denotation with
    | AuxiliaryVariable (FrozenTestValue (fv, taddr, jaddr)) ->
       Ok (fv, taddr, jaddr)
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a frozen test value: " ^ self#get_name]

  method get_call_site: ctxt_iaddress_t traceresult =
    match denotation with
    | (AuxiliaryVariable (FunctionReturnValue a))
    | (AuxiliaryVariable (SideEffectValue (a, _, _))) -> Ok a
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a function return value or sideeffect value: "
              ^ self#get_name]

  method get_se_argument_descriptor: string traceresult =
    match denotation with
    | (AuxiliaryVariable (SideEffectValue (_, name, _))) -> Ok name
    | _ -> Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                  ^ "Variable is not a sideeffect value: " ^ self#get_name]

  method is_auxiliary_variable =
    match denotation with AuxiliaryVariable _ -> true | _ -> false

  method is_return_value =
    match denotation with
    | AuxiliaryVariable (FunctionReturnValue _) -> true | _ -> false

  method is_sideeffect_value =
    match denotation with
    | AuxiliaryVariable (SideEffectValue _) -> true | _ -> false

  method is_initial_memory_value =
    match denotation with
    | AuxiliaryVariable (InitialMemoryValue _) -> true | _ -> false

  (* a variable with a value determined by the environment of the function that
     does not change during the execution of the function. *)
  method is_function_initial_value =
    match denotation with
    | AuxiliaryVariable a ->
      begin
	match a with
	| InitialRegisterValue _
	  | InitialMemoryValue _
	  | FunctionReturnValue _
          | TypeCastValue _
	  | CallTargetValue _
	  | SideEffectValue _
	  | FieldValue _
          | SymbolicValue _
          | SignedSymbolicValue _ -> true
	| _ -> false
      end
    | _ -> false

  method get_register: register_t traceresult =
    match denotation with
    | RegisterVariable r -> Ok r
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a register: " ^ self#get_name]

  method is_initial_register_value =
    match denotation with
    | AuxiliaryVariable (InitialRegisterValue (_, 0)) -> true | _ -> false

  method is_initial_mips_argument_value =
    match denotation with
    | AuxiliaryVariable (InitialRegisterValue (reg,0)) ->
       (match reg with
        | MIPSRegister mipsreg ->
           (match mipsreg with
            | MRa0 | MRa1 | MRa2 | MRa3 -> true
            | _ -> false)
        | _ -> false)
    | _ -> false

  method is_initial_arm_argument_value =
    match denotation with
    | AuxiliaryVariable (InitialRegisterValue (reg, 0)) ->
       (match reg with
        | ARMRegister armreg ->
           (match armreg with
            | AR0 | AR1 | AR2 | AR3 -> true
            | _ -> false)
        | _ -> false)
    | _ -> false

  method is_initial_stackpointer_value =
    match denotation with
    | AuxiliaryVariable (InitialRegisterValue (reg, 0)) ->
       (match reg with
        | CPURegister Esp  (* x86 *)
          | MIPSRegister MRsp
          | ARMRegister ARSP
          | PowerGPRegister 1  (* power32 *) -> true
        | _ -> false)
    | _ -> false

  method get_initial_register_value_register: register_t traceresult =
    match denotation with
    | AuxiliaryVariable (InitialRegisterValue (CPURegister _ as reg, 0)) ->
       Ok reg
    | AuxiliaryVariable (InitialRegisterValue (MIPSRegister _ as reg, 0)) ->
       Ok reg
    | AuxiliaryVariable (InitialRegisterValue (MIPSSpecialRegister _ as reg, 0)) ->
       Ok reg
    | AuxiliaryVariable (InitialRegisterValue (ARMRegister _ as reg, 0)) ->
       Ok reg
    | AuxiliaryVariable (InitialRegisterValue (ARMExtensionRegister _ as reg, 0)) ->
       Ok reg
    | AuxiliaryVariable (InitialRegisterValue (PowerGPRegister _ as reg, 0)) ->
       Ok reg
    | AuxiliaryVariable (InitialRegisterValue (PowerSPRegister _ as reg, 0)) ->
       Ok reg
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not an initial register value: " ^ self#get_name]

  method get_initial_memory_value_variable: variable_t traceresult =
    match denotation with
    | AuxiliaryVariable (InitialMemoryValue v) -> Ok v
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not an initial memory value: " ^ self#get_name]

  method is_memory_variable =
    match denotation with MemoryVariable _ -> true | _ -> false

  method get_memory_reference: memory_reference_int traceresult =
    match denotation with
    | MemoryVariable (i, _, _) ->
       let memref_r = memrefmgr#get_memory_reference i in
       tprop memref_r (__FILE__ ^ ":" ^ (string_of_int __LINE__))
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a memory variable: " ^ self#get_name]

  method get_memory_offset: memory_offset_t traceresult =
    match denotation with
    | MemoryVariable (_, _, o) -> Ok o
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a memory variable: " ^ self#get_name]

  method is_register_variable =
    match denotation with RegisterVariable _ -> true | _ -> false

  method is_stackpointer_variable =
    match denotation with
    | RegisterVariable r -> BCHCPURegisters.is_stackpointer_register r
    | _ -> false

  method is_mips_argument_variable =
    match denotation with
    | RegisterVariable reg ->
       (match reg with
        | MIPSRegister mipsreg ->
           (match mipsreg with
            | MRa0 | MRa1 | MRa2 | MRa3 -> true
            | _ -> false)
        | _ -> false)
    | _ -> false

  method is_arm_argument_variable =
    match denotation with
    | RegisterVariable reg ->
       (match reg with
        | ARMRegister armreg ->
           (match armreg with
            | AR0 | AR1 | AR2 | AR3 -> true
            | _ -> false)
        | ARMDoubleRegister (AR0, AR1) -> true
        | ARMDoubleRegister (AR2, AR3) -> true
        | _ -> false)
    | _ -> false

  method is_arm_extension_register_variable =
    match denotation with
    | RegisterVariable reg ->
       (match reg with
        | ARMExtensionRegister _ -> true
        | _ -> false)
    | _ -> false

  method is_special_variable =
    match denotation with
    | AuxiliaryVariable (Special _) -> true | _ -> false

  method is_runtime_constant =
    match denotation with
    | AuxiliaryVariable (RuntimeConstant _) -> true | _ -> false

  method is_bridge_value =
    match denotation with
    | AuxiliaryVariable (BridgeVariable _) -> true | _ -> false

  method is_bridge_value_at (iaddr:ctxt_iaddress_t) =
    match denotation with
    | AuxiliaryVariable (BridgeVariable (a, _)) -> a = iaddr
    | _ -> false

  method is_symbolic_value =
    match denotation with
    | AuxiliaryVariable (SymbolicValue _)
      | AuxiliaryVariable (SignedSymbolicValue _) -> true
    | _ -> false

  method is_signed_symbolic_value =
    match denotation with
    | AuxiliaryVariable (SignedSymbolicValue _) -> true
    | _ -> false

  method get_symbolic_value_expr: xpr_t traceresult =
    match denotation with
    | AuxiliaryVariable (SymbolicValue x) -> Ok x
    | AuxiliaryVariable (SignedSymbolicValue (x, _, _)) -> Ok x
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Variable is not a symbolic value: " ^ self#get_name]

  method toPretty = STR self#get_name

end


class variable_manager_t
        (faddr: doubleword_int)
        (optnode: xml_element_int option)
        (vard: vardictionary_int)
        (memrefmgr: memory_reference_manager_int): variable_manager_int =
object (self)

  val faddr = faddr
  val vartable = H.create 3     (* index -> assembly_variable_int *)
  val vard = vard
  val memrefmgr = memrefmgr

  initializer
    match optnode with
    | Some xvard ->
       begin
         vard#read_xml xvard;
         memrefmgr#initialize;
         List.iter
           (fun (index, denotation) ->
             H.add
               vartable
               index
               (new assembly_variable_t ~vard ~memrefmgr ~index ~denotation))
           vard#get_indexed_variables
       end
    | _ -> ()

  method faddr = faddr

  method reset = vard#reset

  method vard = vard

  method memrefmgr = memrefmgr

  method private mk_variable (denotation:assembly_variable_denotation_t) =
    let index = vard#index_assembly_variable_denotation denotation in
    if  H.mem vartable index then
      H.find vartable index
    else
      let var = new assembly_variable_t ~memrefmgr ~vard ~index ~denotation in
      begin
        H.add vartable index var;
        var
      end

  method get_variable (v:variable_t): assembly_variable_int traceresult =
    self#get_variable_by_index v#getName#getSeqNumber

  method get_assembly_variables = H.fold (fun _ v acc -> v::acc) vartable []

  method get_variable_by_index (index:int): assembly_variable_int traceresult =
    if H.mem vartable index then
      Ok (H.find vartable index)
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ (string_of_int index)]

  method get_variable_type (v: variable_t): btype_t option =
    tfold_default
      (fun var -> var#get_type)
      None
      (self#get_variable v)

  method get_memvar_reference (v: variable_t): memory_reference_int traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_memory_reference)
      (self#get_variable v)

  method get_memval_reference (v: variable_t): memory_reference_int traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun var -> self#get_memvar_reference var)
      (self#get_initial_memory_value_variable v)

  method get_memvar_offset (v:variable_t): memory_offset_t traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_memory_offset)
      (self#get_variable v)

  method add_memvar_offset
           (v: variable_t)
           (memoff: memory_offset_t): assembly_variable_int traceresult =
    tbind
      (fun memvarref ->
        tbind
          (fun memvaroff ->
            if is_unknown_offset memvaroff then
              Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                     ^ "Variable " ^ (p2s v#toPretty) ^ " has unknown offset"]
            else
              let newoff = add_offset memvaroff memoff in
              Ok (self#make_memory_variable memvarref newoff))
          (self#get_memvar_offset v))
      (self#get_memvar_reference v)

  method has_variable_index_offset (v: variable_t): bool =
    match self#get_memvar_offset v with
    | Ok (IndexOffset (v, _, _)) -> self#is_register_variable v
    | Ok (ArrayIndexOffset (x, _)) ->
       (match x with
        | XConst (IntConst _) -> false
        | _ -> true)
    | _ -> false

  method get_memval_offset (v: variable_t): memory_offset_t traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun var -> self#get_memvar_offset var)
      (self#get_initial_memory_value_variable v)

  method private has_var (v:variable_t) =
    (not v#isTmp) && self#has_index v#getName#getSeqNumber

  method private has_sym (s:symbol_t) = self#has_index s#getSeqNumber

  method private has_index (index:int) = H.mem vartable index

  method make_memory_variable
           ?(size=4)
           (memref:memory_reference_int)
           (offset:memory_offset_t): assembly_variable_int =
    self#mk_variable (MemoryVariable (memref#index, size, offset))

  method make_memref_from_basevar
           (v: variable_t): memory_reference_int traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (fun av ->
        match av#to_basevar_reference with
        | Some memref -> Ok memref
        | _ ->
           (match av#get_denotation with
            | AuxiliaryVariable a ->
               (match a with
                | InitialRegisterValue (CPURegister _, _)
                  | InitialRegisterValue (MIPSRegister _, _)
                  | InitialRegisterValue (ARMRegister _, _)
                  | InitialRegisterValue (PowerGPRegister _, _)
                  | InitialRegisterValue (PowerSPRegister _, _)
                  | InitialMemoryValue _
                  | FunctionReturnValue _
                  | TypeCastValue _ ->
                   Ok (memrefmgr#mk_basevar_reference v)
                | _ ->
                   Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                          ^ "Unable to make memref basevar from auxiliary variable: "
                          ^ v#getName#getBaseName])
            | _ ->
               Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                      ^ "Unable to make memref basevar from variable: "
                      ^ v#getName#getBaseName]))
      (self#get_variable v)

  method make_register_variable (reg:register_t): assembly_variable_int =
    self#mk_variable (RegisterVariable reg)

  method make_flag_variable (flag: flag_t): assembly_variable_int =
    self#mk_variable (CPUFlagVariable flag)

  method make_global_variable ?(size=4) ?(offset=NoOffset) (n:numerical_t) =
    let offset = ConstantOffset (n, offset) in
    let memref = memrefmgr#mk_global_reference in
    self#make_memory_variable ~size memref offset

  method make_frozen_test_value
           (var:variable_t) (taddr:ctxt_iaddress_t) (jaddr:ctxt_iaddress_t) =
    self#mk_variable (AuxiliaryVariable (FrozenTestValue (var, taddr, jaddr)))

  method make_bridge_value (address:ctxt_iaddress_t) (argnr:int) =
    self#mk_variable (AuxiliaryVariable (BridgeVariable (address, argnr)))

  method make_initial_register_value (reg:register_t) (level:int) =
    self#mk_variable (AuxiliaryVariable (InitialRegisterValue (reg, level)))

  method make_initial_memory_value (var:variable_t) =
    self#mk_variable (AuxiliaryVariable (InitialMemoryValue var))

  method make_return_value (iaddr:ctxt_iaddress_t) =
    self#mk_variable (AuxiliaryVariable (FunctionReturnValue iaddr))

  method make_typecast_value
           (iaddr: ctxt_iaddress_t) (name: string) (ty: btype_t) (reg: register_t) =
    self#mk_variable (AuxiliaryVariable (TypeCastValue (iaddr,name, ty, reg)))

  method make_function_pointer_value
           (fname:string) (cname:string) (address:ctxt_iaddress_t) =
    self#mk_variable (AuxiliaryVariable (FunctionPointer (fname,cname,address)))

  method make_calltarget_value (tgt:call_target_t) =
    self#mk_variable (AuxiliaryVariable (CallTargetValue tgt))

  method make_side_effect_value
           (iaddr:ctxt_iaddress_t) ?(global=false) (arg:string) =
    self#mk_variable (AuxiliaryVariable (SideEffectValue (iaddr,arg,global)))

  method make_field_value (sname:string) (offset:int) (fname:string) =
    self#mk_variable (AuxiliaryVariable (FieldValue (sname,offset,fname)))

  method make_symbolic_value (x: xpr_t) =
    self#mk_variable (AuxiliaryVariable (SymbolicValue x))

  method make_signed_symbolic_value (x: xpr_t) (s0: int) (sx: int) =
    self#mk_variable (AuxiliaryVariable (SignedSymbolicValue (x, s0, sx)))

  method make_special_variable (name: string) =
    self#mk_variable (AuxiliaryVariable (Special name))

  method make_runtime_constant (name:string) =
    self#mk_variable (AuxiliaryVariable (RuntimeConstant name))

  method get_initial_memory_value_variable (v: variable_t): variable_t traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_initial_memory_value_variable)
      (self#get_variable v)

  method get_pointed_to_function_name (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_pointed_to_function_name)
      (self#get_variable v)

  method get_stack_parameter_index (v: variable_t): int option =
    tfold
      ~ok:(fun memref ->
        if memref#is_stack_reference then
          tfold
            ~ok:(fun offset ->
              if is_constant_offset offset then
                tfold
                  ~ok:(fun numoffset ->
                    let four = mkNumerical 4 in
                    if numoffset#gt numerical_zero
                       && (numoffset#modulo four)#equal numerical_zero then
                      Some ((numoffset#div four)#toInt)
                    else
                      None)
                  ~error:(fun _ -> None)
                  (get_total_constant_offset offset)
              else
                None)
            ~error:(fun _ -> None)
            (self#get_memvar_offset v)
        else
          None)
      ~error:(fun _ -> None)
      (self#get_memvar_reference v)

  method get_register (v: variable_t): register_t traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_register)
      (self#get_variable v)

  method get_call_site (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_call_site)
      (self#get_variable v)

  method get_se_argument_descriptor (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_se_argument_descriptor)
      (self#get_variable v)

  method get_initial_register_value_register (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_initial_register_value_register)
      (self#get_variable v)

  method get_frozen_variable (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_frozen_variable)
      (self#get_variable v)

  method get_calltarget_value (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_calltarget_value)
      (self#get_variable v)

  method get_symbolic_value_expr (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_symbolic_value_expr)
      (self#get_variable v)

  method has_global_variable_address (v: variable_t) =
    self#is_global_variable v
    && (tfold_default is_constant_offset false (self#get_memvar_offset v))

  method get_global_variable_address (v: variable_t): doubleword_result =
    if self#has_global_variable_address v then
      tbind
        ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
        (fun offset ->
          tbind numerical_to_doubleword (get_total_constant_offset offset))
        (self#get_memvar_offset v)
    else
      Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
             ^ "Variable is not a global variable: "
             ^ v#getName#getBaseName]

  method get_global_sideeffect_target_address (v: variable_t) =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": " ^ (p2s v#toPretty))
      (fun av -> av#get_global_sideeffect_target_address)
      (self#get_variable v)

  method private compare_memory_vars
                   (av1: assembly_variable_int) (av2: assembly_variable_int) =
    let memref1 = TR.tget_ok (av1#get_memory_reference) in
    let memref2 = TR.tget_ok (av2#get_memory_reference) in
    match (memref1#get_base, memref2#get_base) with
    | (BGlobal, _) -> -1
    | (_, BGlobal) -> 1
    | (BaseVar _, _) -> -1
    | (_, BaseVar _) -> 1
    | (BLocalStackFrame, BLocalStackFrame) -> memref1#compare memref2
    | (BLocalStackFrame, _) -> -1
    | (_, BLocalStackFrame) -> 1
    | (BRealignedStackFrame, _) -> -1
    | (_, BRealignedStackFrame) -> 1
    | _ -> memref1#compare memref2

  method private compare_auxiliary_vars
                   (ix1: int)
                   (ix2: int)
                   (cv1: constant_value_variable_t)
                   (cv2: constant_value_variable_t) =
    match (cv1, cv2) with
    | (FunctionReturnValue _, FunctionReturnValue _) -> Stdlib.compare ix1 ix2
    | (FunctionReturnValue _, _) -> -1
    | (_, FunctionReturnValue _) -> 1

    | (SymbolicValue _, SymbolicValue _) -> Stdlib.compare ix1 ix2
    | (SymbolicValue _, _) -> -1
    | (_, SymbolicValue _) -> 1

    | (SignedSymbolicValue _, SignedSymbolicValue _) -> Stdlib.compare ix1 ix2
    | (SignedSymbolicValue _, _) -> -1
    | (_, SignedSymbolicValue _) -> 1

    | (CallTargetValue _, CallTargetValue _) -> Stdlib.compare ix1 ix2
    | (CallTargetValue _, _) -> -1
    | (_, CallTargetValue _) -> 1

    | (InitialRegisterValue _, InitialRegisterValue _) -> Stdlib.compare ix1 ix2
    | (InitialRegisterValue _, _) -> -1
    | (_, InitialRegisterValue _) -> 1

    | (InitialMemoryValue _, InitialMemoryValue _) -> Stdlib.compare ix1 ix2
    | (InitialMemoryValue _, _) -> -1
    | (_, InitialMemoryValue _) -> 1

    | (FunctionPointer _, FunctionPointer _) -> Stdlib.compare ix1 ix2
    | (FunctionPointer _, _) -> -1
    | (_, FunctionPointer _) -> 1

    | (FieldValue _, FieldValue _) -> Stdlib.compare ix1 ix2
    | (FieldValue _, _) -> -1
    | (_, FieldValue _) -> 1

    | (SideEffectValue _, SideEffectValue _) -> Stdlib.compare ix1 ix2
    | (SideEffectValue _, _) -> -1
    | (_, SideEffectValue _) -> 1

    | _ -> Stdlib.compare ix1 ix2

  method get_external_variable_comparator =
    fun (v1: variable_t) (v2: variable_t) ->
    if v1#equal v2 then
      0
    else
      if v1#isTmp then
        1
      else if v2#isTmp then
        -1
      else
	let var1 = TR.tget_ok (self#get_variable v1) in
	let var2 = TR.tget_ok (self#get_variable v2) in
        match (var1#get_denotation, var2#get_denotation) with
        | (AuxiliaryVariable a1, AuxiliaryVariable a2) ->
           self#compare_auxiliary_vars var1#index var2#index a1 a2

        | (MemoryVariable _, MemoryVariable _) ->
           self#compare_memory_vars var1 var2

        | (RegisterVariable _, RegisterVariable _) ->
           Stdlib.compare var1#index var2#index

        | (AuxiliaryVariable _, _) -> -1
        | (_, AuxiliaryVariable _) -> 1

	| (MemoryVariable _, _) when self#is_global_variable v1 -> -1

	| (_, MemoryVariable _) when self#is_global_variable v2 -> 1

        | (MemoryVariable _, _) when self#is_basevar_memory_variable v1 -> -1

        | (_, MemoryVariable _) when self#is_basevar_memory_variable v2 -> 1

        | _ -> Stdlib.compare var1#index var2#index

  method is_stack_parameter_variable (v:variable_t) =
    if (self#is_stack_variable v) && (self#has_constant_offset v) then
      let memoff_r = tbind get_total_constant_offset (self#get_memvar_offset v) in
      tfold_default (fun memoff -> memoff#geq numerical_zero) false memoff_r
    else
      false

  method is_realigned_stack_variable (v:variable_t) =
    (self#is_memory_variable v)
    && (tfold_default
          (fun memref -> memref#is_realigned_stack_reference)
          false
          (self#get_memvar_reference v))

  method is_function_initial_value (v:variable_t) =
    tfold_default
      (fun av -> av#is_function_initial_value) false (self#get_variable v)

  method is_local_variable (v:variable_t) =
    (self#is_register_variable v) || (self#is_stack_variable v)

  method is_global_variable (v:variable_t) =
    (self#is_memory_variable v)
    && (tfold_default
          (fun memref -> memref#is_global_reference)
          false
          (self#get_memvar_reference v))

  method is_register_variable (v:variable_t) =
    tfold_default
      (fun av -> av#is_register_variable) false (self#get_variable v)

  method is_stackpointer_variable (v: variable_t) =
    tfold_default
      (fun av -> av#is_stackpointer_variable) false (self#get_variable v)

  method is_mips_argument_variable (v:variable_t) =
    tfold_default
      (fun av -> av#is_mips_argument_variable) false (self#get_variable v)

  method is_arm_argument_variable (v:variable_t) =
    tfold_default
      (fun av -> av#is_arm_argument_variable) false (self#get_variable v)

  method is_arm_extension_register_variable (v: variable_t) =
    tfold_default
    (fun av -> av#is_arm_extension_register_variable) false (self#get_variable v)

  method is_stack_variable (v: variable_t) =
    (self#is_memory_variable v)
    && (let memref_r = self#get_memvar_reference v in
        tfold_default (fun memref -> memref#is_stack_reference) false memref_r)

  method is_memory_variable (v: variable_t) =
    tfold_default (fun av -> av#is_memory_variable) false (self#get_variable v)

  method is_basevar_memory_variable (v: variable_t) =
    (self#is_memory_variable v)
    && (let memref_r = self#get_memvar_reference v in
        tfold_default (fun memref -> memref#has_external_base) false memref_r)

  method is_basevar_memory_value (v: variable_t) =
    (self#is_initial_memory_value v)
    && (let var_r = self#get_initial_memory_value_variable v in
         tfold_default self#is_basevar_memory_variable false var_r)

  method get_memvar_basevar (v: variable_t): variable_t traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (fun memref -> memref#get_external_base)
      (self#get_memvar_reference v)

  method get_memval_basevar (v:variable_t): variable_t traceresult =
    tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (fun var -> self#get_memvar_basevar var)
      (self#get_initial_memory_value_variable v)

  method is_fixed_value_offset (offset: memory_offset_t) =
    (is_constant_offset offset)
    || ((is_index_offset offset)
        && (List.for_all
              self#is_function_initial_value
              (get_index_offset_variables offset)))

  method has_fixed_value_offset (v: variable_t) =
    (self#is_memory_variable v)
    && (tfold_default
          self#is_fixed_value_offset false (self#get_memvar_offset v))

  method has_constant_offset (v: variable_t) =
    (self#is_memory_variable v)
    && (tfold_default is_constant_offset false (self#get_memvar_offset v))

  method is_unknown_base_memory_variable (v: variable_t) =
    (self#is_memory_variable v)
    && (tfold_default
          (fun memref -> memref#is_unknown_reference)
          false
          (self#get_memvar_reference v))

  method is_unknown_offset_memory_variable (v: variable_t) =
    (self#is_memory_variable v)
    && (tfold_default is_unknown_offset false (self#get_memvar_offset v))

  method is_unknown_memory_variable (v: variable_t) =
    (self#is_unknown_base_memory_variable v)
    || (self#is_unknown_offset_memory_variable v)

  method is_frozen_test_value (v:variable_t) =
    tfold_default
      (fun av -> av#is_frozen_test_value) false (self#get_variable v)

  method is_initial_register_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_initial_register_value) false (self#get_variable v)

  method is_initial_mips_argument_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_initial_mips_argument_value) false (self#get_variable v)

  method is_initial_arm_argument_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_initial_arm_argument_value) false (self#get_variable v)

  method is_initial_memory_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_initial_memory_value) false (self#get_variable v)

  method is_initial_stackpointer_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_initial_stackpointer_value) false (self#get_variable v)

  method is_bridge_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_bridge_value) false (self#get_variable v)

  method is_bridge_value_at (a: ctxt_iaddress_t) (v: variable_t) =
    tfold_default
      (fun av -> av#is_bridge_value_at a) false (self#get_variable v)

  method is_symbolic_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_symbolic_value) false (self#get_variable v)

  method is_signed_symbolic_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_signed_symbolic_value) false (self#get_variable v)

  method is_in_test_jump_range (a: ctxt_iaddress_t) (v: variable_t) =
    tbind
      ~msg:"varmgr:is_in_test_jump_range"
      (fun av -> av#is_in_test_jump_range a)
      (self#get_variable v)

  method is_return_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_return_value) false (self#get_variable v)

  method is_sideeffect_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_sideeffect_value) false (self#get_variable v)

  method is_special_variable (v: variable_t) =
    tfold_default
      (fun av -> av#is_special_variable) false (self#get_variable v)

  method is_runtime_constant (v: variable_t) =
    tfold_default
      (fun av -> av#is_runtime_constant) false (self#get_variable v)

  method is_function_pointer (v: variable_t) =
    tfold_default
      (fun av -> av#is_function_pointer) false (self#get_variable v)

  method is_calltarget_value (v: variable_t) =
    tfold_default
      (fun av -> av#is_calltarget_value) false (self#get_variable v)

  method is_global_sideeffect (v: variable_t) =
    tfold_default
      (fun av -> av#is_global_sideeffect) false (self#get_variable v)

end


let make_variable_manager
      (faddr: doubleword_int) (optnode:xml_element_int option) =
  let xd = mk_xprdictionary () in
  let vard = mk_vardictionary faddr xd in
  let memrefmgr = make_memory_reference_manager vard in
  new variable_manager_t faddr optnode vard memrefmgr
