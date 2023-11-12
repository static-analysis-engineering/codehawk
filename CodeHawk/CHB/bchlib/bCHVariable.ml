(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
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
(* A variable manager and variable dictionary are created per function. *)

(* chlib *)
open CHCommon
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open XprDictionary
open XprToPretty
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHCallTarget
open BCHCPURegisters
open BCHDoubleword
open BCHFunctionStub
open BCHLibTypes
open BCHMemoryReference
open BCHVarDictionary
open BCHVariableNames
open BCHXmlUtil

module H = Hashtbl
module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)


let raise_xml_error (node: xml_element_int) (msg: pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
        INT node#getColumnNumber;
	STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


let raise_var_type_error (v: assembly_variable_int) (msg: pretty_t) =
  let errormsg =
    LBLOCK [STR "Expected: "; msg; STR "; Found: "; v#toPretty] in
  begin
    ch_error_log#add "var type error" errormsg;
    raise (BCH_failure errormsg)
  end


let raise_memref_type_error (r: memory_reference_int) (msg: pretty_t) =
  let errormsg =
    LBLOCK [STR "Expected: "; msg; STR "; Found: "; r#toPretty] in
  begin
    ch_error_log#add "memref type error" errormsg;
    raise (BCH_failure errormsg)
  end


let rec denotation_to_pretty (v:assembly_variable_denotation_t) =
  match v with
  | MemoryVariable (memref, size, offset) ->
     LBLOCK [STR "Mem "; INT memref; STR "(size:"; INT size; STR ")"]
  | RegisterVariable r -> LBLOCK [STR "Reg "; STR (register_to_string r)]
  | CPUFlagVariable f -> LBLOCK [STR "Flag "; STR (flag_to_string f)]
  | AuxiliaryVariable v -> LBLOCK [STR "Aux "; aux_var_to_pretty v]


and aux_var_to_pretty (cvv: constant_value_variable_t) =
  match cvv with
  | InitialRegisterValue (r, level) ->
     LBLOCK [STR "InitR("; INT level; STR ") "; STR (register_to_string r)]
  | InitialMemoryValue v ->
     LBLOCK [STR "InitM("; v#toPretty; STR ")"]
  | FrozenTestValue (fv,taddr,jaddr) -> 
     LBLOCK [
         STR "Frozen(";
         fv#toPretty;
         STR " )@ ";
         STR taddr;
	 STR " for ";
         STR jaddr]
  | FunctionReturnValue addr -> LBLOCK [STR "Return("; STR addr; STR ")"]
  | SyscallErrorReturnValue addr ->
     LBLOCK [STR "ErrorValue("; STR addr; STR ")"]
  | SSARegisterValue (r, addr, optname, ty) ->
     LBLOCK [
         STR "SSARegisterValue(";
         STR (register_to_string r);
         STR ", ";
         STR (match optname with Some name -> name | _ -> "none");
         STR ", ";
         STR (btype_to_string ty)]
  | FunctionPointer (f, c, addr) ->
     LBLOCK [STR "FunctionP("; STR f; STR ","; STR c; STR ","; STR addr; STR ")"]
  | CallTargetValue tgt -> 
     LBLOCK [ STR "CallTarget("; call_target_to_pretty tgt; STR ")"]
  | SideEffectValue (addr, arg, _) ->
     LBLOCK [STR "SideEffect("; STR arg; STR addr; STR ")"]
  | FieldValue (sname, offset, fname) ->
     LBLOCK [
         STR "FieldValue(" ;
         STR sname ;
         STR "," ;
         INT offset ;
	 STR "," ;
         STR fname]
  | SymbolicValue x -> LBLOCK [STR "SymbolicValue("; x2p x; STR ")"]
  | SignedSymbolicValue (x, s0, sx) ->
     LBLOCK [
         STR "SignedSymbolicValue(";
         x2p x;
         STR ", ";
         INT s0;
         STR ">";
         INT sx;
         STR ")"]
  | BridgeVariable (addr,arg) ->
    LBLOCK [ STR "Bridge(" ; STR addr ; STR "," ; INT arg ; STR ")" ]
  | Special s -> LBLOCK [ STR "Special " ; STR s ]
  | RuntimeConstant s -> LBLOCK [ STR "Runtime " ; STR s ]
  | MemoryAddress (i,offset) -> LBLOCK [ STR "memaddr-" ; INT i ]
  | ChifTemp -> STR "ChifTemp"


class assembly_variable_t
        ~(vard:vardictionary_int)
        ~(memrefmgr:memory_reference_manager_int)
        ~(index:int) 
        ~(denotation:assembly_variable_denotation_t):assembly_variable_int =
object (self:'a)
  method index = index

  method compare (other:'a) = Stdlib.compare self#index other#index

  method get_denotation = denotation

  method get_name  = 
    let rec aux den = match den with
      | MemoryVariable (i, size, offset) ->
         let basename = (memrefmgr#get_memory_reference i)#get_name in
         (match basename with
          | "var" -> stack_offset_to_name offset
          | "varr" -> realigned_stack_offset_to_name offset
          | "gv" -> global_offset_to_name size offset
          | _ -> basename ^ (memory_offset_to_string offset))
      | RegisterVariable reg -> register_to_string reg
      | CPUFlagVariable flag -> flag_to_string flag
      | AuxiliaryVariable a ->
	match a with
	| InitialRegisterValue (r,level) -> (register_to_string r) ^ "_in" ^ 
	  (if level = 0 then "" else "_" ^ (string_of_int level))
	| InitialMemoryValue v -> v#getName#getBaseName ^ "_in"
	| FrozenTestValue (fv,taddr,jaddr) -> 
	  fv#getName#getBaseName ^ "_val@_" ^ taddr ^ "_@_" ^ jaddr
	| FunctionPointer (fname,cname,address) -> 
	  "fp_" ^ fname ^ "_" ^ cname ^ "_" ^ address
	| FunctionReturnValue address -> "rtn_" ^ address
        | SyscallErrorReturnValue address -> "errval_" ^ address
        | SSARegisterValue (r, addr, optname, ty) ->
           (match optname with
            | Some name -> name
            | _ -> (register_to_string r) ^ "_" ^ addr)
	| CallTargetValue tgt -> 
	  (match tgt with
	  | StubTarget fs -> "stub:" ^ (function_stub_to_string fs)
	  | StaticStubTarget (dw,fs) ->
             "staticstub:" ^ (function_stub_to_string fs)
	  | AppTarget a -> "tgt_" ^ a#to_hex_string
	  | _ -> "tgt_?")
	| SideEffectValue (address,arg,_) -> "se_" ^ address ^ "_" ^ arg
	| FieldValue (sname,offset,fname) ->
	   sname ^ "." ^ fname ^ "@" ^ (string_of_int offset)
        | SymbolicValue x -> "sv__" ^ (x2s x) ^ "__sv"
        | SignedSymbolicValue (x, s0, sx) ->
           "ssv__"
           ^ (x2s x)
           ^ "_"
           ^ (string_of_int s0)
           ^ "_"
           ^ (string_of_int sx)
           ^ "_"
	| BridgeVariable (address, n) -> 
	  "arg_" ^ (string_of_int n) ^ "_for_call_at_" ^ address
	| Special s -> "special_" ^ s
  	| RuntimeConstant s -> "rtc_" ^ s
        | MemoryAddress (i,offset) -> "memaddr-" ^ (string_of_int i)
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
    else name
      
  method is_function_pointer =
    match denotation with AuxiliaryVariable (FunctionPointer _) -> true | _ -> false

  method is_calltarget_value =
    match denotation with AuxiliaryVariable (CallTargetValue _) -> true | _ -> false

  method get_calltarget_value =
    match denotation with
    | AuxiliaryVariable (CallTargetValue tgt) -> tgt
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR self#get_name; STR " is not a calltarget value "]))

  method is_global_sideeffect =
    match denotation with 
    | AuxiliaryVariable (SideEffectValue (_,_,isglobal)) -> isglobal
    | _ -> false

  method get_global_sideeffect_target_address =
    match denotation with
    | AuxiliaryVariable (SideEffectValue (_, arg, true)) ->
       TR.tget_ok (string_to_doubleword arg)
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Variable is not a global side effect: ";
		 self#toPretty]))
	
  method get_pointed_to_function_name =
    match denotation with
    | AuxiliaryVariable (FunctionPointer (name,_,_)) -> name
    | _ ->
      begin
	ch_error_log#add
          "assembly variable access"
	  (LBLOCK [
               STR "assembly_variable#get_pointed_to_function_name: ";
	       self#toPretty]);
	raise
          (BCH_failure
             (LBLOCK [
                  STR "get pointed to function name on "; self#toPretty]))
      end

  method is_frozen_test_value =
    match denotation with
    | AuxiliaryVariable (FrozenTestValue _) -> true
    | _ -> false

  method is_ssa_register_value =
    match denotation with
    | AuxiliaryVariable (SSARegisterValue _) -> true
    | _ -> false

  method is_ssa_register_value_at (iaddr: ctxt_iaddress_t): bool =
    match denotation with
    | AuxiliaryVariable (SSARegisterValue (_, a, _, _)) -> a = iaddr
    | _ -> false

  method is_in_test_jump_range (a:ctxt_iaddress_t) =
    match denotation with
    | AuxiliaryVariable (FrozenTestValue (_,taddr,jaddr)) -> taddr < a && a <= jaddr
    | _ -> raise (BCH_failure (LBLOCK [ STR "Variable is not a frozen test value" ]))

  method get_frozen_variable = (* the variable associated with the frozen value *)
    match denotation with
    | AuxiliaryVariable (FrozenTestValue (fv,taddr,jaddr)) -> (fv,taddr,jaddr)
    | _ -> 
      begin
	ch_error_log#add "assembly variable acess" 
	  (LBLOCK [ STR "assembly_variable#get_frozen_variable: " ; self#toPretty ]) ;
	raise (BCH_failure 
		 (LBLOCK [ STR "variable is not a frozen test value: " ; self#toPretty ]))
      end

  method get_call_site =
    match denotation with 
    | (AuxiliaryVariable (FunctionReturnValue a)) 
    | (AuxiliaryVariable (SideEffectValue (a,_,_))) -> a
    | _ ->
      raise (BCH_failure (LBLOCK [ STR "Variable is not a return value: " ; 
				   self#toPretty ]))

  method get_se_argument_descriptor =
    match denotation with
    | (AuxiliaryVariable (SideEffectValue (_,name,_))) -> name
    | _ ->
      raise (BCH_failure (LBLOCK [ STR "Variable is not a sideeffect value: " ;
				   self#toPretty ]))
	
  method is_auxiliary_variable =
    match denotation with AuxiliaryVariable _ -> true | _ -> false

  method is_return_value =
    match denotation with AuxiliaryVariable (FunctionReturnValue _) -> true | _ -> false

  method is_sideeffect_value =
    match denotation with AuxiliaryVariable (SideEffectValue _) -> true | _ -> false

  method is_initial_memory_value =
    match denotation with AuxiliaryVariable (InitialMemoryValue _) -> true | _ -> false

  (* a variable with a value determined by the environment of the function that 
     does not change during the execution of the function
  *)
  method is_function_initial_value =
    match denotation with
    | AuxiliaryVariable a ->
      begin
	match a with
	| InitialRegisterValue _
	  | InitialMemoryValue _
	  | FunctionReturnValue _
	  | CallTargetValue _
	  | SideEffectValue _
	  | FieldValue _
          | SymbolicValue _
          | SignedSymbolicValue _ -> true
	| _ -> false
      end
    | _ -> false
	
  method get_register =
    match denotation with
    | RegisterVariable r -> r
    | _ ->
      begin
	ch_error_log#add "assembly variable access" 
	  (LBLOCK [ STR "get_register with " ; self#toPretty ]) ;
	raise (BCH_failure (LBLOCK [ STR "variable is not a register variable: " ; 
				   self#toPretty ]))
      end
	
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
    self#is_initial_register_value
	      
  method get_initial_register_value_register =
    match denotation with
    | AuxiliaryVariable (InitialRegisterValue (CPURegister r, 0)) ->
       CPURegister r
    | AuxiliaryVariable (InitialRegisterValue (MIPSRegister r, 0)) ->
       MIPSRegister r
    | AuxiliaryVariable (InitialRegisterValue (ARMRegister r, 0)) ->
       ARMRegister r
    | AuxiliaryVariable (InitialRegisterValue (ARMExtensionRegister r, 0)) ->
       ARMExtensionRegister r
    | AuxiliaryVariable (InitialRegisterValue (PowerGPRegister i, 0)) ->
       PowerGPRegister i
    | AuxiliaryVariable (InitialRegisterValue (PowerSPRegister r, 0)) ->
       PowerSPRegister r
    | _ ->
      begin
	ch_error_log#add
          "assembly variable access"
	  (LBLOCK [
               STR "get_register_parameter_register with ";
               self#toPretty]);
	raise
          (BCH_failure
             (LBLOCK [
                  STR "variable is not a parameter register: ";
		  self#toPretty]))
      end

  method get_ssa_register_value_register =
    match denotation with
    | AuxiliaryVariable (SSARegisterValue (r, _, _, _)) -> r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "get_ssa_register_value_register: "; self#toPretty]))

  method get_initial_memory_value_variable =
    match denotation with
    | AuxiliaryVariable (InitialMemoryValue v) -> v
    | _ ->
      begin
	ch_error_log#add
          "assembly variable access"
	  (LBLOCK [
               STR "get_initial_memory_value_variable with "; self#toPretty]);
	raise
          (BCH_failure
	     (LBLOCK [
                  STR "variable is not an initial memory value: ";
                  self#toPretty]))
      end

  method is_memory_variable = 
    match denotation with MemoryVariable _ -> true | _ -> false

  method is_register_variable = 
    match denotation with RegisterVariable _ -> true | _ -> false

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

  method is_special_variable = 
    match denotation with AuxiliaryVariable (Special _) -> true | _ -> false
    
  method is_runtime_constant = 
    match denotation with AuxiliaryVariable (RuntimeConstant _) -> true | _ -> false
                        
  method is_bridge_value =
    match denotation with AuxiliaryVariable (BridgeVariable _) -> true | _ -> false

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

  method get_symbolic_value_expr =
    match denotation with
    | AuxiliaryVariable (SymbolicValue x) -> x
    | AuxiliaryVariable (SignedSymbolicValue (x, _, _)) -> x
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Variable is not a symbolic value: " ;
                 self#toPretty]))

  method toPretty = STR self#get_name

end


class variable_manager_t
        (optnode: xml_element_int option)
        (vard: vardictionary_int)
        (memrefmgr: memory_reference_manager_int): variable_manager_int =
object (self)

  val vartable = H.create 3     (* index -> assembly_variable_int *)
  val vard = vard
  val memrefmgr = memrefmgr

  initializer
    match optnode with
    | Some xvard ->
       begin
         vard#read_xml xvard;
         memrefmgr#read_xml xvard;
         List.iter
           (fun (index, denotation) ->
             H.add
               vartable
               index
               (new assembly_variable_t ~vard ~memrefmgr ~index ~denotation))
           vard#get_indexed_variables
       end
    | _ -> ()

  method reset = vard#reset
  method vard = vard
  method memrefmgr = memrefmgr

  method private mk_variable (denotation:assembly_variable_denotation_t) =
    let index = vard#index_assembly_variable_denotation denotation in
    if  H.mem vartable index then
      H.find vartable index
    else
      let var = new assembly_variable_t ~vard ~memrefmgr ~index ~denotation in
      begin
        H.add vartable index var ;
        var
      end

  method get_variable (v:variable_t) =
    self#get_variable_by_index v#getName#getSeqNumber

  method get_assembly_variables = H.fold (fun _ v acc -> v::acc) vartable []

  method private get_variable_by_index (index:int) =
    if H.mem vartable index then
      H.find vartable index
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No variable found with index "; INT index]))

  method get_memvar_reference (v:variable_t) =
    let av = self#get_variable v in
    match av#get_denotation with
    | MemoryVariable (i, _, _) -> memrefmgr#get_memory_reference i
    | _ ->
       raise_var_type_error av (STR "Memory Variable")

  method get_memvar_offset (v:variable_t) =
    if self#is_initial_memory_value v then
      self#get_memval_offset v
    else if self#has_var v then
      let av = self#get_variable v in
      match av#get_denotation with
      | MemoryVariable (_, s, o) -> o
      | _ -> raise_var_type_error av (STR "Memory Variable")
    else
      raise (BCH_failure (LBLOCK [STR "Temporary variable: "; v#toPretty]))

  method get_memval_offset (v:variable_t) =
    if self#has_var v then
      if self#is_initial_memory_value v then
        let iv = self#get_initial_memory_value_variable v in
        self#get_memvar_offset iv
      else
        raise
          (BCH_failure
             (LBLOCK [
                  STR "Not an initial memory variable: "; v#toPretty]))
    else
      raise (BCH_failure (LBLOCK [STR "Temporary variable: "; v#toPretty]))

  method private get_memaddress_reference (v:variable_t) =
    let av = self#get_variable v in
    match av#get_denotation with
    | AuxiliaryVariable (MemoryAddress (i, _)) ->
       memrefmgr#get_memory_reference i
    | _ ->
       raise_var_type_error av (STR "Memory Address")
    
  method private has_var (v:variable_t) = 
    (not v#isTmp) && self#has_index v#getName#getSeqNumber

  method private has_sym (s:symbol_t) = self#has_index s#getSeqNumber

  method private has_memvar (v:variable_t) =
    self#has_var v &&
      (match (self#get_variable v)#get_denotation with
       | MemoryVariable _ -> true | _ -> false)

  method private has_index (index:int) = H.mem vartable index

  method make_memory_variable
           ?(size=4)
           (memref:memory_reference_int)
           (offset:memory_offset_t) =
    self#mk_variable (MemoryVariable (memref#index, size, offset))

  method make_memref_from_basevar (v:variable_t) =
    if self#has_var v then
      let av = self#get_variable v in
      match av#get_denotation with
      | AuxiliaryVariable a ->
         (match a with
          | InitialRegisterValue (CPURegister Esp, 0) ->
             memrefmgr#mk_local_stack_reference
          | InitialRegisterValue (CPURegister Esp, 1) ->
             memrefmgr#mk_realigned_stack_reference
          | InitialRegisterValue (MIPSRegister MRsp, 0) ->
             memrefmgr#mk_local_stack_reference
          | InitialRegisterValue (MIPSRegister MRsp, 1) ->
             memrefmgr#mk_realigned_stack_reference
          | InitialRegisterValue (ARMRegister ARSP, 0) ->
             memrefmgr#mk_local_stack_reference
          | InitialRegisterValue (ARMRegister ARSP, 1) ->
             memrefmgr#mk_realigned_stack_reference
          | InitialRegisterValue (PowerGPRegister 1, 0) ->
             memrefmgr#mk_local_stack_reference
          | InitialRegisterValue (PowerGPRegister 1, 1) ->
             memrefmgr#mk_realigned_stack_reference
          | InitialRegisterValue (CPURegister _, _)
            | InitialRegisterValue (MIPSRegister _, _)
            | InitialRegisterValue (ARMRegister _, _)
            | InitialRegisterValue (PowerGPRegister _, _)
            | InitialRegisterValue (PowerSPRegister _, _)
            | InitialMemoryValue _
            | FunctionReturnValue _ -> memrefmgr#mk_basevar_reference v
          | _ ->
             memrefmgr#mk_unknown_reference ("base:" ^ v#getName#getBaseName))
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "unable to use variable as memory base: ";
                   v#toPretty]))
    else
      raise
        (BCH_failure (LBLOCK [STR "base variable not found: "; v#toPretty ]))
           
  method make_register_variable (reg:register_t) =
    self#mk_variable (RegisterVariable reg)

  method make_flag_variable (flag: flag_t) =
    self#mk_variable (CPUFlagVariable flag)

  method make_global_variable ?(size=4) ?(offset=NoOffset) (n:numerical_t) =
    let offset = ConstantOffset (n, offset) in
    let memref = memrefmgr#mk_global_reference in
    self#make_memory_variable ~size memref offset

  method make_frozen_test_value 
           (var:variable_t) (taddr:ctxt_iaddress_t) (jaddr:ctxt_iaddress_t) =
    self#mk_variable (AuxiliaryVariable (FrozenTestValue (var, taddr, jaddr)))
      
  method make_bridge_value (address:ctxt_iaddress_t) (argnr:int) =
    self#mk_variable (AuxiliaryVariable (BridgeVariable (address,argnr)))

  method make_initial_register_value (reg:register_t) (level:int) =
    self#mk_variable (AuxiliaryVariable (InitialRegisterValue (reg, level)))

  method make_initial_memory_value (var:variable_t) =
    self#mk_variable (AuxiliaryVariable (InitialMemoryValue var))

  method make_return_value (iaddr:ctxt_iaddress_t) =
    self#mk_variable (AuxiliaryVariable (FunctionReturnValue iaddr))

  method make_ssa_register_value
           ?(name: string option=None)
           (reg: register_t)
           (iaddr: ctxt_iaddress_t)
           (ty: btype_t) =
    self#mk_variable (AuxiliaryVariable (SSARegisterValue (reg, iaddr, name, ty)))

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

  method make_symbolic_value (x:xpr_t) =
    self#mk_variable (AuxiliaryVariable (SymbolicValue x))

  method make_signed_symbolic_value (x: xpr_t) (s0: int) (sx: int) =
    self#mk_variable (AuxiliaryVariable (SignedSymbolicValue (x, s0, sx)))
      
  method make_special_variable (name:string) =
    self#mk_variable (AuxiliaryVariable (Special name))

  method make_runtime_constant (name:string) =
    self#mk_variable (AuxiliaryVariable (RuntimeConstant name))
    
  method get_initial_memory_value_variable (v:variable_t) =
    (self#get_variable v)#get_initial_memory_value_variable

  method has_global_variable_address (v: variable_t): bool =
    let memref = self#get_memvar_reference v in
    if memref#is_global_reference then
      let offset = self#get_memvar_offset v in
      is_constant_offset offset
    else
      false

  method get_global_variable_address (v: variable_t) =
    let memref = self#get_memvar_reference v in
    if memref#is_global_reference then
      let offset = self#get_memvar_offset v in
      if is_constant_offset offset then
        let noffset = get_total_constant_offset offset in
        TR.tget_ok (numerical_to_doubleword noffset)
      else
        raise_memref_type_error
          memref
          (LBLOCK [
               STR "Global reference: non-constant offset: ";
               v#toPretty])
    else
      raise_memref_type_error
        memref
        (LBLOCK [
             STR "Global reference: not a global reference: ";
             v#toPretty])
	
  method get_pointed_to_function_name (v:variable_t) =
    (self#get_variable v)#get_pointed_to_function_name
	
  method get_stack_parameter_index (v:variable_t) =
    let memref = self#get_memvar_reference v in
    if memref#is_stack_reference then
      let offset = self#get_memvar_offset v in
      if is_constant_offset offset then
        let four = mkNumerical 4 in
        let noffset = get_total_constant_offset offset in
        if noffset#gt numerical_zero
           && (noffset#modulo four)#equal numerical_zero then
          Some ((noffset#div (mkNumerical 4))#toInt)
        else
          None
      else
        None
    else
      raise_memref_type_error memref (STR "Stack parameter index")

  method get_register (v: variable_t) =	(self#get_variable v)#get_register

  method get_call_site (v:variable_t) = (self#get_variable v)#get_call_site

  method get_se_argument_descriptor (v:variable_t) =
    (self#get_variable v)#get_se_argument_descriptor

  method get_ssa_register_value_register (v: variable_t) =
    (self#get_variable v)#get_ssa_register_value_register
    
  method get_initial_register_value_register (v:variable_t) =
    (self#get_variable v)#get_initial_register_value_register

  method get_frozen_variable (v:variable_t) =
    (self#get_variable v)#get_frozen_variable

  method get_calltarget_value (v:variable_t) =
    (self#get_variable v)#get_calltarget_value

  method get_symbolic_value_expr (v:variable_t) =
    (self#get_variable v)#get_symbolic_value_expr
      
  method has_global_address (v:variable_t) =
    self#is_global_variable v
    && is_constant_offset (self#get_memvar_offset v)

  method get_global_sideeffect_target_address (v:variable_t) =
    (self#get_variable v)#get_global_sideeffect_target_address

  method get_external_variable_comparator =
    fun v1 v2 ->
      if v1#equal v2 then 0 else
	if v1#isTmp then 1 else if v2#isTmp then -1 else
	    let var1 = self#get_variable v1 in
	    let var2 = self#get_variable v2 in
	    match (var1#get_denotation, var2#get_denotation) with
            | (AuxiliaryVariable (SymbolicValue _), _) -> -1
            | (_, AuxiliaryVariable (SymbolicValue _)) -> 1
            | (AuxiliaryVariable (SignedSymbolicValue _), _) -> -1
            | (_, AuxiliaryVariable (SignedSymbolicValue _)) -> 1
	    | (AuxiliaryVariable (CallTargetValue _), _) -> -1
	    | (_, AuxiliaryVariable (CallTargetValue _)) -> 1
	    | (AuxiliaryVariable (InitialRegisterValue _), _) -> -1
	    | (_, AuxiliaryVariable (InitialRegisterValue _)) -> 1
	    | (AuxiliaryVariable (InitialMemoryValue _), _) -> -1
	    | (_, AuxiliaryVariable (InitialMemoryValue _)) -> 1
	    | (AuxiliaryVariable (FunctionPointer _), _) -> -1
	    | (_, AuxiliaryVariable (FunctionPointer _)) -> 1
	    | (AuxiliaryVariable (FieldValue _), _) -> -1
	    | (_, AuxiliaryVariable (FieldValue _)) -> 1
	    | (MemoryVariable _, _) 
		 when (let memref = self#get_memvar_reference v1 in
                       match memref#get_base with
                       | BGlobal -> true | _ -> false) -> -1
	    | (_, MemoryVariable (i1, _, _)) 
		 when (let memref = self#get_memvar_reference v2 in
                       match memref#get_base with
                       |BGlobal -> true | _ -> false) -> 1
	    | (AuxiliaryVariable (SideEffectValue _), _) -> -1
	    | (_, AuxiliaryVariable (SideEffectValue _)) -> 1
	    | (AuxiliaryVariable (RuntimeConstant _), _) -> -1
	    | (_, AuxiliaryVariable (RuntimeConstant _)) -> 1
	    | (MemoryVariable _, _) 
		 when (let memref =  self#get_memvar_reference v1 in
                       match memref#get_base with 
		  BGlobal -> true | _ -> false) -> -1
	    | (_, MemoryVariable _) 
		 when (let memref = self#get_memvar_reference v2 in
                       match memref#get_base with 
		  BGlobal -> true | _ -> false) -> 1
	    | (AuxiliaryVariable (FunctionReturnValue _), _) -> -1
	    | (_, AuxiliaryVariable (FunctionReturnValue _)) -> 1
            | (AuxiliaryVariable (SSARegisterValue _), _) -> -1
            | (_, AuxiliaryVariable (SSARegisterValue _)) -> 1
	    | (MemoryVariable _, MemoryVariable _) ->
	      begin
		let memref1 = self#get_memvar_reference v1 in
		let memref2 = self#get_memvar_reference v2 in
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
	      end
	    | (MemoryVariable _, _) ->
               let memref = self#get_memvar_reference v1 in
	       if memref#is_unknown_reference then 1 else -1
            | (_, MemoryVariable _) ->
               let memref = self#get_memvar_reference v2 in
	       if memref#is_unknown_reference then -1 else 1
	    | (RegisterVariable r1, RegisterVariable r2) -> register_compare r1 r2
	    | (RegisterVariable _, _) -> -1
	    | (_, RegisterVariable _) -> 1
	    | (AuxiliaryVariable (FrozenTestValue _), _) -> -1
	    | (_, AuxiliaryVariable (FrozenTestValue _)) -> 1
	    | (AuxiliaryVariable (BridgeVariable _), _) -> -1
	    | (_, AuxiliaryVariable (BridgeVariable _)) -> 1
	    | _ -> Stdlib.compare var1#index var2#index

  method is_stack_parameter_variable (v:variable_t) =
    (self#has_var v) && (self#has_memvar v)
    && (self#get_memvar_reference v)#is_stack_reference
    && is_constant_offset (self#get_memvar_offset v)
    && (get_total_constant_offset (self#get_memvar_offset v))#geq numerical_zero

  method is_realigned_stack_variable (v:variable_t) =
    (self#has_var v) && (self#has_memvar v)
    && (self#get_memvar_reference v)#is_realigned_stack_reference

  method is_function_initial_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_function_initial_value

  method is_local_variable (v:variable_t) =
    (self#has_var v) &&
      ((match (self#get_variable v)#get_denotation with
        | RegisterVariable _ | CPUFlagVariable _ -> true | _ -> false)
       ||
         ((self#has_memvar v) &&
           (self#get_memvar_reference v)#is_stack_reference))
      
  method is_global_variable (v:variable_t) =
    (self#has_var v) && (self#has_memvar v)  &&
      (self#get_memvar_reference v)#is_global_reference

  method is_register_variable (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_register_variable

  method is_mips_argument_variable (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_mips_argument_variable

  method is_arm_argument_variable (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_arm_argument_variable

  method is_stack_variable (v:variable_t) =
    (self#has_var v) && (self#has_memvar v) &&
      (self#get_memvar_reference v)#is_stack_reference

  method is_memory_variable (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_memory_variable

  method is_basevar_memory_variable (v:variable_t) =
    (self#has_var v) && (self#has_memvar v)
    && (self#get_memvar_reference v)#has_external_base

  method is_basevar_memory_value (v:variable_t) =
    (self#is_initial_memory_value v)
    && self#is_basevar_memory_variable (self#get_initial_memory_value_variable v)

  method get_memvar_basevar (v:variable_t) =
    if self#is_basevar_memory_variable v then
      (self#get_memvar_reference v)#get_external_base
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "variable does not have an external base: " ;
                v#toPretty ]))

  method get_memval_basevar (v:variable_t) =
    if self#is_basevar_memory_value v then
      self#get_memvar_basevar (self#get_initial_memory_value_variable v)
    else
      raise (BCH_failure
               (LBLOCK [
                    STR "variable is not an initial value of a basevar" ;
                    STR "memory variable";
                    v#toPretty]))

  method is_constant_offset (offset: memory_offset_t) =
    match offset with
    | NoOffset -> true
    | ConstantOffset (_, suboffset) -> self#is_constant_offset suboffset
    | IndexOffset (v, _, suboffset) ->
       (self#is_function_initial_value v)
       && self#is_constant_offset suboffset
    | _ -> false

  method is_numerical_offset (offset: memory_offset_t) =
    is_constant_offset offset

  method has_numerical_offset (v: variable_t) =
    if (self#has_var v) && (self#has_memvar v) then
      self#is_numerical_offset (self#get_memvar_offset v)
    else
      false

  method has_constant_offset (v: variable_t) =
    if (self#has_var v) && (self#has_memvar v) then
      self#is_constant_offset (self#get_memvar_offset v)
    else
      false

  method is_unknown_base_memory_variable (v:variable_t) =
    (self#has_var v) && (self#has_memvar v) && 
      (self#get_memvar_reference v)#is_unknown_reference

  method is_unknown_offset_memory_variable (v:variable_t) =
    (self#has_var v)
      && (match (self#get_variable v)#get_denotation with
          | MemoryVariable (_, s, o) -> is_unknown_offset o
          | _ -> false)

  method is_unknown_memory_variable (v:variable_t) =
    (self#is_unknown_base_memory_variable v)
    || (self#is_unknown_offset_memory_variable v)
      
  method is_frozen_test_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_frozen_test_value

  method is_ssa_register_value (v: variable_t) =
    (self#has_var v) && (self#get_variable v)#is_ssa_register_value

  method is_ssa_register_value_at (iaddr: ctxt_iaddress_t) (v: variable_t) =
    (self#has_var v) && ((self#get_variable v)#is_ssa_register_value_at iaddr)
      
  method is_initial_register_value (v:variable_t) = 
    (self#has_var v) && (self#get_variable v)#is_initial_register_value

  method is_initial_mips_argument_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_initial_mips_argument_value

  method is_initial_arm_argument_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_initial_arm_argument_value

  method is_initial_memory_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_initial_memory_value

  method is_initial_stackpointer_value (v:variable_t) =
    (self#has_var v)
    && (self#get_variable v)#is_initial_stackpointer_value

  method is_bridge_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_bridge_value

  method is_bridge_value_at (a:ctxt_iaddress_t) (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_bridge_value_at a

  method is_symbolic_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_symbolic_value

  method is_signed_symbolic_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_signed_symbolic_value

  method is_in_test_jump_range (a:ctxt_iaddress_t) (v:variable_t) =
    (self#has_var v) &&  (self#get_variable v)#is_in_test_jump_range a

  method is_return_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_return_value

  method is_sideeffect_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_sideeffect_value
      
  method is_special_variable (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_special_variable
      
  method is_runtime_constant (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_runtime_constant
      
  method is_function_pointer (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_function_pointer

  method is_calltarget_value (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_calltarget_value

  method is_global_sideeffect (v:variable_t) =
    (self#has_var v) && (self#get_variable v)#is_global_sideeffect

end


let make_variable_manager (optnode:xml_element_int option) =
  let xd = mk_xprdictionary () in
  let vard = mk_vardictionary xd in
  let memrefmgr = make_memory_reference_manager vard in
  new variable_manager_t optnode vard memrefmgr

