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
open CHCommon
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes
open XprXml
open XprToPretty
open Xsimplify

(* bchlib *)
open BCHApiParameter
open BCHBasicTypes
open BCHBTerm
open BCHCallTarget
open BCHCallTargetInfo
open BCHCPURegisters
open BCHConstantDefinitions
open BCHCppClass
open BCHCStruct
open BCHDoubleword
open BCHFunctionApi
open BCHFunctionData
open BCHFunctionSemantics
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHJavaSignatures
open BCHLibTypes
open BCHLocation
open BCHMemoryAccesses
open BCHMemoryReference
open BCHPreFileIO
open BCHSideeffect
open BCHSystemInfo
open BCHUtilities
open BCHVariable
open BCHVariableNames
open BCHVariableType
open BCHXmlUtil
open BCHXprUtil

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory
module P = Pervasives

module NumericalCollections = CHCollections.Make
  (struct
    type t = numerical_t
    let compare x y = x#compare y
    let toPretty n = n#toPretty
   end)

module DoublewordCollections = CHCollections.Make
  (struct
    type t = doubleword_int
    let compare dw1 dw2 = dw1#compare dw2
    let toPretty dw = STR dw#to_fixed_length_hex_string
   end)

module SideEffectCollections = CHCollections.Make
  (struct
    type t = sideeffect_t
    let compare = sideeffect_compare
    let toPretty = sideeffect_to_pretty
  end)

let bd = BCHDictionary.bdictionary
let id = BCHInterfaceDictionary.interface_dictionary

let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; INT node#getColumnNumber ; 
	     STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

let get_sorted_kv_list t f =
  let l = ref [] in
  let _ = H.iter (fun k v -> l := (k,v) :: !l) t in
  List.sort f !l


type po_anchor_t =                      (* proof obligation anchor *)
| DirectAccess
| IndirectAccess of bterm_t

let po_anchor_compare a1 a2 =
  match (a1,a2) with
    (DirectAccess, DirectAccess) -> 0
  | (DirectAccess, _) -> -1
  | (_, DirectAccess ) -> 1
  | (IndirectAccess n1, IndirectAccess n2) -> bterm_compare n1 n2
    
let po_anchor_to_pretty a =
  match a with
  | DirectAccess -> STR "direct"
  | IndirectAccess n -> LBLOCK [ STR "indirect ( " ; bterm_to_pretty n ; STR " )" ]


class type saved_register_int =
object ('a)
  
  method compare              : 'a -> int
    
  method set_save_address     : ctxt_iaddress_t -> unit
  method add_restore_address  : ctxt_iaddress_t -> unit
    
  method get_register         : register_t
  method get_save_address     : ctxt_iaddress_t
  method get_restore_addresses: ctxt_iaddress_t list
    
  method has_save_address     : bool
  method has_restore_addresses: bool
    
  method is_save_or_restore_address: ctxt_iaddress_t -> bool

  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end
	
class saved_register_t (reg:register_t) =
object (self:'a)
  val mutable save_address = None
  val restore_addresses = new StringCollections.set_t
    
  method compare (other:'a) = P.compare reg other#get_register
    
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
    
  method has_save_address = match save_address with Some _ -> true | _ -> false
    
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
      | l -> LBLOCK [ STR "restored: " ; 
		      pretty_print_list l (fun a -> STR a) "[" ", " "]" ] in
    LBLOCK [ STR (register_to_string reg) ; STR ". " ; pSaved ; STR "; " ; pRestored ]
      
end
  
module SavedRegistersCollections = CHCollections.Make 
  (struct
    type t = saved_register_int
    let compare r1 r2 = r1#compare r2
    let toPretty r = r#toPretty
   end)
  
let pr_expr = xpr_formatter#pr_expr
    
		
class function_environment_t
        (faddr:doubleword_int)
        (varmgr:variable_manager_int):function_environment_int =
object (self)
    
  val scope = LF.mkScope ()
  val virtual_calls = H.create 3
  val initial_call_target_values = H.create 3
  val initial_string_values = H.create 3

  initializer
    List.iter (fun av -> ignore (self#mk_variable av)) varmgr#get_assembly_variables

  method get_variable_comparator =  varmgr#get_external_variable_comparator

  (* ------------------------------------------------------ variable names -- *)

  val variable_names = make_variable_names ()

  method variable_names = variable_names

  method varmgr = varmgr

  method set_variable_name (v:variable_t) (name:string) =
    variable_names#add v#getName#getSeqNumber name

  method variable_name_to_string v =
    let index = v#getName#getSeqNumber in
    if variable_names#has index then variable_names#get index else v#getName#getBaseName

  method variable_name_to_pretty v = STR (self#variable_name_to_string v)

  method private set_pointedto_struct_field_names
                   (level:int) (v:variable_t) (vname:string) (ty:btype_t) =
    if level > 2 then () else
      let cstruct = get_pointedto_struct ty in
      let _ = chlog#add "c-struct field names" cstruct#toPretty in
      cstruct#iter (fun fld ->
          let memref = self#mk_base_variable_reference v in
          let fldvar = self#mk_memory_variable ~save_name:false memref (mkNumerical fld.fld_offset) in
          let fldname = vname ^ "->" ^ fld.fld_name in
          let fldtype = fld.fld_type in
          let ifldvar = self#mk_initial_memory_value fldvar in
          let ifldname = fldname ^  "_in" in
          let _ = chlog#add "set field var" (STR  fldname) in
          begin
	    self#set_variable_name fldvar fldname ;
            self#set_variable_name ifldvar ifldname ;
	    if is_ptrto_known_struct fldtype then 
	      self#set_pointedto_struct_field_names (level + 1) ifldvar fldname fldtype
          end)

  method set_java_native_method_signature (api:java_native_method_api_t) =
    let args = api.jnm_signature#descriptor#arguments in
    let isStatic = api.jnm_static in
    let jthis = if isStatic then "this$obj" else "this$class" in
    let stackPars = [  (8, jthis, t_voidptr) ; (4, "jni$Env", t_voidptr) ] in
    let (_,_,stackPars) = List.fold_left (fun (count,off,pars) ty ->
      let name = (get_java_type_name_prefix ty) ^ "_" ^ (string_of_int count) in
      (count+1, off + (get_java_type_length ty), 
       (off, name, (get_java_type_btype ty)) :: pars)) (3,12,stackPars) args in
    List.iter (fun (offset,name,ty) ->
      let memref = self#mk_local_stack_reference in
      let v = self#mk_memory_variable memref (mkNumerical offset) in
      let initV = self#mk_initial_memory_value v in
      begin
	self#set_variable_name initV name ;
        if offset = 4 then
	  let jniInterfacePtrRef = self#mk_base_variable_reference initV in
	  let jniInterfacePtr = self#mk_memory_variable jniInterfacePtrRef numerical_zero in
	  let jniInterfacePtrIn = self#mk_initial_memory_value jniInterfacePtr in
	  self#set_variable_name jniInterfacePtrIn "jni$Ifp"
      end ) stackPars	 

  method set_unknown_java_native_method_signature =
    let stackPars = [ (4, "jni$Env", t_voidptr) ] in
    List.iter (fun (offset,name,ty) ->
      let memref = self#mk_local_stack_reference in
      let v = self#mk_memory_variable memref (mkNumerical offset) in
      let initV = self#mk_initial_memory_value v in
      begin
	self#set_variable_name initV name ;
        if offset = 4 then
	  let jniInterfacePtrRef = self#mk_base_variable_reference initV in
	  let jniInterfacePtr = self#mk_memory_variable jniInterfacePtrRef numerical_zero in
	  let jniInterfacePtrIn = self#mk_initial_memory_value jniInterfacePtr in
	  self#set_variable_name jniInterfacePtrIn "jni$Ifp"
      end ) stackPars	 

  method set_argument_structconstant par sc =
    match par.apar_location with
    | StackParameter i ->
      let memref = self#mk_local_stack_reference  in
      let argvar = self#mk_memory_variable ~save_name:false memref (mkNumerical (4*i)) in
      let argvarin = self#mk_initial_memory_value argvar in
      begin
	match sc with 
	| FieldValues l ->
	  List.iter (fun (offset,ssc) ->
	      let mref = self#mk_base_variable_reference argvarin in
	      let mvar = self#mk_memory_variable mref (mkNumerical offset) in
	      let mvarin = self#mk_initial_memory_value mvar in
	      match ssc with
	      | FieldString s ->
		begin
		  H.add initial_string_values (argvarin#getName#getSeqNumber,offset) s ;
		  chlog#add "struct constant string"
		    (LBLOCK [ faddr#toPretty ; STR ": &" ; mvarin#toPretty ; STR " -- " ;
			      STR s ])
		end
	      | FieldCallTarget tgt ->
		begin
		  H.add initial_call_target_values mvarin#getName#getSeqNumber tgt ;
		  chlog#add "struct constant invariant"
		    (LBLOCK [ faddr#toPretty ; STR ": " ; mvarin#toPretty ; STR " -- " ; 
			      call_target_to_pretty tgt ])
		end
	      | FieldValues ll ->
		List.iter (fun (offset,ssc) ->
		  let mref = self#mk_base_variable_reference mvarin in
		  let mvar = self#mk_memory_variable mref (mkNumerical offset) in
		  let mvarin = self#mk_initial_memory_value mvar in
		  match ssc with
		  | FieldCallTarget tgt ->
		    begin
		      H.add initial_call_target_values mvarin#getName#getSeqNumber tgt ;
		      chlog#add "struct constant invariant"
			(LBLOCK [ faddr#toPretty ; STR ": " ; mvarin#toPretty ; STR " -- " ; 
				  call_target_to_pretty tgt ])
		    end
		  | _ -> ()) ll
	      | _ -> ()) l
	| _ -> ()
      end
    | _ -> ()

  method set_class_member_variable_names 
    (classinfos:(string * function_api_t * bool) list) =
    match classinfos with
    | [ (classname,api,isStatic) ] ->
       let stackParams =
         List.fold_left (fun a p ->
	     match p.apar_location with
             | StackParameter i -> (i,p.apar_name) :: a | _ -> a)
	[] api.fapi_parameters in
       let regParams =
         List.fold_left (fun a p ->
	     match p.apar_location with
             | RegisterParameter r -> (r,p.apar_name) :: a | _ -> a)
	[] api.fapi_parameters in
      let stackVars = List.map (fun (i,name) ->
	let memref = self#mk_local_stack_reference in
	let memvar =
          self#mk_memory_variable ~save_name:false memref (mkNumerical (i * 4)) in
	let memInitVar = self#mk_initial_memory_value memvar in
	(name,memInitVar)) stackParams in
      let regVars = List.map (fun (r,name) ->
	let regInitVar = self#mk_initial_register_value ~level:0 r in
	(name,regInitVar)) regParams in
      let paramVars = stackVars @ regVars in
      let _ = List.iter (fun (name,v) -> self#set_variable_name v name) paramVars in
      if isStatic then () else
      let (_,thisVar) = 
	try List.find (fun (name,_) -> name = "this") paramVars with Not_found ->
	  raise
            (BCH_failure
               (LBLOCK [ STR "No this variable found in function " ;
			 faddr#toPretty ; STR " in class " ;
			 STR classname ])) in
      let cppClass = get_cpp_class classname in
      let add_dm_class_members (ty:btype_t) (basevar:variable_t) =
	if is_class_type ty then
	  let _= chlog#add "member class type" 
	    (LBLOCK [ basevar#toPretty ; STR ": " ; STR (btype_to_string ty) ]) in
	  let cls = get_class_from_type ty in
	  begin
	    cls#dm_iter (fun dm ->
	      let memref = self#mk_base_variable_reference basevar in
	      let memberVar =
                self#mk_memory_variable
                  ~save_name:false memref (mkNumerical dm.cppdm_offset) in
	      let memberInitVar = self#mk_initial_memory_value memberVar in
	      let mName = self#variable_name_to_string basevar in
	      let name = mName ^ "->" ^ dm.cppdm_name in
	      self#set_variable_name memberInitVar name ) ;
	    cls#vf_iter (fun vf ->
	      let memref = self#mk_base_variable_reference basevar in
	      let vfptrVar =
                self#mk_memory_variable
                  ~save_name:false memref (mkNumerical vf.cppvf_offset) in
	      let vfptrInitVar = self#mk_initial_memory_value vfptrVar in
	      let mName = self#variable_name_to_string basevar in
	      let vfptrName = mName ^ "->vtableptr" in
	      let vfsummaries = get_vtable_summaries vf.cppvf_table in
	      begin
		List.iter (fun (vfOffset,summary) ->
		  let vfmemref = self#mk_base_variable_reference vfptrInitVar in
		  let vfVar =
                    self#mk_memory_variable
                      ~save_name:false vfmemref (mkNumerical vfOffset) in
		  let vfInitVar = self#mk_initial_memory_value vfVar in
		  self#register_virtual_call vfInitVar summary) vfsummaries ;
		self#set_variable_name vfptrInitVar vfptrName
	      end)
	  end
	else
	  () in
      begin
	cppClass#dm_iter (fun dm ->
	  let memref = self#mk_base_variable_reference thisVar in
	  let memberVar =
            self#mk_memory_variable
              ~save_name:false memref (mkNumerical dm.cppdm_offset) in
	  let memberInitVar = self#mk_initial_memory_value memberVar in
	  let name = "this->" ^ dm.cppdm_name in
	  begin
	    self#set_variable_name memberInitVar name ;
	    add_dm_class_members dm.cppdm_type memberInitVar
	  end) ;
	cppClass#vf_iter (fun vf ->
	  let memref = self#mk_base_variable_reference thisVar in
	  let vfptrVar =
            self#mk_memory_variable
              ~save_name:false memref (mkNumerical vf.cppvf_offset) in
	  let vfptrInitVar = self#mk_initial_memory_value vfptrVar in
	  let vfptrVarName = "this->" ^ "vtableptr" in
	  let vfsummaries = get_vtable_summaries vf.cppvf_table in
	  begin
	    List.iter (fun (vfOffset,summary) ->
	      let vfmemref = self#mk_base_variable_reference vfptrInitVar in
	      let vfVar =
                self#mk_memory_variable
                  ~save_name:false vfmemref (mkNumerical vfOffset) in
	      let vfInitVar = self#mk_initial_memory_value vfVar in
	      self#register_virtual_call vfInitVar summary) vfsummaries ;
	    self#set_variable_name vfptrInitVar vfptrVarName 
	  end)
      end
    | _ ->
      ch_error_log#add "class info ignored"
	(LBLOCK [ faddr#toPretty ; STR ". Class-infos: " ; 
		  pretty_print_list (List.map (fun (c,_,_) -> c) classinfos) (fun s -> STR s) 
		                    "[" ", " "]" ])

  method set_argument_names (faddr:doubleword_int) (api:function_api_t) =
    let pars = api.fapi_parameters in
    let stackPars = List.fold_left (fun acc p ->
      match p.apar_location with
      | StackParameter i -> (i, p.apar_name,p.apar_type) :: acc | _ -> acc) [] pars in
    let regPars = List.fold_left (fun acc p ->
      match p.apar_location with
      | RegisterParameter reg -> 
	(reg, p.apar_name,p.apar_type) :: acc | _ -> acc) [] pars in
    begin
      List.iter (fun (offset,name,ty) ->
	let memref = self#mk_local_stack_reference  in
	let v =
          self#mk_memory_variable
            ~save_name:false memref (mkNumerical (4*offset)) in
        let iv = self#mk_initial_memory_value v in
	let vname = name ^ "$" ^ (string_of_int offset) in
	begin
	  self#set_variable_name iv vname ;
	  if is_ptrto_known_struct ty then 
	    self#set_pointedto_struct_field_names 1 iv vname ty
	end) stackPars ;
      List.iter (fun (reg,name,ty) ->
	let v = self#mk_initial_register_value ~level:0 reg in
	let vname = name ^ "$R" in
	begin
	  self#set_variable_name v vname ;
	  if is_ptrto_known_struct ty then 
	    self#set_pointedto_struct_field_names 1 v vname ty
	end) regPars 
    end
    

  (* --------------------------------------------------- memory references -- *)

  method mk_unknown_memory_reference = 
    varmgr#memrefmgr#mk_unknown_reference

  method mk_local_stack_reference = 
      varmgr#memrefmgr#mk_local_stack_reference

  method mk_realigned_stack_reference = 
      varmgr#memrefmgr#mk_realigned_stack_reference

  method mk_base_variable_reference (v:variable_t) =
    varmgr#make_memref_from_basevar v

  method mk_base_sym_reference (s:symbol_t) =
    self#mk_base_variable_reference (self#get_variable s#getSeqNumber)

  (* --------------------------------------------------- program variables -- *)

  val chifvars = H.create 5

  method private add_chifvar (v:assembly_variable_int) (vt:variable_type_t) =
    if H.mem chifvars v#index then
      H.find chifvars v#index
    else
      let vname = new symbol_t ~seqnr:v#index v#get_name in
      let chifvar = scope#mkVariable vname vt in
      begin
        H.add chifvars v#index chifvar ;
        chifvar
      end

  method private mk_variable (v:assembly_variable_int) = self#add_chifvar v NUM_VAR_TYPE

  method private has_chifvar index = H.mem chifvars index

  method get_variables = H.fold (fun _ v a -> v::a) chifvars []

  method get_variable (index:int) = 
    if H.mem chifvars index then H.find chifvars index else
      raise  (BCH_failure (LBLOCK [ STR "Variable not found: " ; INT index ;
                                    STR "; variables: " ;
                                    pretty_print_list self#get_variables
             (fun v -> v#toPretty) " [" "," "]" ]))


  (* -------------------------------------------------------- transactions -- *)

  val mutable in_transaction = false
  val mutable constant_table = new NumericalCollections.table_t

  method get_scope = scope
    
  method start_transaction = 
    begin
      scope#startTransaction ;
      in_transaction <- true
    end
      
  method end_transaction =
    let constant_assignments =
      constant_table#fold (fun a num tmp -> (ASSIGN_NUM (tmp, NUM num)) :: a) [] in
    begin
      scope#endTransaction ;
      in_transaction <- false ;
      constant_table <- new NumericalCollections.table_t ;
      List.rev constant_assignments
    end
      
  method mk_num_temp = 
    if in_transaction then
      scope#requestNumTmpVariable
    else
      let _ = scope#startTransaction in
      let v = scope#requestNumTmpVariable in
      let _ = scope#endTransaction in
      v
       	
  method mk_sym_temp = scope#requestSymTmpVariable

  method private mk_temp (t:variable_type_t):variable_t =
    if in_transaction then
      if is_numerical_type t then self#mk_num_temp else self#mk_sym_temp
    else
      let _ = self#start_transaction in
      let tmp = if is_numerical_type t then self#mk_num_temp else self#mk_sym_temp in
      let _ = self#end_transaction in
      tmp
      
  method request_num_constant (constant:numerical_t) =
    match constant_table#get constant with
    | Some v -> v
    | _ ->
       let tmp = self#mk_num_temp in 
       begin constant_table#set constant tmp ; tmp end

  (* ------------------------------------------------ create new variables -- *)

  method mk_unknown_memory_variable (s:string) =
    self#mk_variable
      (varmgr#make_memory_variable (self#mk_unknown_memory_reference s) NoOffset)

  method mk_memory_variable
           ?(save_name=true)
           (memref:memory_reference_int)
           (offset:numerical_t) =
    if memref#is_unknown_reference then
      self#mk_num_temp
    else
      let optName = match memref#get_base with
        | BaseVar v when variable_names#has v#getName#getSeqNumber -> 
	   Some (variable_names#get v#getName#getSeqNumber)
        | _ -> None in
      let offset = ConstantOffset (offset,NoOffset) in
      let avar = varmgr#make_memory_variable memref offset in
      let v = self#mk_variable avar in
      let _ = match optName with
	  Some name -> 
	  let name = name ^ (memory_offset_to_string offset) in
	  if save_name && (not (variable_names#has v#getName#getSeqNumber)) then 
	    self#set_variable_name v name 
	  else ()
        | _ -> () in
      v

  method mk_global_variable (offset:numerical_t) =
    self#mk_variable (varmgr#make_global_variable offset)
    
  method mk_register_variable (register:register_t) =
    self#mk_variable (varmgr#make_register_variable register)
      
  method mk_flag_variable (flag:eflag_t) =
    self#mk_variable (varmgr#make_flag_variable flag)
      
  method mk_cpu_register_variable (cpureg:cpureg_t) = 
    self#mk_register_variable (CPURegister cpureg)

  method mk_fpu_register_variable (reg:int) =
    self#mk_register_variable (FloatingPointRegister reg)
      
  method mk_mmx_register_variable (reg:int) =
    self#mk_register_variable (MmxRegister reg)
      
  method mk_xmm_register_variable (reg:int) =
    self#mk_register_variable (XmmRegister reg)

  method mk_control_register_variable (reg:int) =
    self#mk_register_variable (ControlRegister reg)

  method mk_debug_register_variable (reg:int) =
    self#mk_register_variable (DebugRegister reg)
      
  method mk_double_register_variable (reg1:cpureg_t) (reg2:cpureg_t) =
    self#mk_register_variable (DoubleRegister (reg1, reg2))

  method mk_mips_register_variable (reg:mips_reg_t) =
    self#mk_register_variable (MIPSRegister reg)

  method mk_mips_special_register_variable (reg:mips_special_reg_t) =
    self#mk_register_variable (MIPSSpecialRegister reg)

  method mk_mips_fp_register_variable (index:int) =
    self#mk_register_variable (MIPSFloatingPointRegister index)

  method mk_arm_register_variable (reg:arm_reg_t) =
    self#mk_register_variable (ARMRegister reg)

  method mk_bridge_value (address:ctxt_iaddress_t) (argnr:int) =
    self#mk_variable (varmgr#make_bridge_value address argnr)
      
  method mk_frozen_test_value 
    (var:variable_t) (taddr:ctxt_iaddress_t) (jaddr:ctxt_iaddress_t) =
    self#mk_variable (varmgr#make_frozen_test_value var taddr jaddr)
      
  method mk_special_variable (name:string) =
    self#mk_variable (varmgr#make_special_variable name)
      
  method mk_runtime_constant (name:string) =
    self#mk_variable (varmgr#make_runtime_constant name)
      
  method mk_return_value (address:ctxt_iaddress_t) =
    self#mk_variable (varmgr#make_return_value address)
      
  method mk_function_pointer_value
    (fname:string) (cname:string) (address:ctxt_iaddress_t) =
    self#mk_variable (varmgr#make_function_pointer_value fname cname address)

  method mk_calltarget_value (tgt:call_target_t) =
    self#mk_variable (varmgr#make_calltarget_value tgt)
      
  method mk_side_effect_value (iaddr:ctxt_iaddress_t) ?(global=false) (arg:string) =
    self#mk_variable (varmgr#make_side_effect_value iaddr ~global arg)

  method mk_field_value (sname:string) (offset:int) (fname:string) =
    self#mk_variable (varmgr#make_field_value sname offset fname)

  method mk_symbolic_value (x:xpr_t) =
    self#mk_variable (varmgr#make_symbolic_value x)

  method mk_signed_symbolic_value (x: xpr_t) (s0: int) (sx: int) =
    self#mk_variable (varmgr#make_signed_symbolic_value x s0 sx)

  method private probe_global_var_field_values (v:variable_t) (iv:variable_t) =
    let addr = varmgr#get_global_variable_address v in
    if has_symbolic_address_name addr then
      let vname = get_symbolic_address_name addr in
      let btype = get_symbolic_address_type addr in
      let _ = self#set_variable_name v vname in
      let _ = self#set_variable_name iv (vname ^ "_in") in
      if is_ptrto_known_struct btype then
        self#set_pointedto_struct_field_names 1 iv vname btype

  method mk_initial_memory_value (v:variable_t):variable_t =
    if (self#is_memory_variable v) && (self#has_constant_offset v) then
      let iv = self#mk_variable (varmgr#make_initial_memory_value v) in
      let _ =
        if varmgr#is_global_variable v then
          self#probe_global_var_field_values v iv in
      iv        
    else
      begin
	ch_error_log#add "function environment"
	  (LBLOCK [ STR "variable is not suitable for initial memory variable: " ; 
		    v#toPretty ; STR " (" ; faddr#toPretty ; STR ")" ]) ;
	raise (BCH_failure 
		 (LBLOCK [ STR "variable is not suitable for initial memory variable: " ;
			   v#toPretty ]))
      end

  method mk_initial_register_value ?(level=0) (r:register_t) = 
    self#mk_variable (varmgr#make_initial_register_value r level)
      

  (* -------------------------------------------- accessors and predicates -- *)
								       
  method has_initialized_call_target_value (v:variable_t) = 
    H.mem initial_call_target_values v#getName#getSeqNumber

  method get_initialized_call_target_value (v:variable_t) =
    let index = v#getName#getSeqNumber in
    if H.mem initial_call_target_values index then
      H.find initial_call_target_values index
    else
      raise (BCH_failure (LBLOCK [ STR "initialized call target value not found for " ; 
				   v#toPretty ; STR " in " ; faddr#toPretty ]))

  method has_initialized_string_value (v:variable_t) (offset:int) =
    H.mem initial_string_values (v#getName#getSeqNumber,offset)

  method get_initialized_string_value (v:variable_t) (offset:int) =
    let index = v#getName#getSeqNumber in
    if H.mem initial_string_values (index,offset) then
      H.find initial_string_values (index,offset)
    else
      raise (BCH_failure (LBLOCK [ STR "initialized string value not found for " ;
				   v#toPretty ; STR " at offset " ; INT offset ; 
				   STR " in " ; faddr#toPretty ]))


  method private register_virtual_call (v:variable_t) (s:function_api_t) =
    let _ = chlog#add "register virtual call"
      (LBLOCK [ faddr#toPretty ; STR ": " ; v#toPretty ; STR ": " ; 
		STR s.fapi_name ]) in
    H.add virtual_calls v#getName#getSeqNumber s

  method is_virtual_call (v:variable_t) = H.mem virtual_calls v#getName#getSeqNumber

  method get_virtual_target (v:variable_t) =
    try
      H.find virtual_calls v#getName#getSeqNumber
    with
      Not_found ->
	raise (BCH_failure (LBLOCK [ STR "No virtual target found for " ; v#toPretty ]))
      
  method get_frozen_variable (variable:variable_t) =
    varmgr#get_frozen_variable variable 
      
  method private get_register_variables =
    List.filter varmgr#is_register_variable self#get_variables
      
  method private get_function_pointers =
    List.filter varmgr#is_function_pointer self#get_variables

  method private get_side_effect_variables =
    List.filter self#is_sideeffect_value_derivative self#get_variables
      
  method get_local_variables =
    let is_local v = 
      varmgr#is_local_variable v && varmgr#is_stack_variable v in
    List.filter is_local self#get_variables

  method get_external_memory_variables =
    let is_external v =
      self#is_memory_variable v
      && (not (self#is_unknown_memory_variable v))
      && ((not (self#is_local_variable v))
          || (self#is_stack_parameter_variable v)) in
    List.filter is_external self#get_variables
      
  method get_bridge_values_at (callsite:ctxt_iaddress_t) =
    List.filter (self#is_bridge_value_at callsite) self#get_variables

  method get_local_stack_variables =
    let is_local v = varmgr#is_local_variable v && varmgr#is_stack_variable v in
    List.filter is_local self#get_variables

  method get_parent_stack_variables = 
    List.filter varmgr#is_stack_parameter_variable self#get_variables

  method get_mips_argument_values =
    List.filter varmgr#is_initial_mips_argument_value self#get_variables

  method get_arm_argument_values =
    List.filter varmgr#is_initial_arm_argument_value self#get_variables

  method get_realigned_stack_variables = 
    List.filter varmgr#is_realigned_stack_variable self#get_variables

  method get_stack_parameter_index (v:variable_t) =
    try
      if self#is_initial_memory_value v then
        let iv = varmgr#get_initial_memory_value_variable v in
        varmgr#get_stack_parameter_index iv
      else
        varmgr#get_stack_parameter_index v
    with
    | BCH_failure p ->
       raise (BCH_failure (LBLOCK [ STR "Finfo:get-stack-parameter-index: " ; p ]))

  method get_memvar_basevar (v:variable_t) = varmgr#get_memvar_basevar v

  method get_memval_basevar (v:variable_t) = varmgr#get_memval_basevar v

  method get_memvar_offset (v:variable_t) = varmgr#get_memvar_offset v

  method get_memval_offset (v:variable_t) = varmgr#get_memval_offset v

  method get_constant_offsets (v:variable_t) =
    let offset =
      if self#is_initial_memory_value v then
        self#get_memval_offset v
      else if self#is_memory_variable v then
        self#get_memvar_offset v
      else
        raise (BCH_failure (LBLOCK [ STR "Not a memory variable: " ; v#toPretty ])) in
    if is_constant_offset offset then
      Some (get_constant_offsets offset)
    else
      None

  method get_total_constant_offset (v:variable_t) =
    match self#get_constant_offsets v with
    | Some l -> Some (List.fold_left (fun acc n -> acc#add n) numerical_zero l)
    | _ -> None

  method get_calltarget_value = varmgr#get_calltarget_value

  method get_register = varmgr#get_register

  method get_pointed_to_function_name = varmgr#get_pointed_to_function_name 

  method get_call_site = varmgr#get_call_site

  method get_se_argument_descriptor = varmgr#get_se_argument_descriptor

  method get_global_sideeffect_target_address =
    varmgr#get_global_sideeffect_target_address

  method is_global_sideeffect = varmgr#is_global_sideeffect

  method get_var_count = List.length self#get_variables

  method get_globalvar_count = 
    List.length (List.filter self#is_global_variable self#get_variables)

  method get_argvar_count =
    List.length (List.filter self#is_arg_deref_var self#get_variables)

  method get_returnvar_count =
    List.length (List.filter self#is_return_value self#get_variables)

  method get_sideeffvar_count =
    List.length (List.filter self#is_sideeffect_value self#get_variables)

  method is_global_variable (v:variable_t) = 
    (varmgr#is_global_variable v) ||
      ((varmgr#is_initial_memory_value v) &&
	  (let iv = varmgr#get_initial_memory_value_variable v in
	  self#is_global_variable iv))

  method get_global_variable_address (v:variable_t) =
    if varmgr#is_global_variable v then
      varmgr#get_global_variable_address v
    else if varmgr#is_initial_memory_value v then
      self#get_global_variable_address (varmgr#get_initial_memory_value_variable v)
    else
      begin
	ch_error_log#add "function environment"
	  (LBLOCK [ STR "variable is not a global variable: " ; v#toPretty ]) ;
	raise (BCH_failure 
		 (LBLOCK [ STR "variable is not a global variable: " ; v#toPretty ]))
      end

  method is_local_variable = varmgr#is_local_variable

  method is_function_pointer = varmgr#is_function_pointer

  method is_bridge_value = varmgr#is_bridge_value

  method is_bridge_value_at = varmgr#is_bridge_value_at

  method is_memory_variable = varmgr#is_memory_variable

  method is_basevar_memory_variable = varmgr#is_basevar_memory_variable

  method is_basevar_memory_value = varmgr#is_basevar_memory_value

  method is_calltarget_value = varmgr#is_calltarget_value

  method has_constant_offset (v:variable_t) = varmgr#has_constant_offset v

  method is_unknown_memory_variable = varmgr#is_unknown_memory_variable

  method is_unknown_base_memory_variable =
    varmgr#is_unknown_base_memory_variable

  method is_unknown_offset_memory_variable =
    varmgr#is_unknown_offset_memory_variable

  method get_memory_reference (v:variable_t) = 
    if self#is_initial_memory_value v then
      let iv = varmgr#get_initial_memory_value_variable v in
      varmgr#get_memvar_reference iv
    else
      varmgr#get_memvar_reference v

  method is_stack_variable = varmgr#is_stack_variable

  method is_initial_stackpointer_value (v:variable_t) =
    varmgr#is_initial_stackpointer_value v

  method is_stack_parameter_variable (v:variable_t) =
    (varmgr#is_stack_parameter_variable v)

  method is_stack_parameter_value (v:variable_t) =
    ((self#is_initial_memory_value v) &&
       (let iv = varmgr#get_initial_memory_value_variable v in
	self#is_stack_parameter_variable iv))

  method is_stackarg_deref_var (v:variable_t) =
    (self#is_basevar_memory_variable v)
    && (let base = self#get_memvar_basevar v in
        (self#is_stackarg_deref_val base)
        || (self#is_stack_parameter_value base))

  method is_stackarg_deref_val (v:variable_t) =
    (self#is_basevar_memory_value v)
    && (let initvar = self#get_init_value_variable v in
        self#is_stackarg_deref_var initvar)

  method is_regarg_deref_var (v:variable_t) =
    (self#is_basevar_memory_variable v)
    && (let base = self#get_memvar_basevar v in
        (self#is_regarg_deref_val base)
        || (self#is_initial_register_value base))

  method is_regarg_deref_val (v:variable_t) =
    (self#is_basevar_memory_value v)
    && (let initvar = self#get_init_value_variable v in
        self#is_regarg_deref_var initvar)

  method is_arg_deref_var (v:variable_t) =
    self#is_stackarg_deref_var v || self#is_regarg_deref_var v

  method is_arg_deref_val (v:variable_t) =
    self#is_stackarg_deref_val v || self#is_regarg_deref_val v

  method get_regarg_deref_var_register (v:variable_t) =
    if self#is_regarg_deref_var v then
      let base = self#get_memvar_basevar v in
      if self#is_initial_register_value base then
        self#get_initial_register_value_register base
      else
        self#get_regarg_deref_val_register base
    else
      raise (BCH_failure
               (LBLOCK [ STR "variable is not a register arg deref variable: " ;
                         v#toPretty ]))

  method get_regarg_deref_val_register (v:variable_t) =
    if self#is_regarg_deref_val v then
      let initvar = self#get_init_value_variable v in
      self#get_regarg_deref_var_register initvar
    else
      raise (BCH_failure
               (LBLOCK [ STR "variable is nnot a register arg deref value: " ;
                         v#toPretty ]))

  method private get_argbasevar_with_offsets_aux
                   (v:variable_t) (offsets:numerical_t list) =
    if self#is_initial_memory_value v then
      let iv = varmgr#get_initial_memory_value_variable v in
      if self#is_basevar_memory_variable iv then
        let basevar = self#get_memvar_basevar iv in
        match self#get_total_constant_offset iv with
        | Some o ->
           let newoffsets = o :: offsets in
          if self#is_stack_parameter_variable basevar ||
               self#is_initial_register_value basevar then
            Some (basevar,newoffsets)
          else
            self#get_argbasevar_with_offsets_aux basevar newoffsets
        | _ -> None
      else
        None
    else
      None

  method get_argbasevar_with_offsets (v:variable_t) =
    self#get_argbasevar_with_offsets_aux v []

  method private get_globalbasevar_with_offsets_aux
                   (v:variable_t) (offsets:numerical_t list) =
    if self#is_initial_memory_value v then
      let iv = varmgr#get_initial_memory_value_variable v in
      if self#is_basevar_memory_variable iv then
        let basevar = self#get_memvar_basevar iv in
        match self#get_total_constant_offset iv with
        | Some o ->
           let newoffsets = o :: offsets in
           if self#is_global_variable basevar then
             Some (basevar, newoffsets)
           else
             self#get_globalbasevar_with_offsets_aux basevar newoffsets
        | _ -> None
      else
        None
    else
      None

  method get_globalbasevar_with_offsets (v:variable_t) =
    self#get_globalbasevar_with_offsets_aux v []

  method is_return_value = varmgr#is_return_value

  method is_return_value_derivative (v:variable_t) =
    (self#is_return_value v) ||
      ((self#is_initial_memory_value v) &&
	  (let iv = varmgr#get_initial_memory_value_variable v in
	   ((self#is_memory_variable iv) &&
	       (let memref = varmgr#get_memvar_reference iv in
		memref#has_external_base &&
		  (self#is_return_value_derivative memref#get_external_base)))))

  method is_sideeffect_value = varmgr#is_sideeffect_value

  method is_sideeffect_value_derivative (v:variable_t) =
    (self#is_sideeffect_value v) ||
      ((self#is_initial_memory_value v) &&
	  (let iv = varmgr#get_initial_memory_value_variable v in
	   ((self#is_memory_variable iv) &&
	       (let memref = varmgr#get_memvar_reference iv in
		memref#has_external_base &&
		  (self#is_sideeffect_value_derivative memref#get_external_base)))))

  method is_register_variable = varmgr#is_register_variable

  method is_initial_register_value = varmgr#is_initial_register_value

  method is_initial_mips_argument_value = varmgr#is_initial_mips_argument_value

  method is_initial_arm_argument_value = varmgr#is_initial_arm_argument_value

  method is_function_initial_value = varmgr#is_function_initial_value

  method is_initial_memory_value = varmgr#is_initial_memory_value 

  method is_initial_value (v:variable_t) = 
    self#is_initial_memory_value v || self#is_initial_register_value v

  method get_init_value_variable (v:variable_t) =
    if self#is_initial_memory_value v then
      varmgr#get_initial_memory_value_variable v
    else if self#is_initial_register_value v then
      match self#get_initial_register_value_register v with
      | CPURegister r -> self#mk_cpu_register_variable r
      | MIPSRegister r -> self#mk_mips_register_variable r
      | ARMRegister r -> self#mk_arm_register_variable r
      | _ ->
         let msg = LBLOCK [ STR "Variable is not a cpu or mips register: " ;
                            v#toPretty ] in
         begin
           ch_error_log#add "function environment" msg ;
           raise (BCH_failure msg)
         end           
    else
      let msg = LBLOCK [ STR "Variable is not an initial value variable: " ;
                         v#toPretty ] in
      begin
	ch_error_log#add "function environment" msg ;
	raise (BCH_failure msg)
      end
      
  method get_initial_register_value_register (v:variable_t) =
    varmgr#get_initial_register_value_register v

  method is_frozen_test_value = varmgr#is_frozen_test_value

  method is_symbolic_value = varmgr#is_symbolic_value

  method is_signed_symbolic_value = varmgr#is_signed_symbolic_value

  method get_symbolic_value_expr v =
    if self#is_symbolic_value v then
      varmgr#get_symbolic_value_expr v
    else
      let msg =  LBLOCK [ STR "Variable is not a symbolic value expr: " ;
                          v#toPretty ] in
      begin
        ch_error_log#add "function environment" msg ;
        raise (BCH_failure msg)
      end

  method is_in_test_jump_range (v:variable_t) (a:ctxt_iaddress_t) =
    (not v#isTmp) && (varmgr#is_in_test_jump_range a v)

  method is_unknown_reference = varmgr#memrefmgr#is_unknown_reference

  method private write_xml_assembly_variable_id (node:xml_element_int) (v:assembly_variable_int) =
    begin
      node#setAttribute "vn" v#get_name ;
      node#setIntAttribute "vx" v#index
    end

end

class function_info_t 
        (faddr:doubleword_int)
        (varmgr:variable_manager_int)
        (invio:invariant_io_int)
        (tinvio:type_invariant_io_int):function_info_int = 
object (self)
  
  val env = new function_environment_t faddr varmgr
  val constant_table = new VariableCollections.table_t
  val calltargets = H.create 5       (* ctxt_iaddress_t -> call_target_info_int *)
  val jump_targets = H.create 5  
  val mutable base_pointers = new VariableCollections.set_t 
  val memory_access_record = make_memory_access_record ()

  val instrbytes = H.create 5

  val mutable stack_adjustment = None  (* number of bytes this function pops off the stack
				          when it returns *)
  val mutable complete = true
  val saved_registers = H.create 3      (* str(register) -> saved_register_int *)
  val return_values = H.create 3
  val sideeffects = new SideEffectCollections.set_t

  val mutable user_summary = None
  val mutable nonreturning = false
  val api_parameters = H.create 3

  val cc_user_to_setter = H.create 3
  val cc_setter_to_user = H.create 3
  val test_expressions = H.create 3
  val test_variables   = H.create 3

  val mutable dynlib_stub = None                (* call_target_t option *)
  val mutable sideeffects_changed = false
  val mutable call_targets_set = false

  method set_instruction_bytes (ia:ctxt_iaddress_t) (b:string) =
    H.add instrbytes ia b

  method get_instruction_bytes (ia:ctxt_iaddress_t) =
    if H.mem instrbytes ia then
      H.find instrbytes ia
    else
      raise
        (BCH_failure
           (LBLOCK [ STR "No instruction bytes found for " ;
                     STR ia ; STR " in function " ;
                     faddr#toPretty ]))

  method set_dynlib_stub (t:call_target_t) = dynlib_stub <- Some t

  method is_dynlib_stub = match dynlib_stub with Some _ -> true | _ -> false

  method get_dynlib_stub:call_target_t =
    match dynlib_stub with
    | Some t -> t
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Function is not known to be dynamic library stub" ]))

  method sideeffects_changed = sideeffects_changed

  method call_targets_were_set = call_targets_set

  val nonreturning_calls = new StringCollections.set_t 

  val mutable invariants_to_be_reset = false
    
  method get_address = faddr
  method a = faddr
  method env = env
  method finv = invio  
  method ftinv = tinvio
               
  method iinv (iaddr:ctxt_iaddress_t) =
    invio#get_location_invariant iaddr

  method itinv (iaddr:ctxt_iaddress_t) =
    tinvio#get_location_type_invariant iaddr

  method reset_invariants =
    if invariants_to_be_reset then
      begin
	invio#reset ;
	chlog#add "reset invariants" (STR faddr#to_hex_string) ;
      end

  method schedule_invariant_reset = invariants_to_be_reset <- true

  method were_invariants_reset = invariants_to_be_reset      

  method get_name = 
    if functions_data#has_function_name self#get_address then 
      (functions_data#get_function self#get_address)#get_function_name
    else
      self#get_address#to_hex_string

  method get_memory_access_record = memory_access_record

  method get_local_stack_accesses = []

  method get_stack_accesses = []

  method get_global_accesses =  []

  method set_incomplete = complete <- false
  method set_complete = complete <- true
  method is_complete = complete
    
  method set_stack_adjustment (a:int option) =
    let _ =
      match a with
      | Some n when n > 0 ->
         chlog#add
           "set stack adjustment"
           (LBLOCK [ self#get_address#toPretty ; STR ": " ; INT n  ])
      | _ -> () in
    stack_adjustment <- a
      
  method get_stack_adjustment = stack_adjustment
    
  method add_constant (v:variable_t) (c:numerical_t) = constant_table#set v c
                                                     
  method has_constant (v:variable_t) = 
    match constant_table#get v with Some _ -> true | _ -> false
                                                        
  method get_constant (v:variable_t) =
    match constant_table#get v with
      Some c -> c
    | _ -> raise (Invocation_error "function_info#get_constant")
            
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * record register arguments                                                            *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method save_register (iaddr:ctxt_iaddress_t) (reg:register_t) =
    let regstr = register_to_string reg in
    if H.mem saved_registers regstr then
      (H.find saved_registers regstr)#set_save_address iaddr
    else
      let savedReg = new saved_register_t reg in
      begin
	savedReg#set_save_address iaddr ;
	H.add saved_registers regstr savedReg
      end
	
  method restore_register (iaddr:ctxt_iaddress_t) (reg:register_t) =
    let regstr = register_to_string reg in
    if H.mem saved_registers regstr then
      (H.find saved_registers regstr)#add_restore_address iaddr
    else
      let savedReg = new saved_register_t reg in
      begin
	savedReg#add_restore_address iaddr ;
	H.add saved_registers regstr savedReg
      end

  method saved_registers_to_pretty =
    let p = ref [] in
    let _ =
      H.iter (fun _ s -> p := (LBLOCK [ s#toPretty ; NL ]) :: !p) saved_registers in
    match !p with
      [] ->
      LBLOCK [ STR (string_repeat "~" 80) ; NL ; STR "No saved registers" ; NL ;
	       STR (string_repeat "~" 80) ; NL ]
    | l ->
       LBLOCK [ STR "Saved Registers" ; NL ; STR (string_repeat "~" 80) ; NL ;
                LBLOCK l ; NL ;
		STR (string_repeat "~" 80) ; NL]
      
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * record return values                                                                 *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
    
  method record_return_value (iaddr:ctxt_iaddress_t) (x:xpr_t) =
    H.replace return_values iaddr x
      
  method get_return_values = H.fold (fun _ x a -> x :: a) return_values []
    
  method return_values_to_pretty =
    let p = ref [] in
    let _ = H.iter (fun iaddr x ->
      let pp = LBLOCK [ STR iaddr ; STR ": " ; pr_expr x ; NL ] in
      p := pp :: !p ) return_values in
    LBLOCK [ STR "Return values: (" ; INT (H.length return_values) ; STR ")" ; NL ;
	     INDENT (3, LBLOCK !p) ; NL ]									 
      
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * record side effects                                                                  *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
    
  method record_sideeffect (s:sideeffect_t) = 
    if sideeffects#has s then () else
      begin 
	sideeffects#add s ; 
	(match s with
	| UnknownSideeffect -> ()
	| _ -> 
	  begin
	    sideeffects_changed <- true ;
	    chlog#add "sideeffects changed" 
	      (LBLOCK [ self#a#toPretty ; STR ": " ; sideeffect_to_pretty s ])
	  end)
      end

  method private make_postconditions (xlist:xpr_t list) = ([],[])

      
    (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
     * create a function summary from locally available information                         *
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method private add_api_parameter (par:api_parameter_t) = 
    let _ = 
      if H.mem api_parameters par.apar_name then
	if (api_parameter_compare par (H.find api_parameters par.apar_name)) = 0
	|| is_unknown_type par.apar_type then
	  ()
	else
	  H.replace api_parameters par.apar_name par
      else
	H.add api_parameters par.apar_name par in
    H.find api_parameters par.apar_name 

  method private get_api_parameters =
    let l = ref [] in
    let _ = H.iter (fun _ v -> l := v :: !l) api_parameters in
    !l
     
  method set_global_par (gaddr:doubleword_int) (btype:btype_t) =
    self#add_api_parameter (mk_global_parameter ~btype gaddr)

  method set_stack_par (index:int) (btype:btype_t) =
    let set_defaultpar () =
      let par = mk_stack_parameter ~btype index in
      begin ignore(self#add_api_parameter par) ; par end in
    match user_summary with 
    | Some summary ->
      begin
	try List.find (fun p -> 
	  match p.apar_location with
	  | StackParameter i -> i = index
	  | _ -> false) summary#get_parameters
	with
	| Not_found -> set_defaultpar ()
      end
    | _ -> set_defaultpar ()

  method set_register_par (reg:register_t) (btype:btype_t) =
    self#add_api_parameter (mk_register_parameter ~btype reg)

  method set_nonreturning = 
    if nonreturning then () else
      let fa = self#get_address in
      begin
	chlog#add "set nonreturning" (LBLOCK [ fa#toPretty ]) ;
	(functions_data#get_function fa)#set_non_returning ;
	nonreturning <- true
      end

  (* A function summary can have several origins:
     - user applications function summary
     - summary created from present analysis results
     - default summary
     
     The summary returned is created as follows:
     - api:
         (1) take user application function summary if present
         (2) if complete: summary created from present analysis otherwise default api

     - semantics:
         - take user application function semantics if present
         - take library function summary if present
         - if complete: create semantics from analysis results else default
         combine all of the above

     - doc:
         (1) take user application function doc if present
  *)
  method get_summary  = 
    let api = match user_summary with 
      | Some summary -> 
	let sapi = summary#get_function_api in
	let parameters = List.fold_left (fun acc par ->
	  if List.exists (fun p -> (api_parameter_compare p par) = 0) acc then 
	  acc else par::acc) sapi.fapi_parameters self#get_api_parameters in
	{ sapi with fapi_parameters = parameters }
      | _ ->
         if system_info#is_mips then
           self#get_mips_local_function_api
         else if system_info#is_arm then
           self#get_arm_local_function_api
         else
           self#get_local_function_api in
    let sem = self#get_function_semantics in
    let doc = match user_summary with
      | Some summary -> summary#get_function_documentation
      | _ -> (default_summary self#get_name)#get_function_documentation in
    make_function_summary ~api ~sem ~doc

  method private get_function_semantics =
    let usem = match user_summary with 
      | Some summary -> Some summary#get_function_semantics
      | _ -> None in
    let fsem = if self#is_complete then Some self#get_local_function_semantics else None in
    List.fold_left join_semantics (default_summary self#get_name)#get_function_semantics
      [ usem ; fsem ]

  method private get_mips_local_function_api =
    try
      let parameters = env#get_mips_argument_values in
      let paramregs =
        List.map self#env#get_initial_register_value_register parameters in
      let apiparams = List.map mk_register_parameter paramregs in
      let apiparams =
        match apiparams with
        | [] ->
           let argregs = [ MIPSRegister MRa0; MIPSRegister MRa1;
                           MIPSRegister MRa2; MIPSRegister MRa3 ] in
           List.map mk_register_parameter argregs
        | _ -> apiparams in
      let _ =
        List.iter (fun p ->  ignore (self#add_api_parameter p)) apiparams in
      default_function_api self#get_name self#get_api_parameters
    with
    | BCH_failure p ->
       raise (BCH_failure (LBLOCK [ STR "Finfo:get-mips-local-function-api: " ; p ]))

  method private get_arm_local_function_api =
    try
      let parameters = env#get_arm_argument_values in
      let paramregs =
        List.map self#env#get_initial_register_value_register parameters in
      let apiparams = List.map mk_register_parameter paramregs in
      let apiparams =
        match apiparams with
        | [] ->
           let argregs = [ ARMRegister AR0; ARMRegister AR1;
                           ARMRegister AR2; ARMRegister AR3 ] in
           List.map mk_register_parameter argregs
        | _ -> apiparams in
      let _ =
        List.iter (fun p ->  ignore (self#add_api_parameter p)) apiparams in
      default_function_api self#get_name self#get_api_parameters
    with
    | BCH_failure p ->
       raise (BCH_failure (LBLOCK [ STR "Finfo:get-arm-local-function-api: " ; p ]))

  method private get_local_function_api =
    try
      let parameters =
        List.fold_left (fun acc v ->
            match env#get_stack_parameter_index v with 
            | Some i -> (i,v) :: acc | _ -> acc) [] env#get_parent_stack_variables in
      let parameters = List.sort (fun (i1,_) (i2,_) -> P.compare i1 i2) parameters in
      let parameters =
        List.fold_left (fun acc (nr,v) ->
            match env#get_stack_parameter_index v with
            | Some ix -> (mk_stack_parameter ix) :: acc
            | _ -> acc) [] parameters in  
      let adj = self#get_stack_adjustment in  
      let cc = match adj with
        | Some a -> if a > 0 then "stdcall" else "cdecl"
        | _ -> "unknown" in
      let _ = List.iter (fun par -> 
                  ignore (self#add_api_parameter par)) parameters in  
      {  fapi_name = self#get_name;
         fapi_jni_index = None;
         fapi_syscall_index = None;
         fapi_parameters = self#get_api_parameters;
         fapi_varargs = false;
         fapi_va_list = None;
         fapi_returntype = t_unknown;
         fapi_rv_roles = [];
         fapi_calling_convention = cc;
         fapi_inferred = true;
         fapi_stack_adjustment = adj;
         fapi_registers_preserved = []
      }
    with
    | BCH_failure p ->
       raise (BCH_failure (LBLOCK [ STR "Finfo:get-local-function-api: " ; p ]))

  method private get_local_function_semantics:function_semantics_t =
    let post = if nonreturning then [ PostFalse ] else [] in
    { fsem_pre = [] ;
      fsem_post = post ;
      fsem_errorpost = [] ;
      fsem_sideeffects = sideeffects#toList ;
      fsem_io_actions = [] ;
      fsem_throws = [] ;
      fsem_desc = ""
    }

  method read_xml_user_summary (node:xml_element_int) = 
    try
      let summary = read_xml_function_summary node in
      begin
	user_summary <- Some summary ;
	env#set_argument_names self#get_address summary#get_function_api ;
	List.iter (fun p -> ignore (self#add_api_parameter p))
	  summary#get_function_api.fapi_parameters ;
	List.iter (fun p -> match p with
	| PreIncludes(ArgValue par,sc) -> 
	  self#env#set_argument_structconstant par sc
	| _ -> ()) summary#get_preconditions ;
	chlog#add "user function summary" (LBLOCK [ self#get_address#toPretty ])
      end
    with
    | XmlDocumentError (line,col,p)
    | XmlReaderError (line,col,p) ->
	let msg = LBLOCK [ STR "function summary " ; self#get_address#toPretty ; p ] in
	raise (XmlReaderError (line,col,msg))

  method set_unknown_java_native_method_signature =
    self#env#set_unknown_java_native_method_signature

  method set_java_native_method_signature (api:java_native_method_api_t) =
    let _ = self#env#set_java_native_method_signature api in
    let args = api.jnm_signature#descriptor#arguments in
    let isStatic = api.jnm_static in
    let jthis = if isStatic then "this$obj" else "this$class" in
    let stackPars = [ (8, jthis, t_voidptr) ; (4, "jni$Env", t_voidptr) ] in
    let (_,_,stackPars) = List.fold_left (fun (count,off,pars) ty ->
      let name = (get_java_type_name_prefix ty) ^ "_" ^ (string_of_int count) in
      (count+1, off + (get_java_type_length ty), 
       (off, name, (get_java_type_btype ty)) :: pars)) (3,12,stackPars) args in
    let mkparam (offset, name, btype) =
      let desc = if offset = 0 then "JNI interface pointer" else "" in
      let par = mk_stack_parameter ~btype ~desc (offset/4) in
      modify_name_par name par in
    let fapi = {
      fapi_name = api.jnm_signature#name;
      fapi_parameters = List.map mkparam stackPars;
      fapi_varargs = false;
      fapi_va_list = None;
      fapi_returntype = 
	(match api.jnm_signature#descriptor#return_value with
	| Some ty -> get_java_type_btype ty
	| _ -> t_void);
      fapi_rv_roles = [];
      fapi_stack_adjustment = Some (4 * (List.length stackPars));
      fapi_jni_index = None;
      fapi_syscall_index = None;
      fapi_calling_convention = "stdcall";
      fapi_registers_preserved = [];
      fapi_inferred = false } in
    let fsem = default_function_semantics in
    let fdoc = default_function_documentation in
    let summary = make_function_summary ~api:fapi ~sem:fsem ~doc:fdoc in
    begin
      user_summary <- Some summary ;
      List.iter (fun p -> ignore (self#add_api_parameter p))
	summary#get_function_api.fapi_parameters
    end      

  method summary_to_pretty = self#get_summary#toPretty

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * setters and users of condiditon codes; conditional jumps                              
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
    
  method connect_cc_user (user_addr:ctxt_iaddress_t) (setter_addr:ctxt_iaddress_t) =
    begin
      H.replace cc_setter_to_user setter_addr user_addr ;
      H.replace cc_user_to_setter user_addr setter_addr
    end
      
  method has_associated_cc_setter (user_address:ctxt_iaddress_t) = 
    H.mem cc_user_to_setter user_address
      
  method get_associated_cc_setter (user_address:ctxt_iaddress_t) =
    if H.mem cc_user_to_setter user_address then
      H.find cc_user_to_setter user_address
    else
      raise (BCH_failure
               (LBLOCK [ STR "function_info#get_associated_condition: " ; 
			 STR user_address ]))
	
  method has_associated_cc_user (setter_address:ctxt_iaddress_t) = 
    H.mem cc_setter_to_user setter_address
      
  method get_associated_cc_user (setter_address:ctxt_iaddress_t) =
    if H.mem cc_setter_to_user setter_address then
      H.find cc_setter_to_user setter_address
    else
      raise (BCH_failure
               (LBLOCK [ STR "function_info#get_associated_jump: " ;
                         STR setter_address ]))
	
  method set_test_expr (iaddr:ctxt_iaddress_t) (x:xpr_t) = 
    H.replace test_expressions iaddr x
      
  method get_num_conditions_associated = H.length cc_user_to_setter
    
  method get_num_test_expressions = H.length test_expressions
    
  method get_test_expr (iaddr:ctxt_iaddress_t) = 
    if H.mem test_expressions iaddr then 
      H.find test_expressions iaddr
    else 
      random_constant_expr

  method get_test_exprs =
    let result = ref [] in
    let _ = H.iter (fun ix v -> result := (ix,v) :: !result) test_expressions in
    !result
      
  method set_test_variables (test_iaddr:ctxt_iaddress_t) (vars:(variable_t * variable_t) list) = 
    H.replace test_variables test_iaddr vars
      
  method get_test_variables (test_iaddr:ctxt_iaddress_t) =
    if H.mem test_variables test_iaddr then
      H.find test_variables test_iaddr
    else []
      
  method has_test_expr (iaddr:ctxt_iaddress_t) = H.mem test_expressions iaddr
    
  method private conditional_jump_state_to_pretty =
    let p = ref [] in
    begin
      H.iter (fun k v ->
	p := (LBLOCK [ STR k ; STR ": " ; pr_expr v ; NL ]) :: !p)
	test_expressions ;
      LBLOCK [ STR "Test expressions: " ; NL ; (LBLOCK !p) ; NL ]
    end
      
  method private write_xml_cc_users (node:xml_element_int) = 
    let l = ref [] in
    let _ = H.iter (fun k v -> l := (k,v) :: !l) cc_user_to_setter in
    node#appendChildren (List.map (fun (k,v) ->
      let cNode = xmlElement "user" in
      let set = cNode#setAttribute in
      begin set "src" k ; set "tgt" v ; cNode end ) !l)
           
  method private read_xml_cc_users (node:xml_element_int) = 
    let getcc = node#getTaggedChildren in
    List.iter (fun cNode ->
      let get = cNode#getAttribute in
      H.replace cc_user_to_setter (get "src") (get "tgt")) (getcc "user")

  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * call targets                                                             *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  method set_call_target (iaddr:ctxt_iaddress_t) (ctinfo:call_target_info_int) =
    begin
      call_targets_set <- true ;
      track_function
        ~iaddr
        self#a
        (LBLOCK [ STR "set call target: " ; ctinfo#toPretty ]);
      H.replace calltargets iaddr ctinfo
    end

  method get_call_target (i:ctxt_iaddress_t) =
    if H.mem calltargets i then
      H.find calltargets i
    else
      raise
        (BCH_failure
           (LBLOCK [ STR "Function " ; self#a#toPretty ;
                     STR "No call-target-info found at " ; STR i ]))

  method has_call_target (i:ctxt_iaddress_t) =  H.mem calltargets i
	
  method get_callees =	H.fold (fun _ v a -> v::a) calltargets []
    
  method get_callees_located = 
    H.fold (fun k v a -> (k,v)::a) calltargets []

  method get_call_count = H.length calltargets

  method get_call_category_count (cat:string) =
    H.fold
      (fun _ ctinfo acc ->
        if ctinfo#is_call_category cat then acc+1 else acc)
      calltargets 0


  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * base pointers                                                                        *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
      
  method add_base_pointer (var:variable_t) =
    let _ = track_function
              self#a (LBLOCK [ STR "add base pointer: " ; var#toPretty ]) in
    base_pointers#add var 
    
  method get_base_pointers = base_pointers#toList
    
  method is_base_pointer (var:variable_t) = base_pointers#has var
    
  method base_pointers_to_pretty =
    if base_pointers#isEmpty then
      LBLOCK [ STR (string_repeat "." 80) ; NL ; STR "No base pointers" ; NL ; 
	       STR (string_repeat "." 80) ; NL ]
    else
      LBLOCK [ STR (string_repeat "~" 80) ; NL ; STR "Base pointers: " ; 
	       pretty_print_list base_pointers#toList env#variable_name_to_pretty "" ", " "" ;
	       NL ; STR (string_repeat "~" 80) ; NL ]

  method private write_xml_base_pointers (node:xml_element_int) =
    node#appendChildren (List.map (fun v ->
      let vNode = xmlElement "base" in
      begin
	vNode#setAttribute "vn" v#getName#getBaseName ;
	vNode#setIntAttribute "vx" v#getName#getSeqNumber ;
	vNode
      end) self#get_base_pointers)

  method private read_xml_base_pointers (node:xml_element_int) =
    List.iter (fun n ->
      let get = n#getAttribute in
      let geti = n#getIntAttribute in
      let var = new variable_t (new symbol_t ~seqnr:(geti "vx") (get "vn")) NUM_VAR_TYPE in
      self#add_base_pointer var) (node#getTaggedChildren "base")
	
	
  (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *
   * jump table targets                                                                   *
   * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
	
  method set_jumptable_target (jumpAddr:ctxt_iaddress_t) (base:doubleword_int) 
                              (jt:jumptable_int) (reg:register_t)  =
    begin
      H.replace jump_targets jumpAddr (JumptableTarget (base,jt,reg)) ;
      chlog#add "set jumptable target"
                (LBLOCK [ STR jumpAddr ; STR "; base: " ; base#toPretty ;
                          STR "; on register: " ; STR (register_to_string reg) ])
    end

  method set_offsettable_target (jumpAddr:ctxt_iaddress_t) (base:doubleword_int)
    (jt:jumptable_int) (db:data_block_int) =
    H.replace jump_targets jumpAddr (OffsettableTarget (base,jt,db))

  method set_global_jumptarget (jumpAddr:ctxt_iaddress_t) (v:variable_t) =
    if env#is_global_variable v then
      let gaddr = env#get_global_variable_address v in
      H.replace jump_targets jumpAddr (JumpOnTerm (mk_global_parameter_term gaddr))
    else
      raise (BCH_failure (LBLOCK [ STR "set_global_jumptarget: variable is not a global variable: " ;
                                   v#toPretty ]))

  method set_argument_jumptarget (jumpAddr:ctxt_iaddress_t) (v:variable_t) =
    try
      if env#is_stackarg_deref_var v then
        match env#get_stack_parameter_index v with
        | Some index ->
           H.replace jump_targets jumpAddr (JumpOnTerm (mk_stack_parameter_term index))
        | _ ->
           raise (BCH_failure (
                      LBLOCK [ STR "set_argument_jumptarget: variable is not a stack parameter: " ;
                               v#toPretty ]))
      else
        raise (BCH_failure
                 (LBLOCK [ STR "Finfo:set-argument-jumptarget: " ;
                           STR "variable is not a stack parameter: " ;  v#toPretty ]))
    with
    | BCH_failure p ->
       raise (BCH_failure (LBLOCK [ STR "Finfo:set-argument-jumptarget: " ; p ]))

  method set_so_jumptarget
           (jumpAddr:ctxt_iaddress_t) (fname:string) (ctinfo:call_target_info_int) =
    begin
      track_function
        ~iaddr:jumpAddr self#a
        (LBLOCK [ STR "set so jumptarget: " ; STR fname ]) ;
      H.replace jump_targets jumpAddr (SOJumpTarget fname) ;
      self#set_call_target jumpAddr ctinfo
    end

  method set_dll_jumptarget
           (jumpAddr:ctxt_iaddress_t)
           (lib:string)
           (fname:string)
           (ctinfo:call_target_info_int) =
    begin
      track_function
        ~iaddr:jumpAddr self#a
        (LBLOCK [ STR "set dll jumptarget: " ; STR lib ;
                  STR  ", " ;  STR fname ]) ;
      H.replace jump_targets jumpAddr (DllJumpTarget (lib,fname)) ;
      self#set_call_target jumpAddr ctinfo
    end

  method is_dll_jumptarget (iaddr:ctxt_iaddress_t) =
    H.mem jump_targets iaddr &&
      (match H.find jump_targets iaddr with DllJumpTarget _ -> true | _ -> false)

  method get_dll_jumptarget (iaddr:ctxt_iaddress_t) =
    if H.mem jump_targets iaddr then
      match H.find jump_targets iaddr with
      | DllJumpTarget (lib,fname) -> (lib,fname)
      | _ ->
	 raise (BCH_failure
                  (LBLOCK [ STR iaddr ; STR ": " ; 
			    STR "Jump target is not a dll target" ]))
    else
      raise (BCH_failure (LBLOCK [ STR iaddr ; STR ": " ;
				   STR "No jump target found" ]))

  method set_unknown_jumptarget (jumpAddr:ctxt_iaddress_t) =
    if H.mem jump_targets jumpAddr then () else 
      H.add jump_targets jumpAddr UnknownJumpTarget
      
  method get_jump_target (jumpAddr:ctxt_iaddress_t) =
    if H.mem jump_targets jumpAddr then
      H.find jump_targets jumpAddr
    else
      UnknownJumpTarget

  method get_jumptable_jumps =
    H.fold (fun k v acc ->
      match v with JumptableTarget _ -> k :: acc | _ -> acc)
      jump_targets []

  method get_indirect_jumps_count = H.length jump_targets

  method get_unknown_jumps_count =
    H.fold (fun _ v acc -> 
      match v with UnknownJumpTarget -> acc+1 | _ -> acc) jump_targets 0

  method get_dll_jumps_count =
    H.fold (fun _ v acc ->
      match v with DllJumpTarget _ -> acc+1 | _ -> acc) jump_targets 0

  method get_jumptable_count =
    H.fold (fun _ v acc -> 
      match v with JumptableTarget _ -> acc+1 | _ -> acc) jump_targets 0

  method get_offsettable_count =
    H.fold (fun _ v acc ->
      match v with OffsettableTarget _ -> acc+1 | _ -> acc) jump_targets 0

  method get_global_jump_count =
    H.fold (fun _ v acc ->
        match v with
        | JumpOnTerm (ArgValue p) when is_global_parameter p -> acc+1
        | _ -> acc) jump_targets 0

  method get_argument_jump_count =
    H.fold (fun _ v acc ->
        match v with
        | JumpOnTerm (ArgValue p) when is_arg_parameter p -> acc+1
        | _ -> acc) jump_targets 0

  method has_jump_target (jumpAddr:ctxt_iaddress_t) =
    H.mem jump_targets jumpAddr && 
      (match H.find jump_targets jumpAddr with
       | UnknownJumpTarget -> false | _ -> true)

  method has_unknown_jump_target =
    H.fold (fun _ v acc -> 
        acc || match v with UnknownJumpTarget -> true | _ -> acc) jump_targets false

  method private write_xml_call_targets (node:xml_element_int) =
    let calltargets = H.fold (fun k v a -> (k,v)::a) calltargets [] in
    node#appendChildren
      (List.map
         (fun (k,v) ->
           let ctnode = xmlElement "ctinfo" in
           begin
             v#write_xml ctnode ;
             ctnode#setAttribute "a" k ;
             ctnode
           end) calltargets)

  method private read_xml_call_targets (node:xml_element_int) =
    List.iter (fun cnode ->
        let a = cnode#getAttribute "a" in
        H.add calltargets a (read_xml_call_target_info cnode))
              (node#getTaggedChildren "ctinfo")
    
  method private write_xml_constants (node:xml_element_int) =
    let var_to_xml (v,n) =
      let varNode = xmlElement "var" in
      let set = varNode#setAttribute in
      let seti = varNode#setIntAttribute in
      begin 
	seti "id" v#getName#getSeqNumber ;
	set "name" v#getName#getBaseName ;
	set "value" n#toString ;
	varNode
      end in
    node#appendChildren (List.map var_to_xml constant_table#listOfPairs) 

  method private read_xml_constants (node:xml_element_int) =
    List.iter (fun n ->
      let vn = n#getAttribute "name" in
      let seqnr = n#getIntAttribute "id" in
      let v = new variable_t (new symbol_t ~seqnr vn) NUM_VAR_TYPE in
      constant_table#set v (mkNumericalFromString (n#getAttribute "value")))
      (node#getTaggedChildren "var")
      
  method private constants_from_xml (xconstants:xml_element_int) = ()
         
  method private write_xml_test_expressions (node:xml_element_int) =
    let l = ref [] in
    let _ = H.iter (fun k e -> l := (k,e) :: !l) test_expressions in
    let l = List.sort (fun (k1,_) (k2,_) -> P.compare k1 k2) !l in
    begin
      node#appendChildren (List.map (fun (k, e) ->
	let eNode = xmlElement "expr" in
	begin
	  varmgr#vard#xd#write_xml_xpr eNode e ;
	  eNode#setAttribute "addr" k ;
	  eNode
	end) l) ;
    end

  method private read_xml_test_expressions (node:xml_element_int) =
    let getcc = node#getTaggedChildren in
    List.iter (fun eNode ->
      let get = eNode#getAttribute in
      H.add test_expressions (get "addr") (varmgr#vard#xd#read_xml_xpr eNode)) (getcc "expr")
      
  method private write_xml_test_variables (node:xml_element_int) =
    let aux (v,f) =
      let vNode = xmlElement "fvar" in
      let set = vNode#setAttribute in
      let seti = vNode#setIntAttribute in
      begin
	seti "vid" v#getName#getSeqNumber ;
	set "vn" v#getName#getBaseName ;
	seti "fid" f#getName#getSeqNumber ;
	set "fn" f#getName#getBaseName ;
	vNode
      end in
    let l = ref [] in
    begin
      H.iter (fun k vars ->
	let vNode = xmlElement "vars" in
	begin
	  vNode#setAttribute "addr" k ;
	  vNode#appendChildren (List.map aux vars) ;
	  l := vNode :: !l
	end) test_variables ;
      node#appendChildren !l ;
    end

  method private read_xml_test_variables (node:xml_element_int) =
    let make_variable seqnr name = new variable_t (new symbol_t ~seqnr name) NUM_VAR_TYPE in
    List.iter (fun aNode ->
      let address = aNode#getAttribute "addr" in
      let vars =
        List.map
          (fun vNode ->
	    let get = vNode#getAttribute in
	    let geti = vNode#getIntAttribute in
	    let v = make_variable (geti "vid") (get "vn") in
	    let f = make_variable (geti "fid") (get "fn") in
	    (v,f))  (aNode#getTaggedChildren "fvar") in
      H.add test_variables address vars) (node#getTaggedChildren "vars")

  method private write_xml_variable_names (node:xml_element_int) =
    self#env#variable_names#write_xml node

  method private read_xml_variable_names (node:xml_element_int) =
    self#env#variable_names#read_xml node

  method private write_xml_saved_registers (node:xml_element_int) =
    let savedregs = H.fold (fun _ v a -> v::a) saved_registers [] in
    node#appendChildren
      (List.map (fun s ->
           let n = xmlElement "sr" in begin s#write_xml n ; n end) savedregs)
    
  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let ccNode = xmlElement "cc-users" in
    let cNode = xmlElement "constants" in
    let tvNode = xmlElement "test-variables" in
    let teNode = xmlElement "test-expressions" in
    let jtNode = xmlElement "jump-targets" in
    let ctNode = xmlElement "call-targets" in
    let bpNode = xmlElement "base-pointers" in
    let vvNode = xmlElement "variable-names" in
    let srNode = xmlElement "saved-registers" in
    let espNode = xmlElement "stack-adjustment" in
    begin
      self#write_xml_constants cNode ; 
      self#write_xml_cc_users ccNode ; 
      self#write_xml_test_expressions teNode ;
      self#write_xml_test_variables tvNode ; 
      (* self#write_xml_jump_targets jtNode ; *)
      self#write_xml_call_targets ctNode ;
      self#write_xml_base_pointers bpNode ;
      self#write_xml_variable_names vvNode ;
      self#write_xml_saved_registers srNode ;
      (match stack_adjustment with
       | Some i -> espNode#setIntAttribute "adj" i | _ -> ()) ;
      append [ ccNode ; tvNode ; teNode ; cNode ; 
	       ctNode ; jtNode ; bpNode ; vvNode ;
               srNode ; espNode ] ;
    end
      
  method read_xml (node:xml_element_int) =
    let hasc = node#hasOneTaggedChild in
    try
      let getc = node#getTaggedChild in
      begin
	self#read_xml_constants (getc "constants") ;
        (if hasc "call-targets" then
           self#read_xml_call_targets (getc "call-targets")) ;
	(if hasc "cc-users" then self#read_xml_cc_users (getc "cc-users")) ; 
	(if hasc "test-variables" then 
	    self#read_xml_test_variables (getc "test-variables")) ;
	(if hasc "test-expressions" then
	    self#read_xml_test_expressions (getc "test-expressions")) ;
	(if hasc "base-pointers" then 
	   self#read_xml_base_pointers (getc "base-pointers")) ;
        (if hasc "variable-names" then
           self#read_xml_variable_names (getc "variable-names")) ;
        (if hasc "stack-adjustment" then
           let espNode = getc "stack-adjustment" in
           if espNode#hasNamedAttribute "adj" then
             stack_adjustment <- Some (espNode#getIntAttribute "adj"))
      end
    with
    | XmlDocumentError (line,col,p)
    | XmlReaderError (line,col,p) ->
      let msg = LBLOCK [ STR "function info " ; self#get_address#toPretty ; STR ": " ; p ] in
      raise (XmlReaderError (line,col,msg))
    | Failure s ->
      pr_debug [ STR "error in reading function info xml: " ; STR s ; STR " (" ;
		 self#get_address#toPretty ; STR ")" ; NL ]
    
  method state_to_pretty = 
    LBLOCK [ self#conditional_jump_state_to_pretty ; NL ]
      
end
  
  
let function_infos = H.create 13


let load_function_info ?(reload=false) (faddr:doubleword_int) =
  let is_java_native_method () =
    let names = (functions_data#get_function faddr)#get_names in
    List.exists is_java_native_method_name names in 
  if H.mem function_infos faddr#index && (not reload) then
    H.find function_infos faddr#index
  else
    try
      let fname = faddr#to_hex_string in
      let varmgr = read_vars fname  in
      let invio = read_invs fname varmgr#vard in
      let tinvio = read_tinvs fname varmgr#vard in
      let finfo = new function_info_t faddr varmgr invio tinvio in
      let _ = match extract_function_info_file fname with
        | Some node -> finfo#read_xml node
        | _ -> () in
      let _ = match load_userdata_function_file faddr#to_hex_string with
        | Some node -> finfo#read_xml_user_summary node
        | _ -> match extract_inferred_function_summary_file faddr#to_hex_string with
	       | _ -> () in
      let _ = match extract_inferred_function_arguments_from_summary_file faddr#to_hex_string with
        | _ -> () in
      let _ = if system_info#is_class_member_function faddr then
	        let classinfos = system_info#get_class_infos faddr in
	        finfo#env#set_class_member_variable_names classinfos in
      let _ =
        if is_java_native_method () then
	  let names = List.filter is_java_native_method_name 
	                          (functions_data#get_function faddr)#get_names in
	  match get_java_native_method_signature faddr#to_hex_string names with
	  | Some api -> finfo#set_java_native_method_signature api
	  | _ -> finfo#set_unknown_java_native_method_signature in  
      begin 
        H.replace function_infos faddr#index finfo ;
        finfo 
      end
    with
    | CHFailure p | BCH_failure p ->
       raise (BCH_failure
                (LBLOCK [ STR "Error in loading function info for: " ;
                          faddr#toPretty ; STR ": " ; p ]))
    
let get_function_info (faddr:doubleword_int) = load_function_info faddr
      
let get_function_infos () = Hashtbl.fold (fun _ v a -> v::a) function_infos []
  
let get_jni_calls () =
  let result =  ref [] in
  let table = H.create 3 in
  let add faddr iaddr jniindex =
    if H.mem table faddr#index then
      H.replace table faddr#index ((iaddr,jniindex) :: (H.find table faddr#index))
    else
      H.add table faddr#index [ (iaddr,jniindex) ] in
  let _ =
    List.iter (fun finfo ->
        List.iter (fun (iaddr,ctinfo) ->
            if ctinfo#is_jni_call then
              add finfo#get_address iaddr ctinfo#get_jni_index)
                  finfo#get_callees_located) (get_function_infos ()) in
  let _ = H.iter (fun k v -> result := (index_to_doubleword k,v) :: !result) table in
  !result


let get_vars_metrics (env:function_environment_int) = {
    mvars_count = env#get_var_count ;
    mvars_global = env#get_globalvar_count ;
    mvars_args = env#get_argvar_count ;
    mvars_return = env#get_returnvar_count ;
    mvars_sideeff = env#get_sideeffvar_count
}
