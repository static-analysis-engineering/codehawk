(* =============================================================================
   CodeHawk C Analyzer 
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
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open XprDictionary
open Xprt
open XprTypes
open XprToPretty
open XprUtil
open XprXml

(* cchlib *)
open CCHBasicTypes
open CCHDeclarations
open CCHDictionary
open CCHBasicTypesXml
open CCHFileEnvironment
open CCHLibTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHIndexedCollections
open CCHMemoryReference
open CCHMemoryRegion
open CCHPreSumTypeSerializer
open CCHPreTypes
open CCHVarDictionary

module H = Hashtbl


let cd = CCHDictionary.cdictionary
let cdecls = CCHDeclarations.cdeclarations

let fenv = CCHFileEnvironment.file_environment

let pr2s = CHPrettyUtil.pretty_to_string
let pr_expr = xpr_formatter#pr_expr
let expr_compare = syntactic_comparison

let constant_value_variable_compare c1 c2 =
  match (c1,c2) with
  | (InitialValue (v1,_), InitialValue (v2,_)) -> v1#compare v2
  | (InitialValue _, _) -> -1
  | (_, InitialValue _) -> 1
  | (FunctionReturnValue (loc1,_,_,_), FunctionReturnValue (loc2,_,_,_)) ->
     location_compare loc1 loc2
  | (FunctionReturnValue _, _) -> -1
  | (_, FunctionReturnValue _) -> 1
  | (ExpReturnValue (loc1,_,_,_,_), ExpReturnValue (loc2,_,_,_,_)) ->
     location_compare loc1 loc2
  | (ExpReturnValue _, _) -> -1
  | (_, ExpReturnValue _) -> 1
  | (FunctionSideEffectValue (loc1, _, _, _, a1, _),
     FunctionSideEffectValue (loc2, _, _, _, a2, _)) ->
     let l0 = location_compare loc1 loc2 in
     if l0 = 0 then Stdlib.compare a1 a2 else l0
  | (FunctionSideEffectValue _,_) -> -1
  | (_, FunctionSideEffectValue _) -> 1
  | (ExpSideEffectValue (loc1, _, _, _, a1, _),
     ExpSideEffectValue (loc2, _, _, _, a2, _)) ->
     let l0 = location_compare loc1 loc2 in
     if l0 = 0 then Stdlib.compare a1 a2 else l0
  | (ExpSideEffectValue _,_) -> -1
  | (_, ExpSideEffectValue _) -> 1
  | (SymbolicValue (x1,t1), SymbolicValue (x2,t2)) ->
     let r1 = expr_compare x1 x2 in if r1 = 0 then typ_compare t1 t2 else r1
  | (SymbolicValue _, _) -> -1
  | (_, SymbolicValue _) -> 1
  | (TaintedValue (v1,optx11,optx12,t1), TaintedValue (v2,optx21,optx22,t2)) ->
     v1#compare v2
  | (TaintedValue _,_) -> -1
  | (_, TaintedValue _) ->  1
  | (ByteSequence (v1,l1), ByteSequence (v2,l2)) -> v1#compare v2
  | (ByteSequence _, _) -> -1
  | (_, ByteSequence _) -> 1
  | (MemoryAddress (i1,o1), MemoryAddress (i2,o2)) ->
     let l0 = Stdlib.compare i1 i2 in
     if l0 = 0 then offset_compare o1 o2 else l0

let c_variable_denotation_compare v1 v2 =
  match (v1,v2) with
  | (LocalVariable (v1,o1), LocalVariable (v2,o2)) -> 
    let l0 = Stdlib.compare v1.vid v2.vid in
    if l0 = 0 then offset_compare o1 o2 else l0
  | (LocalVariable _, _) -> -1
  | (_, LocalVariable _) -> 1
  | (GlobalVariable (v1,o1), GlobalVariable (v2,o2)) ->
     let l0 = Stdlib.compare v1.vid v2.vid in
     if l0 = 0 then offset_compare o1 o2 else l0
  | (GlobalVariable _,_) -> -1
  | (_, GlobalVariable _) -> 1
  | (MemoryVariable (i1,o1), MemoryVariable (i2,o2)) ->
     let l0 = Stdlib.compare i1 i2 in
     if l0 = 0 then offset_compare o1 o2 else l0
  | (MemoryVariable _, _) -> -1
  | (_, MemoryVariable _) -> 1
  | (MemoryRegionVariable i1, MemoryRegionVariable i2) -> Stdlib.compare i1 i2
  | (MemoryRegionVariable _, _) -> -1
  | (_, MemoryRegionVariable _) -> 1
  | (ReturnVariable _, ReturnVariable _) -> 0   (* there is only one return variable per function *)
  | (ReturnVariable _, _) -> -1
  | (_, ReturnVariable _) -> 1
  | (FieldVariable f1, FieldVariable f2) -> fielduse_compare f1 f2
  | (FieldVariable _, _) -> -1
  | (_, FieldVariable _) -> 1
  | (CheckVariable (lst1,_), CheckVariable (lst2,_)) ->
     list_compare lst1 lst2
       (fun x y ->
         triple_compare x y Stdlib.compare Stdlib.compare Stdlib.compare)
  | (CheckVariable _, _) -> -1
  | (_, CheckVariable _) -> 1
  | (AuxiliaryVariable a1, AuxiliaryVariable a2) ->
     constant_value_variable_compare a1 a2
  | (AuxiliaryVariable _,_) -> -1
  | (_, AuxiliaryVariable _) -> 1
  | (AugmentationVariable (n1,p1,i1), AugmentationVariable (n2,p2,i2)) ->
     let l0 = Stdlib.compare n1 n2 in
     if l0 = 0 then
       let l1 = Stdlib.compare p1 p2 in
       if l1 = 0 then
         Stdlib.compare i1 i2
       else l1
     else l0
      

let opt_args_to_pretty opt_args =
  pretty_print_list
    opt_args (fun a ->
      match a with
      | Some a -> pr_expr a
      | _ -> STR "_") "" "^" ""

let constant_value_variable_to_pretty c =
  let optx_to_pretty optx =
    match optx with Some x -> pr_expr x | _ -> STR "?" in
  match c with
  | InitialValue (v,_) -> LBLOCK [ STR "(" ; v#toPretty ; STR ")#init" ]
  | FunctionReturnValue (loc,_,vinfo,opt_args) ->
     LBLOCK [ STR "(" ; STR vinfo.vname ;
              STR "(" ; opt_args_to_pretty opt_args ; STR ")#return" ]
  | ExpReturnValue (loc,_,f,opt_args,_) ->
     LBLOCK [ STR "(" ; pr_expr f ; STR "(" ;
              opt_args_to_pretty opt_args ; STR ")#return" ]
  | FunctionSideEffectValue (loc,_,vinfo,opt_args,arg,_) ->
     LBLOCK [ STR "(" ; STR vinfo.vname ; STR "[arg:" ; INT arg ; STR "](" ;
              opt_args_to_pretty opt_args ; STR ")#sideeffect" ]
  | ExpSideEffectValue (loc,_,f,opt_args,arg,_) ->
     LBLOCK [ STR "(" ; pr_expr f ; STR "[arg:" ; INT arg ; STR "](" ;
              opt_args_to_pretty opt_args ; STR "))#sideeffect" ]
  | SymbolicValue (x,_) -> LBLOCK [ STR "(" ; pr_expr x ; STR ")#fixed" ]
  | TaintedValue (v,optx1,optx2,_) ->
     LBLOCK [ STR "tainted-value(" ; v#toPretty ; STR "_lb:" ;
              optx_to_pretty optx1 ; STR "_ub:" ;
              optx_to_pretty optx2 ;  STR  ")" ]
  | ByteSequence (v,optlen) ->
     LBLOCK [ STR "byte-sequence(" ; v#toPretty ; STR "_len:" ;
              optx_to_pretty optlen ; STR ")" ]
  | MemoryAddress (i,o) ->
     match o with
     | NoOffset ->  LBLOCK [ STR "memaddr-" ; INT i ]
     | _ ->
        LBLOCK [STR "memaddr-"; INT i; STR ":"; offset_to_pretty o]


let c_variable_denotation_to_pretty v =
  match v with
  | LocalVariable (vinfo,offset)
    | GlobalVariable (vinfo,offset) ->
     LBLOCK [ STR vinfo.vname ; offset_to_pretty offset ]
  | MemoryVariable (i,offset) -> 
     LBLOCK [ STR "memvar-" ; INT i ; offset_to_pretty offset ]
  | MemoryRegionVariable i ->
     LBLOCK [ STR "memreg-" ; INT i ]
  | ReturnVariable _ -> STR "return"
  | FieldVariable ((fname,fkey)) ->
     LBLOCK [ STR "field(" ; STR fname ; STR "_" ; INT fkey ; STR ")" ]
  | CheckVariable (l,_) ->
     let pp (x,y,z) =
       LBLOCK [
           STR "(";
           STR (if x then "ppo:" else "spo:");
           INT y;
           STR ":";
           INT z;
           STR ")"] in
     LBLOCK [
         STR "check#";
	 (match l with
	  | [] -> STR ""
	  | [p] -> pp p
	  | _ -> pretty_print_list l pp "{" ";" "}")]
  | AuxiliaryVariable a -> constant_value_variable_to_pretty a
  | AugmentationVariable (name,purpose,index) ->
     LBLOCK [ STR "augv[" ; STR purpose ; STR "]:" ; STR name ;
              STR "(" ; INT index ; STR ")" ]


class c_variable_t 
        ~(vard:vardictionary_int)
        ~(index:int)
        ~(denotation:c_variable_denotation_t):c_variable_int =
object (self:'a)
  method index = index
  method compare (other:'a) = Stdlib.compare index other#index
    
  method get_name =
    match denotation with
    | CheckVariable (l,_) ->
       "check_" ^
         (String.concat
            "_"
            (List.map (fun (x,y,z) ->
                 "(" ^ (if x then "ppo:" else "spo:")
                 ^ (string_of_int y) ^ ":" ^ (string_of_int z) ^ ")") l))
    | _ -> pr2s (c_variable_denotation_to_pretty denotation)

  method get_type (memrefmgr:memory_reference_manager_int) =
    try
      let fdecls = vard#fdecls in
      match denotation with
      | LocalVariable (vinfo,offset)
        | GlobalVariable (vinfo,offset) ->
         type_of_offset fdecls vinfo.vtype offset
      | MemoryVariable (i,offset) ->
         type_of_offset fdecls (memrefmgr#get_memory_reference i)#get_type offset
      | MemoryRegionVariable i -> TVoid []
      | ReturnVariable t -> t
      | FieldVariable (fname,ckey) -> fenv#get_field_type ckey fname
      | CheckVariable (_,t) -> t
      | AugmentationVariable _ -> TVoid []
      | AuxiliaryVariable a ->
         match a with
         | InitialValue (_,t) -> t
         | FunctionReturnValue (_,_,vinfo,_) ->
            begin
              match vinfo.vtype with
              | TFun (t,_,_,_) -> t
              | _ ->
                 raise (CCHFailure
                          (LBLOCK [
                               STR "Unexpected type for function return value: ";
                               typ_to_pretty vinfo.vtype]))
            end
         | ExpReturnValue (_,_,_,_,t) -> t
         | FunctionSideEffectValue (_,_,_,_,_,t) -> t
         | ExpSideEffectValue(_,_,_,_,_,t) -> t
         | SymbolicValue (_,t) -> t
         | TaintedValue (_,_,_,t) -> t
         | ByteSequence _ -> TVoid []
         | MemoryAddress (i,offset) ->
            TPtr (type_of_offset
                    fdecls
                    ((memrefmgr#get_memory_reference i)#get_type) offset, [])
    with
    | CCHFailure p ->
       begin
         ch_error_log#add
           "c_variable:get_type"
           (LBLOCK [self#toPretty; STR ": "; p]) ;
         raise (CCHFailure p)
       end

  method get_denotation = denotation

  method get_initial_value_variable =
    match denotation with
    | AuxiliaryVariable (InitialValue (v,_)) -> v
    | _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Variable is not an initial value: ";
                 self#toPretty]))

  method get_function_return_value_callee =
    match denotation with
    | AuxiliaryVariable (FunctionReturnValue (_,_,vinfo,_)) -> vinfo
    | AuxiliaryVariable (FunctionSideEffectValue (_,_,vinfo,_,_,_)) -> vinfo
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not a function return value: " ;
                          self#toPretty ]))

  method get_function_return_value_args =
    match denotation with
    | AuxiliaryVariable (FunctionReturnValue (_,_,_,args)) -> args
    | AuxiliaryVariable (FunctionSideEffectValue (_,_,_,args,_,_)) -> args
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not a function return value: " ;
                          self#toPretty ]))

  method get_function_return_value_context =
    match denotation with
    | AuxiliaryVariable (FunctionReturnValue (_,pctxt,_,_)) -> pctxt
    | AuxiliaryVariable (FunctionSideEffectValue (_,pctxt,_,_,_,_)) -> pctxt
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not a function return value: " ;
                          self#toPretty ]))

  method get_function_return_value_location =
    match denotation with
    | AuxiliaryVariable (FunctionReturnValue (loc,_,_,_)) -> loc
    | AuxiliaryVariable (FunctionSideEffectValue (loc,_,_,_,_,_)) -> loc
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not a function return value: " ;
                          self#toPretty ]))

  method get_purpose =
    match denotation with
    | AugmentationVariable (_,p,_) -> p
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not an augmentation variable: " ;
                          self#toPretty ]))

  method get_indicator =
    match denotation with
    | AugmentationVariable (_,_,i) -> i
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not an augmentation variable: " ;
                          self#toPretty ]))

  method get_tainted_value_origin =
    match denotation with
    | AuxiliaryVariable  (TaintedValue (v,_,_,_)) -> v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not a tainted value: " ;
                          self#toPretty ]))

  method get_tainted_value_bounds =
    match denotation with
    | AuxiliaryVariable (TaintedValue (_,xlb,xub,_)) -> (xlb,xub)
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not a tainted value: " ;
                          self#toPretty ]))

  method get_byte_sequence_origin =
    match denotation with
    | AuxiliaryVariable (ByteSequence (v,_)) ->  v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Variable is not a byte sequence: " ;
                          self#toPretty ]))
                           

  method is_program_variable =
    match denotation with
    |  AuxiliaryVariable  _ -> false | _ -> true

  method is_fixed_value =
    match denotation with
    | AuxiliaryVariable _ -> true | _ -> false

  method is_initial_value =
    match denotation with
    | AuxiliaryVariable (InitialValue _) -> true | _ -> false

  method is_function_return_value =
    match denotation with
    | AuxiliaryVariable (FunctionReturnValue _) -> true
    | _ -> false

  method is_function_sideeffect_value =
    match denotation with
    | AuxiliaryVariable (FunctionSideEffectValue _) -> true
    | _ -> false

  method is_tainted_value =
    match denotation with
    | AuxiliaryVariable (TaintedValue _) -> true
    | _ -> false

  method is_byte_sequence =
    match denotation with
    | AuxiliaryVariable (ByteSequence _) -> true
    | _ -> false

  method is_augmentation_variable =
    match denotation with
    | AugmentationVariable _ -> true
    | _ -> false

  method has_constant_offset =
    let rec is_constant_offset offset result =
      result &&
        match offset with
        | NoOffset -> true
        | Field (f,o) -> is_constant_offset o result
        | Index (e,o) ->
           match e with
           | CnApp _ -> false
           | _ -> is_constant_offset o result in
    match denotation with
    | LocalVariable (_,offset)
      | GlobalVariable (_,offset)
      | MemoryVariable (_,offset) -> is_constant_offset offset true
    | _ -> true

  method applies_to_po ?(argindex=(-1)) (isppo:bool) (po_id:int) =
    match denotation with
    | CheckVariable (l,_) ->
       if argindex > 0 then
         List.exists (fun (b,x,y) -> b = isppo && x = po_id && y = argindex) l
       else
         List.exists (fun (b,x,_) -> b = isppo && x = po_id) l
    | _ -> false
      
  method toPretty = c_variable_denotation_to_pretty denotation
    
end
  
class variable_manager_t
    (optnode:xml_element_int option)
    (fdecls:cfundeclarations_int)
    (vard:vardictionary_int)
    (memregmgr:memory_region_manager_int)
    (memrefmgr:memory_reference_manager_int):variable_manager_int =
object (self)
  
  (* val table = new variable_table_t *)
  val vartable = H.create 3
  val vard = vard
  val memregmgr = memregmgr
  val memrefmgr = memrefmgr

  initializer
    match optnode with
    | Some node ->
       let getc = node#getTaggedChild in
       begin
         vard#read_xml (getc "var-dictionary") ;
         List.iter
           (fun (index,denotation) ->
             H.add vartable index (new c_variable_t ~vard ~index ~denotation))
           vard#get_indexed_variables
       end
    | _ -> ()

  method vard = vard

  method memrefmgr = memrefmgr

  method memregmgr = memregmgr

  method get_variable (index:int) =
    if H.mem vartable index then
      H.find vartable index
    else
      raise (CCHFailure 
	       (LBLOCK [ STR "No variable found with index " ; INT index ]))
         
  method get_variable_type (index:int) =
    let v = self#get_variable index in
    v#get_type memrefmgr

  method get_symbolic_value (index:int) =
    let v = self#get_variable index in
    match v#get_denotation with
    | AuxiliaryVariable (SymbolicValue (x,_)) -> x
    | _ ->
       raise
         (CCHFailure
	    (LBLOCK [
                 STR "Index does not belong to a frozen value: ";
		 v#toPretty]))
	
  method get_check_variable (index:int) =
    let v = self#get_variable index in
    match v#get_denotation with
    | CheckVariable (l,t) -> (l,t)
    | _ ->
       raise
         (CCHFailure
	    (LBLOCK [
                 STR "Index does not belong to check value variable: ";
		 v#toPretty]))

  method private mk_variable (denotation:c_variable_denotation_t) =
    let index = vard#index_c_variable_denotation denotation in
    if H.mem vartable index then
      H.find vartable index
    else
      let var = new c_variable_t ~vard ~index ~denotation in
      begin
        H.add vartable index var ;
        var
      end

  method mk_local_variable (vinfo:varinfo) (offset:offset) =
    self#mk_variable (LocalVariable (vinfo,offset))

  method mk_global_variable (vinfo:varinfo) (offset:offset)  =
    self#mk_variable (GlobalVariable (vinfo,offset))
      
  method mk_memory_variable (m_index:int) (offset:offset) =
    self#mk_variable (MemoryVariable (m_index,offset))

  method mk_memreg_variable (mindex:int) =
    self#mk_variable (MemoryRegionVariable mindex)
      
  method mk_return_variable t =
    self#mk_variable (ReturnVariable t)

  method mk_augmentation_variable name purpose index =
    self#mk_variable (AugmentationVariable (name,purpose,index))

  method mk_initial_value (v:variable_t) (typ:typ) =
    self#mk_variable (AuxiliaryVariable (InitialValue (v,typ)))

  method mk_function_return_value
           (loc:location)
           (pctxt:program_context_int)
           (callee:varinfo)
           (args:xpr_t option list) =
    self#mk_variable
      (AuxiliaryVariable (FunctionReturnValue (loc,pctxt,callee,args)))

  method mk_function_sideeffect_value
           (loc:location)
           (pctxt:program_context_int)
           (callee:varinfo)
           (args:xpr_t option list)
           (argindex:int)
           (argtype:typ) =
    self#mk_variable
      (AuxiliaryVariable
         (FunctionSideEffectValue (loc,pctxt,callee,args,argindex,argtype)))

  method mk_tainted_value
           (v:variable_t) (xopt1:xpr_t option) (xopt2:xpr_t option) (t:typ) =
    self#mk_variable (AuxiliaryVariable (TaintedValue (v,xopt1,xopt2,t)))

  method mk_byte_sequence (v:variable_t) (len:xpr_t option) =
    self#mk_variable (AuxiliaryVariable (ByteSequence (v,len)))

  method mk_exp_return_value
           (loc:location)
           (pctxt:program_context_int)
           (callee:xpr_t)
           (args:xpr_t option list)
           (t:typ) =
    self#mk_variable
      (AuxiliaryVariable (ExpReturnValue (loc,pctxt,callee,args,t)))
      
  method mk_symbolic_value (x:xpr_t) (t:typ) =
    self#mk_variable (AuxiliaryVariable (SymbolicValue (x,t)))

  method mk_memory_address (mindex:int) (offset:offset)=
    self#mk_variable (AuxiliaryVariable (MemoryAddress (mindex,offset)))

  method mk_string_address (s:string) (offset:offset) (t:typ):c_variable_int =
    let memref = memrefmgr#mk_string_reference s t in
    self#mk_memory_address memref#index offset
            
  method mk_check_variable l t =
    self#mk_variable (CheckVariable (l,t))

  method mk_field_variable f =
    self#mk_variable (FieldVariable f)      

  method get_parameter_exp (index:int) =
    if self#is_initial_value index then
      let initvar = (self#get_variable index)#get_initial_value_variable in
      if self#is_program_lval initvar#getName#getSeqNumber then
        match (self#get_variable initvar#getName#getSeqNumber)#get_denotation with
        | LocalVariable (vinfo,offset) ->
           Lval (Var (vinfo.vname,vinfo.vid), offset)
        | MemoryVariable (i,offset) ->
           let memref = memrefmgr#get_memory_reference i in
           if memref#has_external_base then
             let basevar = memref#get_external_basevar in
             if self#is_initial_value basevar#getName#getSeqNumber then
               let bvar =
                 self#get_initial_value_variable basevar#getName#getSeqNumber in
               begin
                 match (self#get_variable bvar#getName#getSeqNumber)#get_denotation with
                 | LocalVariable (vinfo,voffset) ->
                    Lval (Mem (Lval (Var (vinfo.vname, vinfo.vid),voffset)),offset)
                 | _ ->
                    raise (CCHFailure
                             (LBLOCK [ STR "Not yet implemented: get_parameter_exp" ]))
               end
             else
               raise (CCHFailure
                        (LBLOCK [ STR "Not yet implemented: get_parameter_exp" ]))
           else
             raise (CCHFailure
                      (LBLOCK [ STR "Not yet implemented: get_parameter_exp" ]))
        | _ ->
           raise (CCHFailure
                    (LBLOCK [ STR "Not yet implemented: get_parameter_exp" ]))
      else
        raise (CCHFailure
                 (LBLOCK [ STR "Unexpected variable in get_parameter_exp: " ;
                                    initvar#toPretty ]))
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not an initial value variable: " ; INT index ]))

  method get_global_exp (index:int) =
    if self#is_initial_value index then
      let initvar = (self#get_variable index)#get_initial_value_variable in
      if self#is_program_lval initvar#getName#getSeqNumber then
        match (self#get_variable initvar#getName#getSeqNumber)#get_denotation with
        | GlobalVariable (vinfo,offset) ->
           Lval (Var (vinfo.vname, vinfo.vid),offset)
        | _ ->
           raise (CCHFailure
                    (LBLOCK [ STR "Not yet implemented: get_global_exp" ]))
      else
        raise (CCHFailure
                 (LBLOCK [ STR "Not yet implemented: get_global_exp" ]))
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not yet implemented: get_global_exp" ]))

  method get_callee (index:int) =
    if self#is_function_return_value index
       || self#is_function_sideeffect_value index then
      (self#get_variable index)#get_function_return_value_callee
    else
      raise (CCHFailure (LBLOCK [ STR "Not a function return value variable: " ;
                                  INT index ]))

  method get_callee_args (index:int) =
    if self#is_function_return_value index
       || self#is_function_sideeffect_value index then
      (self#get_variable index)#get_function_return_value_args
    else
      raise (CCHFailure (LBLOCK [ STR "Not a function return value variable: " ;
                                  INT index ]))

  method get_callee_context (index:int) =
    if self#is_function_return_value index
       || self#is_function_sideeffect_value index then
      (self#get_variable index)#get_function_return_value_context
    else
      raise (CCHFailure (LBLOCK [ STR "Not a function return value variable: " ;
                                  INT index ]))

  method get_callee_location (index:int) =
    if self#is_function_return_value index
       || self#is_function_sideeffect_value index then
      (self#get_variable index)#get_function_return_value_location
    else
      raise (CCHFailure (LBLOCK [ STR "Not a function return value variable: " ;
                                  INT index ]))

  method get_tainted_value_bounds (index:int) =
    if self#is_tainted_value index then
      (self#get_variable index)#get_tainted_value_bounds
    else
      raise (CCHFailure (LBLOCK [ STR "Variable is not a tainted value: " ;
                                  INT index ]))

  method get_tainted_value_origin (index:int) =
    if self#is_tainted_value index then
      (self#get_variable index)#get_tainted_value_origin
    else
      raise (CCHFailure (LBLOCK [ STR "Variable is not a tainted value: " ;
                                  INT index ]))

  method get_byte_sequence_origin (index:int) =
    if self#is_byte_sequence index then
      (self#get_variable index)#get_byte_sequence_origin
    else
      raise (CCHFailure (LBLOCK [ STR  "Variable is not a byte sequence: " ;
                                  INT index ]))

  method get_initial_value_variable (index:int) =
    if self#is_initial_value index then
      (self#get_variable index)#get_initial_value_variable
    else
      raise (CCHFailure
               (LBLOCK [ STR "No an initial value variable: " ; INT index ]))
      
  method is_symbolic_value (index:int) =
    index >= 0 &&
      (match (self#get_variable index)#get_denotation with
	AuxiliaryVariable (SymbolicValue _ ) -> true | _ -> false)

  method is_memory_address (index:int) =
    index >= 0 &&
      (match (self#get_variable index)#get_denotation with
	 AuxiliaryVariable (MemoryAddress _) -> true | _ -> false)

  method get_memory_reference (index:int) =
    match (self#get_variable index)#get_denotation with
    | AuxiliaryVariable (MemoryAddress (i,offset)) ->
       memrefmgr#get_memory_reference i
    | MemoryVariable (i,offset) ->
       memrefmgr#get_memory_reference i
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Not a memory address: " ; INT index ]))

  method is_local_variable (index:int) =
    index > 0 &&
      (match (self#get_variable index)#get_denotation with
       | LocalVariable _ -> true
       | _ -> false)

  method is_global_variable (index:int) =
    index > 0 &&
      (match (self#get_variable index)#get_denotation with
       | GlobalVariable _ -> true
       | _ -> false)

  method get_local_variable (index:int) =
    if index > 0 then
      (match (self#get_variable index)#get_denotation with
       | LocalVariable (vinfo,offset) -> (vinfo,offset)
       | _ ->
          raise (CCHFailure
                   (LBLOCK [ STR "Not a local variable: " ; INT index ])))
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not a local variable: " ; INT index ]))

  method get_global_variable (index:int) =
    if index > 0 then
      (match (self#get_variable index)#get_denotation with
       | GlobalVariable (vinfo,offset) -> (vinfo,offset)
       | _ ->
          raise (CCHFailure
                   (LBLOCK [ STR "Not a global variable: " ; INT index ])))
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not a global variable: " ; INT index ]))

  method get_memory_variable (index:int) =
    if index > 0 then
      (match (self#get_variable index)#get_denotation with
       | MemoryVariable (i,offset) ->
          (memrefmgr#get_memory_reference i, offset)
       | _ ->
          raise (CCHFailure
                   (LBLOCK [ STR "Not a memory variable: " ; INT index ])))
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not a memory variable: " ; INT index ]))

  method get_memory_address (index:int) =
    if index > 0 then
      (match (self#get_variable index)#get_denotation with
       | AuxiliaryVariable (MemoryAddress (i,offset)) ->
          (memrefmgr#get_memory_reference i, offset)
       | _ ->
          raise (CCHFailure
                   (LBLOCK [ STR "Not a memory address: " ; INT index ])))
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not a memory address: " ; INT index ]))

  method get_purpose (index:int) =
    if self#is_augmentation_variable index then
      (self#get_variable index)#get_purpose
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not an augmentation variable: " ; INT index ]))

  method get_indicator (index:int) =
    if self#is_augmentation_variable index then
      (self#get_variable index)#get_indicator
    else
      raise (CCHFailure
               (LBLOCK [ STR "Not an augmentation variable: " ; INT index ]))

  method get_canonical_fnvar_index (index:int) =
    if index > 0 then
      (match (self#get_variable index)#get_denotation with
       | AuxiliaryVariable (FunctionReturnValue (loc,ctxt,vinfo,args)) ->
          (self#mk_function_return_value
             loc ctxt vinfo (List.map (fun  _ -> None) args))#index
       | AuxiliaryVariable (FunctionSideEffectValue (loc,ctxt,vinfo,args,argindex,typ)) ->
          (self#mk_function_sideeffect_value
             loc ctxt vinfo (List.map (fun _ -> None) args) argindex typ)#index
       | _ ->
          raise
            (CCHFailure
               (LBLOCK [
                    STR "Not a function return value or sideeffect value: ";
                    INT index])))
    else
      raise
        (CCHFailure
           (LBLOCK [
                STR "Not a function return value or sideeffect value: ";
                INT index]))

  method is_program_lval (index:int) =
    index > 0 &&
      (match (self#get_variable index)#get_denotation with
       | LocalVariable _ -> true
       | GlobalVariable _ -> true
       | MemoryVariable _ -> true
       | _ -> false)

  method is_memory_variable (index:int) =
    index > 0 && 
      (match (self#get_variable index)#get_denotation with
       | MemoryVariable _ -> true | _ -> false)

  method is_check_variable (index:int) =
    index >= 0 &&
      match (self#get_variable index)#get_denotation with 
      | CheckVariable _ -> true | _ -> false

  method is_program_variable (index:int) =
    index >= 0 && (self#get_variable index)#is_program_variable

  method is_augmentation_variable (index:int) =
    index >= 0 && (self#get_variable index)#is_augmentation_variable

  method is_fixed_value (index:int) =
    index >= 0 && (self#get_variable index)#is_fixed_value

  method is_initial_value (index:int) =
    index >= 0 && (self#get_variable index)#is_initial_value

  method is_initial_parameter_value (index:int) =
    (self#is_initial_value index)
    && (let initvar = (self#get_variable index)#get_initial_value_variable in
         let initindex = initvar#getName#getSeqNumber in
         (self#is_program_lval initindex)
         && (match (self#get_variable initindex)#get_denotation with
             | LocalVariable _ -> true
             | _ -> false))

  method is_initial_parameter_deref_value (index:int) =
    (self#is_initial_value index)
    && (let initvar = (self#get_variable index)#get_initial_value_variable in
        let initindex = initvar#getName#getSeqNumber in
        (self#is_memory_variable initindex)
        && (match (self#get_variable initindex)#get_denotation with
            | MemoryVariable (i,offset) ->
               let memref = memrefmgr#get_memory_reference i in
               let memrefbase = memref#get_base in
               begin
                 match memrefbase with
                 | CBaseVar v ->
                    self#is_initial_parameter_value v#getName#getSeqNumber
                 | _ -> false
               end
            | _ -> false))
                        

  method is_initial_global_value (index:int) =
    (self#is_initial_value index)
    && (let initvar = (self#get_variable index)#get_initial_value_variable in
        let initindex = initvar#getName#getSeqNumber in
        (self#is_program_lval initindex)
        && (match (self#get_variable initindex)#get_denotation with
            | GlobalVariable _ -> true
            | _ -> false))

  method is_function_return_value (index:int) =
    index >= 0 && (self#get_variable index)#is_function_return_value

  method is_function_sideeffect_value (index:int) =
    index >= 0 && (self#get_variable index)#is_function_sideeffect_value

  method is_tainted_value (index:int) =
    index >= 0 && (self#get_variable index)#is_tainted_value

  method is_byte_sequence (index:int) =
    index >= 0 && (self#get_variable index)#is_byte_sequence

  method has_constant_offset (index:int) =
    index >= 0 && (self#get_variable index)#has_constant_offset

  method applies_to_po (index:int) ?(argindex=(-1)) (isppo:bool) (po_id:int) =
    index >= 0 && (self#get_variable index)#applies_to_po ~argindex isppo po_id

  method variable_to_pretty (var:variable_t) =
    let index = var#getName#getSeqNumber in
    if index >= 0 then
      (self#get_variable index)#toPretty
    else
      var#toPretty

  method write_xml (node:xml_element_int) =
    let dnode = xmlElement "var-dictionary" in
    begin
      vard#write_xml dnode ;
      node#appendChildren [ dnode ]
    end
      
end
  
let mk_variable_manager
      (optnode:xml_element_int option) (fdecls:cfundeclarations_int) =
  let xd = mk_xprdictionary () in
  let vard = mk_vardictionary xd fdecls in
  let memregmgr = mk_memory_region_manager vard in
  let memrefmgr = mk_memory_reference_manager vard in
  new variable_manager_t optnode fdecls vard memregmgr memrefmgr
  
  
