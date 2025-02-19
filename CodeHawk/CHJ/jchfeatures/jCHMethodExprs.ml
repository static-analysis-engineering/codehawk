(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024-2025 Aarno Labs LLC

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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary

(* jchpre *)
open JCHPreAPI
open JCHIFSystem

(* jchfeatures *)
open JCHFeaturesAPI


let get_stack_top_slot (mInfo:method_info_int) (pc:int) =
  ((chif_system#get_method_stack_layout mInfo)#get_stack_layout pc)#get_top_slot


let get_stack_top_slots (mInfo:method_info_int) (pc:int) (n:int) =
  ((chif_system#get_method_stack_layout mInfo)#get_stack_layout pc)#get_top_slots n


class expr_extractor_t (mInfo:method_info_int) =
object (self)

  method private tsv pc =
    self#get_slot_value pc (get_stack_top_slot mInfo pc)

  method private ts2v pc =
    try
      let topslots = get_stack_top_slots mInfo pc 2 in
      let topslot = List.nth topslots 0 in
      let sndslot = List.nth topslots 1 in
      match self#get_dup2 topslot sndslot with
      | Some (sv1,sv2) -> (sv1,sv2)
      | _ ->
         let sv1 = self#get_slot_value pc sndslot in
         let sv2 = self#get_slot_value pc topslot in
         (sv1,sv2)
    with
    | JCH_failure p ->
       raise
         (JCH_failure
            (LBLOCK [STR "opcode: ";
                     opcode_to_pretty (mInfo#get_opcode pc);
                     STR "; error: ";
                     p]))

  method private ts3v pc =
    try
      let topslots = get_stack_top_slots mInfo pc 3 in
      let topslot = List.nth topslots  0 in
      let slot2 = List.nth topslots 1 in
      let slot3 = List.nth topslots 2 in
      let sv1 = self#get_slot_value pc slot3 in
      let sv2 = self#get_slot_value pc slot2 in
      let sv3 = self#get_slot_value pc topslot in
      (sv1,sv2,sv3)
    with
    | JCH_failure p ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "opcode: ";
                 opcode_to_pretty (mInfo#get_opcode pc);
                 STR "; error: ";
                 p]))

  method private get_dup2 slot1 slot2 =
    match (slot1#get_sources, slot2#get_sources) with
    | ([opSrc1], [opSrc2]) when opSrc1 = opSrc2 ->
       begin
         match mInfo#get_opcode opSrc1 with
         | OpDup2 -> Some (self#ts2v opSrc1)
         | _ -> None
       end
    | _ -> None

  method get_stack_expr (pc:int):fxpr_t = self#tsv pc

  method get_assignment (pc:int):(fxpr_t  * fxpr_t) =
    let opc = mInfo#get_opcode pc in
    let tsv () = self#tsv pc in
    let ts3v () = self#ts3v pc in
    match opc with
    | OpStore (ty, _v) -> (FXVar (TBasic ty), tsv ())
    | OpPutStatic (cn,fs)
      | OpPutField (cn,fs) -> (FXField (make_cfs cn fs), tsv ())
    | OpArrayStore t ->
        let (aref,index,aval)  = ts3v () in
        (FXArrayElem (t,aref,index), aval)
    | OpIInc (_, n) ->
       let lhs = FXVar (TBasic Int) in
       let rhs =
         FXOp (OpAdd Int, [lhs; FXConst (ConstInt  (Int32.of_int n))]) in
       (lhs,rhs)
    |  _ ->
        raise
          (JCH_failure
             (LBLOCK [
                  STR "Invalid argument for get_assignment: ";
                  opcode_to_pretty opc]))

  method private get_slot_source_value (_pc:int) (src:int):fxpr_t =
    let tsv () = self#tsv src in
    let ts2v () = self#ts2v src in
    let opc = mInfo#get_opcode src in
    match opc with
    | OpAConstNull -> FXNull
    | OpIntConst i32 -> FXConst  (ConstInt i32)
    | OpLongConst i64 -> FXConst (ConstLong i64)
    | OpDoubleConst f -> FXConst (ConstDouble f)
    | OpFloatConst f -> FXConst (ConstFloat f)
    | OpByteConst i -> FXConst (ConstInt  (Int32.of_int i))
    | OpShortConst i -> FXConst (ConstInt (Int32.of_int i))
    | OpStringConst s -> FXConst (ConstString s)
    | OpClassConst c -> FXConst (ConstClass c)
    | OpInstanceOf t -> FXOp (OpInstanceOf t, [tsv ()])
    | OpLoad (ty,_) -> FXVar (TBasic ty)
    | opc when is_converter_opcode opc -> FXOp (opc, [tsv ()])
    | opc when is_binop_opcode opc ->
       let (sv1,sv2) = ts2v () in FXOp (opc, [sv1; sv2])
    | opc when is_comparison_opcode opc ->
       let (sv1,sv2) = ts2v () in FXOp (opc, [sv1; sv2])
    | OpNeg t -> FXOp (OpNeg t, [tsv ()])
    | OpDup | OpDup2 -> tsv ()
    | OpDupX1 -> tsv ()
    | OpNew _ -> FXOp (opc, [])
    | OpNewArray _ -> FXOp (opc, [tsv ()])
    | OpAMultiNewArray (_,n) ->
       (try
          let slots = get_stack_top_slots mInfo src n in
          let argsv = List.map (self#get_slot_value src) slots in
          FXOp (opc, argsv)
        with
        | JCH_failure p ->
           raise
             (JCH_failure
                (LBLOCK [
                     STR "OpAMultiNewArray with n = : ";
                     INT n;
                     STR "; error: ";
                     p])))
    | OpArrayLength -> FXOp (opc, [tsv ()])
    | OpArrayLoad t -> let (sv1, sv2) = ts2v () in FXArrayElem (t, sv1, sv2)
    | OpGetStatic (cn, fs)
      | OpGetField (cn, fs) -> FXField (make_cfs cn fs)
    | OpInvokeStatic (cn, ms) -> self#get_static_call_value src cn ms
    | OpInvokeVirtual (b, ms) -> self#get_virtual_call_value src b ms
    | OpInvokeSpecial (cn, ms) -> self#get_special_call_value src cn ms
    | OpInvokeInterface (cn, ms) -> self#get_interface_call_value src cn ms
    | opc ->
       let  _ =
         chlog#add
           "source expression not covered"
           (LBLOCK [
                mInfo#get_class_method_signature#toPretty;
                STR " at pc = ";
                INT src;
                STR  ": ";
                opcode_to_pretty opc])  in
       FXOp (opc,  [])

  method private get_slot_value (pc:int) (slot:logical_stack_slot_int):fxpr_t =
    match slot#get_sources with
    | [opSrc] when opSrc = -1 -> FXException
    | [opSrc] ->  self#get_slot_source_value pc opSrc
    | l -> FXMultiple (List.map  (self#get_slot_source_value pc) l)

  method private get_static_call_value
                   (pc:int) (cn:class_name_int) (ms:method_signature_int):fxpr_t =
    try
      let nArgs = List.length  ms#descriptor#arguments in
      let slots = get_stack_top_slots mInfo pc nArgs in
      let argsv = List.map (self#get_slot_value pc) slots in
      FXFunctionCall (make_cms cn ms, argsv)
    with
    | JCH_failure p ->
       raise  (JCH_failure (LBLOCK [STR "static call to: "; ms#toPretty;
                                     STR "; error: "; p]))

  method private get_special_call_value
                   (pc:int) (cn:class_name_int) (ms:method_signature_int):fxpr_t =
    try
      let nArgs = List.length  ms#descriptor#arguments in
      let slots = get_stack_top_slots mInfo pc nArgs in
      let argsv = List.map (self#get_slot_value pc) slots in
      FXFunctionCall (make_cms cn ms, argsv)
    with
    | JCH_failure p ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "special call to: ";
                 ms#toPretty;
                 STR "; error: ";
                 p]))

  method  private get_virtual_call_value
                    (pc:int) (b:object_type_t) (ms:method_signature_int):fxpr_t =
    try
      let nArgs = List.length  ms#descriptor#arguments in
      let slots = get_stack_top_slots mInfo pc nArgs in
      let argsv = List.map (self#get_slot_value pc) slots in
      match b with
      | TClass cn -> FXFunctionCall (make_cms cn ms, argsv)
      | _ ->
         let _ =
           chlog#add
             "array call not covered"
             (LBLOCK [
                  mInfo#get_class_method_signature#toPretty;
                  STR " at pc = ";
                  INT pc;
                  STR  ": ";
                  ms#toPretty]) in
         FXUnknown
    with
    | JCH_failure p ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "virtual call to: ";
                 ms#toPretty;
                 STR "; error: ";
                 p]))

  method private get_interface_call_value
                   (pc:int) (cn:class_name_int) (ms:method_signature_int):fxpr_t =
    try
      let nArgs = List.length  ms#descriptor#arguments in
      let slots = get_stack_top_slots mInfo pc nArgs in
      let argsv = List.map (self#get_slot_value pc) slots in
      FXFunctionCall (make_cms cn ms, argsv)
    with
    | JCH_failure p ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "interface call to: "; ms#toPretty; STR "; error: "; p]))

  method get_procedure_call (pc:int) =
    let opc = mInfo#get_opcode pc in
    match opc with
    | OpInvokeStatic (cn, ms)
      | OpInvokeVirtual (TClass cn, ms)
      | OpInvokeSpecial (cn, ms)
      | OpInvokeInterface (cn,ms) ->
       (try
          let nArgs = List.length  ms#descriptor#arguments in
          let slots = get_stack_top_slots mInfo pc nArgs in
          let argsv = List.map (self#get_slot_value pc) slots in
          FXProcedureCall (make_cms cn ms, argsv)
        with
        | JCH_failure p ->
           raise
             (JCH_failure
                (LBLOCK [
                     STR "procedure call to: "; ms#toPretty; STR "; error: "; p])))
    | OpInvokeVirtual (_b, ms) ->
       (try
          let cn = make_cn "java.lang.Object" in
          let nArgs = List.length  ms#descriptor#arguments in
          let slots = get_stack_top_slots mInfo pc nArgs in
          let argsv = List.map (self#get_slot_value pc) slots in
          FXProcedureCall (make_cms cn ms, argsv)
        with
        | JCH_failure p ->
           raise
             (JCH_failure
                (LBLOCK [
                     STR "static call to: "; ms#toPretty; STR "; error: "; p])))
    | _ ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Invalid argument to get_procedure_call: ";
                 mInfo#get_class_method_signature#toPretty;
                 STR " at pc = ";
                 INT pc;
                 STR ": ";
                 opcode_to_pretty opc]))

  method get_branch_condition (pc:int) =
    let opc = mInfo#get_opcode pc in
    let tsv () = self#tsv pc in
    let ts2v () = self#ts2v pc in
    match opc with
    | OpIfCmpNe _
      | OpIfCmpANe _
      | OpIfCmpEq _
      | OpIfCmpAEq _
      | OpIfCmpLt _
      | OpIfCmpLe _
      | OpIfCmpGt _
      | OpIfCmpGe _ -> let (sv1,sv2) = ts2v () in FXOp (opc, [sv1; sv2])
    | OpIfEq _
      | OpIfNe _
      | OpIfLt _
      | OpIfLe _
      | OpIfGt _
      | OpIfGe _
      | OpIfNull _
      | OpIfNonNull _ -> FXOp (opc, [tsv ()])
    | _ ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Invalid argument to get_branch_condition: ";
                 mInfo#get_class_method_signature#toPretty;
                 STR " at pc = ";
                 INT pc;
                 STR ": ";
                 opcode_to_pretty opc]))

end



let get_assignment_expr (mInfo:method_info_int) (pc:int):fxfeature_t =
  try
    let extractor = new expr_extractor_t mInfo in
    let (lhs,rhs) = extractor#get_assignment pc in
    FXAssignment (lhs,rhs)
  with
  | JCH_failure p ->
     raise
       (JCH_failure
          (LBLOCK [
               mInfo#get_class_method_signature#toPretty; STR ": "; p]))


let get_procedurecall (mInfo:method_info_int) (pc:int):fxfeature_t =
  try
    let extractor = new expr_extractor_t mInfo in
    extractor#get_procedure_call pc
  with
  | JCH_failure p ->
     raise
       (JCH_failure
          (LBLOCK [
               mInfo#get_class_method_signature#toPretty; STR ": "; p]))


let get_branch_condition (mInfo:method_info_int) (pc:int):fxfeature_t =
  try
    let extractor = new expr_extractor_t mInfo in
    FXCondition (extractor#get_branch_condition pc)
  with
  | JCH_failure p ->
     raise
       (JCH_failure
          (LBLOCK [
               mInfo#get_class_method_signature#toPretty; STR ": "; p]))


let get_throwable (mInfo:method_info_int) (pc:int):fxfeature_t =
  try
    let extractor = new expr_extractor_t mInfo in
    FXThrow (extractor#get_stack_expr pc)
  with
  | JCH_failure p ->
     raise
       (JCH_failure
          (LBLOCK [
               mInfo#get_class_method_signature#toPretty; STR ": "; p]))


let get_returnexpr (mInfo:method_info_int) (pc:int):fxfeature_t =
  try
    let extractor = new expr_extractor_t mInfo in
    FXReturn (Some (extractor#get_stack_expr pc))
  with
  | JCH_failure p ->
     raise
       (JCH_failure
          (LBLOCK [mInfo#get_class_method_signature#toPretty; STR ": "; p]))
