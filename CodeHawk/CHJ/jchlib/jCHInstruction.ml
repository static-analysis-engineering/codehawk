(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2920-2024 Henny B. Sipma

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

open IO

(* chlib *)
open CHPretty

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHRawBasicTypes
open JCHRawClass


let count =
  List.fold_left
    (fun n vt ->
      n + match vt with
      | TBasic (Double | Long) -> 2
      | _ -> 1)
    1


let opcode2instruction consts (raw:raw_opcode_t):opcode_t =
  match raw with
  | OpNop -> OpNop
  | OpAConstNull -> OpAConstNull
  | OpIConst v -> OpIntConst v
  | OpLConst v -> OpLongConst v
  | OpFConst v -> OpFloatConst v
  | OpDConst v -> OpDoubleConst v
  | OpBIPush v -> OpByteConst v
  | OpSIPush v -> OpShortConst v
  | OpLdc1 n
  | OpLdc1w n ->
    (match get_constant_value consts n with
    | ConstInt c ->  OpIntConst c
    | ConstFloat c -> OpFloatConst c
    | ConstString c -> OpStringConst c
    | ConstClass c -> OpClassConst c
    | ConstLong _ | ConstDouble _ ->
       raise
         (JCH_class_structure_error
            (STR "Illegal constant for Ldc1: long/double")))
  | OpLdc2w n ->
    (match get_constant_value consts n with
    | ConstInt _ | ConstFloat _ | ConstString _ | ConstClass _ ->
       raise
         (JCH_class_structure_error
            (STR "Illegal constant for Ldc2: int/float/string/class"))
    | ConstLong c -> OpLongConst c
    | ConstDouble c -> OpDoubleConst c)

  | OpLoad (k, l) -> OpLoad (k, l)
  | OpALoad l -> OpLoad (Object, l)

  | OpArrayLoad k -> OpArrayLoad k
  | OpAALoad -> OpArrayLoad Object
  | OpBALoad -> OpArrayLoad ByteBool
  | OpCALoad -> OpArrayLoad Char
  | OpSALoad -> OpArrayLoad Short

  | OpStore (k, l) -> OpStore (k, l)
  | OpAStore l -> OpStore (Object, l)

  | OpArrayStore k -> OpArrayStore k

  | OpAAStore -> OpArrayStore Object
  | OpBAStore -> OpArrayStore ByteBool
  | OpCAStore -> OpArrayStore Char
  | OpSAStore -> OpArrayStore Short

  | OpPop -> OpPop
  | OpPop2 -> OpPop2
  | OpDup -> OpDup
  | OpDupX1 -> OpDupX1
  | OpDupX2 -> OpDupX2
  | OpDup2 -> OpDup2
  | OpDup2X1 -> OpDup2X1
  | OpDup2X2 -> OpDup2X2
  | OpSwap -> OpSwap

  | OpAdd k -> OpAdd k
  | OpSub k -> OpSub k
  | OpMult k -> OpMult k
  | OpDiv k -> OpDiv k
  | OpRem k -> OpRem k
  | OpNeg k -> OpNeg k

  | OpIShl -> OpIShl
  | OpLShl -> OpLShl
  | OpIShr -> OpIShr
  | OpLShr -> OpLShr
  | OpIUShr -> OpIUShr
  | OpLUShr -> OpLUShr
  | OpIAnd -> OpIAnd
  | OpLAnd -> OpLAnd
  | OpIOr -> OpIOr
  | OpLOr -> OpLOr
  | OpIXor -> OpIXor
  | OpLXor -> OpLXor

  | OpIInc (index, incr) -> OpIInc (index, incr)

  | OpI2L -> OpI2L
  | OpI2F -> OpI2F
  | OpI2D -> OpI2D
  | OpL2I -> OpL2I
  | OpL2F -> OpL2F
  | OpL2D -> OpL2D
  | OpF2I -> OpF2I
  | OpF2L -> OpF2L
  | OpF2D -> OpF2D
  | OpD2I -> OpD2I
  | OpD2L -> OpD2L
  | OpD2F -> OpD2F
  | OpI2B -> OpI2B
  | OpI2C -> OpI2C
  | OpI2S -> OpI2S

  | OpLCmp -> OpCmpL
  | OpFCmpL -> OpCmpFL
  | OpFCmpG -> OpCmpFG
  | OpDCmpL -> OpCmpDL
  | OpDCmpG -> OpCmpDG
  | OpIfEq pc -> OpIfEq pc
  | OpIfNe pc -> OpIfNe pc
  | OpIfLt pc -> OpIfLt pc
  | OpIfGe pc -> OpIfGe pc
  | OpIfGt pc -> OpIfGt pc
  | OpIfLe pc -> OpIfLe pc
  | OpICmpEq pc -> OpIfCmpEq pc
  | OpICmpNe pc -> OpIfCmpNe pc
  | OpICmpLt pc -> OpIfCmpLt pc
  | OpICmpGe pc -> OpIfCmpGe pc
  | OpICmpGt pc -> OpIfCmpGt pc
  | OpICmpLe pc -> OpIfCmpLe pc
  | OpACmpEq pc -> OpIfCmpAEq pc
  | OpACmpNe pc -> OpIfCmpANe pc
  | OpGoto pc
  | OpGotoW pc -> OpGoto pc
  | OpJsr pc
  | OpJsrW pc -> OpJsr pc
  | OpRet l -> OpRet l

  | OpTableSwitch (def, low, high, tbl) -> OpTableSwitch  (def, low, high, tbl)
  | OpLookupSwitch (def, tbl) -> OpLookupSwitch (def, tbl)

  | OpReturn k -> OpReturn k
  | OpAReturn -> OpReturn Object
  | OpReturnVoid -> OpReturn Void

  | OpGetStatic i ->
     let cs, fs = get_field consts i in
     OpGetStatic (cs, fs)

  | OpPutStatic i ->
     let cs, fs = get_field consts i in
     OpPutStatic (cs, fs)

  | OpGetField i ->
     let cs, fs = get_field consts i in
     OpGetField (cs, fs)

  | OpPutField i ->
     let cs, fs = get_field consts i in
     OpPutField (cs, fs)

  | OpInvokeVirtual i ->
     let t, ms = get_method consts i in
     OpInvokeVirtual (t, ms)

  | OpInvokeNonVirtual i ->
    (match get_method consts i with
    | TClass cs, ms -> OpInvokeSpecial (cs, ms)
    | _ ->
       raise
         (JCH_class_structure_error (STR "Illegal invokespecial: array class")))

  | OpInvokeStatic i ->
    (match get_method consts i with
    | TClass cs, ms ->
       let ms = make_ms true ms#name ms#descriptor in
       OpInvokeStatic (cs, ms)
    | _ ->
       raise
         (JCH_class_structure_error (STR "Illegal invokestatic: array class")))

  | OpInvokeInterface (i, c) ->
     let cs, ms = get_interface_method consts i in
     begin
       (if count (ms#descriptor#arguments) <> c then
          raise
            (JCH_class_structure_error (STR "wrong count in invokeinterface")));
       OpInvokeInterface (cs, ms)
     end

  | OpInvokeDynamic i ->
     (match get_callsite_specifier consts i with
      | (index,ms) -> OpInvokeDynamic (index,ms))

  | OpNew i -> OpNew (get_class consts i)
  | OpNewArray bt -> OpNewArray (TBasic bt)
  | OpANewArray i ->
     OpNewArray (TObject (get_object_type consts i))
  | OpArrayLength -> OpArrayLength
  | OpThrow -> OpThrow
  | OpCheckCast i -> OpCheckCast (get_object_type consts i)
  | OpInstanceOf i -> OpInstanceOf (get_object_type consts i)
  | OpMonitorEnter -> OpMonitorEnter
  | OpMonitorExit -> OpMonitorExit
  | OpAMultiNewArray (ot, dims) -> OpAMultiNewArray
    ((get_object_type consts ot), dims)
  | OpIfNull pc -> OpIfNull pc
  | OpIfNonNull pc -> OpIfNonNull pc
  | OpBreakpoint -> OpBreakpoint

  | OpInvalid -> OpInvalid


let opcodes2code consts opcodes =
  Array.map (opcode2instruction consts) opcodes


let instruction2opcode consts length (opcode:opcode_t) =
  match opcode with
  | OpNop -> OpNop
  | OpAConstNull
    | OpIntConst _
    | OpLongConst _
    | OpFloatConst _
    | OpDoubleConst _
    | OpByteConst _
    | OpShortConst _
    | OpStringConst _
    | OpClassConst _ ->
     let opldc_w c =
       let index = (value_to_int consts c) in
       if length = 2 && index <= 0xFF then
         OpLdc1 index
       else if length = 3 then
         OpLdc1w index
       else
         raise
	   (JCH_class_structure_error
              (LBLOCK [STR "OpConst cannot be encoded in "; INT length;
                        STR " bytes"] )) in
     (match opcode with
      | OpAConstNull -> OpAConstNull
      | OpIntConst v ->
         if length = 1 && -1l <= v && v <= 5l then
           OpIConst v
         else
           opldc_w (ConstInt v)
      | OpLongConst v ->
         if length = 1 && (v=0L || v=1L) then
           OpLConst v
         else
           OpLdc2w (value_to_int consts (ConstLong v))
      | OpFloatConst v ->
         if length = 1 && (v=0. || v=1. || v=2.) then
           OpFConst v
         else
           opldc_w (ConstFloat v)
      | OpDoubleConst v ->
         if length = 1 && (v=0. || v=1.) then
           OpDConst v
         else
           OpLdc2w (value_to_int consts (ConstDouble v))
      | OpByteConst v -> OpBIPush v
      | OpShortConst v -> OpSIPush v
      | OpStringConst v -> opldc_w (ConstString v)
      | OpClassConst v -> opldc_w (ConstClass v)
      | _ -> raise (JCH_failure (STR "Unreachable"))
     )

  | OpLoad (k, l) -> (match k with | Object -> OpALoad l | _ -> OpLoad (k, l))

  | OpArrayLoad k ->
     (match k with
      | Object -> OpAALoad
      | ByteBool -> OpBALoad
      | Char -> OpCALoad
      | Short -> OpSALoad
      | _ -> OpArrayLoad k)

  | OpStore (k, l) -> (match k with | Object -> OpAStore l | _ -> OpStore (k, l))

  | OpArrayStore k ->
     (match k with
      | Object -> OpAAStore
      | ByteBool -> OpBAStore
      | Char -> OpCAStore
      | Short -> OpSAStore
      | _ -> OpArrayStore k)

  | OpPop -> OpPop
  | OpPop2 -> OpPop2
  | OpDup -> OpDup
  | OpDupX1 -> OpDupX1
  | OpDupX2 -> OpDupX2
  | OpDup2 -> OpDup2
  | OpDup2X1 -> OpDup2X1
  | OpDup2X2 -> OpDup2X2
  | OpSwap -> OpSwap

  | OpAdd k -> OpAdd k
  | OpSub k -> OpSub k
  | OpMult k -> OpMult k
  | OpDiv k -> OpDiv k
  | OpRem k -> OpRem k
  | OpNeg k -> OpNeg k

  | OpIShl -> OpIShl
  | OpLShl -> OpLShl
  | OpIShr -> OpIShr
  | OpLShr -> OpLShr
  | OpIUShr -> OpIUShr
  | OpLUShr -> OpLUShr
  | OpIAnd -> OpIAnd
  | OpLAnd -> OpLAnd
  | OpIOr -> OpIOr
  | OpLOr -> OpLOr
  | OpIXor -> OpIXor
  | OpLXor -> OpLXor

  | OpIInc (index, incr) -> OpIInc (index, incr)

  | OpI2L -> OpI2L
  | OpI2F -> OpI2F
  | OpI2D -> OpI2D
  | OpL2I -> OpL2I
  | OpL2F -> OpL2F
  | OpL2D -> OpL2D
  | OpF2I -> OpF2I
  | OpF2L -> OpF2L
  | OpF2D -> OpF2D
  | OpD2I -> OpD2I
  | OpD2L -> OpD2L
  | OpD2F -> OpD2F
  | OpI2B -> OpI2B
  | OpI2C -> OpI2C
  | OpI2S -> OpI2S
  | OpCmpL -> OpLCmp
  | OpCmpFL -> OpFCmpL
  | OpCmpFG -> OpFCmpG
  | OpCmpDL -> OpDCmpL
  | OpCmpDG -> OpDCmpG
  | OpIfEq pc -> OpIfEq pc
  | OpIfNe pc -> OpIfNe pc
  | OpIfLt pc -> OpIfLt pc
  | OpIfGe pc -> OpIfGe pc
  | OpIfGt pc -> OpIfGt pc
  | OpIfLe pc -> OpIfLe pc
  | OpIfNull pc -> OpIfNull pc
  | OpIfNonNull pc -> OpIfNonNull pc
  | OpIfCmpEq pc -> OpICmpEq pc
  | OpIfCmpNe pc -> OpICmpNe pc
  | OpIfCmpLt pc -> OpICmpLt pc
  | OpIfCmpGe pc -> OpICmpGe pc
  | OpIfCmpGt pc -> OpICmpGt pc
  | OpIfCmpLe pc -> OpICmpLe pc
  | OpIfCmpAEq pc -> OpACmpEq pc
  | OpIfCmpANe pc -> OpACmpNe pc
  | OpGoto pc ->
     if length = 3 then
       OpGoto pc
     else if length = 5 then
       OpGotoW pc
     else
       raise
         (JCH_class_structure_error
            (LBLOCK [
                 STR "OpGoto ";
                 INT pc;
                 STR " cannot be encoded in ";
	         INT length;
                 STR " bytes"]))
  | OpJsr pc ->
     if length = 3 then
       OpJsr pc
     else if length = 5 then
       OpJsrW pc
     else
       raise
         (JCH_class_structure_error
            (LBLOCK [
                 STR "OpJsr ";
                 INT pc;
                 STR " cannot be encoded in ";
	         INT length;
                 STR " bytes"] ))
  | OpRet l -> OpRet l

  | OpTableSwitch (def, low, high, tbl) -> OpTableSwitch  (def, low, high, tbl)
  | OpLookupSwitch (def, tbl) -> OpLookupSwitch (def, tbl)

  | OpReturn k ->
     (match k with
      | Object -> OpAReturn
      | Void -> OpReturnVoid
      | _ -> OpReturn k)

  | OpGetStatic (cs, fs) -> OpGetStatic (field_to_int consts (cs,fs))
  | OpPutStatic (cs, fs) -> OpPutStatic (field_to_int consts (cs,fs))
  | OpGetField (cs, fs) ->  OpGetField (field_to_int consts (cs, fs))
  | OpPutField (cs, fs) ->  OpPutField (field_to_int consts (cs, fs))
  | OpInvokeVirtual (t, ms) ->  OpInvokeVirtual (method_to_int consts (t, ms))
  | OpInvokeSpecial (t, ms) ->
     OpInvokeNonVirtual(method_to_int consts (TClass t, ms))
  | OpInvokeStatic (t, ms) ->
     OpInvokeStatic (method_to_int consts (TClass t, ms))
  | OpInvokeInterface (t, ms) ->
    OpInvokeInterface
      (constant_to_int consts
	 (ConstInterfaceMethod (t, ms)), count (ms#descriptor#arguments))
  | OpInvokeDynamic (aindex,ms) ->
     OpInvokeDynamic (constant_to_int consts (ConstDynamicMethod (aindex,ms)))

  | OpNew cs -> OpNew (class_to_int consts cs)
  | OpNewArray t ->
    (match t with
    | TBasic bt -> OpNewArray bt
    | TObject ot ->
      OpANewArray (object_type_to_int consts ot)
    )
  | OpArrayLength -> OpArrayLength
  | OpThrow -> OpThrow
  | OpCheckCast ot -> OpCheckCast (object_type_to_int consts ot)
  | OpInstanceOf ot -> OpInstanceOf (object_type_to_int consts ot)
  | OpMonitorEnter -> OpMonitorEnter
  | OpMonitorExit -> OpMonitorExit
  | OpAMultiNewArray (i, dims) ->
    OpAMultiNewArray (object_type_to_int consts i, dims)
  | OpBreakpoint -> OpBreakpoint

  | OpInvalid -> OpInvalid


let check_space _consts offset length (opcode:raw_opcode_t) =
  let ch = output_string () in
  let ch, count = pos_out ch in
  let offsetmod4 = offset mod 4 in
  begin
    (* for aligned instructions *)
    for _i = 1 to offsetmod4 do write_byte ch 0 done;
    JCHParseCode.unparse_instruction ch count length opcode;
    let space_taken = count () - offsetmod4 in
    let opcodestring = close_out ch in
    (if not (is_permissive ())
       && not  (String.length opcodestring - offsetmod4 = length) then
      failwith "check_space: count does not seems to provide the right result");
    length = space_taken
  end


let code2opcodes consts (code:opcode_t array) =
  let opcodes = Array.make (Array.length code) OpNop in
  begin
    (Array.iteri
       (fun i (instr:opcode_t) ->
         if instr <> OpInvalid then
           (let length =
              let j = ref (i+1) in
              while !j < Array.length code && code.(!j) = OpInvalid do
                opcodes.(!j) <- OpInvalid;
                incr j
              done;
              !j-i in
	    let opcode = instruction2opcode consts length instr in
            begin
	      opcodes.(i) <- opcode;
	      if not (is_permissive ())
                 && not (check_space consts i length opcode) then
                raise
                  (JCH_class_structure_error
                     (LBLOCK [
                          STR "Low level translation of instruction is too long ";
                          STR "for the allocated space in high level code"]));
            end)) code);
    opcodes
  end
