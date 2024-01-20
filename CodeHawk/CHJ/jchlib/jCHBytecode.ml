(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI


let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c ->
    if !found then
      ()
    else if Char.code c = 10 then      (* NL *)
      ()
    else if (Char.code c) < 32 || (Char.code c) > 126 then
      found  := true) s in
  !found


let replace_control_characters s =
  String.map (fun c ->
      if (Char.code c) < 32 || (Char.code c) > 126 then
        'x'
      else
        c) s


let jvm_basic_type place = function
  | Int2Bool -> 0
  | Long -> 1
  | Float -> 2
  | Double -> 3
  | _ -> raise (JCH_class_structure_error
                  (LBLOCK [STR "Illegal type of "; STR place]))

let jvm_basic_type' place = function
  | Int -> 0
  | Long -> 1
  | Float -> 2
  | Double -> 3
  | _ -> raise (JCH_class_structure_error
                  (LBLOCK [STR "Illegal type of "; STR place]))

let opcode_to_opcode_index (opc:opcode_t) =
  match opc with
  | OpNop -> 0
  | OpAConstNull -> 1
  | OpIntConst n when (Int32.compare Int32.minus_one n) = 0 -> 2
  | OpIntConst n when (Int32.to_int n) >= 0 && (Int32.to_int n) <= 5 ->
     (Int32.to_int n) + 5
  | OpLongConst n when (Int64.compare Int64.zero n) = 0 -> 9
  | OpLongConst n when (Int64.compare Int64.one n) = 0 -> 10
  | OpFloatConst n when (n -. 11.) >= 0. && (n -. 11.) <= 2. ->
     int_of_float (n +. 11.)
  | OpDoubleConst 0. -> 14
  | OpDoubleConst 1. -> 15
  | OpByteConst _ -> 16
  | OpShortConst _ -> 17
  | OpStringConst _ | OpClassConst _ | OpIntConst _ | OpFloatConst _ -> 18
  | OpLongConst _ | OpDoubleConst _ -> 20
  | OpLoad (Int2Bool, n) when n < 0 || n > 3 -> 21
  | OpLoad (Long, n) when n < 0 || n > 3 -> 22
  | OpLoad (Float, n) when n < 0 || n > 3 -> 23
  | OpLoad (Double, n) when n < 0 || n > 3 -> 24
  | OpLoad (Object, n) when n < 0 || n > 3 -> 25
  | OpLoad (Int2Bool, n) when n >= 0 && n <= 3 -> n + 26
  | OpLoad (Long, n) when n >= 0 && n <= 3 -> n + 30
  | OpLoad (Float, n) when n >= 0 && n <= 3 -> n + 34
  | OpLoad (Double, n) when n >= 0 && n <= 3 -> n + 38
  | OpLoad (Object, n) when n >= 0 && n <= 3 -> n + 42
  | OpArrayLoad (Int) -> 46
  | OpArrayLoad (Long) -> 47
  | OpArrayLoad (Float) -> 48
  | OpArrayLoad (Double) -> 49
  | OpArrayLoad (Object) -> 50
  | OpArrayLoad (ByteBool) -> 51
  | OpArrayLoad (Char) -> 52
  | OpArrayLoad (Short) -> 53
  | OpStore (Object, t) when t < 0 || t > 3 -> 58
  | OpStore (Int2Bool, t) when t >= 0 && t <= 3 -> t + 59
  | OpStore (Long, t) when t >= 0 && t <= 3 -> t + 63
  | OpStore (Float, t) when t >= 0 && t <= 3 -> t + 67
  | OpStore (Double, t) when t >= 0 && t <= 3 -> t + 71
  | OpStore (Object, t) when t >= 0 && t <= 3 -> t + 75
  | OpStore (n, _t) -> (jvm_basic_type "store" n) + 54
  | OpArrayStore t when t = Int || t = Long || t = Float || t = Double ->
     (jvm_basic_type' "arraystore" t) + 79
  | OpArrayStore Object -> 83
  | OpArrayStore ByteBool -> 84
  | OpArrayStore Char -> 85
  | OpArrayStore Short -> 86
  | OpPop -> 87
  | OpPop2 -> 88
  | OpDup -> 89
  | OpDupX1 -> 90
  | OpDupX2 -> 91
  | OpDup2 -> 92
  | OpDup2X1 -> 93
  | OpDup2X2 -> 94
  | OpSwap -> 95
  | OpAdd n -> (jvm_basic_type "add" n) + 96
  | OpSub n -> (jvm_basic_type "sub" n) + 100
  | OpMult n -> (jvm_basic_type "mult" n) + 104
  | OpDiv n -> (jvm_basic_type "div" n) + 108
  | OpRem n -> (jvm_basic_type "rem" n) + 112
  | OpNeg n -> (jvm_basic_type "neg" n) + 116
  | OpIShl -> 120
  | OpLShl -> 121
  | OpIShr -> 122
  | OpLShr -> 123
  | OpIUShr -> 124
  | OpLUShr -> 125
  | OpIAnd -> 126
  | OpLAnd -> 127
  | OpIOr -> 128
  | OpLOr -> 129
  | OpIXor -> 130
  | OpLXor -> 131
  | OpIInc (_, _) -> 132
  | OpI2L -> 133
  | OpI2F -> 134
  | OpI2D -> 135
  | OpL2I -> 136
  | OpL2F -> 137
  | OpL2D -> 138
  | OpF2I -> 139
  | OpF2L -> 140
  | OpF2D -> 141
  | OpD2I -> 142
  | OpD2L -> 143
  | OpD2F -> 144
  | OpI2B -> 145
  | OpI2C -> 146
  | OpI2S -> 147
  | OpCmpL -> 148
  | OpCmpFL -> 149
  | OpCmpFG -> 150
  | OpCmpDL -> 151
  | OpCmpDG -> 152
  | OpIfEq _ -> 153
  | OpIfNe _ -> 154
  | OpIfLt _ -> 155
  | OpIfGe _ -> 156
  | OpIfGt _ -> 157
  | OpIfLe _ -> 158
  | OpIfCmpEq _ -> 159
  | OpIfCmpNe _ -> 160
  | OpIfCmpLt _ -> 161
  | OpIfCmpGe _ -> 162
  | OpIfCmpGt _ -> 163
  | OpIfCmpLe _ -> 164
  | OpIfCmpAEq _ -> 165
  | OpIfCmpANe _ -> 166
  | OpGoto _ -> 167       (* and 200 *)
  | OpJsr _ -> 168        (* and 201 *)
  | OpRet _ -> 169
  | OpTableSwitch (_, _, _, _) -> 170
  | OpLookupSwitch (_, _) -> 171
  | OpReturn n when n = Int2Bool || n = Long || n = Float || n = Double ->
     (jvm_basic_type "return" n) + 172
  | OpReturn Object -> 176
  | OpReturn Void -> 177
  | OpGetStatic _ -> 178
  | OpPutStatic _ -> 179
  | OpGetField _ -> 180
  | OpPutField _ -> 181
  | OpInvokeVirtual _ -> 182
  | OpInvokeSpecial(_, _) -> 183
  | OpInvokeStatic _ -> 184
  | OpInvokeInterface (_, _) -> 185
  | OpInvokeDynamic (_, _) -> 186
  | OpNew _ -> 187
  | OpNewArray (TBasic _) -> 188
  | OpNewArray (TObject _) -> 189
  | OpArrayLength -> 190
  | OpThrow -> 191
  | OpCheckCast _ -> 192
  | OpInstanceOf _ -> 193
  | OpMonitorEnter -> 194
  | OpMonitorExit -> 195
  | OpAMultiNewArray (_, _) -> 197
  | OpIfNull _ -> 198
  | OpIfNonNull _ -> 199
  | OpBreakpoint -> 202
  | OpInvalid -> 255
  | _ -> (-1)


let opcode_to_opcode_index_string (opc:opcode_t) =
  Printf.sprintf "%x" (opcode_to_opcode_index opc)


let name_hex_of_opcode (opc:opcode_t) =
  match opc with
  | OpLoad _  -> ("load","19")
  | OpStore _ -> ("store","3a")
  | OpIInc _  -> ("iinc","84")

  | OpPop    -> ("pop","57")
  | OpPop2   -> ("pop2","58")
  | OpDup    -> ("dup","59")
  | OpDupX1  -> ("dupX1","5a")
  | OpDupX2  -> ("dupX2","5b")
  | OpDup2   -> ("dup2","5c")
  | OpDup2X1 -> ("dup2X1","5d")
  | OpDup2X2 -> ("dup2X2","5e")
  | OpSwap   -> ("swap","5f")

  | OpAConstNull    -> ("aconstnull","01")
  | OpIntConst _    -> ("iconst","02")
  | OpLongConst _   -> ("lconst","09")
  | OpFloatConst _  -> ("fconst","0b")
  | OpDoubleConst _ -> ("dconst","0e")
  | OpByteConst _   -> ("biconst","10")
  | OpShortConst _  -> ("siconst","11")
  | OpStringConst _ -> ("ld string","14")
  | OpClassConst _  -> ("ld object","12")

  | OpAdd _   -> ("add","63")
  | OpSub _   -> ("sub","67")
  | OpMult _  -> ("mult","6b")
  | OpDiv _   -> ("div","6f")
  | OpRem _   -> ("rem","73")
  | OpNeg _   -> ("neg","77")

  | OpIShl  -> ("ishl","78")
  | OpLShl  -> ("lshl","79")
  | OpIShr  -> ("ishr","7a")
  | OpLShr  -> ("lshr","7b")
  | OpIUShr -> ("iushr","7c")
  | OpLUShr -> ("lushr","7d")
  | OpIAnd  -> ("iand","7e")
  | OpLAnd  -> ("land","7f")
  | OpIOr   -> ("ior","80")
  | OpLOr   -> ("lor","81")
  | OpIXor  -> ("ixor","82")
  | OpLXor  -> ("lxor","83")

  (* Conversion *)
  | OpI2L   -> ("i2l","85")
  | OpI2F   -> ("i2f","86")
  | OpI2D   -> ("i2d","87")
  | OpL2I   -> ("l2i","88")
  | OpL2F   -> ("l2f","89")
  | OpL2D   -> ("l2d","8a")
  | OpF2I   -> ("f2i","8b")
  | OpF2L   -> ("f2l","8c")
  | OpF2D   -> ("f2d","8d")
  | OpD2I   -> ("d2i","8e")
  | OpD2L   -> ("d2l","8f")
  | OpD2F   -> ("d2f","90")
  | OpI2B   -> ("i2b","91")
  | OpI2C   -> ("i2c","92")
  | OpI2S   -> ("i2s","93")

  | OpCmpL  -> ("cmpl","94")
  | OpCmpFL -> ("cmpfl","95")
  | OpCmpFG -> ("cmpfg","96")
  | OpCmpDL -> ("cmpdl","97")
  | OpCmpDG -> ("cmpdg","98")

  | OpIfEq _      -> ("ifEq","99")
  | OpIfNe _      -> ("ifNe","9a")
  | OpIfLt _      -> ("ifLt","9b")
  | OpIfGe _      -> ("ifGe","9c")
  | OpIfGt _      -> ("ifGt","9d")
  | OpIfLe _      -> ("ifLe","9e")
  | OpIfNull _    -> ("ifnull","c6")
  | OpIfNonNull _ -> ("ifnonnull","c7")
  | OpIfCmpEq _   -> ("ifcmpEq","9f")
  | OpIfCmpNe _   -> ("ifcmpNe","a0")
  | OpIfCmpLt _   -> ("ifcmpLt","a1")
  | OpIfCmpGe _   -> ("ifcmpGe","a2")
  | OpIfCmpGt _   -> ("ifcmpGt","a3")
  | OpIfCmpLe _   -> ("ifcmpLe","a4")
  | OpIfCmpAEq _  -> ("ifacmpEq","a5")
  | OpIfCmpANe _  -> ("ifacmpNe","a6")

  | OpGoto _      -> ("goto","a7")
  | OpJsr _       -> ("jsr","a8")
  | OpRet _       -> ("ret","a9")
  | OpTableSwitch _ -> ("tableswitch","aa")
  | OpLookupSwitch _ -> ("lookupswitch","ab")

  | OpNew _        -> ("new","bb")
  | OpNewArray _   -> ("new array","bd")
  | OpAMultiNewArray _  -> ("new multi array","c5")
  | OpCheckCast _     -> ("checkcast","c0")
  | OpInstanceOf _    -> ("instanceof","c1")
  | OpGetStatic _     -> ("getstatic","b2")
  | OpPutStatic _     -> ("putstatic","b3")
  | OpGetField _      -> ("getfield","b4")
  | OpPutField _      -> ("putfield","b5")
  | OpArrayLength     -> ("arraylength","be")
  | OpArrayLoad _     -> ("arrayload","32")
  | OpArrayStore _    -> ("arraystore","53")

  | OpInvokeVirtual _   -> ("invokevirtual","b6")
  | OpInvokeSpecial _   -> ("invokespecial","b7")
  | OpInvokeStatic _    -> ("invokestatic","b8")
  | OpInvokeInterface _ -> ("invokeinterface","b9")
  | OpInvokeDynamic _   -> ("invokedynamic","ba")
  | OpReturn _          -> ("return","b0")

  | OpThrow -> ("throw","bf")
  | OpMonitorEnter -> ("enter monitor","c2")
  | OpMonitorExit  -> ("exit monitor","c3")

  | OpNop -> ("nop","00")
  | OpBreakpoint -> ("breakpoint","ca")
  | OpInvalid -> ("invalid","ff")


let name_of_opcode (opc:opcode_t) =  fst (name_hex_of_opcode opc)

let hex_of_opcode (opc:opcode_t)  = snd (name_hex_of_opcode opc)


let hex_of_arithmetic_opcode (opc:opcode_t) =
  match opc with
  | OpAdd Long -> "61"
  | OpAdd Float -> "62"
  | OpAdd Double -> "63"
  | OpAdd _ -> "60"

  | OpDiv Long -> "6d"
  | OpDiv Float -> "6e"
  | OpDiv Double -> "6f"
  | OpDiv  _ -> "6c"

  | OpMult Long -> "69"
  | OpMult Float -> "6a"
  | OpMult Double -> "6b"
  | OpMult _ -> "68"

  | OpNeg Long -> "75"
  | OpNeg Float -> "76"
  | OpNeg Double -> "77"
  | OpNeg _ -> "74"

  | OpRem Long -> "71"
  | OpRem Float -> "72"
  | OpRem Double -> "73"
  | OpRem _ -> "70"

  | OpSub Long -> "65"
  | OpSub Float -> "66"
  | OpSub Double -> "67"
  | OpSub _ -> "64"

  | _ ->
     raise
       (JCH_failure (
            LBLOCK
              [STR "Invalid argument to hex_of_arithmetic_opcode: ";
               STR (name_of_opcode opc)]))


let ms_arg_types (ms:method_signature_int) =
  ms#descriptor#arguments @
    (match ms#descriptor#return_value with Some vt -> [vt] | _ -> [])


let opcode_arg_types (opc:opcode_t) =
  match opc with
  | OpClassConst ot -> [TObject ot]
  | OpAdd bt
  | OpSub bt
  | OpMult bt
  | OpDiv bt
  | OpRem bt
  | OpNeg bt -> [TBasic bt]
  | OpNew cn -> [TObject (TClass cn)]
  | OpNewArray vt -> [vt]
  | OpAMultiNewArray (ot,_) -> [TObject ot]
  | OpCheckCast ot -> [TObject ot]
  | OpInstanceOf ot -> [TObject ot]
  | OpGetStatic (cn,fs)
  | OpGetField (cn,fs)
  | OpPutStatic (cn,fs)
  | OpPutField (cn,fs) -> [TObject (TClass cn); fs#descriptor]
  | OpArrayLoad bt
  | OpArrayStore bt -> [TBasic bt]
  | OpInvokeVirtual (ot,ms) -> (TObject ot) :: (ms_arg_types ms)
  | OpInvokeSpecial (cn,ms)
    | OpInvokeStatic (cn,ms)
    | OpInvokeInterface (cn,ms) -> (TObject (TClass cn)) :: (ms_arg_types ms)
  | OpInvokeDynamic (_index, _ms)  -> []       (* TBD *)
  | OpReturn bt -> [TBasic bt]
  | _ -> []


let opcode_to_string opc =
  let stri = string_of_int in
  let jb  = java_basic_type_to_string in
  let ot  = object_type_to_string in
  let vt  = value_type_to_string in
  match opc with
    OpLoad (ty,i)  -> "load "  ^ (jb ty) ^ " " ^ (stri i)
  | OpStore (ty,i) -> "store " ^ (jb ty) ^ " " ^ (stri i)
  | OpIInc (i1, i2)-> "iinc "  ^ (stri i1) ^ " " ^ (stri i2)

  | OpPop    -> "pop"
  | OpPop2   -> "pop2"
  | OpDup    -> "dup"
  | OpDupX1  -> "dupX1"
  | OpDupX2  -> "dupX2"
  | OpDup2   -> "dup2"
  | OpDup2X1 -> "dup2X1"
  | OpDup2X2 -> "dup2X2"
  | OpSwap   -> "swap"

  | OpAConstNull    -> "aconstnull"
  | OpIntConst i    -> "iconst "  ^ (Int32.to_string i)
  | OpLongConst i   -> "lconst "  ^ (Int64.to_string i)
  | OpFloatConst f  -> "fconst "  ^ (Printf.sprintf "%f" f)
  | OpDoubleConst d -> "dconst "  ^ (Printf.sprintf "%f" d)
  | OpByteConst i   -> "biconst " ^ (stri i)
  | OpShortConst i  -> "siconst " ^ (stri i)
  | OpStringConst s -> "ld string " ^ s
  | OpClassConst c  -> "ld object " ^ (ot c)

  | OpAdd ty   -> "add "  ^ (jb ty)
  | OpSub ty   -> "sub "  ^ (jb ty)
  | OpMult ty  -> "mult " ^ (jb ty)
  | OpDiv ty   -> "div "  ^ (jb ty)
  | OpRem ty   -> "rem "  ^ (jb ty)
  | OpNeg ty   -> "neg "  ^ (jb ty)

  | OpIShl  -> "ishl"
  | OpLShl  -> "lshl"
  | OpIShr  -> "ishr"
  | OpLShr  -> "lshr"
  | OpIUShr -> "iushr"
  | OpLUShr -> "lushr"
  | OpIAnd  -> "iand"
  | OpLAnd  -> "land"
  | OpIOr   -> "ior"
  | OpLOr   -> "lor"
  | OpIXor  -> "ixor"
  | OpLXor  -> "lxor"

  (* Conversion *)
  | OpI2L   -> "i2l"
  | OpI2F   -> "i2f"
  | OpI2D   -> "i2d"
  | OpL2I   -> "l2i"
  | OpL2F   -> "l2f"
  | OpL2D   -> "l2d"
  | OpF2I   -> "f2i"
  | OpF2L   -> "f2l"
  | OpF2D   -> "f2d"
  | OpD2I   -> "d2i"
  | OpD2L   -> "d2l"
  | OpD2F   -> "d2f"
  | OpI2B   -> "i2b"
  | OpI2C   -> "i2c"
  | OpI2S   -> "i2s"

  | OpCmpL  -> "cmpl"
  | OpCmpFL -> "cmpfl"
  | OpCmpFG -> "cmpfg"
  | OpCmpDL -> "cmpdl"
  | OpCmpDG -> "cmpdg"

  | OpIfEq i      -> "ifEq " ^ (stri i)
  | OpIfNe i      -> "ifNe " ^ (stri i)
  | OpIfLt i      -> "ifLt " ^ (stri i)
  | OpIfGe i      -> "ifGe " ^ (stri i)
  | OpIfGt i      -> "ifGt " ^ (stri i)
  | OpIfLe i      -> "ifLe " ^ (stri i)
  | OpIfNull i    -> "ifnull " ^ (stri i)
  | OpIfNonNull i -> "ifnonnull " ^ (stri i)
  | OpIfCmpEq i   -> "ifcmpEq " ^ (stri i)
  | OpIfCmpNe i   -> "ifcmpNe " ^ (stri i)
  | OpIfCmpLt i   -> "ifcmpLt " ^ (stri i)
  | OpIfCmpGe i   -> "ifcmpGe " ^ (stri i)
  | OpIfCmpGt i   -> "ifcmpGt " ^ (stri i)
  | OpIfCmpLe i   -> "ifcmpLe " ^ (stri i)
  | OpIfCmpAEq i  -> "ifacmpEq " ^ (stri i)
  | OpIfCmpANe i  -> "ifacmpNe " ^ (stri i)

  | OpGoto i      -> "goto " ^ (stri i)
  | OpJsr i       -> "jsr "  ^ (stri i)
  | OpRet i       -> "ret "  ^ (stri i)
  | OpTableSwitch _ -> "tableswitch"
  | OpLookupSwitch _ -> "lookupswitch"

  | OpNew cn       -> "new " ^ cn#simple_name
  | OpNewArray ty  -> "new array " ^ (vt ty)
  | OpAMultiNewArray (ty,i) -> "new multi array " ^ (ot ty) ^ " " ^ (stri i)
  | OpCheckCast ty     -> "checkcast " ^ (ot ty)
  | OpInstanceOf ty    -> "instanceof " ^ (ot ty)
  | OpGetStatic (cn,f) -> "getstatic " ^ cn#simple_name ^ ":" ^ f#name
  | OpPutStatic (cn,f) -> "putstatic " ^ cn#simple_name ^ ":" ^ f#name
  | OpGetField (cn,f)  -> "getfield "  ^ cn#simple_name ^ ":" ^ f#name
  | OpPutField (cn,f)  -> "putfield "  ^ cn#simple_name ^ ":" ^ f#name
  | OpArrayLength      -> "arraylength"
  | OpArrayLoad ty     -> "arrayload " ^ (jb ty)
  | OpArrayStore ty    -> "arraystore " ^ (jb ty)

  | OpInvokeVirtual (ty, m) ->
     "invokevirtual " ^ (ot ty) ^ ":" ^ m#name
  | OpInvokeSpecial (cn, m) ->
     "invokespecial " ^ cn#simple_name ^ ":" ^ m#name
  | OpInvokeStatic (cn, m) ->
     "invokestatic "  ^ cn#simple_name ^ ":" ^ m#name
  | OpInvokeInterface (cn, m) ->
     "invokeinterface " ^ cn#simple_name ^ ":" ^ m#name
  | OpInvokeDynamic (index, m) ->
     "invokedynamic " ^ (string_of_int index) ^ ":" ^ m#name
  | OpReturn ty -> "return " ^ (jb ty)

  | OpThrow -> "throw"
  | OpMonitorEnter -> "enter monitor"
  | OpMonitorExit  -> "exit monitor"

  | OpNop -> "nop"
  | OpBreakpoint -> "breakpoint"
  | OpInvalid -> "invalid"


let opcode_to_pretty = function
    OpLoad (ty, i)  ->
     LBLOCK [STR "load " ; java_basic_type_to_pretty ty; STR " "; INT i]
  | OpStore (ty, i) ->
     LBLOCK [STR "store "; java_basic_type_to_pretty ty; STR " "; INT i]
  | OpIInc (i1, i2)->
     LBLOCK [STR "iinc " ; INT i1; STR " "; INT i2]

  | OpPop    -> STR "pop"
  | OpPop2   -> STR "pop2"
  | OpDup    -> STR "dup"
  | OpDupX1  -> STR "dupX1"
  | OpDupX2  -> STR "dupX2"
  | OpDup2   -> STR "dup2"
  | OpDup2X1 -> STR "dup2X1"
  | OpDup2X2 -> STR "dup2X2"
  | OpSwap   -> STR "swap"

  | OpAConstNull    -> STR "aconstnull"
  | OpIntConst i    -> LBLOCK [STR "iconst " ; STR (Int32.to_string i)]
  | OpLongConst i   -> LBLOCK [STR "lconst " ; STR (Int64.to_string i)]
  | OpFloatConst f  -> LBLOCK [STR "fconst " ; STR (Printf.sprintf "%f" f)]
  | OpDoubleConst d -> LBLOCK [STR "dconst " ; STR (Printf.sprintf "%f" d)]
  | OpByteConst i   -> LBLOCK [STR "biconst "; INT i]
  | OpShortConst i  -> LBLOCK [STR "siconst "; INT i]
  | OpStringConst s ->
     let s =
       if has_control_characters s then replace_control_characters s else s in
     LBLOCK [STR "ld string "; STR s]
  | OpClassConst c ->
     LBLOCK [STR "ld object "; object_type_to_pretty c]

  | OpAdd ty  -> LBLOCK [STR "add " ; java_basic_type_to_pretty ty]
  | OpSub ty  -> LBLOCK [STR "sub " ; java_basic_type_to_pretty ty]
  | OpMult ty -> LBLOCK [STR "mult "; java_basic_type_to_pretty ty]
  | OpDiv ty  -> LBLOCK [STR "div " ; java_basic_type_to_pretty ty]
  | OpRem ty  -> LBLOCK [STR "rem " ; java_basic_type_to_pretty ty]
  | OpNeg ty  -> LBLOCK [STR "neg " ; java_basic_type_to_pretty ty]

  | OpIShl  -> STR "ishl"
  | OpLShl  -> STR "lshl"
  | OpIShr  -> STR "ishr"
  | OpLShr  -> STR "lshr"
  | OpIUShr -> STR "iushr"
  | OpLUShr -> STR "lushr"
  | OpIAnd  -> STR "iand"
  | OpLAnd  -> STR "land"
  | OpIOr   -> STR "ior"
  | OpLOr   -> STR "lor"
  | OpIXor  -> STR "ixor"
  | OpLXor  -> STR "lxor"

  (* Conversion *)
  | OpI2L   -> STR "i2l"
  | OpI2F   -> STR "i2f"
  | OpI2D   -> STR "i2d"
  | OpL2I   -> STR "l2i"
  | OpL2F   -> STR "l2f"
  | OpL2D   -> STR "l2d"
  | OpF2I   -> STR "f2i"
  | OpF2L   -> STR "f2l"
  | OpF2D   -> STR "f2d"
  | OpD2I   -> STR "d2i"
  | OpD2L   -> STR "d2l"
  | OpD2F   -> STR "d2f"
  | OpI2B   -> STR "i2b"
  | OpI2C   -> STR "i2c"
  | OpI2S   -> STR "i2s"

  | OpCmpL  -> STR "cmpl"
  | OpCmpFL -> STR "cmpfl"
  | OpCmpFG -> STR "cmpfg"
  | OpCmpDL -> STR "cmpdl"
  | OpCmpDG -> STR "cmpdg"

  | OpIfEq i      -> LBLOCK [STR "ifEq "; INT i]
  | OpIfNe i      -> LBLOCK [STR "ifNe "; INT i]
  | OpIfLt i      -> LBLOCK [STR "ifLt "; INT i]
  | OpIfGe i      -> LBLOCK [STR "ifGe "; INT i]
  | OpIfGt i      -> LBLOCK [STR "ifGt "; INT i]
  | OpIfLe i      -> LBLOCK [STR "ifLe "; INT i]
  | OpIfNull i    -> LBLOCK [STR "ifnull "; INT i]
  | OpIfNonNull i -> LBLOCK [STR "ifnonnull "; INT i]
  | OpIfCmpEq i   -> LBLOCK [STR "ifcmpEq "; INT i]
  | OpIfCmpNe i   -> LBLOCK [STR "ifcmpNe "; INT i]
  | OpIfCmpLt i   -> LBLOCK [STR "ifcmpLt "; INT i]
  | OpIfCmpGe i   -> LBLOCK [STR "ifcmpGe "; INT i]
  | OpIfCmpGt i   -> LBLOCK [STR "ifcmpGt "; INT i]
  | OpIfCmpLe i   -> LBLOCK [STR "ifcmpLe "; INT i]
  | OpIfCmpAEq i  -> LBLOCK [STR "ifacmpEq "; INT i]
  | OpIfCmpANe i  -> LBLOCK [STR "ifacmpNe "; INT i]

  | OpGoto i      -> LBLOCK [STR "goto "; INT i]
  | OpJsr i       -> LBLOCK [STR "jsr " ; INT i]
  | OpRet i       -> LBLOCK [STR "ret " ; INT i]

  | OpTableSwitch (default, low, high, table) ->
     LBLOCK [
         STR "tableswitch ";
         INT default;
         STR " (";
         STR (Int32.to_string low);
         STR ",";
         STR (Int32.to_string high);
         STR "): ";
         pretty_print_list (Array.to_list table) (fun i -> INT i) "[" "," "]"]

  | OpLookupSwitch (n, l) ->
     LBLOCK [
         STR "lookupswitch ";
         INT n;
         STR ": ";
         pretty_print_list
           l (fun (i32,i) ->
             LBLOCK [STR "("; STR (Int32.to_string i32); STR ", "; INT i; STR ")"])
           "[" "; " "]"]

  | OpNew cn ->
     LBLOCK [STR "new "; STR cn#abbreviated_name]

  | OpNewArray ty ->
     LBLOCK [STR "new array "; value_type_to_abbreviated_pretty ty]

  | OpAMultiNewArray (ty, i) ->
     LBLOCK [
         STR "new multi array ";
         object_type_to_abbreviated_pretty ty;
         STR " ";
         INT i]

  | OpCheckCast ty ->
     LBLOCK [STR "checkcast "; object_type_to_abbreviated_pretty ty]

  | OpInstanceOf ty ->
     LBLOCK [STR "instanceof "; object_type_to_abbreviated_pretty ty]

  | OpGetStatic (cn, f) ->
     LBLOCK [
         STR "getstatic "; STR cn#simple_name; STR ":"; f#to_abbreviated_pretty]

  | OpPutStatic (cn, f) ->
     LBLOCK [
         STR "putstatic "; STR cn#simple_name; STR ":"; f#to_abbreviated_pretty]

  | OpGetField (cn, f) ->
     LBLOCK [
         STR "getfield "; STR cn#simple_name; STR ":"; f#to_abbreviated_pretty]

  | OpPutField (cn, f) ->
     LBLOCK [
         STR "putfield "; STR cn#simple_name; STR ":"; f#to_abbreviated_pretty]

  | OpArrayLength ->
     STR "arraylength"

  | OpArrayLoad ty ->
     LBLOCK [STR "arrayload "; java_basic_type_to_pretty ty]

  | OpArrayStore ty ->
     LBLOCK [STR "arraystore "; java_basic_type_to_pretty ty]

  | OpInvokeVirtual (ty, m) ->
     LBLOCK [
         STR "invokevirtual ";
         object_type_to_abbreviated_pretty ty;
	 STR ":";
         m#to_abbreviated_pretty]

  | OpInvokeSpecial (cn, m) ->
     LBLOCK [
         STR "invokespecial ";
         STR cn#abbreviated_name;
         STR ":";
	 m#to_abbreviated_pretty]

  | OpInvokeStatic (cn, m) ->
     LBLOCK [
         STR "invokestatic ";
         STR cn#abbreviated_name;
         STR ":";
	 m#to_abbreviated_pretty]

  | OpInvokeInterface (cn, m) ->
     LBLOCK [
         STR "invokeinterface ";
         STR cn#abbreviated_name;
         STR ":";
	 m#to_abbreviated_pretty]

  | OpInvokeDynamic (index, m) ->
     LBLOCK [
         STR "invokedynamic ";
         INT index;
         STR ":";
         m#to_abbreviated_pretty]

  | OpReturn ty ->
     LBLOCK [STR "return "; java_basic_type_to_pretty ty]

  | OpThrow -> STR "throw"
  | OpMonitorEnter -> STR "enter monitor"
  | OpMonitorExit -> STR "exit monitor"

  | OpNop -> STR "nop"
  | OpBreakpoint -> STR "breakpoint"
  | OpInvalid -> STR "invalid"


let is_binop_opcode (opc:opcode_t) =
  match opc with
  (* Arithmetic *)
  | OpAdd _
    | OpSub _
    | OpMult _
    | OpDiv _
    | OpRem _

    (* Logic *)
    | OpIShl
    | OpLShl
    | OpIShr
    | OpLShr
    | OpIUShr
    | OpLUShr
    | OpIAnd
    | OpLAnd
    | OpIOr
    | OpLOr
    | OpIXor
    | OpLXor  -> true
  | _ -> false


let is_arithmetic_binop_opcode  (opc:opcode_t) =
  match opc with
  | OpAdd _ | OpSub _ | OpMult _ | OpDiv _ | OpRem _ -> true
  | _ -> false


let is_logical_binop_opcode (opc:opcode_t) =
  (is_binop_opcode opc) && (not (is_arithmetic_binop_opcode opc))


let is_converter_opcode (opc:opcode_t) =
  match opc with
  | OpI2L
    | OpI2F
    | OpI2D
    | OpL2I
    | OpL2F
    | OpL2D
    | OpF2I
    | OpF2L
    | OpF2D
    | OpD2I
    | OpD2L
    | OpD2F
    | OpI2B
    | OpI2C
    | OpI2S -> true
  | _ -> false


let is_test_opcode (opc:opcode_t) =
  match opc with
  | OpIfEq _
  | OpIfNe _
  | OpIfLt _
  | OpIfGe _
  | OpIfGt _
  | OpIfLe _
  | OpIfNull _
  | OpIfNonNull _
  | OpIfCmpEq _
  | OpIfCmpNe _
  | OpIfCmpLt _
  | OpIfCmpGe _
  | OpIfCmpGt _
  | OpIfCmpLe _
  | OpIfCmpAEq _
  | OpIfCmpANe _ -> true
  | _ -> false


let get_target_offset (opc:opcode_t) =
  match opc with
  | OpIfEq n
    | OpIfNe n
    | OpIfLt n
    | OpIfGe n
    | OpIfGt n
    | OpIfLe n
    | OpIfNull n
    | OpIfNonNull n
    | OpIfCmpEq n
    | OpIfCmpNe n
    | OpIfCmpLt n
    | OpIfCmpGe n
    | OpIfCmpGt n
    | OpIfCmpLe n
    | OpIfCmpAEq n
    | OpIfCmpANe n
    | OpGoto n -> n
  | _ ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "Opcode ";
               opcode_to_pretty opc;
               STR " does not have an offset"]))


let is_backward_test_opcode (opc:opcode_t) =
  (is_test_opcode opc) && ((get_target_offset opc) < 0)


let is_unary_test_opcode (opc:opcode_t) =
  match opc with
  | OpIfEq _
    | OpIfNe _
    | OpIfLt _
    | OpIfGe _
    | OpIfGt _
    | OpIfLe _
    | OpIfNull _
    | OpIfNonNull _ -> true
  | _ -> false


let is_forward_unary_test_opcode (opc:opcode_t) =
  (is_unary_test_opcode opc) && ((get_target_offset opc) > 0)


let is_binary_test_opcode (opc:opcode_t) =
  match opc with
  | OpIfCmpEq _
    | OpIfCmpNe _
    | OpIfCmpLt _
    | OpIfCmpGe _
    | OpIfCmpGt _
    | OpIfCmpLe _
    | OpIfCmpAEq _
    | OpIfCmpANe _ -> true
  | _ -> false


let is_forward_binary_test_opcode (opc:opcode_t) =
  (is_binary_test_opcode opc) && ((get_target_offset opc) > 0)


let is_comparison_opcode (opc:opcode_t) =
  match opc with
  | OpCmpL
    | OpCmpFL
    | OpCmpFG
    | OpCmpDL
    | OpCmpDG -> true
  | _ -> false

let invert_conditional_opcode (opc:opcode_t) =
  match opc with
    OpIfEq offset -> OpIfNe offset
  | OpIfNe offset -> OpIfEq offset
  | OpIfLt offset -> OpIfGe offset
  | OpIfGe offset -> OpIfLt offset
  | OpIfGt offset -> OpIfLe offset
  | OpIfLe offset -> OpIfGt offset
  | OpIfCmpAEq offset   -> OpIfCmpANe offset
  | OpIfCmpANe offset   -> OpIfCmpAEq offset
  | OpIfCmpGt offset    -> OpIfCmpLe offset
  | OpIfCmpGe offset    -> OpIfCmpLt offset
  | OpIfCmpLt offset    -> OpIfCmpGe offset
  | OpIfCmpLe offset    -> OpIfCmpGt offset
  | OpIfCmpNe offset    -> OpIfCmpEq offset
  | OpIfCmpEq offset    -> OpIfCmpNe offset
  | OpIfNull offset     -> OpIfNonNull offset
  | OpIfNonNull offset  -> OpIfNull offset
  | _ ->
     raise
       (JCH_failure
	  (LBLOCK [STR "opcode is not a conditional : "; opcode_to_pretty opc]))


class opcodes_t (opcodes: opcode_t array):opcodes_int =
object (self: _)

  method opcodes = opcodes

  method length = Array.length self#opcodes

  method replace (i:int) (opcode:opcode_t) =
    if i >= 0 && i < self#length then
      Array.set opcodes i opcode

  method instr_count =
    Array.fold_right (fun opc acc ->
      match opc with OpInvalid ->  acc | _ -> acc + 1) opcodes 0

  method at (i: int) =
    try
      self#opcodes.(i)
    with
    | Invalid_argument _ ->
       raise (JCH_failure (LBLOCK [STR "No bytecode at "; INT i]))

  method iteri (f:int -> opcode_t -> unit) =
    let oparray = Array.mapi (fun i opc -> (i,opc)) opcodes in
    let oplist = Array.fold_right (fun (i,opc) acc ->
      match opc with OpInvalid -> acc | _ -> (i,opc) :: acc) oparray [] in
    List.iter (fun (i,opc) -> f i opc) oplist

  method private is_valid (i:int) =
    i >= 0
    && i < self#length
    && (match self#opcodes.(i) with OpInvalid -> false | _ -> true)

  method next (i:int) =
    if i >= 0 && i < self#length then
      let k = ref (i+1) in
      begin
	while not (self#is_valid !k) && !k < (self#length -1) do k := !k+1 done;
	if self#is_valid !k then Some !k else None
      end
    else
      None

  method previous (i:int) =
    if i > 0 && i < self#length then
      let k = ref (i-1) in
      begin
	while not (self#is_valid !k) && !k > 0 do k := !k-1 done;
	if self#is_valid !k then Some !k else None
      end
    else
      None

  method offset_to_instrn_array =
    let length = self#length in
    let a = Array.make length 0 in
    let  instr = ref (-1) in
    for i = 0 to length - 1 do
      begin
	match self#opcodes.(i) with
	| OpInvalid -> ()
	| _ ->
	    instr := !instr + 1
      end;
      a.(i) <- !instr
    done;
    a

  method offset_to_from_instrn_arrays =
    let length = self#length in
    let a = Array.make length 0 in
    let pcs = ref [] in
    let  instr = ref (-1) in
    for i = 0 to length - 1 do
      begin
	match self#opcodes.(i) with
	| OpInvalid -> ()
	| _ ->
	    instr := !instr + 1;
	    pcs := i :: !pcs
      end;
      a.(i) <- !instr
    done;
    (a, Array.of_list (List.rev !pcs))

  method toPretty =
    let oparray = Array.mapi (fun i opc -> (i,opc)) opcodes in
    let oppretty = Array.fold_right
	(fun (i,opc) acc ->
	  match opc with
	  | OpInvalid -> acc
	  | _ -> LBLOCK [INT i; STR " "; opcode_to_pretty opc; NL; acc])
	oparray (STR "") in
    oppretty

end

let make_opcodes = new opcodes_t


class exception_handler_t
  ~(h_start: int)
  ~(h_end: int)
  ~(handler: int)
  ?(catch_type: class_name_int option)
  ():exception_handler_int =
object

  method h_start = h_start

  method h_end = h_end

  method handler = handler

  method catch_type = catch_type

  method toPretty =
    LBLOCK [
        fixed_length_pretty ~alignment:StrRight (INT h_start) 4;
        STR "  ";
	fixed_length_pretty ~alignment:StrRight (INT h_end) 4;
        STR "  ";
	fixed_length_pretty ~alignment:StrRight (INT handler) 4;
        STR "  ";
	(match catch_type with Some c -> c#toPretty | _ -> STR "any")]

end

let make_exception_handler = new exception_handler_t


class bytecode_t
  ~(max_stack: int)
  ~(max_locals: int)
  ~(code: opcodes_int)
  ~(exception_table: exception_handler_int list)
  ?(line_number_table: (int * int) list option)
  ?(local_variable_table: (int * int * string * value_type_t * int) list option)
  ?(local_variable_type_table:
      (int * int * string * field_type_signature_int * int) list option)
  ?(stack_map_midp: stackmap_int list option)
  ?(stack_map_java6: stackmap_int list option)
  ~(attributes: (string * string) list)
  ():bytecode_int =
object (self: _)

  method get_max_stack = max_stack

  method get_max_locals = max_locals

  method get_code = code

  method get_exception_table = exception_table

  method get_line_number_table = line_number_table

  method get_local_variable_table = local_variable_table

  method get_local_variable_type_table = local_variable_type_table

  method get_stack_map_midp = stack_map_midp

  method get_stack_map_java6 = stack_map_java6

  method get_attributes = attributes

  method get_local_variable_info ~(variable: int) ~(program_point: int) =
    match self#get_local_variable_table with
      | None -> None
      | Some lvt ->
          let offset =
            let code = self#get_code in
	      match code#at program_point with
		| OpStore _ ->
                    let i = ref (program_point + 1) in
                      while !i < code#length && (code#at !i) = OpInvalid do
			i := !i + 1
                      done;
                      !i - program_point
		| _ -> 0
          in
	    try
	      let (_, _, name, variable_type, _) =
		List.find
		  (fun (start, len, _, _, index) ->
		     program_point + offset >= start
                     && program_point + offset <= start + len
                     && index = variable
                  ) lvt
              in
		Some (name, variable_type)
            with _ -> None

  method get_source_line_number (program_point: int) =
    match self#get_line_number_table with
      | None -> None
      | Some lnt ->
          let rec find_line prev = function
            | (start_pc, line_number) :: r ->
		if (start_pc > program_point) then Some prev
		else find_line line_number r
            | [] -> Some prev
          in
            try
	      find_line (snd (List.hd lnt)) lnt
            with _ -> None

  method get_opcodes_per_line:((int * int list) list) =
    let lt = self#get_line_number_table in
    let code = self#get_code#opcodes in
    let opc_indices start len =
      let lst = ref [] in
      begin
	Array.iteri
	  (fun i c -> match c with OpInvalid -> () | _ -> lst := i::!lst)
	  (Array.sub code start len);
	List.map (fun i -> i+start) (List.rev !lst)
      end in
    let rec aux r = function
      | [] -> r
      | [(i1,i2)] -> (i2, opc_indices i1 ((Array.length code)-i1)) :: r
      | (i1,i2) :: (j1,j2) :: tl ->
	  aux ((i2, opc_indices i1 (j1-i1)) :: r) ((j1,j2)::tl) in
    match lt with
    | Some t ->  aux [] t
    | _ -> []

  method toPretty =
    LBLOCK [
        STR "max stack:  ";
        INT max_stack;
        NL;
	STR "max locals: ";
        INT max_locals;
        NL;
	code#toPretty;
        NL]


end

let make_bytecode = new bytecode_t
