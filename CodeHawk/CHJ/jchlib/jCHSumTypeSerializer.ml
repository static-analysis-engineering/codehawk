(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open CHPrettyUtil
   
(* jchlib *)
open JCHBasicTypesAPI
open JCHBasicTypes
   
module H = Hashtbl

class type ['a] sumtype_string_converter_int =
  object
    method to_string: 'a -> string
    method from_string: string -> 'a
  end

class ['a] sumtype_string_converter_t
           (name:string) (pairs:('a * string) list):['a] sumtype_string_converter_int =
object

  val tstable = H.create (List.length pairs)
  val sttable = H.create (List.length pairs)

  initializer
    List.iter (fun (t,s) -> begin H.add tstable t s ; H.add sttable s t end) pairs

  method to_string (t:'a) =
    if H.mem tstable t then
      H.find tstable t
    else
      raise (JCH_failure (LBLOCK [ STR "Type not found for sumtype " ; STR name ]))

  method from_string (s:string) =
    if H.mem sttable s then
      H.find sttable s
    else
      raise (JCH_failure (LBLOCK [ STR "No sumtype " ; STR name ;
                                  STR " for string " ; STR s ]))

end

let mk_sumtype_string_converter = new sumtype_string_converter_t

(* Converter that can be used when only a few types have
   additional data, which can be encoded into and decoded
   from the string
 *)
class ['a] fn_sumtype_string_converter_t
           (name:string)
           (pairs:('a * string) list)
           (f:'a -> string)
           (g:string -> 'a):['a] sumtype_string_converter_int =
object

  inherit ['a] sumtype_string_converter_t name pairs as super

  method to_string (t:'a) =
    try
      super#to_string t
    with
    | JCH_failure _ -> f t

  method from_string (s:string) =
    try
      super#from_string s
    with
    | JCH_failure _ -> g s

end

let mk_fn_sumtype_string_converter = new fn_sumtype_string_converter_t

let java_basic_type_serializer: java_basic_type_t sumtype_string_converter_int =
  mk_sumtype_string_converter
    "java_basic_type_t"
    [ (Int,"I"); (Short,"S"); (Char,"C"); (Byte,"B"); (Bool,"Z"); (Long,"L");
      (Float,"F"); (Double,"D"); (Int2Bool, "XIZX"); (ByteBool,"XBZX");
      (Object,"XLX"); (Void,"V") ]

let reference_kind_serializer: reference_kind_t sumtype_string_converter_int =
  mk_sumtype_string_converter
    "reference_kind_t"
    [ (REFGetField, "gf"); (REFGetStatic, "gs"); (REFPutField,"pf");
      (REFPutStatic,"ps"); (REFInvokeVirtual, "iv"); (REFInvokeStatic, "is");
      (REFInvokeSpecial,"ip"); (REFNewInvokeSpecial,"in"); (REFInvokeInterface,"if") ]

let arithmetic_op_serializer: arithmetic_op_t sumtype_string_converter_int =
  mk_sumtype_string_converter
    "arithmetic_op_t"
    [ (JPlus,"add"); (JMinus, "sub"); (JDivide, "div"); (JTimes, "mult") ]

let relational_op_serializer: relational_op_t sumtype_string_converter_int =
  mk_sumtype_string_converter
    "relational_op_t"
    [ (JEquals,"eq"); (JLessThan,"lt"); (JLessEqual,"le"); (JGreaterEqual,"ge");
      (JGreaterThan,"gt"); (JNotEqual,"ne") ]

class virtual ['a] complextyp_string_converter_t (name:string) =
object

  method virtual to_string: 'a -> string

  method from_string (s:string):'a =
    raise (JCH_failure (LBLOCK [ STR "No reverse construction possible for " ; STR name ]))

end


class jterm_string_converter_t:[jterm_t] sumtype_string_converter_int =
object

  inherit [jterm_t] complextyp_string_converter_t "jterm_t"

  method to_string (t:jterm_t) =
    match t with
    | JAuxiliaryVar _ -> "xv"
    | JLocalVar _ -> "lv"
    | JLoopCounter _ -> "lc"
    | JSymbolicConstant _ -> "symc"
    | JConstant _ -> "c"
    | JStaticFieldValue _ -> "sf"
    | JObjectFieldValue _ -> "of"
    | JBoolConstant _ -> "bc"
    | JFloatConstant _ -> "fc"
    | JStringConstant _ -> "sc"
    | JSize _ -> "si"
    | JPower _ -> "pw"
    | JUninterpreted _ -> "un"
    | JArithmeticExpr _ -> "ar"

end

let jterm_serializer:jterm_t sumtype_string_converter_int =
  new jterm_string_converter_t

class object_type_string_converter_t:[object_type_t] sumtype_string_converter_int =
object

  inherit [object_type_t] complextyp_string_converter_t "object_type_t"

  method to_string (t:object_type_t) =
    match t with
    | TClass _ -> "c"
    | TArray _ -> "a"

end

let object_type_serializer:object_type_t sumtype_string_converter_int =
  new object_type_string_converter_t

class value_type_string_converter_t:[value_type_t] sumtype_string_converter_int =
object

  inherit [value_type_t] complextyp_string_converter_t "value_type_t"

  method to_string (t:value_type_t) =
    match t with
    | TBasic _ -> "b"
    | TObject _ -> "o"

end

let value_type_serializer:value_type_t sumtype_string_converter_int =
  new value_type_string_converter_t
  

class constant_value_string_converter_t:[constant_value_t] sumtype_string_converter_int =
object

  inherit [constant_value_t] complextyp_string_converter_t "constant_value_t"

  method to_string (t:constant_value_t) =
    match t with
    | ConstString _ -> "s"
    | ConstInt _ -> "i"
    | ConstFloat _ -> "f"
    | ConstLong _ -> "l"
    | ConstDouble _ -> "d"
    | ConstClass _ -> "c"

end

let constant_value_serializer:constant_value_t sumtype_string_converter_int =
  new constant_value_string_converter_t

class descriptor_string_converter_t:[descriptor_t] sumtype_string_converter_int =
object

  inherit [descriptor_t] complextyp_string_converter_t "descriptor_t"

  method to_string (d:descriptor_t) =
    match d with
    | SValue _ -> "v"
    | SMethod _ -> "m"

end

let descriptor_serializer:descriptor_t sumtype_string_converter_int =
  new descriptor_string_converter_t

class method_handle_type_string_converter_t:[method_handle_type_t] sumtype_string_converter_int =
object

  inherit [method_handle_type_t] complextyp_string_converter_t "method_handle_type_t"

  method to_string (h:method_handle_type_t) =
    match h with
    | FieldHandle _ -> "f"
    | MethodHandle _ -> "m"
    | InterfaceHandle _ -> "i"

end

let method_handle_type_serializer:method_handle_type_t sumtype_string_converter_int =
  new method_handle_type_string_converter_t

class constant_serializer_t:[constant_t] sumtype_string_converter_int =
object

  inherit [constant_t] complextyp_string_converter_t "constant_t"

  method to_string (c:constant_t) =
    match c with
    | ConstValue _ -> "v"
    | ConstField _ -> "f"
    | ConstMethod _ -> "m"
    | ConstInterfaceMethod _ -> "i"
    | ConstDynamicMethod _ -> "d"
    | ConstNameAndType _ -> "n"
    | ConstStringUTF8 _ -> "s"
    | ConstMethodHandle _ -> "h"
    | ConstMethodType _ -> "t"
    | ConstUnusable -> "u"

end

let constant_serializer:constant_t sumtype_string_converter_int =
  new constant_serializer_t

class bootstrap_argument_serializer_t:[bootstrap_argument_t] sumtype_string_converter_int =
object

  inherit [bootstrap_argument_t] complextyp_string_converter_t "bootstrap_argument_t"

  method to_string (a:bootstrap_argument_t) =
    match a with
    | BootstrapArgConstantValue _ -> "c"
    | BootstrapArgMethodHandle _ -> "h"
    | BootstrapArgMethodType _ -> "t"

end

let bootstrap_argument_serializer:bootstrap_argument_t sumtype_string_converter_int =
  new bootstrap_argument_serializer_t
  
class opcode_serializer_t:[opcode_t] sumtype_string_converter_int =
object

  inherit [opcode_t] complextyp_string_converter_t "opcode_t" as super

  method to_string (opc:opcode_t) =
    match opc with
    | OpLoad _ -> "ld"
    | OpStore _ -> "st"
    | OpIInc _ -> "inc"
    | OpPop -> "pop"
    | OpPop2 -> "pop2"
    | OpDup -> "dup"
    | OpDupX1 -> "dupx1"
    | OpDupX2 -> "dupx2"
    | OpDup2 -> "dup2"
    | OpDup2X1 -> "dup2x1"
    | OpDup2X2 -> "dup2x2"
    | OpSwap -> "swap"
    | OpAConstNull -> "cnull"
    | OpIntConst _ -> "icst"
    | OpLongConst _ -> "lcst"
    | OpFloatConst _ -> "fcst"
    | OpDoubleConst _ -> "dcst"
    | OpByteConst _ -> "bcst"
    | OpShortConst _ -> "shcst"
    | OpStringConst _ -> "scst"
    | OpClassConst _ -> "ccst"
    | OpAdd _ -> "add"
    | OpSub _ -> "sub"
    | OpMult _ -> "mult"
    | OpDiv _ -> "div"
    | OpRem _ -> "rem"
    | OpNeg _ -> "neg"
    | OpIShl -> "shl"
    | OpLShl -> "lshl"
    | OpIShr -> "shr"
    | OpLShr -> "lshr"
    | OpIUShr -> "ushr"
    | OpLUShr -> "lushr"
    | OpIAnd -> "and"
    | OpLAnd -> "land"
    | OpIOr -> "or"
    | OpLOr -> "lor"
    | OpIXor -> "xor"
    | OpLXor -> "lxor"
    | OpI2L -> "i2l"
    | OpI2F -> "i2f"
    | OpI2D -> "i2d"
    | OpL2I -> "l2i"
    | OpL2F -> "l2f"
    | OpL2D -> "l2d"
    | OpF2I -> "f2i"
    | OpF2L -> "f2l"
    | OpF2D -> "f2d"
    | OpD2I -> "d2i"
    | OpD2L -> "d2l"
    | OpD2F -> "d2f"
    | OpI2B -> "i2b"
    | OpI2C -> "i2c"
    | OpI2S -> "i2s"
    | OpCmpL -> "cmpl"
    | OpCmpFL -> "cmpfl"
    | OpCmpFG -> "cmpfg"
    | OpCmpDL -> "cmpdl"
    | OpCmpDG -> "cmpdg"
    | OpIfEq _ -> "ifeq"
    | OpIfNe _ -> "ifne"
    | OpIfLt _ -> "iflt"
    | OpIfGe _ -> "ifge"
    | OpIfGt _ -> "ifgt"
    | OpIfLe _ -> "ifle"
    | OpIfNull _ -> "ifnull"
    | OpIfNonNull _ -> "ifnonnull"
    | OpIfCmpEq _ -> "ifcmpeq"
    | OpIfCmpNe _ -> "ifcmpne"
    | OpIfCmpLt _ -> "ifcmplt"
    | OpIfCmpGe _ -> "ifcmpge"
    | OpIfCmpGt _ -> "ifcmpgt"
    | OpIfCmpLe _ -> "ifcmple"
    | OpIfCmpAEq _ -> "ifcmpaeq"
    | OpIfCmpANe _ -> "ifcmpane"
    | OpGoto _ -> "goto"
    | OpJsr _ -> "jsr"
    | OpRet _ -> "jret"
    | OpTableSwitch _ -> "table"
    | OpLookupSwitch _ -> "loopkup"
    | OpNew _ -> "new"
    | OpNewArray _ -> "newa"
    | OpAMultiNewArray _ -> "mnewa"
    | OpCheckCast _ -> "ccast"
    | OpInstanceOf _ -> "iof"
    | OpGetStatic _ -> "gets"
    | OpPutStatic _ -> "puts"
    | OpGetField _ -> "getf"
    | OpPutField _ -> "putf"
    | OpArrayLength -> "alen"
    | OpArrayLoad _ -> "ald"
    | OpArrayStore _ -> "ast"
    | OpInvokeVirtual _ -> "invv"
    | OpInvokeSpecial _ -> "invsp"
    | OpInvokeStatic _ -> "invst"
    | OpInvokeInterface _ -> "invi"
    | OpInvokeDynamic _ -> "invd"
    | OpReturn _ -> "ret"
    | OpThrow -> "throw"
    | OpMonitorEnter -> "mone"
    | OpMonitorExit -> "monx"
    | OpNop -> "nop"
    | OpBreakpoint -> "bp"
    | OpInvalid -> "invalid"

  method from_string (s:string) =
    match s with
    | "pop" -> OpPop
    | "pop2" -> OpPop2
    | "dup" -> OpDup
    | "dupx1" -> OpDupX1
    | "dupx2" -> OpDupX2
    | "dup2" -> OpDup2
    | "dup2x1" -> OpDup2X1
    | "dup2x2" -> OpDup2X2
    | "swap" -> OpSwap
    | "cnull" -> OpAConstNull
    | "shl" -> OpIShl
    | "lshl" -> OpLShl
    | "shr" -> OpIShr
    | "lshr" -> OpLShr
    | "usrh" -> OpIUShr
    | "lushr" -> OpLUShr
    | "and" -> OpIAnd
    | "land" -> OpLAnd
    | "or" -> OpIOr
    | "lor" -> OpLOr
    | "xor" -> OpIXor
    | "lxor" -> OpLXor
    | "i2l" -> OpI2L
    | "i2f" -> OpI2F
    | "i2d" -> OpI2D
    | "l2i" -> OpL2I
    | "l2f" -> OpL2F
    | "l2d" -> OpL2D
    | "f2i" -> OpF2I
    | "f2l" -> OpF2L
    | "f2d" -> OpF2D
    | "d2i" -> OpD2I
    | "d2l" -> OpD2L
    | "d2f" -> OpD2F
    | "i2b" -> OpI2B
    | "i2c" -> OpI2C
    | "i2s" -> OpI2S
    | "cmpl" -> OpCmpL
    | "cmpfl" -> OpCmpFL
    | "cmpfg" -> OpCmpFG
    | "cmpdl" -> OpCmpDL
    | "cmpdg" -> OpCmpDG
    | "throw" -> OpThrow
    | "mone" -> OpMonitorEnter
    | "monx" -> OpMonitorExit
    | "nop" -> OpNop
    | "bp" -> OpBreakpoint
    | "invalid" -> OpInvalid
    | s -> super#from_string s

end
               
             
let opcode_serializer:opcode_t sumtype_string_converter_int =
  new opcode_serializer_t
