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
open CHNumerical
open CHPretty

(* chutil *)
open CHPrettyUtil
   
(* jchlib *)
open JCHBasicTypesAPI
open JCHBasicTypes
open JCHBytecode

(* jchpre *)
open JCHPreAPI
  
   
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
   from the strin
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

let variable_type_serializer: variable_type_t sumtype_string_converter_int =
  mk_sumtype_string_converter
    "variable_type_t"
    [ (NUM_LOOP_COUNTER_TYPE, "nlc"); (NUM_TMP_VAR_TYPE, "ntv");
      (SYM_TMP_VAR_TYPE, "stv"); (NUM_TMP_ARRAY_TYPE, "nta");
      (SYM_TMP_ARRAY_TYPE, "sta"); (NUM_VAR_TYPE, "nv");
      (SYM_VAR_TYPE, "sv"); (NUM_ARRAY_TYPE, "na");
      (SYM_ARRAY_TYPE, "sa") ]

class converteropcode_serializer_t:[opcode_t] sumtype_string_converter_int =
object

  method to_string (opc:opcode_t) =
    if is_converter_opcode opc then
      opcode_to_string opc
    else
      raise (JCH_failure (LBLOCK [ STR "Opcode " ; opcode_to_pretty opc ;
                                   STR " is not a converter opcode" ]))

  method from_string (s:string) =
    match s with
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
    | s ->
       raise (JCH_failure (LBLOCK [ STR "Opcode tag " ; STR s ;
                                    STR " not recognized as a converter opcode" ]))
end

let converteropcode_serializer = new converteropcode_serializer_t

class binopcode_serializer_t:[opcode_t] sumtype_string_converter_int =
object

  method to_string (opc:opcode_t) =
    let addt s t = s ^ "_" ^ (java_basic_type_to_signature_string t) in
    if is_binop_opcode opc then
      match opc with
      | OpAdd t -> addt "add" t
      | OpSub t -> addt "sub" t
      | OpMult t -> addt "mult" t
      | OpDiv t -> addt "div" t
      | OpRem t -> addt "rem" t
      | _ -> opcode_to_string opc
    else
      raise (JCH_failure (LBLOCK [ STR "Opcode " ; opcode_to_pretty opc ;
                                   STR " is not a binory operation opcode" ]))

  method from_string (s:string) =
    let gett = java_basic_type_of_signature_string in
    match (nsplit '_' s) with
    | [ s1 ; s2 ] ->
       (match s1 with
        | "add" -> OpAdd (gett s2)
        | "sub" -> OpSub (gett s2)
        | "mult" -> OpMult (gett s2)
        | "div" -> OpDiv (gett s2)
        | "rem" -> OpRem (gett s2)
        | s ->
           raise (JCH_failure (LBLOCK [ STR "Opcode tag " ; STR s ;
                                        STR " not recognized" ])))
    | [ s ] ->
       (match s with
        | "ishl" -> OpIShl
        | "lshl" -> OpLShl
        | "ishr" -> OpIShr
        | "lshr" -> OpLShr
        | "iushr" -> OpIUShr
        | "lushr" -> OpLUShr
        | "iand" -> OpIAnd
        | "land" -> OpLAnd
        | "ior" -> OpIOr
        | "lor" -> OpLOr
        | "ixor" -> OpIXor
        | "lxor" -> OpLXor
        | s ->
           raise (JCH_failure (LBLOCK [ STR "Opcode tag " ; STR s ;
                                        STR " not recognized" ])))
    | [] ->
       raise (JCH_failure (LBLOCK [ STR "No opcode tag found" ]))
    | l ->
       raise (JCH_failure (LBLOCK [ STR "Unexpected sequence of strings for opcode: ";
                                    pretty_print_list l (fun s -> STR s) "[" "; " "]" ]))
end
    
let binopcode_serializer = new binopcode_serializer_t
                         
let non_virtual_target_type_serializer: non_virtual_target_type_t sumtype_string_converter_int =
  mk_sumtype_string_converter
    "non_virtual_target_type_t"
    [ (PrivateMethod, "p"); (StaticMethod, "s"); (FinalClass, "fc"); (FinalMethod, "fm");
      (LocalAnalysis, "la") ]

class virtual ['a] complextyp_string_converter_t (name:string) =
        object
          
          method virtual to_string: 'a -> string
                       
          method from_string (s:string):'a =
            raise (JCH_failure (LBLOCK [ STR "No reverse construction possible for " ; STR name ]))
            
        end
        
class call_targets_string_converter_t:[call_targets_t] sumtype_string_converter_int =
object

  inherit [ call_targets_t ] complextyp_string_converter_t "call_targets_t"

  method to_string (e:call_targets_t) =
    match e with
    | NonVirtualTarget _ -> "nv"
    | ConstrainedVirtualTargets _ -> "cv"
    | VirtualTargets _ -> "v"
    | EmptyTarget _ -> "empty"

end

let call_targets_serializer:call_targets_t sumtype_string_converter_int =
  new call_targets_string_converter_t

class taint_origin_type_converter_t:[taint_origin_type_t] sumtype_string_converter_int =
object

  inherit [ taint_origin_type_t ] complextyp_string_converter_t "taint_origin_type_t"

  method to_string (t:taint_origin_type_t) =
    match t with
    | T_ORIG_VAR _ -> "v"
    | T_ORIG_FIELD _ -> "f"
    | T_ORIG_CALL _ -> "c"
    | T_ORIG_TOP_TARGET _ -> "t"
    | T_ORIG_STUB _ -> "s"

end

let taint_origin_type_serializer:taint_origin_type_t sumtype_string_converter_int =
  new taint_origin_type_converter_t

class taint_node_type_converter_t:[taint_node_type_t] sumtype_string_converter_int =
object

  inherit [ taint_node_type_t ] complextyp_string_converter_t "taint_node_type_t"

  method to_string (t:taint_node_type_t) =
    match t with
    | TN_FIELD _ -> "f"
    | TN_OBJECT_FIELD _ -> "o"
    | TN_VAR _ -> "v"
    | TN_VAR_EQ _ -> "q"
    | TN_CALL _ -> "c"
    | TN_UNKNOWN_CALL _ -> "u"
    | TN_CONDITIONAL _ -> "j"
    | TN_SIZE _ -> "s"
    | TN_REF_EQUAL -> "r"

end

let taint_node_type_serializer:taint_node_type_t sumtype_string_converter_int =
  new taint_node_type_converter_t

class bc_basicvalue_converter_t:[bc_basicvalue_t] sumtype_string_converter_int =
object

  inherit [ bc_basicvalue_t ] complextyp_string_converter_t "bc_basicvalue_t"

  method to_string (a:bc_basicvalue_t) =
    match a with
    | BcvArg 0 -> "0"
    | BcvArg 1 -> "1"
    | BcvArg 2 -> "2"
    | BcvArg _ -> "n"
    | BcvIntConst n when numerical_zero#equal n -> "c:0"
    | BcvIntConst n when numerical_one#equal n -> "c:1"
    | BcvIntConst _ -> "c"
    | BcvLongConst _ -> "l"
    | BcvByteConst _ -> "b"
    | BcvShortConst _ -> "si"
    | BcvDoubleConst _ -> "d"
    | BcvFloatConst _ -> "f"
    | BcvArrayElement _ -> "a"
    | BcvThisField _ -> "f"
    | BcvThatField _ -> "t"
    | BcvStaticField _ -> "d"
    | BcvArrayLength _ -> "h"
    | BcvInstanceOf _ -> "i"
    | BcvUnOpResult _ -> "u"
    | BcvBinOpResult _ -> "o"
    | BcvQResult _ -> "q"
    | BcvConvert _ -> "v"
    | BcvCallRv _ -> "r"

end

let bc_basicvalue_serializer:bc_basicvalue_t sumtype_string_converter_int =
  new bc_basicvalue_converter_t

class bc_objectvalue_converter_t:[bc_objectvalue_t] sumtype_string_converter_int =
object

  inherit [ bc_objectvalue_t] complextyp_string_converter_t "bc_objectvalue_t"

  method to_string (a:bc_objectvalue_t) =
    match a with
    | BcoArg 0 -> "0"
    | BcoArg 1 -> "1"
    | BcoArg 2 -> "2"
    | BcoArg _ -> "n"
    | BcoNull -> "u"
    | BcoClassConst _ -> "c"
    | BcoStringConst _ -> "s"
    | BcoNewObject _ -> "o"
    | BcoNewArray _ -> "a"
    | BcoMultiNewArray _ -> "m"
    | BcoArrayElement _ -> "e"
    | BcoThisField _ -> "f"
    | BcoThatField _ -> "t"
    | BcoStaticField _ -> "d"
    | BcoCheckCast _ -> "k"
    | BcoQResult _ -> "q"
    | BcoCallRv _ -> "r"

end

let bc_objectvalue_serializer:bc_objectvalue_t sumtype_string_converter_int =
  new bc_objectvalue_converter_t

class bc_action_converter_t:[bc_action_t] sumtype_string_converter_int =
object

  inherit [ bc_action_t ] complextyp_string_converter_t "bc_action_t"

  method to_string (a:bc_action_t) =
    match a with
    | BcNop -> "n"
    | BcNopX -> "x"
    | BcInitObject -> "i"
    | BcInitSuper -> "s"
    | BcNewObject _ -> "o"
    | BcDropValues _ -> "d"
    | BcPutThisField _ -> "f"
    | BcPutThatField _ -> "p"
    | BcPutStaticField _ -> "d"
    | BcArrayStore _ -> "a"
    | BcConditionalAction _ -> "c"                                            
    | BcWrapCall _ -> "w"
    | BcThrow _ -> "t"

end

let bc_action_serializer:bc_action_t sumtype_string_converter_int =
  new bc_action_converter_t
                    
class bc_pattern_converter_t:[bc_pattern_t] sumtype_string_converter_int =
object

  inherit [ bc_pattern_t ] complextyp_string_converter_t "bc_pattern_t"

  method to_string (p:bc_pattern_t) =
    match p with
    | BcpNop -> "n"
    | BcpNopX -> "x"
    | BcpAction _ -> "a"
    | BcpResult _ -> "r"
    | BcpThrow _ -> "t"
    | BcpResultExcept _ -> "e"
    | BcpResultExceptThrow _ -> "s"
    | BcpActionExcept _ -> "c"
    | BcpActionExceptThrow _ -> "i"
    | BcpInfiniteLoop _ -> "l"
    | BcpIllegalSeq (s,_) -> "i:" ^ s

end

let bc_pattern_serializer:bc_pattern_t sumtype_string_converter_int =
  new bc_pattern_converter_t
