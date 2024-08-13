(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet and Henny Sipma
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
(** Definition of most data types used in jchlib *)

(* chlib *)
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument


(** {1 Basic types} *)

class type indexed_hash_table_int =
  object

    method add: (string list * int list) -> int
    method retrieve: int -> (string list * int list)
    method values: (string list * int list) list
    method items : ((string list * int list) * int) list
    method size: int
    method get_name: string
    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

  end

type constantstring = string * bool * int


type taint_t = TRUSTED | TAINT_UNKNOWN | TAINTED


(** {1 Java byte code types} *)

type field_kind_t = NotFinal | Final | Volatile

type access_t = Default | Public | Private | Protected

type version_t = { major : int; minor : int; }

type reference_kind_t =
  | REFGetField         (* 1 *)
  | REFGetStatic        (* 2 *)
  | REFPutField         (* 3 *)
  | REFPutStatic        (* 4 *)
  | REFInvokeVirtual    (* 5 *)
  | REFInvokeStatic     (* 6 *)
  | REFInvokeSpecial    (* 7 *)
  | REFNewInvokeSpecial (* 8 *)
  | REFInvokeInterface  (* 9 *)

type java_basic_type_t =
  | Int
  | Short
  | Char
  | Byte
  | Bool
  | Long
  | Float
  | Double
  | Int2Bool
  | ByteBool
  | Object
  | Void


class type class_name_int =
object ('a)
  method compare: 'a -> int
  method equal: 'a -> bool
  method index: int
  method name: string
  method package: string list
  method abbreviated_package_name: string
  method package_name: string
  method simple_name: string
  method abbreviated_name: string
  method toPretty: pretty_t
end

type object_type_t = TClass of class_name_int | TArray of value_type_t

and value_type_t = TBasic of java_basic_type_t | TObject of object_type_t

type constant_value_t =
  | ConstString of string
  | ConstInt of int32
  | ConstFloat of float
  | ConstLong of int64
  | ConstDouble of float
  | ConstClass of object_type_t

type element_value_t =
  | EVCstByte of int
  | EVCstChar of int
  | EVCstInt of int32
  | EVCstShort of int
  | EVCstBoolean of int
  | EVCstDouble of float
  | EVCstFloat of float
  | EVCstLong of int64
  | EVCstString of string
  | EVEnum of (class_name_int * string)
  | EVClass of value_type_t option
  | EVAnnotation of annotation_t
  | EVArray of element_value_t list

and annotation_t = {
  kind : class_name_int;
  element_value_pairs : (string * element_value_t) list;
}

type verification_type_t =
  | VTop
  | VInteger
  | VFloat
  | VDouble
  | VLong
  | VNull
  | VUninitializedThis
  | VObject of object_type_t
  | VUninitialized of int


class type stackmap_int =
object
  method stack: int * verification_type_t list * verification_type_t list
end

class type field_signature_data_int =
object ('a)
  method compare     : 'a -> int
  method descriptor  : value_type_t
  method name        : string
  method toPretty    : pretty_t
  method to_string   : string
end

class type field_signature_int =
object ('a)
  method compare     : 'a -> int
  method equal       : 'a -> bool
  method index       : int
  method name        : string
  method descriptor  : value_type_t
  method field_signature_data: field_signature_data_int
  method toPretty    : pretty_t
  method to_abbreviated_pretty: pretty_t
  method to_signature_string: string
  method to_string   : string
end

class type method_descriptor_int =
object ('a)
  method compare     : 'a -> int
  method arguments   : value_type_t list    (* does not include this *)
  method return_value: value_type_t option
  method toPretty    : pretty_t
  method to_string   : string
end

class type method_signature_data_int =
object ('a)
  method compare     : 'a -> int
  method name        : string
  method descriptor  : method_descriptor_int
  method is_static   : bool
  method toPretty    : pretty_t
  method to_string   : string
end

class type method_signature_int =
object ('a)
  method compare     : 'a -> int
  method equal       : 'a -> bool
  method index       : int
  method name        : string
  method descriptor  : method_descriptor_int
  method method_signature_data: method_signature_data_int
  method is_static   : bool
  method has_return_value: bool
  method has_object_return_value: bool
  method has_basic_return_value : bool
  method argcount    : int
  method write_xmlx  :
           ?varnamemapping:(int -> string) option -> xml_element_int -> unit
  method toPretty    : pretty_t
  method to_abbreviated_pretty: pretty_t
  method to_signature_string: string
  method to_string   : string
end

class type class_field_signature_data_int =
object ('a)
  method compare        : 'a -> int
  method class_name     : class_name_int
  method name           : string
  method field_signature: field_signature_int
  method toPretty       : pretty_t
end

class type class_method_signature_data_int =
object ('a)
  method compare         : 'a -> int
  method name            : string
  method class_name      : class_name_int
  method method_signature: method_signature_int
  method is_static       : bool
  method toPretty        : pretty_t
  method to_abbreviated_pretty: pretty_t
end

class type class_field_signature_int =
object ('a)
  method compare         : 'a -> int
  method equal           : 'a -> bool
  method index           : int
  method class_name      : class_name_int
  method name            : string
  method field_signature : field_signature_int
  method class_field_signature_data: class_field_signature_data_int
  method toPretty        : pretty_t
  method to_string       : string
end

class type class_method_signature_int =
object ('a)
  method compare         : 'a -> int
  method equal           : 'a -> bool
  method index           : int
  method name            : string
  method class_name      : class_name_int
  method method_signature: method_signature_int
  method class_method_signature_data  : class_method_signature_data_int
  method is_static       : bool
  method class_method_signature_string: string
  method class_method_signature_string_md5: string
  method method_signature_string      : string
  method method_name_string           : string
  method toPretty        : pretty_t
  method to_abbreviated_pretty: pretty_t
end

type descriptor_t =
  | SValue of value_type_t
  | SMethod of method_descriptor_int

type method_handle_type_t =
  | FieldHandle of class_name_int * field_signature_int
  | MethodHandle of object_type_t * method_signature_int
  | InterfaceHandle of class_name_int * method_signature_int

type constant_t =
  | ConstValue of constant_value_t
  | ConstField of (class_name_int * field_signature_int)
  | ConstMethod of (object_type_t * method_signature_int)
  | ConstInterfaceMethod of (class_name_int * method_signature_int)
  | ConstDynamicMethod of int * method_signature_int
  | ConstNameAndType of string * descriptor_t
  | ConstStringUTF8 of string
  | ConstMethodHandle of reference_kind_t * method_handle_type_t
  | ConstMethodType of method_descriptor_int
  | ConstUnusable

type bootstrap_argument_t =
  | BootstrapArgConstantValue of constant_value_t
  | BootstrapArgMethodHandle of reference_kind_t * method_handle_type_t
  | BootstrapArgMethodType of method_descriptor_int

type bootstrap_method_data_t = {
    bm_kind:reference_kind_t ;
    bm_handle: method_handle_type_t ;
    bm_args: bootstrap_argument_t list }

class type bootstrap_method_int =
  object
    method get_kind: reference_kind_t
    method get_method_ref: method_handle_type_t
    method get_arguments: bootstrap_argument_t list
    method get_data: bootstrap_method_data_t
    method get_lambda_function: (object_type_t * method_signature_int) option
    method toPretty: pretty_t
  end

(** {1 Dictionary} *)

class type dictionary_int =
object
  method make_class_name: string -> class_name_int
  method make_field_signature: string -> value_type_t -> field_signature_int
  method make_class_field_signature :
    class_name_int -> field_signature_int -> class_field_signature_int
  method make_method_signature      :
    bool -> string -> method_descriptor_int -> method_signature_int
  method make_class_method_signature:
           class_name_int -> method_signature_int -> class_method_signature_int

  method retrieve_class_name: int -> class_name_int
  method retrieve_field_signature: int -> field_signature_int
  method retrieve_method_signature: int -> method_signature_int
  method retrieve_class_method_signature: int -> class_method_signature_int
  method retrieve_class_field_signature : int -> class_field_signature_int

  method index_string: string -> int
  method index_class_name: string -> int
  method index_object_type: object_type_t -> int
  method index_value_type: value_type_t -> int
  method index_field_signature_data: field_signature_data_int -> int
  method index_class_field_signature_data: class_field_signature_data_int -> int
  method index_method_descriptor: method_descriptor_int -> int
  method index_method_signature_data: method_signature_data_int -> int
  method index_class_method_signature_data:
           class_method_signature_data_int -> int
  method index_constant_value: constant_value_t -> int
  method index_descriptor: descriptor_t -> int
  method index_method_handle_type: method_handle_type_t -> int
  method index_constant: constant_t -> int
  method index_bootstrap_argument: bootstrap_argument_t -> int
  method index_bootstrap_method_data: bootstrap_method_data_t -> int

  method get_string: int -> string
  method get_class_name: int -> string
  method get_object_type: int -> object_type_t
  method get_value_type: int -> value_type_t
  method get_field_signature_data: int -> field_signature_data_int
  method get_class_field_signature_data: int -> class_field_signature_data_int
  method get_method_descriptor: int -> method_descriptor_int
  method get_method_signature_data: int -> method_signature_data_int
  method get_class_method_signature_data: int -> class_method_signature_data_int
  method get_constant_value: int -> constant_value_t
  method get_descriptor: int -> descriptor_t
  method get_method_handle_type: int -> method_handle_type_t
  method get_constant: int -> constant_t
  method get_bootstrap_argument: int -> bootstrap_argument_t
  method get_bootstrap_method_data: int -> bootstrap_method_data_t

  method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
  method write_xml_object_type:
           ?tag:string -> xml_element_int -> object_type_t -> unit
  method write_xml_value_type :
           ?tag:string -> xml_element_int -> value_type_t -> unit
  method write_xml_method_descriptor:
           ?tag:string -> xml_element_int -> method_descriptor_int -> unit
  method write_xml_constant_value:
           ?tag:string -> xml_element_int -> constant_value_t -> unit
  method write_xml_descriptor:
           ?tag:string -> xml_element_int -> descriptor_t -> unit
  method write_xml_method_handle_type:
           ?tag:string -> xml_element_int -> method_handle_type_t -> unit
  method write_xml_constant:
           ?tag:string -> xml_element_int -> constant_t -> unit
  method write_xml_bootstrap_argument:
           ?tag:string -> xml_element_int -> bootstrap_argument_t -> unit
  method write_xml_bootstrap_method_data:
           ?tag:string -> xml_element_int -> bootstrap_method_data_t -> unit

  method read_xml_object_type : ?tag:string -> xml_element_int -> object_type_t
  method read_xml_value_type  : ?tag:string -> xml_element_int -> value_type_t
  method read_xml_descriptor : ?tag:string -> xml_element_int -> descriptor_t
  method read_xml_constant_value:
           ?tag:string -> xml_element_int -> constant_value_t
  method read_xml_method_descriptor:
           ?tag:string -> xml_element_int -> method_descriptor_int
  method read_xml_method_handle_type:
           ?tag:string -> xml_element_int -> method_handle_type_t
  method read_xml_constant:
           ?tag:string -> xml_element_int -> constant_t
  method read_xml_bootstrap_argument:
           ?tag:string -> xml_element_int -> bootstrap_argument_t
  method read_xml_bootstrap_method_data:
           ?tag:string -> xml_element_int -> bootstrap_method_data_t

  method get_method_signatures: method_signature_int list

  method list_class_names: class_name_int list
  method list_unrecognized_class_names: (string * string) list
  method list_converted_method_names: (string * string) list

  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit
end


(** {1 Signatures} *)

type type_argument_kind_t =
  | ArgumentExtends
  | ArgumentInherits
  | ArgumentIs
  | ArgumentIsAny

type throws_signature_kind_t =
  | ThrowsClass
  | ThrowsTypeVariable

type type_signature_kind_t =
  | BasicType
  | ObjectType

type field_type_signature_kind_t =
  | ClassType
  | ArrayType
  | TypeVariable

class type type_variable_int =
object
  method name    : string
  method toPretty: pretty_t
end

class type simple_class_type_signature_int =
object
  method name          : string
  method type_arguments: type_argument_int list
  method toPretty      : pretty_t
end

and class_type_signature_int =
object
  method enclosing_classes: simple_class_type_signature_int list
  method package          : string list
  method simple_class_type_signature: simple_class_type_signature_int
  method toPretty         : pretty_t
end

and formal_type_parameter_int =
object
  method name                : string
  method class_bound         : field_type_signature_int option
  method interface_bounds    : field_type_signature_int list
  method toPretty            : pretty_t
end

and type_argument_int =
object
  method field_type_signature : field_type_signature_int
  method kind                 : type_argument_kind_t
  method toPretty             : pretty_t
end

and throws_signature_int =
object
  method class_type_signature: class_type_signature_int
  method kind                : throws_signature_kind_t
  method type_variable       : type_variable_int
  method toPretty            : pretty_t
end

and type_signature_int =
object
  method basic_type : java_basic_type_t
  method kind       : type_signature_kind_t
  method object_type: field_type_signature_int
  method toPretty   : pretty_t
end

and field_type_signature_int =
object
  method array_type   : type_signature_int
  method class_type   : class_type_signature_int
  method kind         : field_type_signature_kind_t
  method type_variable: type_variable_int
  method toPretty     : pretty_t
end

class type class_signature_int =
object
  method formal_type_parameters: formal_type_parameter_int list
  method super_class           : class_type_signature_int
  method super_interfaces      : class_type_signature_int list
  method toPretty              : pretty_t
end

class type method_type_signature_int =
object
  method formal_type_parameters: formal_type_parameter_int list
  method return_type           : type_signature_int option
  method throws                : throws_signature_int list
  method type_signature        : type_signature_int list
  method toPretty              : pretty_t
end


(** {1 Byte code opcodes} *)

type opcode_t =

(* Access to a local variables *)
  | OpLoad of java_basic_type_t * int
  | OpStore of java_basic_type_t * int
  | OpIInc of int * int

(* Stack permutation *)
  | OpPop
  | OpPop2
  | OpDup
  | OpDupX1
  | OpDupX2
  | OpDup2
  | OpDup2X1
  | OpDup2X2
  | OpSwap

(* Constant loading / it corresponds to bytecodes *const* and ldc* *)
  | OpAConstNull
  | OpIntConst of int32
  | OpLongConst of int64
  | OpFloatConst of float
  | OpDoubleConst of float
  | OpByteConst of int
  | OpShortConst of int
  | OpStringConst of string
  | OpClassConst of object_type_t

  (* Arithmetic *)
  | OpAdd of java_basic_type_t
  | OpSub of java_basic_type_t
  | OpMult of java_basic_type_t
  | OpDiv of java_basic_type_t
  | OpRem of java_basic_type_t
  | OpNeg of java_basic_type_t

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
  | OpLXor

  (* Conversion *)
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
  | OpI2S

  (* Comparison *)
  | OpCmpL
  | OpCmpFL
  | OpCmpFG
  | OpCmpDL
  | OpCmpDG

  (* Conditional jump *)
  | OpIfEq of int
  | OpIfNe of int
  | OpIfLt of int
  | OpIfGe of int
  | OpIfGt of int
  | OpIfLe of int
  | OpIfNull of int
  | OpIfNonNull of int
  | OpIfCmpEq of int
  | OpIfCmpNe of int
  | OpIfCmpLt of int
  | OpIfCmpGe of int
  | OpIfCmpGt of int
  | OpIfCmpLe of int
  | OpIfCmpAEq of int
  | OpIfCmpANe of int

  (* Unconditional jump *)
  | OpGoto of int
  | OpJsr of int          (* deprecated; not handled *)
  | OpRet of int          (* deprecated; not handled *)
  | OpTableSwitch of int * int32 * int32 * int array
  | OpLookupSwitch of int * (int32 * int) list

  (* Heap and static fields *)
  | OpNew of class_name_int
  | OpNewArray of value_type_t
  | OpAMultiNewArray of object_type_t * int
  | OpCheckCast of object_type_t
  | OpInstanceOf of object_type_t
  | OpGetStatic of class_name_int * field_signature_int
  | OpPutStatic of class_name_int * field_signature_int
  | OpGetField of class_name_int * field_signature_int
  | OpPutField of class_name_int * field_signature_int
  | OpArrayLength
  | OpArrayLoad of java_basic_type_t
  | OpArrayStore of java_basic_type_t

  (* Method invocation and return *)
  | OpInvokeVirtual of object_type_t * method_signature_int
  | OpInvokeSpecial of class_name_int * method_signature_int
  | OpInvokeStatic of class_name_int * method_signature_int
  | OpInvokeInterface of class_name_int * method_signature_int
  | OpInvokeDynamic of int * method_signature_int
  | OpReturn of java_basic_type_t

  (* Exceptions and threads *)
  | OpThrow
  | OpMonitorEnter
  | OpMonitorExit

  (* Other *)
  | OpNop
  | OpBreakpoint
  | OpInvalid


class type opcodes_int =
  object
    method replace: int -> opcode_t -> unit
    method at: int -> opcode_t
    method length: int
    method instr_count: int
    method opcodes: opcode_t array

    method offset_to_instrn_array: int array
    method offset_to_from_instrn_arrays: int array * int array

    method iteri: (int -> opcode_t -> unit) -> unit
    method next: int -> int option
    method previous: int -> int option

    method toPretty: pretty_t
  end


class type exception_handler_int =
  object
    method catch_type: class_name_int option
    method h_end: int
    method h_start: int
    method handler: int
    method toPretty: pretty_t
  end


class type bytecode_int =
  object
    method get_attributes          : (string * string) list
    method get_code                : opcodes_int
    method get_exception_table     : exception_handler_int list
    method get_line_number_table   : (int * int) list option
    method get_local_variable_info :
             variable:int -> program_point:int -> (string * value_type_t) option
    method get_local_variable_table:
             (int * int * string * value_type_t * int) list option
    method get_local_variable_type_table:
             (int * int * string * field_type_signature_int * int) list option
    method get_max_locals          : int
    method get_max_stack           : int
    method get_opcodes_per_line    : (int * int list) list
    method get_source_line_number  : int -> int option
    method get_stack_map_java6     : stackmap_int list option
    method get_stack_map_midp      : stackmap_int list option
    method toPretty                : pretty_t
  end


(** {1 Methods} *)

type implementation_t = Native | Bytecode of bytecode_int

class type attributes_int =
  object
    method is_deprecated: bool
    method is_synthetic : bool
    method other        : (string * string) list
  end

class type method_annotations_int =
  object
    method global       : (annotation_t * bool) list
    method parameters   : (annotation_t * bool) list list
  end

class type method_int =
  object
    method generic_signature : method_type_signature_int option

    (* accessors *)
    method get_annotation_default    : element_value_t option
    method get_annotations           : method_annotations_int
    method get_attributes            : attributes_int
    method get_class_method_signature: class_method_signature_int
    method get_exceptions            : class_name_int list
    method get_implementation        : implementation_t
    method get_other_flags           : int list
    method get_signature             : method_signature_int
    method get_visibility            : access_t

    (* predicates *)
    method has_varargs    : bool
    method is_abstract    : bool
    method is_bridge      : bool
    method is_concrete    : bool
    method is_final       : bool
    method is_static      : bool
    method is_strict      : bool
    method is_synchronized: bool
    method is_synthetic   : bool

    (* printing *)
    method toPretty : pretty_t
  end

(** {1 Common (class + interface)} *)

type inner_class_kind_t = ConcreteClass | Abstract | Interface

class type field_int =
  object

    method kind : field_kind_t

    (* accessors *)
    method get_annotations      : (annotation_t * bool) list
    method get_attributes       : attributes_int
    method get_class_signature  : class_field_signature_int
    method get_generic_signature: field_type_signature_int option
    method get_other_flags      : int list
    method get_signature        : field_signature_int
    method get_value            : constant_value_t option
    method get_visibility       : access_t

    (* predicates *)
    method is_synthetic      : bool
    method is_class_field    : bool
    method is_enum           : bool
    method is_interface_field: bool
    method is_static         : bool
    method is_final          : bool
    method is_transient      : bool

    (* printing *)
    method toPretty : pretty_t
  end


class type inner_class_int =
  object

    method kind : inner_class_kind_t

    (* accessors *)
    method get_access          : access_t
    method get_name            : class_name_int option
    method get_other_flags     : int list
    method get_outer_class_name: class_name_int option
    method get_source_name     : string option

    (* predicates *)
    method is_annotation  : bool
    method is_enum        : bool
    method is_final       : bool
    method is_static      : bool
    method is_synthetic   : bool
  end

class type java_class_or_interface_int =
  object

    (* accessors *)
    method get_annotations      : (annotation_t * bool) list
    method get_bootstrap_methods: bootstrap_method_int list
    method get_bootstrap_method : int -> bootstrap_method_int
    method get_concrete_methods : method_int list
    method get_instruction_count: int
    method get_consts           : constant_t array
    method get_enclosing_method :
             (class_name_int * method_signature_int option) option
    method get_field            : field_signature_int -> field_int option
    method get_fields           : field_int list
    method get_field_signatures : field_signature_int list
    method get_generic_signature: class_signature_int option
    method get_initializer      : method_int option
    method get_inner_classes    : inner_class_int list
    method get_interfaces       : class_name_int list
    method get_method           : method_signature_int -> method_int option
    method get_methods          : method_int list
    method get_method_signatures: method_signature_int list
    method get_name             : class_name_int
    method get_other_attributes : (string * string) list
    method get_other_flags      : int list
    method get_source_debug_extension: string option
    method get_source_file      : string option
    method get_super_class      : class_name_int option
    method get_version          : version_t
    method get_source_origin    : string
    method get_md5_digest       : string
    method get_visibility       : access_t

    (* predicates *)
    method defines_field  : field_signature_int -> bool
    method defines_method : method_signature_int -> bool
    method is_abstract    : bool
    method is_annotation  : bool
    method is_class       : bool
    method is_deprecated  : bool
    method is_enum        : bool
    method is_final       : bool
    method is_interface   : bool
    method is_synthetic   : bool

    (* printing *)
    method toPretty : pretty_t

  end

(** {1 Terms and expressions} *)

type arithmetic_op_t =
  | JPlus
  | JMinus
  | JDivide
  | JTimes

type relational_op_t =
  | JEquals
  | JLessThan
  | JLessEqual
  | JGreaterThan
  | JGreaterEqual
  | JNotEqual

type symbolic_jterm_constant_t =
  value_type_t * numerical_t option * numerical_t option * string

type jterm_t =
  | JAuxiliaryVar of string
  | JSymbolicConstant of symbolic_jterm_constant_t
  | JLocalVar of int
  | JLoopCounter of int
  | JConstant of numerical_t
  | JStaticFieldValue of int * string       (* cnix of name, field name *)
  | JObjectFieldValue of int * int * int * string
  (* cmsix, index of local var, cnix of class, field name *)
  | JBoolConstant of bool
  | JFloatConstant of float
  | JStringConstant of string
  | JSize of jterm_t
  | JPower of jterm_t * int
  | JUninterpreted of string * jterm_t list
  | JArithmeticExpr of arithmetic_op_t * jterm_t * jterm_t

type relational_expr_t = relational_op_t * jterm_t * jterm_t

class type jterm_range_int =
  object ('a)
    (* operations *)
    method add_upperbound: jterm_t -> 'a
    method add_lowerbound: jterm_t -> 'a
    method add_term: jterm_t -> 'a  (* adds term to all lower and upper bounds *)

    (* comparisons *)
    method equals: 'a -> bool
    method leq: 'a -> bool  (* is contained in, applicable to intervals only *)

    (* accessors *)
    method index: int
    method get_upperbounds: jterm_t list
    method get_lowerbounds: jterm_t list

    (* converters *)
    method to_interval : interval_t option
    method to_constant : numerical_t option
    method to_jterm    : jterm_t option

    (* predicates *)
    method is_top: bool
    method is_bottom: bool
    method is_constant: bool
    method is_interval: bool
    method is_jterm: bool

    (* xml *)
    method write_xml: xml_element_int -> unit
    method write_xmlx: xml_element_int -> method_signature_int -> unit

    (* printing *)
    method toPretty: pretty_t
  end

class type jtdictionary_int =
  object
    (* indexers *)
    method index_symbolic_jterm_constant: symbolic_jterm_constant_t -> int
    method index_jterm: jterm_t -> int
    method index_relational_expr: relational_expr_t -> int
    method index_jterm_list: jterm_t list -> int
    method index_relational_expr_list: relational_expr_t list -> int
    method index_jterm_range: jterm_t list -> jterm_t list -> int
    method index_numerical: numerical_t -> int
    method index_float: float -> int
    method index_string: string -> int

    (* accessors *)
    method get_symbolic_jterm_constant: int -> symbolic_jterm_constant_t
    method get_jterm: int -> jterm_t
    method get_relational_expr: int -> relational_expr_t
    method get_jterm_list: int -> jterm_t list
    method get_relational_expr_list: int -> relational_expr_t list
    method get_jterm_range: int -> (jterm_t list * jterm_t list)
    method get_numerical: int -> numerical_t
    method get_float: int -> float
    method get_string: int -> string

    (* xml *)
    method write_xml_jterm: ?tag:string -> xml_element_int -> jterm_t -> unit
    method read_xml_jterm : ?tag:string -> xml_element_int -> jterm_t
    method write_xml_relational_expr:
             ?tag:string -> xml_element_int -> relational_expr_t -> unit
    method read_xml_relational_expr :
             ?tag:string -> xml_element_int -> relational_expr_t
    method write_xml_jterm_list:
             ?tag:string -> xml_element_int -> jterm_t list -> unit
    method read_xml_jterm_list :
             ?tag:string -> xml_element_int -> jterm_t list
    method write_xml_relational_expr_list:
             ?tag:string -> xml_element_int -> relational_expr_t list -> unit
    method read_xml_relational_expr_list :
             ?tag:string -> xml_element_int -> relational_expr_t list
    method write_xml_jterm_range:
             ?tag:string
             -> xml_element_int
             -> jterm_t list
             -> jterm_t list
             -> unit
    method read_xml_jterm_range :
             ?tag:string -> xml_element_int -> (jterm_t list * jterm_t list)
    method write_xml_numerical:
             ?tag:string -> xml_element_int -> numerical_t -> unit
    method read_xml_numerical : ?tag:string -> xml_element_int -> numerical_t
    method write_xml_float: ?tag:string -> xml_element_int -> float -> unit
    method read_xml_float: ?tag:string -> xml_element_int -> float
    method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
    method read_xml_string : ?tag:string -> xml_element_int -> string

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    (* printing *)
    method toPretty: pretty_t

  end

(** {1 Translation to CHIF} *)

type catch_info_t = WillCatch | MayCatch | NoCatch

class type exn_info_int =
  object
    method get_exception: class_name_int
    method get_code:
             scope_int -> variable_t -> (code_int, cfg_int) command_t list
    method get_catch_info  : class_name_int -> catch_info_t
  end

type stack_slot_data_t =
  { ss_srcs: int list ;
    ss_dsts: int list ;
    ss_level: int ;
    ss_types: value_type_t list ;
    ss_value: jterm_range_int
  }

(** represents a logical stack element that can occupy one or two levels *)
class type logical_stack_slot_int =
  object

    (** {1 Setters} *)

    method set_type: value_type_t list -> unit

    method set_taint: taint_t -> unit

    method set_value: jterm_range_int -> unit

    method set_transformed_variable: variable_t -> unit

    (** {1 Accessors} *)

    (** Returns the CHIF variable that represents this stack slot *)
    method get_variable: variable_t

    (** Returns the CHIF variable in the transformed CHIF used in the numeric
        and taint analysis *)
    method get_transformed_variable: variable_t

    (** Returns the physical level on the stack, starting from 1. For a double
        slot the lower level is returned *)
    method get_level: int

    method get_type: value_type_t list

    method get_taint: taint_t

    (** Returns the list of pc values at which this slot wast put on the stack *)
    method get_sources: int list

    (** Returns the list of pc values at which this slot was taken off the
        stack *)
    method get_destinations : int list

    method get_value: jterm_range_int

    (** {1 Predicates} *)

    (** Returns true if this slot occupies two levels *)
    method is_double_slot: bool

    (** Returns true if the slot is occupied by a primitive type *)
    method is_numeric: bool

    (** Returns true if the slot is occupied by a referency type *)
    method is_symbolic: bool

    method has_value: bool

    method to_stack_slot_data: stack_slot_data_t

    (** {1 Printing} *)

    method toPretty : pretty_t

  end


class type op_stack_layout_int =
  object

    (** {1 Accessors} *)

    method get_size: int
    method get_slots: logical_stack_slot_int list
    method get_levels: int
    method get_slot: int -> logical_stack_slot_int
    method get_top_slot: logical_stack_slot_int
    method get_top_slots: int -> logical_stack_slot_int list
    method get_slot_for_variable: variable_t -> logical_stack_slot_int

    (** {1 Predicates} *)

    (** [has_slot level] returns [false] if
        - [level] refers to the second level in a double slot, or
        - [level] that is greater than the stack height, or
        - [level] is less than zero
     *)
    method has_slot: int -> bool

    method has_slot_for_variable: variable_t -> bool

    (** {1 Printing} *)

    method toPretty : pretty_t
  end

class type method_stack_layout_int =
  object
    (** {1 Setters} *)

    method set_local_variable_table:
             (int * int * string * value_type_t list * int) list -> unit

    (** {1 Accessors} *)

    method get_stack_layout: int -> op_stack_layout_int

    method get_stack_layouts: op_stack_layout_int list

    method get_pc_stack_layouts: (int * op_stack_layout_int) list

    method get_local_variable_table:
             (int * int * string * value_type_t list * int) list option

    (** {1 Predicates} *)

    method has_stack_layout: int -> bool

    (** {1 Printing} *)

    method toPretty : pretty_t

  end


(** {1 Byte code dictionary} *)

class type bcdictionary_int =
  object
    method index_pc_list: int list -> int
    method index_stack_slot_data: stack_slot_data_t -> int
    method index_stack_slot_data_list: stack_slot_data_t list -> int
    method index_opcode: opcode_t -> int

    method get_pc_list: int -> int list
    method get_stack_slot_data: int -> stack_slot_data_t
    method get_stack_slot_data_list: int -> stack_slot_data_t list
    method get_opcode: int -> opcode_t

    method write_xml_stack_slot_data_list:
             ?tag:string -> xml_element_int -> stack_slot_data_t list -> unit
    method read_xml_stack_slot_data_list:
             ?tag:string -> xml_element_int -> stack_slot_data_t list

    method write_xml_opcode: ?tag:string -> xml_element_int -> opcode_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end
