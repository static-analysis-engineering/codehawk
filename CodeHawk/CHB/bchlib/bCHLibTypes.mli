(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

open Big_int_Z

(* chlib *)
open CHIntervals
open CHLanguage
open CHNumerical
open CHNumericalConstraints
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchcil *)
open BCHCBasicTypes

(* =========================================================== generic types === *)

class type ['a] sumtype_string_converter_int =
  object
    method to_string: 'a -> string
    method from_string: string -> 'a
  end

type print_format_t = ATT | INTEL

type calling_convention_t = StdCall | CDecl

type bool3 = Yes | No | Maybe

type arg_io_t =
| ArgRead
| ArgReadWrite
| ArgWrite


(* ======================================================== Data export spec === *)

type data_export_spec_item_t = {
  dex_offset : int ;
  dex_name   : string ;
  dex_type   : string ;
  dex_size   : int
}

type data_export_spec_t = {
  dex_description : string ;
  dex_items       : data_export_spec_item_t list
}

class type data_export_value_int =
object
  method set_values: (int * string) list -> unit
  method get_spec: data_export_spec_t
  method get_size: int                             (* number of bytes *)
  method get_values: (data_export_spec_item_t * string) list
  method write_xml : xml_element_int -> unit
  method toPretty  : pretty_t
end

(* ============================================================== java types === *)

class type class_name_int =
object ('a)
  method index       : int
  method name        : string
  method simple_name : string
  method equal       : 'a -> bool
  method compare     : 'a -> int
  method package     : string list
  method package_name: string
  method toPretty    : pretty_t
end


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

type object_type_t =
  | TClass of class_name_int
  | TArray of value_type_t
      
and value_type_t =
  | TBasic of java_basic_type_t
  | TObject of object_type_t

type access_t =
  | Default
  | Public
  | Private
  | Protected

class type field_signature_data_int =
object ('a)
  method name      : string
  method descriptor: value_type_t
  method compare   : 'a -> int
  method to_string : string
  method toPretty  : pretty_t
end

class type field_signature_int =
object ('a)
  method index     : int
  method name      : string
  method field_signature_data: field_signature_data_int
  method descriptor: value_type_t
  method equal     : 'a -> bool
  method compare   : 'a -> int
  method to_string : string
  method toPretty  : pretty_t
end

class type method_descriptor_int =
object ('a)
  method arguments : value_type_t list
  method return_value: value_type_t option
  method compare   : 'a -> int
  method to_string : string
  method toPretty  : pretty_t
end

class type method_signature_data_int =
object ('a)
  method name       : string
  method descriptor : method_descriptor_int
  method compare    : 'a -> int
  method to_string  : string
  method toPretty   : pretty_t
end

class type method_signature_int =
object ('a)
  method index      : int
  method method_signature_data: method_signature_data_int
  method name       : string
  method descriptor : method_descriptor_int
  method equal      : 'a -> bool
  method compare    : 'a -> int
  method to_string  : string
  method toPretty   : pretty_t
end

type java_native_method_api_t =
  { jnm_signature : method_signature_int ;
    jnm_access    : access_t ;
    jnm_static    : bool
  }
      

class type java_dictionary_int =
object
  method make_class_name      : string -> class_name_int
  method make_field_signature : string -> value_type_t -> field_signature_int
  method make_method_signature: string -> method_descriptor_int -> method_signature_int
end

type java_native_method_class_t = 
{ jnmc_class : class_name_int ;
  jnmc_native_methods: java_native_method_api_t list
}


class type java_method_name_int =
object
  (* setters *)
  method set_class_name:string -> unit
  method set_method_name:string -> unit
  method add_argument_type: value_type_t -> unit

  (* accessors *)
  method get_class_name : string
  method get_method_name: string
  method get_arguments  : value_type_t list

  (* predicates *)
  method has_arguments : bool

  (* printing *)
  method toPretty: pretty_t
end

(* ================================================================ CH types === *)

type variable_comparator_t = variable_t -> variable_t -> int

type cmd_t = (code_int, cfg_int) command_t 

(* =============================================================== x86 types === *)

(* OFlag : overflow
   CFlag : carry
   ZFlag : zero
   SFlag : sign
   PFlag : parity
   DFlag : direction (set/cleared explicitly by std/cld)
   IFlag : interrupt
*)

type eflag_t = OFlag | CFlag | ZFlag | SFlag | PFlag | DFlag | IFlag

type cpureg_t = 
| Eax
| Ecx
| Ebp
| Ebx
| Edx
| Esp
| Esi
| Edi
| Ax
| Cx
| Dx
| Bx
| Sp
| Bp
| Si
| Di
| Al
| Cl
| Dl
| Bl
| Ah
| Ch
| Dh
| Bh

type segment_t = 
| StackSegment   (* 2 *)
| CodeSegment    (* 1 *)
| DataSegment    (* 3 *)
| ExtraSegment   (* 0 *)
| FSegment       (* 4 *)
| GSegment       (* 5 *)

(* ============================================================== mips types === *)

type mips_reg_t =
  | MRzero    (*  0: constant zero, ignored as destination *)
  | MRat      (*  1: reserved for assembler *)
  | MRv0      (*  2: function return value *)
  | MRv1      (*  3: function return value *)
  | MRa0      (*  4: argument 1 *)
  | MRa1      (*  5: argument 2 *)
  | MRa2      (*  6: argument 3 *)
  | MRa3      (*  7: argument 4 *)
  | MRt0      (*  8: temporary *)
  | MRt1      (*  9: temporary *)
  | MRt2      (* 10: temporary *)
  | MRt3      (* 11: temporary *)
  | MRt4      (* 12: temporary *)
  | MRt5      (* 13: temporary *)
  | MRt6      (* 14: temporary *)
  | MRt7      (* 15: temporary *)
  | MRs0      (* 16: saved temporary *)
  | MRs1      (* 17: saved temporary *)
  | MRs2      (* 18: saved temporary *)
  | MRs3      (* 19: saved temporary *)
  | MRs4      (* 20: saved temporary *)
  | MRs5      (* 21: saved temporary *)
  | MRs6      (* 22: saved temporary *)
  | MRs7      (* 23: saved temporary *)
  | MRt8      (* 24: temporary *)
  | MRt9      (* 25: temporary *)
  | MRk0      (* 26: reserved for OS kernel *)
  | MRk1      (* 27: reserved for OS kernel *)
  | MRgp      (* 28: pointer to global area *)
  | MRsp      (* 29: stack pointer *)
  | MRfp      (* 30: frame pointer, or saved temporary *)
  | MRra      (* 31: return address *)

type mips_special_reg_t =
  | MMHi   (* high multiplication unit register *)
  | MMLo   (* low multiplication unit register *)

(* ======================================================= arm types === *)

type arm_cc_flag_t = APSR_Z | APSR_N | APSR_C | APSR_V

type arm_reg_t =
  | AR0
  | AR1
  | AR2
  | AR3
  | AR4
  | AR5
  | AR6
  | AR7
  | AR8
  | AR9
  | AR10
  | AR11
  | AR12
  | ARSP
  | ARLR
  | ARPC


type arm_special_reg_t =
  | APSR   (* Core processor status word *)
  | FPSCR   (* Floating point processor status word *)
  | APSR_nzcv  (* Condition codes in core processor status word *)


type arm_extension_reg_type_t =
  | XSingle
  | XDouble
  | XQuad


type arm_extension_register_t = {
    armxr_type: arm_extension_reg_type_t;
    armxr_index: int
  }


type arm_extension_register_element_t = {
    armxr: arm_extension_register_t;
    armxr_elem_index: int;
    armxr_elem_size: int
  }


type arm_extension_register_replicated_element_t = {
    armxrr: arm_extension_register_t;
    armxrr_elem_size: int;
    armxrr_elem_count: int
  }


type register_t = 
| SegmentRegister of segment_t
| CPURegister of cpureg_t
| DoubleRegister of cpureg_t * cpureg_t
| FloatingPointRegister of int
| ControlRegister of int
| DebugRegister of int
| MmxRegister of int    (* 64 bit register *)
| XmmRegister of int    (* 128 bit register *)
| MIPSRegister of mips_reg_t
| MIPSSpecialRegister of mips_special_reg_t
| MIPSFloatingPointRegister of int
| ARMRegister of arm_reg_t
| ARMSpecialRegister of arm_special_reg_t
| ARMExtensionRegister of arm_extension_register_t
| ARMExtensionRegisterElement of arm_extension_register_element_t
| ARMExtensionRegisterReplicatedElement of
    arm_extension_register_replicated_element_t


(* =============================================================== Doubleword === *)

(** doubleword_int -------------------------------------------------------------
    32-bit word constructed from an unsigned 64-bit integer (immutable)
    ---------------------------------------------------------------------------- *)

type dw_index_t = int

class type doubleword_int =
object ('a)
  (* identification *)
  method index  : dw_index_t

  (* comparison *)
  method equal  : 'a -> bool
  method compare: 'a -> int
  method lt     : 'a -> bool
  method le     : 'a -> bool

  (* conversion *)
  method to_int                    : int
  method to_big_int                : big_int
  method to_numerical              : numerical_t
  method to_signed_numerical       : numerical_t

  method to_time_date_string       : string     (* raises Invalid_argument *)
  method to_char_string            : string option
  method to_string                 : string     (* convert bytes to characters in a string *)
  method to_string_fragment        : string     (* idem, but in reverse *)
  method to_fixed_length_hex_string: string
  method to_hex_string             : string
  method to_signed_hex_string      : string

  (* operations *)
  method unset_highest_bit: 'a
  method subtract         : 'a  -> 'a      (* raises Invalid_argument *)
  method subtract_int     : int -> 'a      (* raises Invalid_argument *)
  method add              : 'a  -> 'a      (* raises Invalid_argument *)
  method add_int          : int -> 'a      (* raises Invalid_argument *)
  method multiply_int     : int -> 'a      (* raises Invalid_argument *)
  method xor              : 'a -> 'a       (* exclusive or *)

  (* accessors *)
  method get_low: int          (* integer value of low-order 16 bits *)
  method get_high: int         (* integer value of high-order 16 bits *)
  method get_bits_set: int list
  method get_bitval: int -> int    (* value of bit at position (zero-based) *)
  method get_segval: int -> int -> int  (* value of subrange of bits, high, low *)

  (* predicates *)
  method is_highest_bit_set: bool
  method is_nth_bit_set    : int -> bool   (* raises Invalid_argument *)

  (* printing *)
  method toPretty: pretty_t
end

(* ================================================================ Immediate === *)

class type immediate_int =
object ('a)

  (* comparison *)
  method equal:'a -> bool

  (* predicates *)
  method is_doubleword: bool
  method is_quadword: bool

  (* converters *)
  method to_big_int: big_int
  method to_numerical: numerical_t
  method to_int: int option
  method to_doubleword: doubleword_int

  (* transformers *)
  method to_unsigned: 'a
  method sign_extend: int -> 'a

  (* printing *)
  method to_string: string
  method to_hex_string: string

  method toPretty: pretty_t
end

(* ========================================================== Pushback stream === *)

class type virtual stream_wrapper_int = 
object
    
  method read : char
  method nread : int -> string
  method really_nread : int -> string
  method input : string -> int -> int -> int
  method close_in : unit
    
  method read_byte : int
  method read_signed_byte : int
  method virtual read_ui16 : int
  method virtual read_i16 : int
  method virtual read_i32 : int
  method virtual read_real_i32 : int32
  method virtual read_i64 : int64
  method virtual read_double : float
  method read_string : string
  method read_line : string
    
  method virtual read_doubleword : doubleword_int
end

class type pushback_stream_int =
object
  method skip_bytes      : int -> unit
  method read            : char
  method nread           : int -> string
  method really_nread    : int -> string
    
  method read_byte       : int
  method read_signed_byte: int
  method read_ui16       : int
  method read_i16        : int
  method read_i32        : int
  method read_real_i32   : int32
  method read_i64        : int64
  method read_string     : string

  method read_doubleword: doubleword_int

  method read_num_signed_byte      : numerical_t
  method read_num_unsigned_byte    : numerical_t 
  method read_num_signed_word      : numerical_t
  method read_num_signed_doubleword: numerical_t

  method read_imm_signed_byte      : immediate_int
  method read_imm_signed_word      : immediate_int
  method read_imm_signed_doubleword: immediate_int
  method read_imm_signed:     int -> immediate_int

  method read_imm_unsigned_byte      : immediate_int
  method read_imm_unsigned_word      : immediate_int
  method read_imm_unsigned_doubleword: immediate_int
  method read_imm_unsigned:     int -> immediate_int

  method read_null_terminated_string : string
  method read_sized_unicode_string   : string

  method pushback        : int -> unit

  (* accessors *)
  method pos : int
end


(* =========================================================== Data block === *)

class type data_block_int =
object ('a)
  method compare: 'a -> int

  (* setters *)
  method set_data_string: string -> unit
  method set_name: string -> unit
  method set_data_table: (string * string) list -> unit

  (* accessors *)
  method get_start_address: doubleword_int
  method get_end_address: doubleword_int
  method get_name: string
  method get_length: int
  method get_data_string: string
  method get_offset_range: (int * int) option

  (* predicates *)
  method has_name: bool
  method has_data_string: bool
  method is_offset_table: bool

  (* saving *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
  method toString: string
end

(* =========================================================== Jump table === *)

class type jumptable_int =
object

  (* setters *)
  method invalidate_startaddress: unit

  (* accessors *)
  method get_start_address: doubleword_int
  method get_end_address: doubleword_int
  method get_length: int
  method get_all_targets: doubleword_int list
  method get_targets: doubleword_int -> int -> int -> doubleword_int list
  method get_indexed_targets:
           doubleword_int -> int -> int -> (int * doubleword_int) list

  (* predicates *)
  method includes_address: doubleword_int -> bool

  (* saving *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty:
           is_function_entry_point:(doubleword_int -> bool) ->
           get_opt_function_name:(doubleword_int -> string option) -> pretty_t
  method toString:
           is_function_entry_point:(doubleword_int -> bool) ->
           get_opt_function_name:(doubleword_int -> string option) -> string

end

(* ======================================================Call-back tables === *)


type call_back_table_value_t =
  | CBAddress of string
  | CBTag of string
  | CBValue of numerical_t


class type call_back_table_record_int =
  object

    (* getters *)
    method address: string
    method values: (int * call_back_table_value_t) list
    method stringvalue: int -> string  (* string at offset *)
    method intvalue: int -> numerical_t   (* integer value at offset *)
    method addrvalue: int -> string   (* address at offset *)

    (* saving *)
    method write_xml: xml_element_int -> unit

    (* printing *)
    method toPretty: pretty_t

  end


class type call_back_table_int =
  object

    (* setters *)
    method add_record:
             string
             -> (int * call_back_table_value_t) list
             -> unit

    (* getters *)
    method address: string
    method length: int   (* number of records *)
    method record_type: btype_t
    method type_at_offset: int -> btype_t
    method fieldname_at_offset: int -> string
    method field_offset_types: (int * btype_t) list
    method record_length: int   (* number of items in record *)
    method function_pointer_values: (string * btype_t) list

    (* saving *)
    method write_xml: xml_element_int -> unit

  end


class type call_back_tables_int =
  object

    (* setters *)
    method new_table: string -> btype_t -> call_back_table_int
    method add_table_address: string -> string -> unit
    method set_function_pointers: unit

    (* getters *)
    method table_variables: (string * string) list   (* address, name *)
    method get_table: string -> call_back_table_int

    (* predicates *)
    method has_table: string -> bool

    (* saving *)
    method write_xml: xml_element_int -> unit

  end

(* ============================================================= Location === *)

type base_location_t = {
    loc_faddr: doubleword_int ;
    loc_iaddr: doubleword_int ;
  }

type fcontext_t = {
    ctxt_faddr: doubleword_int ;
    ctxt_callsite: doubleword_int ;
    ctxt_returnsite: doubleword_int
  }

type context_t =
  | FunctionContext of fcontext_t
  | BlockContext of doubleword_int

(* ctxt_iaddress_t spec:

   i  ( [], { faddr,iaddr } ) = iaddr
   i  ( [ F{ fa,cs,rs } ], { faddr,iaddr }) = iaddr
   i  ( [ B{ js } ], { faddr,iaddr }) = iaddr

   f  ( [], { faddr,iaddr } ) = faddr
   f  ( [ F{ fa,cs,rs }, _ ],  { faddr,iaddr } ) = fa
   f  ( [ B{ js } ], { faddr,iaddr } ) = faddr
   f  ( B{ js }::ctxt , { faddr,iaddr } ) = f (ctxt, {faddr,iaddr})

   ci ( [], { faddr,iaddr } ) = iaddr
   ci ( [ F{ fa,cs,rs } ], { faddr,iaddr } ) = F:cs_iaddr
   ci ( [ F{ fa1,cs1,rs1 },F{ fa2,cs2,rs2 } ], { faddr,iaddr } ) = F:cs1_F:cs2_iaddr
   ci ( [ B{ js } ], { faddr,iaddr }) = B:js_iaddr
   ci ( [ B{ js1 }, B{ js2 } ], { faddr,iaddr }) = B:js1_B:js2_iaddr
 *)
type ctxt_iaddress_t = string

class type location_int =
  object ('a)

    method compare: 'a -> int

    method i: doubleword_int         (* instruction address *)
    method f: doubleword_int         (* function address of outer context *)
    method ci: ctxt_iaddress_t       (* full context instruction address string *)

    method base_loc: base_location_t (* inner function address, instruction address *)
    method base_f: doubleword_int    (* function address of inner context *)
    method ctxt: context_t list

    method has_context: bool

    method toPretty: pretty_t
  end


(* ========================================================= String table === *)

class type string_table_int =
object
  (* setters *)
  method add_string  : doubleword_int -> string -> unit
  method add_xref    :
           doubleword_int -> string -> doubleword_int -> ctxt_iaddress_t -> unit

  (* accessors *)
  method get_string : doubleword_int -> string
  method get_strings: (doubleword_int * string) list

  (* predicates *)
  method has_string: doubleword_int -> bool

  (* saving *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

end

(* ====================================================== System settings === *)

class type system_settings_int =
object
  (* setters *)
  method set_summary_jar: string -> unit
  method add_so_library: string -> unit    (* name of so-library *)
  method set_jsignature_jar: string -> unit
  method set_verbose: unit
  method set_vftables: unit
  method set_thumb: unit
  method enable_sideeffects_on_globals : string list -> unit
  method disable_sideeffects_on_globals: string list -> unit
  method set_abstract_stackvars_disabled: unit
  method set_apps_dir: string -> unit
  method set_app_summary_jars: string -> unit   (* application name *)
  method set_export_dir: string -> unit

  (* accessors *)
  method get_summary_paths: (string * Zip.in_file) list
  method get_jsignature_paths: (string * Zip.in_file) list
  method get_export_dir: string
  method so_libraries: string list  (* names of so-libraries *)

  (* predicates *)
  method is_verbose: bool
  method is_sideeffects_on_global_enabled: string -> bool
  method is_abstract_stackvars_disabled: bool
  method is_set_vftables_enabled: bool
  method has_thumb: bool

end

(* ============================================================== System data === *)

class type system_data_int =
object

  (* setters *)
  method set_filename: string -> unit
  method set_xfilesize: int -> unit
  method set_image_base: doubleword_int -> unit
  method set_elf: unit

  (* accessors *)
  method get_filename: string
  method get_xfilesize: int
  method get_image_base: doubleword_int

  (* predicates *)
  method is_elf: bool

end

(* ============================================================ Function data === *)

class type function_data_int =
  object

    (* setters *)
    method set_function_type: btype_t -> unit
    method set_non_returning: unit
    method add_name: string -> unit
    method set_ida_provided: unit
    method set_user_provided: unit
    method set_incomplete: unit
    method set_virtual: unit
    method set_inlined: unit
    method set_library_stub: unit
    method set_by_preamble: unit
    method set_class_info: classname:string -> isstatic:bool -> unit
    method add_inlined_block: doubleword_int -> unit

    (* accessors *)
    method get_names: string list  (* raw names *)
    method get_function_name: string  (* demangled or combination of all names *)
    method get_inlined_blocks: doubleword_int list
    method get_function_type: btype_t

    (* predicates *)
    method has_function_type: bool
    method has_name: bool
    method has_class_info: bool
    method is_non_returning: bool
    method is_incomplete: bool
    method is_ida_provided: bool
    method is_user_provided: bool
    method is_virtual: bool
    method is_inlined: bool
    method is_library_stub: bool
    method is_inlined_block: doubleword_int -> bool
    method has_inlined_blocks: bool

    (* save *)
    method to_rep_record: (string list * int list)

  end

class type functions_data_int =
  object

    method reset: unit
    method add_function: doubleword_int -> function_data_int

    (* accessors *)
    method get_functions: function_data_int list
    method get_function_entry_points: doubleword_int list
    method get_library_stubs: doubleword_int list
    method get_function: doubleword_int -> function_data_int
    method get_ida_provided_functions: function_data_int list
    method get_ida_provided_function_entry_points: doubleword_int list

    (* predicates *)
    method is_function_entry_point: doubleword_int -> bool
    method has_function_name: doubleword_int -> bool
    method has_function_by_name: string -> doubleword_int option
    method has_function: doubleword_int -> bool

    (* stats *)
    method get_user_provided_count: int
    method get_ida_provided_count: int

    (* save/restore *)
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

(* ================================================= User-provided directions === *)

class type user_provided_directions_int =
object
  (* setters *)
  method load_dll_ordinal_mappings: string -> unit
  method set_dll_ordinal_mappings : string -> (int * string) list -> unit

  (* getters *)
  method get_dll_ordinal_mapping : string -> int -> string

  (* predicates *)
  method are_DS_and_ES_the_same_segment: bool

  (* xml *)
  method write_xml_ordinal_table : xml_element_int -> string -> unit
end


(* =========================================================== Variable names === *)

class type variable_names_int =
object
  (* setters *)
  method add: int -> string -> unit    (* variable sequence number *)

  (* accessors *)
  method get: int -> string    (* variable sequence number *)

  (* predicates *)
  method has: int -> bool    (* variable sequence number *)

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit
end


(* ============================================================== C struct === *)

type struct_field_t = {
  fld_name: string;
  fld_offset: int;
  fld_size: int;
  fld_type: btype_t
}

class type c_struct_int =
object
  method get_name: string
  method get_field: int -> struct_field_t
  method has_field: int -> bool
  method iter: (struct_field_t -> unit) -> unit
  method toPretty: pretty_t
end

(* ================================================== Constant definitions === *)

type constant_definition_t = {
  xconst_name: string;
  xconst_value: doubleword_int;
  xconst_type: btype_t;
  xconst_desc: string;
  xconst_is_addr: bool
}

type flag_definition_t = {
  xflag_name: string;
  xflag_pos: int;    (* lowest order bit is zero *)
  xflag_desc: string;
  xflag_type: btype_t
}

(* ====================================================== Type definitions === *)

class type type_definitions_int =
  object
    method add_builtin_typeinfo: string -> btype_t -> unit
    method add_builtin_compinfo: string -> bcompinfo_t -> unit
    method add_builtin_enuminfo: string -> benuminfo_t -> unit
         
    method add_typeinfo: string -> btype_t -> unit
    method add_compinfo: string -> bcompinfo_t -> unit
    method add_enuminfo: string -> benuminfo_t -> unit
         
    method get_type: string -> btype_t
    method get_compinfo: string -> bcompinfo_t
    method get_enuminfo: string -> benuminfo_t
         
    method has_type: string -> bool
    method has_compinfo: string -> bool
    method has_enuminfo: string -> bool

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
         
    method toPretty: pretty_t
end

(* ======================================================== Demangled name === *)

type demangled_name_t = {
  dm_name : tname_t ;
  dm_name_space : tname_t list ;
  dm_parameter_types : btype_t list ;
  dm_returntype      : btype_t option ;
  dm_calling_convention: string ;
  dm_accessibility: string ;
  dm_storage_class: string ;
  dm_constructor  : bool ;
  dm_destructor   : bool ;
  dm_static       : bool ;
  dm_virtual      : bool ;
  dm_operator     : bool ;
  dm_const        : bool ;
  dm_vbtable      : bool ;
  dm_vftable      : bool 
  }

(* ======================================================= Type invariants === *)

type type_invariant_fact_t = 
| VarTypeFact of variable_t * btype_t * string list    (* struct, fields *)
| ConstTypeFact of numerical_t * btype_t
| XprTypeFact of xpr_t * btype_t

class type type_invariant_int =
object ('a)
  method index: int
  method compare: 'a -> int
  method get_fact: type_invariant_fact_t
  method get_variables: variable_t list
  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end

class type location_type_invariant_int =
object
  method add_fact: type_invariant_fact_t -> unit

  (* accessors *)
  method get_var_facts: variable_t -> type_invariant_int list
  method get_facts: type_invariant_int list
  method get_count: int

  (* predicates *)
  method has_facts: bool

  (* printing *)
  method toPretty: pretty_t
end

class type type_invariant_io_int =
object
  method add_var_fact:
           string -> variable_t -> ?structinfo:string list -> btype_t -> unit
  method add_const_fact: string -> numerical_t -> btype_t -> unit
  method add_xpr_fact: string -> xpr_t -> btype_t -> unit
  method add_function_var_fact:    (* location independent *)
           variable_t
           -> ?structinfo:string list
           -> btype_t
           -> unit

  (* accessors *)
  method get_location_type_invariant: string -> location_type_invariant_int
  method get_facts: type_invariant_int list (* all facts *)
  method get_function_facts: type_invariant_int list (* function-valid facts *)
  method get_location_facts: (string * type_invariant_int list) list
  method get_variable_facts: string -> variable_t -> type_invariant_int list
  method get_table_size: int
  method get_invariant_count: int

  (* save and restore *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
end

(* ===================================================== Location invariants === *)

type non_relational_value_t =
| FSymbolicExpr of xpr_t
| FIntervalValue of numerical_t option * numerical_t option
| FBaseOffsetValue of symbol_t * numerical_t option * numerical_t option * bool


(* c1 f1 + c2 f2 .... + cn fn = constant *)
type linear_equality_t = {
  leq_factors: (numerical_t * variable_t) list ;
  leq_constant: numerical_t
}


type invariant_fact_t =
  | Unreachable of string      (* domain that signals unreachability *)
  | NonRelationalFact of variable_t * non_relational_value_t
  | RelationalFact of linear_equality_t
  | InitialVarEquality of variable_t * variable_t   (* variable, initial value *)
  | InitialVarDisEquality of variable_t * variable_t (* variable, initial value *)
  | TestVarEquality of variable_t * variable_t * ctxt_iaddress_t * ctxt_iaddress_t
         (* variable, test value *)

class type invariant_int =
object ('a)
  method index: int
  method compare: 'a -> int
  method transfer: variable_t -> 'a
  method get_fact: invariant_fact_t
  method get_variables: variable_t list
  method get_variable_equality_variables: variable_t list
  method is_constant: bool
  method is_interval: bool
  method is_base_offset_value: bool
  method is_symbolic_expr: bool
  method is_linear_equality: bool
  method is_variable_equality: bool
  method is_smaller: 'a -> bool
  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end


class type location_invariant_int =
object

  (* setters *)
  method reset          : unit
  method add_fact       : invariant_fact_t -> unit
  method get_facts      : invariant_int list
  method get_count      : int

  (* accessors *)
  method get_constant       : variable_t -> numerical_t
  method get_interval       : variable_t -> interval_t
  method get_base_offset    : variable_t -> symbol_t * interval_t
  method get_base_offset_constant: variable_t -> symbol_t * numerical_t
  method get_affine_offset  : variable_t -> variable_t -> numerical_t option
  method get_interval_offset: variable_t -> variable_t -> interval_t
  method get_external_exprs : variable_t -> xpr_t list
  method get_known_variables: variable_t list
  method get_known_initial_values: variable_t list 
  method get_init_disequalities  : variable_t list (* initial values *)
  method get_init_equalities     : variable_t list (* initial values *)
  method rewrite_expr      : xpr_t -> (variable_t -> variable_t -> int) ->  xpr_t

  (* predicates *)
  method is_constant   : variable_t -> bool
  method is_interval   : variable_t -> bool
  method is_base_offset: variable_t -> bool
  method is_base_offset_constant: variable_t -> bool
  method are_equal     : variable_t -> variable_t -> bool

  method test_var_is_equal    : variable_t -> ctxt_iaddress_t -> ctxt_iaddress_t -> bool
  method var_has_initial_value: variable_t -> bool
  method var_has_symbolic_expr: variable_t -> bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t
  method toPrettyVar : (variable_t -> string) option -> pretty_t
end


class type invariant_io_int =
object

  (* setters *)
  method set_unreachable: string -> string -> unit
  method reset: unit

  (* add non-relational facts *)
  method add_symbolic_expr_fact: string -> variable_t -> xpr_t -> unit
  method add_interval_fact: string -> variable_t -> interval_t -> unit
  method add_constant_fact: string -> variable_t -> numerical_t -> unit
  method add_valueset_fact:
           string -> variable_t -> symbol_t -> interval_t -> bool -> unit

  (* add special-purpose facts *)
  method add_initial_value_fact: string -> variable_t -> variable_t -> unit
  method add_initial_disequality_fact: string -> variable_t -> variable_t -> unit
  method add_test_value_fact   :
           string
           -> variable_t
           -> variable_t
           -> ctxt_iaddress_t
           -> ctxt_iaddress_t
           -> unit

  (* add relational fact *)
  method add_lineq: string -> numerical_constraint_t -> unit

  (* accessors *)
  method get_location_invariant: string -> location_invariant_int
  method get_constants: string -> variable_t list
  method get_invariant_count: int

  (* save and restore *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
end

(* ----------------------------------------------- Invariant Dictionary ----- *)

class type invdictionary_int =
  object

    method xd: xprdictionary_int
    method index_non_relational_value: non_relational_value_t -> int
    method index_invariant_fact: invariant_fact_t -> int

    method get_non_relational_value: int -> non_relational_value_t
    method get_invariant_fact: int -> invariant_fact_t

    method write_xml_non_relational_value:
             ?tag:string -> xml_element_int -> non_relational_value_t -> unit
    method read_xml_non_relational_value:
             ?tag:string -> xml_element_int -> non_relational_value_t

    method write_xml_invariant_fact:
             ?tag:string -> xml_element_int -> invariant_fact_t -> unit
    method read_xml_invariant_fact:
             ?tag:string -> xml_element_int -> invariant_fact_t

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    method toPretty: pretty_t
  end


class type tinvdictionary_int =
  object

    method xd: xprdictionary_int
    method index_type_invariant_fact: type_invariant_fact_t -> int
    method get_type_invariant_fact: int -> type_invariant_fact_t

    method write_xml_type_invariant_fact:
             ?tag:string -> xml_element_int -> type_invariant_fact_t -> unit
    method read_xml_type_invariant_fact:
             ?tag:string -> xml_element_int -> type_invariant_fact_t

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    method toPretty: pretty_t

  end


(* ====================================================== Function summaries === *)

(* The stack parameter location indicates the location of the argument
   relative to the return address, in increments of 4 (that is, stack
   parameter 1 is located at offset 4, stack parameter 2 is at offset 8,
   etc.

   The size of the argument defaults to 4 bytes.

   Function summaries can be annotated with io-actions and parameter roles.

   An io-action has the following attributes:
   - cat : category (e.g. registry, services, filesystem, network, process, ...)
   - desc: brief description of the action performed by this function
   - pre : condition on argument values that decides whether the function
           warrants reporting

   A parameter has the following annotation attributes:
   - desc : general description of the parameter
   - roles: a list of (rt,rn) pairs that indicate the role of the parameter under
             different circumstances,
            e.g. (ioc:network, protocol)
                 (ioc:filesystem, filename)
                 (ioc:registry, key)
            or
                 (enum:const, <name of the enumeration>)
                 (enum:flags, <name of the flags enumeration>)
            or 
                 (size:structure, <name of datastructure type>)
                 (size:buffer,    <name of function>)
                 (size:memory,    <name of function>)
                 (size:required,  <name of function>)
            or
                 (jni, class)
                 (jni, object)
      the last two will change the representation of the values into a symbolic
      name, or list of names
   -  io : "r", "w", or "rw", depending on the whether the argument provided
        is input, output or both

   The api has an additional attribute for the role of the return value
   - rv-roles: a list of pairs that indicate the role of the return value
               under different circumstances,
               e.g. (ioc:filesystem, filename)
                    (ioc:network, protocol)
                    (jni, object)
*)
type parameter_location_t =
| StackParameter of int
| RegisterParameter of register_t
| GlobalParameter of doubleword_int
| UnknownParameterLocation

type formatstring_type_t =
  | NoFormat
  | PrintFormat
  | ScanFormat

type fts_parameter_t = {
  apar_name: string ;
  apar_type: btype_t ;
  apar_desc: string ;
  apar_roles: (string * string) list ;
  apar_io: arg_io_t ;
  apar_size: int ;
  apar_location: parameter_location_t ;
  apar_fmt: formatstring_type_t
}
    
type arithmetic_op_t =
  PPlus | PMinus | PDivide | PTimes

type relational_op_t = 
  PEquals | PLessThan | PLessEqual | PGreaterThan | PGreaterEqual | PNotEqual


type function_signature_t = {
  fts_parameters: fts_parameter_t list;
  fts_varargs: bool;
  fts_va_list: (fts_parameter_t list) option;
  fts_returntype: btype_t;
  fts_rv_roles: (string * string) list;
  fts_stack_adjustment: int option;
  fts_calling_convention: string;
  fts_registers_preserved: register_t list;
}

type function_interface_t = {
    fintf_name: string;
    fintf_jni_index: int option;
    fintf_syscall_index: int option;
    fintf_type_signature: function_signature_t;
  }

type bterm_t =
  | ArgValue of fts_parameter_t
  | RunTimeValue
  | ReturnValue
  | NamedConstant of string
  | NumConstant of numerical_t
  | ArgBufferSize of bterm_t        (* size of buffer pointed to by term in bytes *)
  | IndexSize of bterm_t (* value of term, to be interpreted as size in type units *)
  | ByteSize of bterm_t  (* value of term, to be interpreted as size in bytes *)
  | ArgAddressedValue of bterm_t * bterm_t    (* address term, offset term *)
  | ArgNullTerminatorPos of bterm_t
  | ArgSizeOf of btype_t
  | ArithmeticExpr of arithmetic_op_t * bterm_t * bterm_t



(* ========================================================= call targets === *)

type function_stub_t =
  | SOFunction of string (* ELF *)
  | DllFunction of string * string (* PE *)
  | JniFunction of int  (* Java Native Methods, call on ( *env) where env is the
    first argument on the calling function, with the jni identification number *)
  | LinuxSyscallFunction of int (* numbers ranging from 4000 to 4999 *)
  | PckFunction of string * string list * string   (* PE, with package names *)
                 
(* Call target types:
   StubTarget: dynamically linked function external to the executable
   StaticStubTarget: library function with summary statically linked 
                     in the executable
   AppTarget: application function with address
   InlinedAppTarget: application function with address that is inlined
   WrappedTarget: application function that wraps a call to another function
      a: address of wrapper function;
      fapi: function api of wrapper function;
      tgt: call target of wrapped function
      mapping: maps wrapped function arguments to wrapper function arguments
                 and constants provided by the wrapper function internally
   VirtualTarget: virtual function specified in class vtable
   IndirectTarget: indirect call on external variable (global variable, 
                   function argument, or return value)
   CallbackTableTarget: indirect call on a field of a struct from a list of
                        those structs
   UnknownTarget: target of indirect call that has not been resolved yet
*)
type call_target_t =
  | StubTarget of function_stub_t
  | StaticStubTarget of doubleword_int * function_stub_t
  | AppTarget of doubleword_int
  | InlinedAppTarget of doubleword_int * string
  | WrappedTarget of
      doubleword_int
      * function_interface_t
      * call_target_t
      * (fts_parameter_t * bterm_t) list
  | VirtualTarget of function_interface_t
  | IndirectTarget of bterm_t option * call_target_t list
  | CallbackTableTarget of doubleword_int * int (* table address, offset *)
  | UnknownTarget

type c_struct_constant_t =
| FieldValues of (int * c_struct_constant_t) list
| FieldConstant of bterm_t
| FieldString of string
| FieldCallTarget of call_target_t


type precondition_t =
| PreNullTerminated of bterm_t
| PreNotNull of bterm_t
| PreNull of bterm_t
| PreDerefRead of btype_t * bterm_t * bterm_t * bool   (* dest, size, canbenull *)
| PreDerefWrite of btype_t * bterm_t * bterm_t * bool  (* dest, size, canbenull *)
| PreAllocationBase of bterm_t
| PreFunctionPointer of btype_t * bterm_t   
| PreNoOverlap of bterm_t * bterm_t
| PreFormatString of bterm_t
| PreEnum of bterm_t * string * bool   (* value must be one of defined enumeration values;
                                          true if constant is set of flags *)
| PreRelationalExpr of relational_op_t * bterm_t * bterm_t
| PreDisjunction of precondition_t list
| PreConditional of precondition_t * precondition_t
| PreIncludes of bterm_t * c_struct_constant_t


type postcondition_t =
| PostNewMemoryRegion of bterm_t * bterm_t    (* pointer returned, size in bytes *)
| PostFunctionPointer of bterm_t * bterm_t     (* return value, name of function *)
| PostAllocationBase of bterm_t
  (* the return value is a pointer to the base
     of a dynamically allocated memory region *)
| PostNull of bterm_t
| PostNotNull of bterm_t
| PostNullTerminated of bterm_t
| PostEnum of bterm_t * string
| PostFalse      (* function does not return *)
| PostRelationalExpr of relational_op_t * bterm_t * bterm_t
| PostDisjunction of postcondition_t list
| PostConditional of precondition_t * postcondition_t


type sideeffect_t =
| BlockWrite of btype_t * bterm_t * bterm_t 
| Modifies of bterm_t
| AllocatesStackMemory of bterm_t
| StartsThread of bterm_t * bterm_t list           (* start address, parameters *)
| Invalidates of bterm_t
| SetsErrno
| ConditionalSideeffect of precondition_t * sideeffect_t
| UnknownSideeffect


type io_action_t = {
  iox_cat : string ;
  iox_desc: string ;                               (* description *)
  iox_pre : precondition_t option ;                (* condition for inclusion *)
}

type function_semantics_t = {
  fsem_pre             : precondition_t list ;
  fsem_post            : postcondition_t list ;
  fsem_errorpost       : postcondition_t list ;
  fsem_sideeffects     : sideeffect_t list ;
  fsem_io_actions      : io_action_t list ;
  fsem_desc            : string ;
  fsem_throws          : string list
}

type function_documentation_t = {
  fdoc_desc   : string ;
  fdoc_remarks: string ;
  fdoc_caution: string ;
  fdoc_apidoc : pretty_t ;
  fdoc_xapidoc: xml_element_int
}


class type function_summary_int =
object ('a)
  (* accessors *)
  method get_function_interface: function_interface_t
  method get_function_signature: function_signature_t
  method get_function_semantics: function_semantics_t
  method get_function_documentation: function_documentation_t

  method get_name: string
  method get_parameters: fts_parameter_t list
  method get_returntype: btype_t
  method get_stack_adjustment: int option
  method get_jni_index: int
  method get_syscall_index: int

  method get_preconditions: precondition_t list
  method get_postconditions: postcondition_t list
  method get_errorpostconditions: postcondition_t list
  method get_sideeffects: sideeffect_t list
  method get_io_actions: io_action_t list

  method get_enums_referenced: string list
  method get_enum_type: fts_parameter_t -> (btype_t * bool) option  (* name, specified as flags *)

  method get_registers_preserved: register_t list   (* deviation from default (Eax,Ecx,Edx) *)

  (* modifiers *)
  method modify_types: string -> type_transformer_t -> 'a

  (* predicates *)
  method sets_errno: bool
  method has_unknown_sideeffects: bool
  method is_nonreturning: bool
  method is_jni_function: bool

  (* i/o *)
  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end


(* ============================================== function summary library == *)
(* The function summary library holds
   -- summaries (models) of dll functions, and
   -- summaries (models) of jni functions

   Dll summaries are searched for by a combination of dll name, which provides
   the directory of the summary, and by name.
   Jni summaries are obtained by index number: jni_<index> from the jni directory.

   Some Windows library functions have two versions: an ASCII version (with 
   suffix A) and an Unicode version (with suffix W). The api and semantics for
   these functions are almost the same, so the models directory provides a
   neutral version (without suffix) that provides all documentation, api, and
   semantics, and an A and W version that refer to the neutral version by name
   and indicate all type changes to be made to obtain the respective version.
   The format of the referring version is, e.g., for CreateProcessA: 
   <refer-to name="CreateProcess">
      <replace_type  src="STARTUPINFO" tgt="STARTUPINFOA"/>
   </refer-to>
   Replacement of the standard types is performed automatically:
     TCHAR   -> char, wchar_t
     LPCTSTR -> LPCSTR, LPCWSTR
     LPTSTR   -> LPSTR, LPWSTR
   and so does not need to be included.

   Some functions appear in multiple libraries. To avoid having to maintain
   multiple copies of the same model, we provide one model and references to
   this model within other libraries (directories). 
   The format of the referring version is, e.g., for send in wsock32.dll :
   <libfun lib="wsock32" name="send">
      <refer-to lib="ws_32" name="send"/>
   </libfun>

   All Jni function models are stored in the jni directory. The name of the
   file for jni function with index x is jni_x.xml . 
   Several jni functions are variations of the same function, only with
   different types. E.g., there are ten jni functions of the form
   Call<type>Method, for ten different types, each with their own index.
   The model directory provides a template version, that all ten other
   model files can refer to.
   The format of the referring version is, e.g., for CallIntMethod,
   <jnifun index="49" prefix="Call" suffix="Method" typename="Int">
      <type>jint</type>
   </jnifun>
   or for GetIntArrayElements,
   <jnifun prefix="Get" suffix="ArrayElements" typename="Int">
      <type>jint</type>
      <arrarytype>jintArray</arraytype>
   </jnifun>

   Dll names are internally always represented with a _dll suffix unless
   the dll has an explicit different suffix (e.g., spools.drv) in which
   case the dll name is represented with the given extension (e.g.,
   spools_drv). All dllnames are internally represented in lower case.
   Windows file systems are case insensitive.

*)

class type function_summary_library_int = 
object
  (* setters *)
  method load_dll_library_function: string -> string -> unit
  method load_so_function: string -> unit
  method read_summary_files: unit
    
  (* accessors *)
  method get_function_dll: string -> string (* dll from which function was loaded *)
  method get_dll_function: string -> string -> function_summary_int
  method get_so_function: string -> function_summary_int
  method get_lib_function: string list -> string -> function_summary_int
  method search_for_library_function: string -> string option (* returns dll for function name *)
  method get_syscall_function: int -> function_summary_int
  method get_jni_function: int -> function_summary_int
  method get_library_functions: function_summary_int list

  (* predicates *)
  method has_function_dll: string -> bool (* true if fname came from a dll *)
  method has_dllname: string -> bool (* true if a function was loaded from this dll *)
  method has_dll_function: string -> string -> bool
  (* tries to locate the summary, true if successful *)
  method has_so_function: string -> bool
  method has_lib_function: string list -> string -> bool
  method has_syscall_function: int -> bool
  method has_jni_function: int -> bool (* tries to locate the summary, true if
                                                    successful *)

  (* xml *)
  method write_xml_requested_summaries: xml_element_int -> unit
  method write_xml_missing_summaries: xml_element_int -> unit
end

(* =============================================================== Cpp class === *)

type cpp_datamember_t = {
  cppdm_name: string;
  cppdm_offset: int;
  cppdm_size: int;
  cppdm_type: btype_t
}

type cppvf_table_t = (int, function_interface_t) Hashtbl.t

type cpp_vfpointer_t = {
  cppvf_offset: int;
  cppvf_address: doubleword_int;
  cppvf_table: cppvf_table_t
}

type cpp_member_t =
| DataMember of cpp_datamember_t
| VFPtr of cpp_vfpointer_t

class type cpp_class_int =
  object
    method initialize_function_interfaces:
             (doubleword_int -> doubleword_int option) -> unit
    method get_name: string
    method get_member: int -> cpp_member_t
    method get_function_interface: doubleword_int -> function_interface_t
    method get_instance_functions: (doubleword_int * string) list  (* faddr, fname *)
    method get_class_functions: (doubleword_int * string) list   (* faddr, fname *)
    method is_class_function: doubleword_int -> bool
    method has_member: int -> bool
    method dm_iter: (cpp_datamember_t -> unit) -> unit
    method vf_iter: (cpp_vfpointer_t -> unit) -> unit
    method stats_to_pretty: pretty_t
end


(* ======================================================== Memory reference === *)

type memory_base_t =
| BLocalStackFrame                                            (* local stack frame *)
| BRealignedStackFrame                      (* local stack frame after realignment *)
| BAllocatedStackFrame                         (* extended stack frame from alloca *)
| BGlobal                                                           (* global data *)
| BaseVar of variable_t      (* base provided by an externally controlled variable *)
| BaseUnknown of string                          (* address without interpretation *)

               
type memory_offset_t =
  | NoOffset
  | ConstantOffset of numerical_t * memory_offset_t
  | IndexOffset of variable_t * int * memory_offset_t
  | UnknownOffset 
  
class type memory_reference_int =
object ('a)
  (* identification *)
  method index: int

  (* comparison *)
  method compare      : 'a -> int

  (* accessors *)
  method get_base : memory_base_t
  method get_name : string
  method get_external_base: variable_t

  (* predicates *)
  method has_external_base: bool
  method is_stack_reference: bool
  method is_realigned_stack_reference: bool
  method is_global_reference: bool
  method is_unknown_reference: bool

  (* printing *)
  method toPretty : pretty_t
end

class type memory_reference_manager_int =
object
  (* reset *)
  method reset: unit

  method mk_local_stack_reference: memory_reference_int
  method mk_global_reference: memory_reference_int
  method mk_allocated_stack_reference: memory_reference_int
  method mk_realigned_stack_reference: memory_reference_int
  method mk_basevar_reference: variable_t -> memory_reference_int
  method mk_unknown_reference: string -> memory_reference_int

  (* accessors *)
  method get_memory_reference: int -> memory_reference_int

  (* predicates *)
  method is_unknown_reference       : int -> bool

  (* save and restore *)
  method read_xml: xml_element_int -> unit
end

(* =============================================================== Variables === *)

(* Denotations

   A bridge variable is used to carry function arguments from the point where
   they are pushed on the stack to the point where they are used in the call:
   BridgeVariable (address_of_call, argument index number (starting at 1))

   At the location where the argument is pushed the call address and argument
   index are recorded in the operand by the disassembly. This information is
   used during translation to create a bridge variable. If the operand holds a
   constant the bridge variable is registered with the constant manager,
   otherwise the bridge variable is assigned the value of the operand.

   At the location where the call is made, bridge variables are created and
   potentially resolved using the linear equality invariants to produce the
   arguments to the function. The bridge variables are abstracted immediately
   after the call

   In general, all auxiliary variable types are constants from the perspective
   of the function. They represent values that are set by the environment, before
   the function is entered (InitialRegisterValue or InitialMemoryValue) or during
   the execution of the function.

   External auxiliary variables are a vehicle to pass values across the call
   graph. An external auxiliary variable carries the address of the function
   and the variable identity of the variable in that function. An external
   variable can refer only to:
   - MemoryVariable (or initial) of global variables
   - Function return values
   - SideEffectValues
   - HeapBase pointers
   External auxiliary variables can be used as the base variable for memory
   references

*)

type assembly_variable_denotation_t =
  | MemoryVariable of int * memory_offset_t    (* memory reference index *)
  | RegisterVariable of register_t
  | CPUFlagVariable of eflag_t
  | AuxiliaryVariable of constant_value_variable_t

and constant_value_variable_t =
  | InitialRegisterValue of register_t * int            (* level *)
  | InitialMemoryValue of variable_t                    (* original variable *)
  | FrozenTestValue of
      variable_t            (* variable being frozen *)
      * ctxt_iaddress_t     (* address of test instruction *)
      * ctxt_iaddress_t     (* address of jump instruction *)
  | FunctionReturnValue  of ctxt_iaddress_t              (* call site *)
  | SyscallErrorReturnValue of ctxt_iaddress_t           (* call site *)
  | FunctionPointer of
      string                (* name of function *)
      * string              (* name of creator *)
      * ctxt_iaddress_t     (* address of creation *)
  | CallTargetValue of call_target_t 
  | SideEffectValue of
      ctxt_iaddress_t       (* callsite *)
      * string              (* argument description *)
      * bool                (* is-global address *) 
  | MemoryAddress of int * memory_offset_t   (* memory reference index *)
  | BridgeVariable of ctxt_iaddress_t * int      (* call site, argument index *)
  | FieldValue of string * int * string     (* struct name, offset, fieldname *)
  | SymbolicValue of xpr_t  (* expression that consists entirely of symbolic constants *)
  | SignedSymbolicValue of
      xpr_t    (* sign-extended symbolic value *)
      * int    (* original size (in bits) *)
      * int    (* extended size (in bits) *)
  | Special of string
  | RuntimeConstant of string
  | ChifTemp

class type vardictionary_int =
  object

    method xd: xprdictionary_int
    method reset: unit
    method get_indexed_variables: (int * assembly_variable_denotation_t) list
    method get_indexed_bases: (int * memory_base_t) list

    method index_memory_offset: memory_offset_t -> int
    method index_memory_base: memory_base_t -> int
    method index_assembly_variable_denotation: assembly_variable_denotation_t -> int
    method index_constant_value_variable: constant_value_variable_t -> int

    method get_memory_offset: int -> memory_offset_t
    method get_memory_base: int -> memory_base_t
    method get_assembly_variable_denotation: int -> assembly_variable_denotation_t
    method get_constant_value_variable: int -> constant_value_variable_t

    method write_xml_memory_offset:
             ?tag:string -> xml_element_int -> memory_offset_t -> unit
    method read_xml_memory_offset:
             ?tag:string -> xml_element_int -> memory_offset_t
    method write_xml_memory_base:
             ?tag:string -> xml_element_int -> memory_base_t -> unit
    method read_xml_memory_base: ?tag:string -> xml_element_int -> memory_base_t
    method write_xml_assembly_variable_denotation:
             ?tag:string -> xml_element_int -> assembly_variable_denotation_t -> unit
    method read_xml_assembly_variable_denotation:
             ?tag:string -> xml_element_int -> assembly_variable_denotation_t

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end
  

class type assembly_variable_int =
object ('a)
  (* identification *)
  method index: int

  (* comparison *)
  method compare: 'a -> int

  (* accessors *)
  method get_name: string
  method get_denotation: assembly_variable_denotation_t
  method get_register: register_t
  method get_pointed_to_function_name: string
  method get_call_site: ctxt_iaddress_t
  method get_se_argument_descriptor: string
  method get_frozen_variable: (variable_t * ctxt_iaddress_t * ctxt_iaddress_t)
  method get_initial_memory_value_variable: variable_t
  method get_initial_register_value_register: register_t
  method get_global_sideeffect_target_address: doubleword_int
  method get_calltarget_value: call_target_t
  method get_symbolic_value_expr: xpr_t

  (* predicates *)
  method is_auxiliary_variable: bool
  method is_register_variable: bool
  method is_mips_argument_variable: bool
  method is_arm_argument_variable: bool
  method is_memory_variable: bool

  method is_function_initial_value: bool    (* value from function environment *)
       
  method is_initial_register_value: bool
  method is_initial_mips_argument_value: bool
  method is_initial_arm_argument_value: bool
  method is_initial_stackpointer_value: bool
       
  method is_initial_memory_value: bool
  method is_frozen_test_value: bool
  method is_bridge_value: bool
  method is_bridge_value_at: ctxt_iaddress_t -> bool
  method is_return_value: bool
  method is_sideeffect_value: bool
  method is_special_variable: bool
  method is_runtime_constant: bool
  method is_function_pointer: bool
  method is_calltarget_value: bool
  method is_global_sideeffect: bool
  method is_symbolic_value: bool
  method is_signed_symbolic_value: bool

  method is_in_test_jump_range    : ctxt_iaddress_t -> bool

  (* printing *)
  method toPretty: pretty_t
                     (* method write_xml  : xml_element_int -> unit *)
end

class type variable_manager_int =
object
  (* reset *)
  method reset: unit
  method vard : vardictionary_int
  method memrefmgr: memory_reference_manager_int

  (* constructors *)
  method make_memory_variable: memory_reference_int -> memory_offset_t -> assembly_variable_int
  method make_register_variable: register_t -> assembly_variable_int
  method make_flag_variable: eflag_t -> assembly_variable_int
  method make_global_variable: numerical_t -> assembly_variable_int
  method make_frozen_test_value: 
    variable_t -> ctxt_iaddress_t -> ctxt_iaddress_t-> assembly_variable_int
  method make_bridge_value: ctxt_iaddress_t -> int -> assembly_variable_int
  method make_initial_register_value: register_t -> int -> assembly_variable_int
  method make_initial_memory_value  : variable_t -> assembly_variable_int
  method make_special_variable: string -> assembly_variable_int
  method make_runtime_constant: string -> assembly_variable_int
  method make_return_value: ctxt_iaddress_t -> assembly_variable_int
  method make_calltarget_value: call_target_t -> assembly_variable_int
  method make_function_pointer_value:
           string -> string -> ctxt_iaddress_t -> assembly_variable_int
  method make_side_effect_value:
           ctxt_iaddress_t -> ?global:bool -> string -> assembly_variable_int
  method make_field_value: string -> int -> string -> assembly_variable_int
  method make_symbolic_value: xpr_t -> assembly_variable_int
  method make_signed_symbolic_value:
           xpr_t -> int -> int -> assembly_variable_int

  method make_memref_from_basevar: variable_t -> memory_reference_int

  (* accessors *)
  method get_variable: variable_t -> assembly_variable_int
  method get_variable_by_index: int -> assembly_variable_int
  method get_memvar_reference: variable_t -> memory_reference_int
  method get_memvar_offset: variable_t -> memory_offset_t
  method get_initial_memory_value_variable: variable_t -> variable_t
  method get_memvar_basevar: variable_t -> variable_t
  method get_memval_basevar: variable_t -> variable_t
  method get_memvar_offset: variable_t -> memory_offset_t
  method get_memval_offset: variable_t -> memory_offset_t
  method get_global_variable_address: variable_t -> doubleword_int
  method get_stack_parameter_index: variable_t -> int option (* assuming 4-byte parameters *)
  method get_register: variable_t -> register_t
  method get_initial_register_value_register: variable_t -> register_t
  method get_pointed_to_function_name: variable_t -> string
  method get_calltarget_value: variable_t -> call_target_t
  method get_call_site: variable_t -> ctxt_iaddress_t
  method get_se_argument_descriptor: variable_t -> string
  method get_frozen_variable:
    variable_t -> (variable_t * ctxt_iaddress_t * ctxt_iaddress_t)
  method get_global_sideeffect_target_address: variable_t -> doubleword_int
  method get_symbolic_value_expr: variable_t -> xpr_t

  method get_assembly_variables: assembly_variable_int list
  method get_external_variable_comparator: variable_comparator_t

  (* predicates *)
  method is_stack_parameter_variable: variable_t -> bool  (* memory variable on the stack above the RA *)
  method is_realigned_stack_variable: variable_t -> bool
  method is_function_initial_value: variable_t -> bool
  method is_local_variable: variable_t -> bool  (* stack or register variable *)
  method is_global_variable: variable_t -> bool
  method is_register_variable: variable_t -> bool
  method is_mips_argument_variable: variable_t -> bool
  method is_arm_argument_variable: variable_t -> bool
  method is_stack_variable: variable_t -> bool  (* memory variable anywhere on the stack  *)
  method is_initial_register_value: variable_t -> bool
  method is_initial_mips_argument_value: variable_t -> bool
  method is_initial_arm_argument_value: variable_t -> bool
  method is_initial_stackpointer_value: variable_t -> bool
  method is_initial_memory_value: variable_t -> bool
  method is_frozen_test_value: variable_t -> bool
  method is_bridge_value: variable_t -> bool
  method is_bridge_value_at: ctxt_iaddress_t -> variable_t -> bool
  method is_in_test_jump_range: ctxt_iaddress_t -> variable_t -> bool
  method is_return_value: variable_t -> bool
  method is_sideeffect_value: variable_t -> bool
  method is_special_variable: variable_t -> bool
  method is_runtime_constant: variable_t -> bool
  method is_function_pointer: variable_t -> bool
  method is_calltarget_value: variable_t -> bool
  method is_symbolic_value: variable_t -> bool
  method is_signed_symbolic_value: variable_t -> bool
       
  method is_memory_variable: variable_t -> bool
  method is_basevar_memory_variable: variable_t -> bool
  method is_basevar_memory_value: variable_t -> bool
  method is_unknown_base_memory_variable: variable_t -> bool
  method is_unknown_offset_memory_variable: variable_t -> bool
  method is_unknown_memory_variable: variable_t -> bool
  method has_constant_offset: variable_t -> bool
  method is_global_sideeffect: variable_t -> bool
    
  method has_global_address: variable_t -> bool
    
  (* save and restore *)
                                             (* method write_xml  : xml_element_int -> unit *)

end

(* ============================================================ Global state === *)

type g_arithmetic_op = GPlus | GMinus | GTimes | GDivide
 
type gterm_t =
| GConstant of numerical_t
| GReturnValue of location_int
| GSideeffectValue of location_int * string    (* call site, argument name *)
| GArgValue of doubleword_int * int * int list (* function, arg index, offset *)
| GUnknownValue
| GArithmeticExpr of g_arithmetic_op * gterm_t * gterm_t
  
class type gv_reader_int =
object
  method get_type : btype_t
  method get_size : int option
  method get_offset: int list
  method is_function_pointer: bool
  method write_xml : xml_element_int -> unit
  method toPretty  : pretty_t
end
	
class type gv_writer_int =
object
  (* accessors *)
  method get_type: btype_t
  method get_size: int option 
  method get_offset: int list
  method get_value : gterm_t

  (* xml *)
  method write_xml : xml_element_int -> unit

  (* printing *)
  method toPretty         : pretty_t
  method to_report_pretty : (gterm_t -> pretty_t) -> pretty_t
end
	
class type global_variable_int =
object
  method add_reader: 
           ?ty:btype_t
           -> ?size:int option
           -> ?offset:int list
           -> ?fp:bool
           -> location_int
           -> unit
  method add_writer: 
           ?ty:btype_t
           -> ?size:int option
           -> ?offset:int list
           -> gterm_t
           -> location_int
           -> unit
  
  (* accessors *)    
  method get_address: doubleword_int
  method get_values: gterm_t list
  method get_types : btype_t list

  (* predicates *)
  method is_function_pointer: bool
    
  (* xml *)
  method write_xml : xml_element_int -> unit
  method read_xml  : xml_element_int -> unit

  (* printing *)
  method toPretty        : pretty_t
  method to_report_pretty: (gterm_t -> pretty_t) -> pretty_t
end

class type global_system_state_int =
object
  method initialize: unit

  method add_reader: 
           ?ty:btype_t
           -> ?size:int option
           -> ?offset:int list
           -> ?fp:bool
           -> doubleword_int
           -> location_int
           -> unit
  method add_writer:
           ?ty:btype_t
           -> ?size:int option
           -> ?offset:int list
           -> gterm_t
           -> doubleword_int
           -> location_int
           -> unit

  (* accessors *)
  method get_values: doubleword_int -> gterm_t list
  method get_types: doubleword_int -> btype_t list
  method get_destinations: gterm_t -> doubleword_int list

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
  method to_report_pretty: (gterm_t -> pretty_t) -> pretty_t
end



(* ============================================================== dictionary ==== *)

type constantstring = string * bool * int

class type bdictionary_int =
  object

    method reset: unit

    method index_string: string -> int
    method index_address: doubleword_int -> int
    method index_address_string: string -> int
    method index_arm_extension_register: arm_extension_register_t -> int
    method index_arm_extension_register_element:
             arm_extension_register_element_t -> int
    method index_arm_extension_register_replicated_element:
             arm_extension_register_replicated_element_t -> int
    method index_register: register_t -> int
         
    method get_string: int -> string
    method get_address: int -> doubleword_int
    method get_address_string: int -> string
    method get_arm_extension_register: int -> arm_extension_register_t
    method get_arm_extension_register_element:
             int -> arm_extension_register_element_t
    method get_arm_extension_register_replicated_element:
             int -> arm_extension_register_replicated_element_t
    method get_register: int -> register_t

    method write_xml_register: ?tag:string -> xml_element_int -> register_t -> unit
    method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
    method read_xml_register: ?tag:string -> xml_element_int -> register_t
    method read_xml_string: ?tag:string -> xml_element_int -> string

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

class type interface_dictionary_int =
  object
    method reset: unit

    method index_parameter_location: parameter_location_t -> int
    method index_role: (string * string) -> int
    method index_roles: (string * string) list -> int
    method index_fts_parameter: fts_parameter_t -> int
    method index_bterm: bterm_t -> int
    method index_gterm: gterm_t -> int
    method index_fts_parameter_list: fts_parameter_t list -> int
    method index_fts_parameter_value:  (fts_parameter_t * bterm_t) -> int
    method index_function_signature: function_signature_t -> int
    method index_function_interface: function_interface_t -> int
    method index_precondition: precondition_t -> int
    method index_postcondition: postcondition_t -> int
    method index_sideeffect: sideeffect_t -> int
    method index_function_stub: function_stub_t -> int
    method index_call_target: call_target_t -> int
    method index_c_struct_constant: c_struct_constant_t -> int
    method index_struct_field_value: (int * c_struct_constant_t) -> int

    method get_parameter_location: int -> parameter_location_t
    method get_role: int -> (string * string)
    method get_roles: int -> (string * string) list
    method get_fts_parameter: int -> fts_parameter_t
    method get_bterm: int -> bterm_t
    method get_fts_parameter_list: int -> fts_parameter_t list
    method get_fts_parameter_value:  int -> (fts_parameter_t * bterm_t)
    method get_function_signature: int -> function_signature_t
    method get_function_interface: int -> function_interface_t
    method get_precondition: int -> precondition_t
    method get_postcondition: int -> postcondition_t
    method get_sideeffect: int -> sideeffect_t
    method get_function_stub: int -> function_stub_t
    method get_call_target: int -> call_target_t
    method get_c_struct_constant: int -> c_struct_constant_t
    method get_struct_field_value: int -> (int * c_struct_constant_t)

    method write_xml_parameter_location:
             ?tag:string -> xml_element_int -> parameter_location_t -> unit
    method write_xml_fts_parameter:
             ?tag:string -> xml_element_int -> fts_parameter_t -> unit
    method write_xml_bterm: ?tag:string -> xml_element_int -> bterm_t -> unit

    method write_xml_gterm: ?tag:string -> xml_element_int -> gterm_t -> unit
    method write_xml_function_stub:
             ?tag:string -> xml_element_int -> function_stub_t -> unit
    method write_xml_call_target:
             ?tag:string -> xml_element_int -> call_target_t -> unit
    method write_xml_function_signature:
             ?tag:string -> xml_element_int -> function_signature_t -> unit
    method write_xml_function_interface:
             ?tag:string -> xml_element_int -> function_interface_t -> unit

    method write_xml_precondition:
             ?tag:string -> xml_element_int -> precondition_t -> unit
    method write_xml_postcondition:
             ?tag:string -> xml_element_int -> postcondition_t -> unit
    method write_xml_sideeffect:
             ?tag:string -> xml_element_int -> sideeffect_t -> unit
        
    method read_xml_parameter_location:
             ?tag:string -> xml_element_int -> parameter_location_t
    method read_xml_fts_parameter:
             ?tag:string -> xml_element_int -> fts_parameter_t
    method read_xml_bterm: ?tag:string -> xml_element_int -> bterm_t
    method read_xml_function_stub:
             ?tag:string -> xml_element_int -> function_stub_t
    method read_xml_call_target: ?tag:string -> xml_element_int -> call_target_t
    method read_xml_function_signature:
             ?tag:string -> xml_element_int -> function_signature_t
    method read_xml_function_interface:
             ?tag:string -> xml_element_int -> function_interface_t
    method read_xml_precondition:
             ?tag:string -> xml_element_int -> precondition_t
    method read_xml_postcondition:
             ?tag:string -> xml_element_int -> postcondition_t
    method read_xml_sideeffect:
             ?tag:string -> xml_element_int -> sideeffect_t

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

(* =========================================================== Function info === *)

class type argument_values_int =
object
  method add_argument_values : variable_t -> xpr_t list -> unit
  method get_argument_values : variable_t -> xpr_t list
  method write_xml           : xml_element_int -> unit
  method read_xml            : xml_element_int -> unit
  method toPretty            : pretty_t
end

(* Indirect jump target types:
   JumptableTarget (offset,jumptable,reg)
      jmp* offset(.,reg,4) with offset within a jump table
   OffsettableTarget (joffset,jumptable,datablock)
      movzx (reg, doffset(_)) where doffset is the start of an an offset table
      jmp* joffset(.,reg,4) where joffset is within a jump table
   JumpOnGlobal gvar
      jump target is provided in a global variable
   JumpOnArgument avar
      jump target is provided in an argument variable (or one of its dereferences)
   UnknownTarget: target of indirect jump has not been resolved yet
*)

type jump_target_t =
| JumptableTarget of doubleword_int * jumptable_int * register_t
| OffsettableTarget of doubleword_int * jumptable_int * data_block_int
| JumpOnTerm of bterm_t
| DllJumpTarget of string * string   (* PE *)
| SOJumpTarget of string  (* shared object, ELF *)
| UnknownJumpTarget

(* The function environment keeps track of all variables known to the
   function
*)
class type function_environment_int =
  object

    method varmgr : variable_manager_int
    method variable_names: variable_names_int
         
    (* setters *)
    method set_variable_name: variable_t -> string -> unit
    method set_class_member_variable_names:
             (string * function_interface_t * bool) list -> unit
    method set_java_native_method_signature: java_native_method_api_t -> unit
    method set_unknown_java_native_method_signature: unit
    method set_argument_names: doubleword_int -> function_interface_t -> unit
    method set_argument_structconstant: fts_parameter_t -> c_struct_constant_t -> unit
    method register_virtual_call: variable_t -> function_interface_t -> unit

    (* memory reference / assembly variable constructors *)
    method mk_unknown_memory_reference: string -> memory_reference_int
    method mk_local_stack_reference: memory_reference_int
    method mk_realigned_stack_reference: memory_reference_int
    method mk_base_variable_reference: variable_t -> memory_reference_int
    method mk_base_sym_reference: symbol_t -> memory_reference_int

    method mk_register_variable: register_t -> variable_t
    method mk_cpu_register_variable: cpureg_t -> variable_t
    method mk_fpu_register_variable: int -> variable_t
    method mk_mmx_register_variable: int -> variable_t
    method mk_xmm_register_variable: int -> variable_t
    method mk_control_register_variable: int -> variable_t
    method mk_debug_register_variable: int -> variable_t
    method mk_double_register_variable: cpureg_t -> cpureg_t -> variable_t

    method mk_mips_register_variable: mips_reg_t -> variable_t
    method mk_mips_special_register_variable: mips_special_reg_t -> variable_t
    method mk_mips_fp_register_variable: int -> variable_t

    method mk_arm_register_variable: arm_reg_t -> variable_t
    method mk_arm_extension_register_variable:
             arm_extension_register_t -> variable_t
    method mk_arm_extension_register_element_variable:
             arm_extension_register_element_t -> variable_t

    method mk_global_variable: numerical_t -> variable_t

    method mk_initial_register_value: ?level:int -> register_t -> variable_t
    method mk_initial_memory_value  : variable_t -> variable_t

    method mk_flag_variable  : eflag_t -> variable_t
    method mk_bridge_value   : ctxt_iaddress_t -> int -> variable_t

    method mk_memory_variable:
             ?save_name:bool -> memory_reference_int -> numerical_t -> variable_t
    method mk_index_offset_memory_variable:
             memory_reference_int -> memory_offset_t -> variable_t
    method mk_unknown_memory_variable: string -> variable_t
    method mk_frozen_test_value:
             variable_t -> ctxt_iaddress_t -> ctxt_iaddress_t -> variable_t
    method mk_special_variable: string -> variable_t
    method mk_runtime_constant: string -> variable_t
    method mk_return_value: ctxt_iaddress_t -> variable_t

    method mk_calltarget_value: call_target_t -> variable_t
    method mk_function_pointer_value:
             string -> string -> ctxt_iaddress_t -> variable_t
    method mk_side_effect_value:
             ctxt_iaddress_t -> ?global:bool-> string -> variable_t
    method mk_field_value: string -> int -> string -> variable_t
    method mk_symbolic_value: xpr_t -> variable_t
    method mk_signed_symbolic_value: xpr_t -> int -> int -> variable_t

    (* accessors *)
    method get_variable_comparator: variable_t -> variable_t -> int
 
    method get_frozen_variable:
             variable_t -> (variable_t * ctxt_iaddress_t * ctxt_iaddress_t)

    method get_local_stack_variables: variable_t list
    method get_realigned_stack_variables: variable_t list
    method get_parent_stack_variables: variable_t list
    method get_mips_argument_values: variable_t list
    method get_arm_argument_values: variable_t list
    method get_bridge_values_at: ctxt_iaddress_t -> variable_t list

    method get_variable: int -> variable_t
    method get_variables: variable_t list
    method get_local_variables: variable_t list
    method get_external_memory_variables: variable_t list
    method get_virtual_target : variable_t -> function_interface_t
    method get_global_sideeffect_target_address: variable_t -> doubleword_int

    method get_memory_reference: variable_t -> memory_reference_int
    method get_memvar_basevar: variable_t -> variable_t
    method get_memval_basevar: variable_t -> variable_t
    method get_memvar_offset: variable_t -> memory_offset_t
    method get_memval_offset: variable_t -> memory_offset_t
    method get_register: variable_t -> register_t
    method get_constant_offsets: variable_t -> numerical_t list option
    method get_total_constant_offset: variable_t -> numerical_t option
         
    method get_stack_parameter_index: variable_t -> int option
    method get_init_value_variable: variable_t -> variable_t (* memory or register *)
    method get_initial_register_value_register: variable_t -> register_t         
    method get_pointed_to_function_name: variable_t -> string
    method get_call_site: variable_t -> ctxt_iaddress_t
    method get_se_argument_descriptor: variable_t -> string
    method get_global_variable_address: variable_t -> doubleword_int
    method get_calltarget_value: variable_t -> call_target_t
    method get_symbolic_value_expr: variable_t -> xpr_t
         
    method get_argbasevar_with_offsets: variable_t -> (variable_t * numerical_t list) option
    method get_globalbasevar_with_offsets: variable_t -> (variable_t * numerical_t list) option
         
    method get_initialized_call_target_value: variable_t -> call_target_t
    method get_initialized_string_value: variable_t -> int -> string

    method get_regarg_deref_val_register: variable_t -> register_t
    method get_regarg_deref_var_register: variable_t -> register_t
         
    method get_var_count: int
    method get_globalvar_count: int
    method get_argvar_count: int
    method get_returnvar_count: int
    method get_sideeffvar_count: int
         
    (* scope and transactions *)
    method get_scope           : scope_int
    method start_transaction   : unit
    method end_transaction     : cmd_t list
    method mk_num_temp         : variable_t
    method mk_sym_temp         : variable_t
    method request_num_constant: numerical_t -> variable_t
         
    (* variable manager predicates *)
    method is_unknown_base_memory_variable: variable_t -> bool
    method is_unknown_offset_memory_variable: variable_t -> bool
    method is_unknown_memory_variable: variable_t -> bool
    method is_global_variable: variable_t -> bool
    method is_stack_variable: variable_t -> bool
    method is_local_variable: variable_t -> bool
    method is_memory_variable: variable_t -> bool
    method is_basevar_memory_variable: variable_t -> bool
    method is_basevar_memory_value: variable_t -> bool
    method has_constant_offset: variable_t -> bool
    method is_function_initial_value: variable_t -> bool
    method is_bridge_value: variable_t -> bool
    method is_bridge_value_at: ctxt_iaddress_t -> variable_t -> bool
    method is_function_pointer: variable_t -> bool
    method is_global_sideeffect: variable_t -> bool
    method is_return_value: variable_t -> bool
    method is_sideeffect_value: variable_t -> bool
    method is_frozen_test_value: variable_t -> bool
    method is_calltarget_value: variable_t -> bool
    method is_symbolic_value: variable_t -> bool
    method is_signed_symbolic_value: variable_t -> bool
         
    method is_stack_variable: variable_t -> bool  (* memory variable on the stack *)
    method is_stack_parameter_variable: variable_t -> bool (* stack-variable with positive offset *)
         
    method is_register_variable: variable_t -> bool
    method is_initial_register_value: variable_t -> bool
    method is_initial_mips_argument_value: variable_t -> bool
    method is_initial_arm_argument_value: variable_t -> bool
    method is_initial_stackpointer_value : variable_t -> bool
         
    method is_initial_memory_value: variable_t -> bool
    method is_in_test_jump_range: variable_t -> ctxt_iaddress_t -> bool
         
    method is_unknown_reference: int -> bool
         
    (* derived variable manager predicates *)
    method is_stack_parameter_value: variable_t -> bool  (* initial value of stack-parameter *)
         
    method is_initial_value: variable_t -> bool   (* memory or register initial value *)
         
    method is_stackarg_deref_var: variable_t -> bool
    method is_stackarg_deref_val: variable_t -> bool
    method is_regarg_deref_var: variable_t -> bool
    method is_regarg_deref_val: variable_t -> bool
    method is_arg_deref_var: variable_t -> bool
    method is_arg_deref_val: variable_t -> bool
         
    method is_return_value_derivative: variable_t -> bool
         
    method is_sideeffect_value_derivative: variable_t -> bool
         
    (* envionment data predicates *)
    method is_virtual_call : variable_t -> bool
    method has_initialized_call_target_value: variable_t -> bool
    method has_initialized_string_value     : variable_t -> int -> bool       
         
    (* printing *)
    method variable_name_to_string: variable_t -> string
    method variable_name_to_pretty: variable_t -> pretty_t
         
  end

(* ======================================================== call-target-info === *)

class type call_target_info_int =
  object

    (* accessors *)
    method get_target: call_target_t
    method get_name: string
    method get_app_address: doubleword_int
    method get_application_target: doubleword_int
    method get_wrapped_app_address: doubleword_int
    method get_wrapped_app_parameter_mapping: (fts_parameter_t * bterm_t) list
    method get_dll_target: string * string
    method get_inlined_target: doubleword_int * string
    method get_static_lib_target: doubleword_int * string * string list * string
    method get_jni_target_index: int
    method get_jni_index: int

    method get_semantics: function_semantics_t
    method get_function_interface: function_interface_t
    method get_signature: function_signature_t
    method get_parameters: fts_parameter_t list
    method get_returntype: btype_t
    method get_target: call_target_t
    method get_stack_adjustment: int option

    method get_preconditions: precondition_t list
    method get_postconditions: postcondition_t list
    method get_errorpostconditions: postcondition_t list
    method get_sideeffects: sideeffect_t list
    method get_io_actions: io_action_t list

    method get_enums_referenced : string list
    method get_enum_type:
             fts_parameter_t -> (btype_t * bool) option  (* name, specified as flags *)

    (* predicates *)
    method is_nonreturning: bool
    method has_sideeffects: bool

    method is_signature_valid: bool
    method is_semantics_valid: bool

    method is_app_call: bool
    method is_in_application_call: bool   (* target is in application code *)
    method is_wrapped_app_call: bool
    method is_dll_call: bool    (* static or dynamic *)
    method is_static_dll_call: bool
    method is_wrapped_dll_call: bool
    method has_dll_target: bool  (* either direct or wrapped *)
    method is_inlined_call: bool
    method is_wrapped_call: bool
    method is_unknown: bool
    method is_static_lib_call: bool
    method is_jni_call: bool
    method is_indirect_call: bool
    method is_virtual_call: bool
    method is_call_category: string -> bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toPretty: pretty_t

end

(* ============================================================ function-info === *)

(* The function info keeps track of the following information:
   - variables known to the function
   - call targets
   - jump targets
*)
class type function_info_int =
object

  method a  : doubleword_int  (* address of this function *)
  method env: function_environment_int
  method finv : invariant_io_int   (* function invariant *)
  method ftinv: type_invariant_io_int  (* function type invariant *)
  method iinv : ctxt_iaddress_t -> location_invariant_int (* instruction invariant *)
  method itinv: ctxt_iaddress_t -> location_type_invariant_int

  (* setters *)

  method schedule_invariant_reset: unit
  method reset_invariants: unit

  (* a function is considered complete if (1) all instructions are known, (2) all 
     indirect jumps are resolved. If a
     function is not complete its summary is not used for calls to this function,
     instead the default summary is used *)
  method set_incomplete: unit
  method set_complete  : unit
  method set_dynlib_stub: call_target_t -> unit

  method set_instruction_bytes: ctxt_iaddress_t -> string -> unit

  (* auxiliary variable that has a constant value within the function; 
     typically a bridge
     variable that represents an argument to a function call  *)
  method add_constant: variable_t -> numerical_t -> unit

  (* sets the number of bytes that are popped off the stack by this function when 
     it returns *)
  method set_stack_adjustment: int option -> unit

  method set_global_par: doubleword_int -> btype_t -> fts_parameter_t
  method set_stack_par: int -> btype_t -> fts_parameter_t
  method set_register_par: register_t -> btype_t -> fts_parameter_t

  (* records the test expression and auxiliary variable mappings for a
   * conditional jump at the given address *)
  method set_test_expr: ctxt_iaddress_t -> xpr_t -> unit
  method set_test_variables:
           ctxt_iaddress_t -> (variable_t * variable_t) list -> unit

  (* declares the variable to be a pointer that is dereferenced within
   * the function, causing it to be added as a base to the value set domain *)
  method add_base_pointer: variable_t -> unit

  (* connects the user of a condition code (such as a conditional jump
   * (at first address) to the address of the instruction that sets the
   * condition code (second address) *)
  method connect_cc_user         : ctxt_iaddress_t -> ctxt_iaddress_t -> unit

  (* set targets for indirect jumps *)
  method set_java_native_method_signature: java_native_method_api_t -> unit
  method set_unknown_java_native_method_signature: unit
  method set_jumptable_target   : 
    ctxt_iaddress_t -> doubleword_int -> jumptable_int -> register_t -> unit
  method set_offsettable_target : 
    ctxt_iaddress_t -> doubleword_int -> jumptable_int -> data_block_int -> unit
  method set_global_jumptarget  : ctxt_iaddress_t -> variable_t -> unit
  method set_argument_jumptarget: ctxt_iaddress_t -> variable_t -> unit
  method set_dll_jumptarget:
           ctxt_iaddress_t -> string -> string -> call_target_info_int -> unit
  method set_so_jumptarget:
           ctxt_iaddress_t -> string -> call_target_info_int -> unit
  method set_unknown_jumptarget : ctxt_iaddress_t -> unit

  method set_call_target: ctxt_iaddress_t -> call_target_info_int -> unit

  method set_nonreturning: unit

  method save_register: ctxt_iaddress_t -> register_t -> unit
  method restore_register: ctxt_iaddress_t -> register_t -> unit
    
  method record_sideeffect: ctxt_iaddress_t -> sideeffect_t -> unit
  method record_return_value: ctxt_iaddress_t -> xpr_t -> unit

  (* accessors *)
  method get_associated_cc_setter : ctxt_iaddress_t -> ctxt_iaddress_t
  method get_associated_cc_user   : ctxt_iaddress_t -> ctxt_iaddress_t
  method get_num_conditions_associated: int
  method get_num_test_expressions     : int

  method get_instruction_bytes: ctxt_iaddress_t -> string

  method get_dynlib_stub: call_target_t

  method get_call_target: ctxt_iaddress_t -> call_target_info_int

  method get_callees         : call_target_info_int list
  method get_callees_located : (ctxt_iaddress_t * call_target_info_int) list

  method get_address         : doubleword_int (* address of this function *)
  method get_name            : string
  method get_summary         : function_summary_int
  method get_constant        : variable_t -> numerical_t  (* auxiliary variable with constant value *)
  method get_base_pointers   : variable_t list (* list of base pointers used *)
  method get_stack_adjustment: int option

  method get_test_exprs    : (ctxt_iaddress_t * xpr_t) list (* all test expressions in the function *)
  method get_test_expr: ctxt_iaddress_t -> xpr_t  (* branch expr (simplified) *)

  (* variable mapping for conditional jump expression *)
  method get_test_variables:
           ctxt_iaddress_t -> (variable_t * variable_t) list

  (* indirect jump targets *)
  method get_dll_jumptarget        : ctxt_iaddress_t -> (string * string)
  method get_jump_target           : ctxt_iaddress_t -> jump_target_t
  method get_jumptable_jumps       : ctxt_iaddress_t list 
  method get_jumptable_count       : int
  method get_offsettable_count     : int
  method get_global_jump_count     : int
  method get_argument_jump_count   : int
  method get_unknown_jumps_count   : int
  method get_dll_jumps_count       : int
  method get_indirect_jumps_count  : int

  method get_return_values   : xpr_t list

  method get_call_count : int
  method get_call_category_count: string -> int

  (* predicates *)
  method is_complete : bool
  method is_dynlib_stub : bool
  method were_invariants_reset: bool
  method sideeffects_changed  : bool
  method call_targets_were_set: bool

  method has_associated_cc_user: ctxt_iaddress_t -> bool
  method has_associated_cc_setter: ctxt_iaddress_t -> bool
  method has_call_target: ctxt_iaddress_t -> bool
  method is_dll_jumptarget: ctxt_iaddress_t -> bool
  method has_jump_target: ctxt_iaddress_t -> bool
  method has_unknown_jump_target : bool
  method has_constant: variable_t -> bool
  method has_test_expr: ctxt_iaddress_t -> bool
  method is_base_pointer: variable_t -> bool

  (* save and restore *)
  method read_xml_user_summary: xml_element_int -> unit
  method set_bc_summary: function_summary_int -> unit
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

  (* printing *)
  method state_to_pretty: pretty_t 
  method summary_to_pretty: pretty_t
  method saved_registers_to_pretty: pretty_t
  method base_pointers_to_pretty: pretty_t
  method return_values_to_pretty: pretty_t


end


(* ==================================================================== Floc === *)

class type floc_int =
object

  (* setters *)
  method set_instruction_bytes: string -> unit

  (* sets the targets for an indirect jump at this instruction *)
  method set_jumptable_target: doubleword_int -> jumptable_int -> register_t -> unit

  method set_call_target: call_target_info_int -> unit
  method update_call_target: unit

  (* sets the test expression for this instruction *)
  method set_test_expr: xpr_t -> unit

  (* sets the mapping between auxiliary variables and regular variables for a 
     test expression *)
  method set_test_variables: (variable_t * variable_t) list -> unit
 
  (* evaluates the value of eax at this location and reports it to the function 
     info *)
  method record_return_value: unit

  (* add type facts *)
  method add_var_type_fact:
           variable_t -> ?structinfo:string list -> btype_t -> unit
  method add_const_type_fact: numerical_t -> btype_t -> unit
  method add_xpr_type_fact: xpr_t -> btype_t -> unit


  (* accessors *)
  method ia: doubleword_int            (* local instruction address *)
  method cia: string                   (* full-context instruction address string *)
  method fa: doubleword_int            (* address of function info *)
  method l: location_int               (* location of this instruction *)
  method f: function_info_int          (* function_info that this instruction belongs to *)
  method env: function_environment_int (* variable environment of the function *)
  method inv: location_invariant_int
  method tinv: location_type_invariant_int

  method evaluate_summary_address_term: bterm_t -> variable_t option
  method evaluate_summary_term: bterm_t -> variable_t -> xpr_t

  (* returns the bytes of the instruction as a hexstring *)
  method get_instruction_bytes: string

  (* returns the value of the nth argument (starting from 1) to this call instruction *)
  method get_function_arg_value: int -> xpr_t

  (* returns the value of an api parameter *)
  method get_fts_parameter_expr: fts_parameter_t -> xpr_t option

  (* rewrites the variable to an expression with external variables *)
  method rewrite_variable_to_external: variable_t -> xpr_t

  (* converts an expr into a list of expressions based on variables of another function *)
  method externalize_expr: doubleword_int -> xpr_t -> bterm_t list

  (* returns the constant value of a variable at this instruction *)
  method get_constant: variable_t -> numerical_t

  (* returns the interval value of a variable at this instruction *)
  method get_interval: variable_t -> interval_t

  (* returns the memory reference corresponding to the address in variable plus offset *)
  method get_memory_variable_1: ?align:int -> variable_t -> numerical_t -> variable_t

  (* returns the memory reference corresponding to a base and index variable plust offset *)
  method get_memory_variable_2: variable_t -> variable_t -> numerical_t -> variable_t

  (* returns the memory reference corresponding to a base and scaled index variable 
     plus offset *)
  method get_memory_variable_3: variable_t -> variable_t -> int -> numerical_t -> variable_t

  (* returns the memory reference corresponding to a global base and scaled index variable *)
  method get_memory_variable_4: variable_t -> int -> numerical_t -> variable_t

  (* returns the memory reference that corresponds to the address expression *)
  method decompose_address: xpr_t -> (memory_reference_int * memory_offset_t)

  (* returns the variable associated with the address expression *)
  method get_lhs_from_address: xpr_t -> variable_t

  (* returns the value of the bridge variable for a given stack parameter at this instruction *)
  method get_bridge_variable_value: int -> variable_t -> xpr_t

  (* returns the difference between esp and the location of the return address, 
     or the difference between esp and a level of alignment indicated with the 
     first returned value *)
  method get_stackpointer_offset: string -> int * interval_t

  (* returns the targets for the indirect jump instruction *)
  method get_jump_target         : jump_target_t
  method get_jump_successors     : doubleword_int list

  method get_call_target: call_target_info_int
  method get_call_args: (fts_parameter_t * xpr_t) list
  method get_mips_call_arguments : (fts_parameter_t * xpr_t) list
  method get_arm_call_arguments: (fts_parameter_t * xpr_t) list

  (* method get_jumptable_indexed_targets: (int * doubleword_int) list *)

  (* returns the test expression for a conditional jump in this instruction *)
  method get_test_expr: xpr_t
  method get_raw_test_expr: xpr_t (* branch expr *)

  (* returns the auxiliary variables used in a test expression *)
  method get_test_variables: (variable_t * variable_t) list

  (* returns the CHIF code associated with the call instruction *)
  method get_call_commands: (doubleword_int -> string option) -> cmd_t list

  method get_mips_call_commands: cmd_t list
  method get_mips_syscall_commands: cmd_t list

  method get_arm_call_commands: cmd_t list

  (* returns the CHIF code associated with an assignment instruction *)
  method get_assign_commands:
           variable_t
           -> ?size:xpr_t
           -> ?vtype:btype_t
           -> xpr_t
           -> cmd_t list

  method get_conditional_assign_commands:
           xpr_t -> variable_t -> xpr_t -> cmd_t list

  method get_sideeffect_assigns: function_semantics_t -> cmd_t list

  (* returns the CHIF code associated with an abstraction of variables *)
  method get_abstract_commands:
           variable_t -> ?size:xpr_t -> ?vtype:btype_t -> unit -> cmd_t list

  method get_abstract_cpu_registers_command: cpureg_t list -> cmd_t

  method get_abstract_registers_command: register_t list -> cmd_t

  (* returns the CHIF code associated with an unmodeled operation *)
  method get_operation_commands:
           variable_t
           -> ?size:xpr_t
           -> ?vtype:btype_t
           -> symbol_t
           -> op_arg_t list
           -> cmd_t list

  (* predicates *)

  (* returns true if the given variable evaluates to a constant at this location *)
  method is_constant: variable_t -> bool

  (* returns true if the given variable evaluates to a non-trivial interval at this location *)
  method is_interval: variable_t -> bool

  (* returns true if the given expression is a memory address *)
  method is_address : xpr_t -> bool

  method is_base_offset: variable_t -> bool

  (* returns true if the given variable evaluates to an initial value of a register *)
  method has_initial_value: variable_t -> bool

  (* returns true if this instruction has a test expression for a conditional jump *)
  method has_test_expr: bool

  method has_call_target: bool

  (* returns true if this instruction has jump table targets *)
  method has_jump_target: bool

 (* printing *)
  method stackpointer_offset_to_string: string -> string

end

(* ========================================================= Specializations === *)

type block_restriction_t =
  | BranchAssert of bool

class type specialization_int =
  object
    method get_name: string
    method get_functions: string list
    method get_blocks: string -> string list
    method get_block_restriction: string -> string -> block_restriction_t
    method has_block_restriction: string -> string -> bool
    method toPretty: pretty_t
  end

class type specializations_int =
  object
    method activate_specialization: string -> unit
    method get_specialization: string -> specialization_int  (* function address *)
    method has_specialization: string -> bool  (* function address *)
    method read_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end

(* ===================================================== Section header info === *)

class type section_header_info_int =
  object
    (* accessors *)
    method get_name: string
    method get_addr: doubleword_int
    method get_offset: doubleword_int
    method get_size: doubleword_int
    method get_type: doubleword_int
    method get_link: doubleword_int
    method get_info: doubleword_int
    method get_addralign: doubleword_int
    method get_entsize: doubleword_int

    (* predicates *)
    method has_addr: bool
    method has_offset: bool
    method has_size: bool
    method has_type: bool
    method has_link: bool
    method has_info: bool
    method has_addralign: bool
    method has_entsize: bool

    (* i/o *)
    method read_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end

class type section_header_infos_int  =
  object
    (* accessors *)
    method get_section_header_names: string list
    method get_section_header_info: string -> section_header_info_int

    (* predicates *)
    method has_section_header_info: string -> bool   (* section name *)

    (* i/o *)
    method read_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


(* ============================================================= System info === *)

class type system_info_int =
object

  (* initialization *)
  method initialize: unit
  method initialize_jumptables:
           (doubleword_int -> bool) -> (doubleword_int * string) list -> unit
  method initialize_datablocks: (doubleword_int * string) list -> unit
  method initialize_function_entry_points: (unit -> doubleword_int list) -> unit
  method initialize_type_definitions     : unit
    
  (* setters *)
  method set_filename: string -> unit
  method set_xfilesize: int -> unit
  method set_file_string: string -> unit
  method set_elf: unit
  method set_mips: unit
  method set_arm: unit
  method set_big_endian: unit
  method set_preamble_cutoff: int -> unit
  method set_image_base: doubleword_int -> unit
  method set_base_of_code_rva: doubleword_int -> unit
  method set_elf_is_code_address: doubleword_int -> doubleword_int -> unit
  method set_code_size: doubleword_int -> unit
  method set_address_of_entry_point: doubleword_int -> unit
  method set_thread_start_address  : 
    doubleword_int -> ctxt_iaddress_t -> doubleword_int -> bterm_t list -> unit
  (* creation faddr, iaddr, function start addr, arguments *)

  method add_exported_item_name: doubleword_int -> string -> unit
  method add_locked_instruction: doubleword_int -> unit
  method add_bound_library_function: doubleword_int -> (string * string) -> unit
  method add_ifile: string -> unit (* file to be parsed by cil *)

  method add_data_block: data_block_int -> unit
  method add_jumptable: jumptable_int -> unit
  method set_jump_target:
           doubleword_int
           -> doubleword_int
           -> jumptable_int
           -> data_block_int
           -> unit

  method add_lib_function_loaded: string -> string -> unit
  method add_esp_adjustment: doubleword_int -> doubleword_int -> int -> unit
  method add_goto_return: doubleword_int -> doubleword_int -> unit
  method set_virtual_function_table: doubleword_int -> unit

  method set_arm_thumb_switch: string -> string -> unit

  method import_ida_function_entry_points: unit

  method decode_string: string -> doubleword_int -> string
    
  (* accessors *)
  method get_size: int
  method get_code_size: doubleword_int
  method get_data_blocks: data_block_int list
  method get_jumptables: jumptable_int list
  method ifiles: string list
  method get_call_target:
           doubleword_int -> doubleword_int -> call_target_t
  method get_jump_table_target:
           doubleword_int
           -> doubleword_int
           -> (jumptable_int * doubleword_int * int * int)
  method get_indirect_jump_targets:
           doubleword_int -> doubleword_int -> doubleword_int list
  method get_esp_adjustment: doubleword_int -> doubleword_int -> int

  method get_preamble_cutoff: int
  method get_filename: string
  method get_xfilesize: int
  method get_file_string: ?hexSize:doubleword_int -> doubleword_int -> string
  method get_file_input:
           ?hexSize:doubleword_int -> doubleword_int ->  stream_wrapper_int
  method get_string_stream: string -> pushback_stream_int
  method get_image_base: doubleword_int
  method get_base_of_code_rva: doubleword_int    (* relative virtual address *)
  method get_address_of_entry_point: doubleword_int
  method get_bound_library_function: doubleword_int -> (string * string)
  method get_exported_item_name: doubleword_int -> string
  method get_exported_data_spec: string -> data_export_spec_t
  method get_data_block: doubleword_int -> data_block_int
  method get_jumptable: doubleword_int -> jumptable_int
  method get_class_infos:
           doubleword_int -> (string * function_interface_t * bool) list
  method get_jump_target: 
    doubleword_int -> (doubleword_int * jumptable_int * data_block_int)
  method get_lib_functions_loaded : (string * string list) list
  method get_thread_start_arguments: doubleword_int -> bterm_t list list
  method get_goto_return: doubleword_int -> doubleword_int
  method get_cfnop: doubleword_int -> int * string
  method get_cfjmp: doubleword_int -> doubleword_int * int * string
  method get_successors: doubleword_int -> doubleword_int list
  method get_arm_thumb_switch: string -> string option
  method get_argument_constraints:
           (* name, offset, lower bound, upper bound *)
           string -> (string * int option * int option * int option) list

  method get_ida_function_entry_points: doubleword_int list
  method get_userdeclared_codesections: doubleword_int list

  method get_initialized_memory_strings: (doubleword_int * string) list

  method get_user_data_block_count: int
  method get_user_call_target_count: int
  method get_user_struct_count: int
  method get_user_nonreturning_count: int
  method get_user_class_count: int

  (* predicates *)
  method is_elf: bool
  method is_mips: bool
  method is_arm: bool
  method is_little_endian: bool
  method is_nonreturning_call: doubleword_int -> doubleword_int -> bool
  method is_fixed_true_branch: doubleword_int -> bool
  method is_thread_start_address: doubleword_int -> bool
  method is_class_member_function: doubleword_int -> bool
  method has_call_target: doubleword_int -> doubleword_int -> bool
  method has_jump_table_target: doubleword_int -> doubleword_int -> bool
  method has_esp_adjustment: doubleword_int -> doubleword_int -> bool
  method has_exported_item_name: doubleword_int -> bool
  method has_exported_data_spec: string -> bool
  method has_data_block: doubleword_int -> bool
  method has_jumptable: doubleword_int -> bool
  method has_bound_library_function: doubleword_int -> bool
  method is_locked_instruction: doubleword_int -> bool
  method has_jump_target: doubleword_int -> bool
  method has_indirect_jump_targets: doubleword_int -> doubleword_int -> bool
  method has_argument_constraints: string -> bool
  method is_code_address: doubleword_int -> bool
  method is_in_data_block: doubleword_int -> data_block_int option
  method is_in_jumptable: doubleword_int -> jumptable_int option
  method is_in_readonly_range: doubleword_int -> bool
  method is_goto_return: doubleword_int -> bool
  method is_cfnop: doubleword_int -> bool
  method is_cfjmp: doubleword_int -> bool
  method is_inlined_function: doubleword_int -> bool

  (* xml *)
  method read_xml_constant_file    : string -> unit

  (* saving *)
  method write_xml: xml_element_int -> unit

end


(* ============================================================== Code graph === *)

class type cmd_list_int =
object
  method cmd_list : cmd_t list
  method reverse_cmds: unit
  method toPretty: pretty_t
end

class type code_graph_int =
object 
  (* setters *)
  method add_node  : symbol_t -> cmd_t list -> unit
  method add_edge  : symbol_t -> symbol_t -> unit
  method set_cmd   : symbol_t -> cmd_t list -> unit

  (* accessors *)
  method get_cmds     : symbol_t -> cmd_list_int

  (* actions *)
  method remove_edge: symbol_t -> symbol_t -> unit

  (* converters *)
  method to_cfg: symbol_t -> symbol_t -> cfg_int
end


(* ============================================================== Call graph === *)

class type callgraph_int =
object
  (* setters *)
  method add_app_node: doubleword_int -> unit
       
  method add_app_edge:
           doubleword_int
           -> doubleword_int
           -> ctxt_iaddress_t
           -> (int * string * xpr_t) list
           -> unit
       
  method add_so_edge:
           doubleword_int
           -> string
           -> ctxt_iaddress_t
           -> (int * string * xpr_t) list
           -> unit
       
  method add_dll_edge:
           doubleword_int
           -> string
           -> ctxt_iaddress_t
           -> (int * string * xpr_t) list
           -> unit
       
  method add_jni_edge:
           doubleword_int
           -> int
           -> ctxt_iaddress_t
           -> (int * string * xpr_t) list
           -> unit
       
  method add_unresolved_edge:
           doubleword_int
           -> int
           -> ctxt_iaddress_t
           -> (int * string * xpr_t) list
           -> unit
       
  method add_virtual_edge:
           doubleword_int
           -> function_interface_t
           -> ctxt_iaddress_t
           -> (int * string * xpr_t) list
           -> unit
      
  (* saving *)
  method write_xml  : xml_element_int -> unit

end

(* ============================================================== Metrics === *)

class type ['a] metrics_handler_int =
  object
    method name: string
    method init_value: 'a
    method add: 'a -> 'a -> 'a
    method calc: int -> 'a
    method write_xml: xml_element_int -> 'a -> unit
    method read_xml: xml_element_int -> 'a
    method toPretty: 'a -> pretty_t
  end

type exports_metrics_t = {
  exm_count  : int ;       (* number of functions exported *)
  exm_cpp    : int ;       (* C++ functions *)
  exm_java   : int         (* Java native methods *)
  }

type disassembly_metrics_t = {
  dm_unknown_instrs : int ;     (* # unknown or inconsisten instructions *)
  dm_instrs         : int ;     (* total number of instructions from disassembly *)
  dm_functions      : int ;     (* # functions *)
  dm_coverage       : int ;     (* # instructions within functions *)
  dm_pcoverage      : float ;   (* percent coverage of all instructions *) 
  dm_overlap        : int ;     (* # instructions in multiple functions *)
  dm_alloverlap     : int ;     (* total number of instructions in multiple functions *)
  dm_jumptables     : int ;     (* # jumptables identified *)
  dm_datablocks     : int ;     (* # datablocks provided and identified *)
  dm_imports        : (string * int * int * bool) list ; 
                                (* number of functions imported per dll, LoadLib *)
  dm_exports        : exports_metrics_t 
}

type memacc_metrics_t = {
  mmem_reads : int ;
  mmem_qreads: int ;      (* memory reads from unknown address *)
  mmem_writes: int ;
  mmem_qwrites: int ;     (* memory writes to unknown address *)
  mmem_esptop : int ;     (* locations where esp is unknown *)
  mmem_esprange: int      (* locations where only range is known for esp *)
}

type prec_metrics_t = {
  prec_esp : float ;
  prec_reads: float ;
  prec_writes: float
}

type cfg_metrics_t = {
  mcfg_instrs : int ;
  mcfg_bblocks: int ;
  mcfg_loops: int ;
  mcfg_loopdepth: int ;
  mcfg_complexity: int ;
  mcfg_vc_complexity: float        (* product of cfg complexity and variable count *)
}

type vars_metrics_t = {
  mvars_count  : int ;
  mvars_global : int ;
  mvars_args   : int ;
  mvars_return : int ;
  mvars_sideeff: int
}

type calls_metrics_t = {
  mcalls_count : int ;
  mcalls_dll   : int ;
  mcalls_app   : int ;        (* known application calls *)
  mcalls_jni   : int ;        (* jni call-backs *)
  mcalls_arg   : int ;        (* calls on an argument value *)
  mcalls_arg_x : int ;        (* calls on an argument value without targets *)
  mcalls_global: int ;        (* calls on global variable *)
  mcalls_global_x: int ;      (* calls on global variable without targets *)
  mcalls_unr   : int ;        (* unresolved indirect calls *)
  mcalls_nosum : int ;        (* dll calls without a function summary *)
  mcalls_inlined: int ;       (* inlined application calls *)
  mcalls_staticdll: int ;     (* calls to statically linked dll functions *)
  mcalls_staticlib: int ;     (* calls to statically linked library functions *)
  mcalls_appwrapped: int ;    (* calls to a function that wraps an application call *)
  mcalls_dllwrapped: int ;    (* calls to a function that wraps a dll call *)
}

type jumps_metrics_t = {
  mjumps_indirect: int ;
  mjumps_unknown    : int ;           (* no information *)
  mjumps_dll        : int ;           (* indirect jump to import table *)
  mjumps_jumptable  : int ;           (* target is a jump table *)
  mjumps_jumptable_norange: int ;     (* target is a jump table, no range info on index reg *)
  mjumps_global     : int ;           (* target is provided in global variable *)
  mjumps_argument   : int ;           (* target is provided in argument variable *)
  mjumps_offsettable: int             (* target is a jump table accessed via offset table *)
}

type cc_metrics_t = {
  mcc_instrs : int ;           (* instructions that depend on a condition code *)
  mcc_assoc  : int ;           (* cc-instructions associated with cc-setting instruction *)
  mcc_test   : int             (* cc-instructions with a test expression *)
}

type invs_metrics_t = {
  minvs_table : int ;          (* number of distinct invariants *)
  minvs_count : int            (* total number of invariants *)
}

type tinvs_metrics_t = {
  mtinvs_table : int ;            (* number of distinct type invariants *)
  mtinvs_count : int              (* total number of type invariants *)
}

type result_metrics_t = {
  mres_prec : prec_metrics_t ;
  mres_memacc: memacc_metrics_t ;
  mres_cfg: cfg_metrics_t ;
  mres_vars: vars_metrics_t ;
  mres_calls: calls_metrics_t ;
  mres_jumps: jumps_metrics_t ;
  mres_cc: cc_metrics_t ;
  mres_invs: invs_metrics_t ;
  mres_tinvs: tinvs_metrics_t
}

type function_run_t = {
  frun_index : int ;
  frun_time  : float ;
  frun_skip  : bool ;
  frun_nonrel: bool ;
  frun_reset : bool ;         (* invariants were reset *)
  frun_delta_instrs: int ;    (* difference in number of instrs compared to previous *)
  frun_unresolved_calls: int ; 
  frun_unresolved_jumps: int ; 
  frun_delta_vars: int ;      (* difference in number of variables *)
  frun_delta_invs: int        (* difference in number of invariants *)
}

type function_results_t = {
  fres_addr   : string ;
  fres_stable : bool ;
  fres_time   : float ;
  fres_runs   : function_run_t list ;
  fres_results: result_metrics_t
}

type file_run_t = {
  ffrun_index : int ;
  ffrun_ftime : float ;          (* sum of function analysis times *)
  ffrun_time  : float ;          (* total analysis time, including disassembly *)
  ffrun_propagation_time: float ; (* time to propagate arguments forward to callees *)
  ffrun_fns_analyzed: int ;
  ffrun_skips : int ;
  ffrun_nonrel: int ;
  ffrun_resets: int ;            (* number of functions for which invariants were reset *)
  ffrun_vc_complexity : float ;  (* composite variable-cfg complexity measure *)
  ffrun_fns          : int ;     (* functions in the system *)
  ffrun_delta_instrs : int ;     (* instructions added or removed during this run *)
  ffrun_unresolved_calls : int ;  
  ffrun_unresolved_jumps : int ;  
  ffrun_delta_vars : int ;       (* variables added during this run *)
  ffrun_delta_invs : int         (* invariants added during this run *)
}

type aggregate_metrics_t = {
  agg_avg_function_size: float ;
  agg_max_function_size: int ;
  agg_avg_block_count: float ;
  agg_avg_cfgc: float ;
  agg_max_cfgc: int ;
  agg_max_vc_complexity: float ;
  agg_median_function_size: int ;
  agg_median_block_count: int ;
  agg_median_cfgc: int ;
  agg_loop_activity: float 
}

type userdata_metrics_t = {
  um_function_entry : int ;
  um_data_block : int ;
  um_struct : int ;
  um_nonreturning : int ;
  um_class : int 
}

type ida_data_t = {
  ida_function_entry_points : doubleword_int list
}

type file_results_t = {
  ffres_stable: bool ;
  ffres_time : float ;
  ffres_runs : file_run_t list ;
  ffres_functions: function_results_t list ;
  ffres_totals: result_metrics_t ; 
  ffres_aggregate: aggregate_metrics_t ;
  ffres_disassembly : disassembly_metrics_t ;
  ffres_userdata : userdata_metrics_t ;
  ffres_idadata : ida_data_t
}

class type file_metrics_int =
object
  method record_results:
           ?skip:bool
           -> ?nonrel:bool
           -> ?reset:bool
           -> doubleword_int
           -> float
           -> memacc_metrics_t
           -> cfg_metrics_t
           ->unit
  method record_runtime: float -> unit
  method record_propagation_time: float -> unit
  method set_disassembly_results: disassembly_metrics_t -> unit
  method get_index: int
  method get_unresolved_calls: int
  method get_dll_calls_no_sum: int
  method is_stable: string -> string list -> bool
  method load_xml: unit
  method write_xml_analysis_stats   : xml_element_int -> unit
  method read_xml : xml_element_int -> unit
  method write_xml: xml_element_int -> unit
  method function_to_pretty: string -> pretty_t
  method toPretty : pretty_t
end

class type disassembly_summary_int =
object
  method record_disassembly_time: float -> unit
  method record_construct_functions_time: float -> unit
  method set_disassembly_metrics: disassembly_metrics_t -> unit
  method write_xml : xml_element_int -> unit
  method toPretty  : pretty_t
end
                           
