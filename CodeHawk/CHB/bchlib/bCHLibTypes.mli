(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBCTypes


(** {b Principal type definitions for [bchlib].} *)


(** {1 Generic types}*)

class type ['a] sumtype_string_converter_int =
  object
    method to_string: 'a -> string
    method from_string: string -> 'a
  end

type print_format_t = ATT | INTEL

type calling_convention_t = StdCall | CDecl

type bool3 = Yes | No | Maybe


(** {1 Constants and addresses} *)

(** {2 Doubleword (32-bit value)} *)

(** Underlying type for doubleword. Int is assumed to be sufficient wide to
    represent a 32-bit value (i.e., it must be at least a 64-bit ocaml
    integer.*)
type dw_index_t = int


(** representation of a 32-bit unsigned value (created from and indexed by a
    64-bit ocaml integer, assumed to be the default width). Immutable. *)
class type doubleword_int =
object ('a)
  (* identification *)
  method index: dw_index_t

  (** Returns the unsigned value represented by this doubleword. *)
  method value: int

  (* comparison *)

  (** [dw#equal other] returns true if [other#value] is equal to [dw#value].*)
  method equal: 'a -> bool

  (** [dw#compare other] returns 0 if [dw#value] is equal to [other#value],
      [-1] if [dw#value] is less than [other#value] and [1] otherwise.*)
  method compare: 'a -> int

  (** [dw#lt other] returns true if [dw#value] is less than [other#value].*)
  method lt: 'a -> bool

  (** [dw#le other] returns true if [dw#value] is less than or equal to
      [other#value].*)
  method le: 'a -> bool

  (* alignment *)

  (** [dw#to_aligned true n] returns a pair (dw', d), where dw' is the doubleword
      with value the nearest value greater than or equal to the value of dw
      that is a multiple of [n], and [d] the difference [dw' - dw].

      [dw#to_aligned false n] (default) returns a pair (dw', d) where dw' is the
      doubleword with value the nearest value less than or equal to the value of
      [dw] that is a multiple of [n], and [d] the difference [dw - dw'].

      @raises Invalid_argument if [n <= 0]. *)
  method to_aligned: ?up:bool -> int -> ('a * int)

  (* conversion *)

  (** Returns [dw#value].*)
  method to_int: int

  (** Returns [dw#value] represented as a big_int.*)
  method to_big_int: big_int

  (** Returns [dw#value] represented as a numerical_t.*)
  method to_numerical: numerical_t

  (** Returns [dw#value] as a numerical_t if [dw#value] is less than [2^31],
      [dw#value - 2^31] as a numerical_t otherwise.*)
  method to_signed_numerical: numerical_t

  (** Returns a date-time string by converting [dw#value] to a Unix.tm structure.

      @raise Invalid_argument if the intermediate Unix.tm structure is invalid.*)
  method to_time_date_string: string

  (** Returns a string representing a list of four characters if all four
      bytes represent printable characters. Otherwise returns [None].

      Example: [dw(0x64636261)#to_char_string] returns "['a' 'b' 'c' 'd']".
   *)
  method to_char_string: string option

  (** Returns a string representing four characters in order.

      Example: [dw(0x61626364)#to_string] returns "abcd".*)
  method to_string: string

  (** Returns a string representing four characters in reverse order.

      Example: [dw(0x61626364)#to_string_fragment] returns "dcba".*)
  method to_string_fragment: string

  (** Returns an eight-character string representing the eight nibbles
      (as bytes) (most significant byte first, big endian).

      Example: [dw(0)#to_fixed_length_hex_string] returns "00000000";
      [dw(255)#to_fixed_length_hex_string] returns "000000ff".*)
  method to_fixed_length_hex_string: string

  (** Returns an eight-character string representing the eight nibbles
      (as bytes) (least significant byte first, little endian).

      Example: [dw(0)#to_fixed_length_hex_string_le] returns "00000000";
      [dw(255)#to_fixed_length_hex_string_le] returns "ff000000".*)
  method to_fixed_length_hex_string_le: string

  (** Returns a standard hexadecimal notation of [dw#value] (without
      leading zeroes).

      Example: [dw(0)#to_hex_string] returns "0x0"; dw(255)#to_hex_string]
      returns "0xff".*)
  method to_hex_string: string

  (** Returns a standard hexadecial string representation of [dw#value]
      if [dw#value] is less than [2^31], and otherwise returns
      [-hex(dw#value - 2^32)].

      Example: [dw(0xffffffff)#to_signed_hex_string] returns "-0x1".*)
  method to_signed_hex_string: string

  (** operations *)

  (** Returns [dw] if [dw#value] is less than [2^31], otherwise returns
      dw(dw#value - 2^31).*)
  method unset_highest_bit: 'a

  (** [dw#subtract other] returns [dw(dw#value - other#value)] if
      [dw#value] is greater than or equal to other#value, otherwise
      returns Error.*)
  method subtract: 'a  -> 'a traceresult

  (** [dw#subtract i] returns dw(dw#value - i)] if [dw#value] is greater
      than or equal to [i], otherwise returns Error.*)
  method subtract_int: int -> 'a traceresult

  (** [dw#subtract_to_int other] returns [dw#value - other#value] if
      [other#value] is less than or equal to [self#value], [Error]
      otherwise.*)
  method subtract_to_int: 'a -> int traceresult

  (** [dw#add other] returns [dw#value + other#value] if the sum is less
      than [2^32], otherwise returns [dw#value + other#value mod 2^32].*)
  method add: 'a  -> 'a

  (** [dw#add i] returns [dw#value + i] if the sum is less than [2^32],
      otherwise returns [(dw#value + i) mod 2^32].*)
  method add_int: int -> 'a

  (** [dw#multiply_int i] returns [dw#value * i] if the product is less than
      [2^32], otherwise returns Error.*)
  method multiply_int: int -> 'a  traceresult

  (** [dw#xor other] returns the bitwise xor of [dw#value] and [other#value].*)
  method xor: 'a -> 'a

  (* accessors *)
  method get_low: int          (* integer value of low-order 16 bits *)
  method get_high: int         (* integer value of high-order 16 bits *)
  method get_bits_set: int list
  method get_bitval: int -> int    (* value of bit at position (zero-based) *)
  method get_reverse_bitval: int -> int -> int  (* reverse numbering *)
  method get_segval: int -> int -> int  (* value of subrange of bits, high, low *)
  method get_reverse_segval:   (* value of subrange with reverse numbering *)
           int -> int -> int -> int

  (* predicates *)
  method is_highest_bit_set: bool
  method is_nth_bit_set: int -> bool   (* raises Invalid_argument *)

  (* printing *)
  method toPretty: pretty_t
end


(** [doubleword_int] with possible error value.*)
type doubleword_result = doubleword_int traceresult


(** {2 Immediate value}*)

(** Constant value with explicit size in bytes and signedness.*)
class type immediate_int =
object ('a)

  (* comparison *)
  method equal:'a -> bool

  (* predicates *)

  (** Return true if the size-in-bytes is equal to four.*)
  method is_doubleword: bool

  (** Return true if the size-in-bytes is equal to eight.*)
  method is_quadword: bool

  (* converters *)
  method to_numerical: numerical_t

  (** Convert into a native integer. If conversion to a native integer fails,
      return None.*)
  method to_int: int option

  (** Convert into a doubleword if the size in bytes is less than or equal to
      four. Otherwise return None. The value of the immediate is sign-extended
      if signed and its size is less than two bytes; negative values are
      represented in two's complement.*)
  method to_doubleword: doubleword_int option

  (* transformers *)
  method to_unsigned: 'a

  (** [imm#sign_extend n] returns the signed extension of imm to length [n]
      in bytes if [n] is larger than or equal to the size-in-bytes of [imm]
      and if [n] is a supported size (1, 2, 4, 8). Otherwise [Error] is
      returned.*)
  method sign_extend: int -> 'a traceresult

  (* operations *)
  method shift_left: int -> 'a

  method arithmetic_shift_right: int -> 'a

  (* printing *)

  (** Return the value represented as a decimal string. *)
  method to_dec_string: string

  (** Return the value represented as a hexadecimal string. *)
  method to_hex_string: string

  (** Return the value as a decimal string if its absolute value is less than 10
      else as a hexadecimal string.*)
  method to_string: string

  (** Return the value as represented by to_string as a pretty_t object.*)
  method toPretty: pretty_t
end


(** [immediate_int] with possible error value.*)
type immediate_result = immediate_int traceresult


(** {2 Location} *)

type base_location_t = {
    loc_faddr: doubleword_int;
    loc_iaddr: doubleword_int;
  }


type fcontext_t = {
    ctxt_faddr: doubleword_int;
    ctxt_callsite: doubleword_int;
    ctxt_returnsite: doubleword_int
  }


type context_t =
  | FunctionContext of fcontext_t
  | BlockContext of doubleword_int
  | PathContext of string
  | ConditionContext of bool  (* conditional instrs turned into blocks *)


(** ctxt_iaddress_t spec:
   {[
   i  ( [], { faddr,iaddr } ) = iaddr
   i  ( [ F{ fa,cs,rs } ], { faddr,iaddr }) = iaddr
   i  ( [ B{ js } ], { faddr,iaddr }) = iaddr
   i  ( [ C{c}], {faddr, iaddr}) = iaddr

   f  ( [], { faddr,iaddr } ) = faddr
   f  ( [ F{ fa,cs,rs }, _ ],  { faddr,iaddr } ) = fa
   f  ( [ B{ js } ], { faddr,iaddr } ) = faddr
   f  ( B{ js }::ctxt , { faddr,iaddr } ) = f (ctxt, {faddr,iaddr})
   f  ( C{c}::ctxt, {faddr, iaddr}) = f(ctxt, {faddr, iaddr})

   ci ( [], { faddr,iaddr } ) = iaddr
   ci ( [ F{ fa,cs,rs } ], { faddr,iaddr } ) = F:cs_iaddr
   ci ( [ F{ fa1,cs1,rs1 },F{ fa2,cs2,rs2 } ], { faddr,iaddr } ) = F:cs1_F:cs2_iaddr
   ci ( [ B{ js } ], { faddr,iaddr }) = B:js_iaddr
   ci ( [ B{ js1 }, B{ js2 } ], { faddr,iaddr }) = B:js1_B:js2_iaddr
   ci ( [ C{true}], {faddr, iaddr}) = T_iaddr
   ci ( [ C{false}], {faddr, iaddr}) = F_iaddr
   ]}
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


(** {1 Data export spec}*)

type data_export_spec_item_t = {
  dex_offset : int;
  dex_name: string;
  dex_type: string;
  dex_size: int
}


type data_export_spec_t = {
  dex_description: string;
  dex_items: data_export_spec_item_t list
}


class type data_export_value_int =
object
  method set_values: (int * string) list -> unit
  method get_spec: data_export_spec_t
  method get_size: int                             (* number of bytes *)
  method get_values: (data_export_spec_item_t * string) list
  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end


(** {1 C-related types} *)

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


(** Definition used for user-defined named addresses and constants.*)
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


(** {1 JNI-related types}*)

class type class_name_int =
object ('a)
  method index: int
  method name: string
  method simple_name: string
  method equal: 'a -> bool
  method compare: 'a -> int
  method package: string list
  method package_name: string
  method toPretty: pretty_t
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
  method name: string
  method descriptor: value_type_t
  method compare: 'a -> int
  method to_string: string
  method toPretty: pretty_t
end


class type field_signature_int =
object ('a)
  method index: int
  method name: string
  method field_signature_data: field_signature_data_int
  method descriptor: value_type_t
  method equal: 'a -> bool
  method compare: 'a -> int
  method to_string: string
  method toPretty: pretty_t
end


class type method_descriptor_int =
object ('a)
  method arguments: value_type_t list
  method return_value: value_type_t option
  method compare: 'a -> int
  method to_string: string
  method toPretty: pretty_t
end


class type method_signature_data_int =
object ('a)
  method name: string
  method descriptor: method_descriptor_int
  method compare: 'a -> int
  method to_string: string
  method toPretty: pretty_t
end


class type method_signature_int =
object ('a)
  method index: int
  method method_signature_data: method_signature_data_int
  method name: string
  method descriptor: method_descriptor_int
  method equal: 'a -> bool
  method compare: 'a -> int
  method to_string: string
  method toPretty: pretty_t
end


type java_native_method_api_t =
  { jnm_signature: method_signature_int;
    jnm_access: access_t;
    jnm_static: bool
  }


class type java_dictionary_int =
object
  method make_class_name: string -> class_name_int
  method make_field_signature: string -> value_type_t -> field_signature_int
  method make_method_signature: string -> method_descriptor_int -> method_signature_int
end


type java_native_method_class_t =
{ jnmc_class: class_name_int ;
  jnmc_native_methods: java_native_method_api_t list
}


class type java_method_name_int =
object
  (* setters *)
  method set_class_name:string -> unit
  method set_method_name:string -> unit
  method add_argument_type: value_type_t -> unit

  (* accessors *)
  method get_class_name: string
  method get_method_name: string
  method get_arguments: value_type_t list

  (* predicates *)
  method has_arguments: bool

  (* printing *)
  method toPretty: pretty_t
end


(** {1 CHIF types} *)

type variable_comparator_t = variable_t -> variable_t -> int

type cmd_t = (code_int, cfg_int) command_t


class type cmd_list_int =
object
  method cmd_list : cmd_t list
  method reverse_cmds: unit
  method toPretty: pretty_t
end


(** {2 Code graph} *)

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


(** {1 Architecture-specific types} *)

(** {2 X86 types} *)

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
| StackSegment   (** 2 *)
| CodeSegment    (** 1 *)
| DataSegment    (** 3 *)
| ExtraSegment   (** 0 *)
| FSegment       (** 4 *)
| GSegment       (** 5 *)


(** {2 MIPS types} *)

type mips_reg_t =
  | MRzero    (**  0: constant zero, ignored as destination *)
  | MRat      (**  1: reserved for assembler *)
  | MRv0      (**  2: function return value *)
  | MRv1      (**  3: function return value *)
  | MRa0      (**  4: argument 1 *)
  | MRa1      (**  5: argument 2 *)
  | MRa2      (**  6: argument 3 *)
  | MRa3      (**  7: argument 4 *)
  | MRt0      (**  8: temporary *)
  | MRt1      (**  9: temporary *)
  | MRt2      (** 10: temporary *)
  | MRt3      (** 11: temporary *)
  | MRt4      (** 12: temporary *)
  | MRt5      (** 13: temporary *)
  | MRt6      (** 14: temporary *)
  | MRt7      (** 15: temporary *)
  | MRs0      (** 16: saved temporary *)
  | MRs1      (** 17: saved temporary *)
  | MRs2      (** 18: saved temporary *)
  | MRs3      (** 19: saved temporary *)
  | MRs4      (** 20: saved temporary *)
  | MRs5      (** 21: saved temporary *)
  | MRs6      (** 22: saved temporary *)
  | MRs7      (** 23: saved temporary *)
  | MRt8      (** 24: temporary *)
  | MRt9      (** 25: temporary *)
  | MRk0      (** 26: reserved for OS kernel *)
  | MRk1      (** 27: reserved for OS kernel *)
  | MRgp      (** 28: pointer to global area *)
  | MRsp      (** 29: stack pointer *)
  | MRfp      (** 30: frame pointer, or saved temporary *)
  | MRra      (** 31: return address *)


type mips_special_reg_t =
  | MMHi   (** high multiplication unit register *)
  | MMLo   (** low multiplication unit register *)


(** {2 ARM types} *)

type arm_cc_flag_t =
  | APSR_Z    (** zero condition flag. Set to 1 if the result of the instruction
                 is zero, and to 0 otherwise.*)
  | APSR_N    (** negative condition flag. Set to bit[31] of the result of the
                 instruction. If the result is regarded as a twos' complement
                 signed integer, then the processor sets N to 1 if the result is
                 negative, and sets N to 0 if it is positive or zero.*)
  | APSR_C    (** carry condition flag. Set to 1 if the instruction results in a
                 carry condition, for example an unsigned overflow on an
                 addition.*)
  | APSR_V    (** overflow condition flag. Set to 1 if the instruction results in
                 an overflow condition, for example a signed overflow on an
                 addition.*)
  | APSR_Q    (** overflow or saturation flag. Set to 1 to indicate overflow or
                 saturation occurred in some instructions, normally related to
                 DSP.*)

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
  | CPSR   (** Core processor status word *)
  | SPSR   (** Saved Program Status Registers *)
  | FPSCR   (** Floating point processor status word *)
  | APSR_nzcv  (** Condition codes in core processor status word *)


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


(** {2 Power32 types} *)

type pwr_special_reg_t =
  | PowerCR    (** Condition Register (contain CR0, CR1, CR2) *)
  | PowerCTR   (** Count Register *)
  | PowerMSR   (** Machine Status Register *)
  | PowerLR    (** Link Register *)
  | PowerXER   (** Integer Exception Register *)
  | PowerSRR0  (** Save/Restore Register 0 *)
  | PowerSRR1  (** Save/Restore Register 1 *)
  | PowerCSRR0 (** Critical Save/Restore Register 0 *)
  | PowerCSRR1 (** Critical Save/Restore Register 1 *)
  | PowerDSRR0 (** Debug Save/Restore Register 0 *)
  | PowerDSRR1 (** Debug Save/Restore Register 1 *)
  | PowerMCSRR0 (** Machine Check Save/Restore Register 0 *)
  | PowerMCSRR1 (** Machine Check Save/Restore Register 1 *)


type pwr_register_field_t =
  | PowerCR0   (** Condition Register, bits 32-35 *)
  | PowerCR1   (** Condition Register, bits 36-39 *)
  | PowerCR2   (** Condition Register, bits 40-43 *)
  | PowerCR3   (** Condition Register, bits 44-47 *)
  | PowerCR4   (** Condition Register, bits 48-51 *)
  | PowerCR5   (** Condition Register, bits 52-55 *)
  | PowerCR6   (** Condition Register, bits 56-59 *)
  | PowerCR7   (** Condition Register, bits 60-63 *)
  | PowerXERSO (** Integer Exception Register, summary overflow *)
  | PowerXEROV (** Integer Exception Register, overflow *)
  | PowerXERCA (** Integer Exception Register, carry *)


(** {2 Combining architecture registers} *)

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
| ARMDoubleRegister of arm_reg_t * arm_reg_t
| ARMSpecialRegister of arm_special_reg_t
| ARMExtensionRegister of arm_extension_register_t
| ARMDoubleExtensionRegister of
    arm_extension_register_t * arm_extension_register_t
| ARMExtensionRegisterElement of arm_extension_register_element_t
| ARMExtensionRegisterReplicatedElement of
    arm_extension_register_replicated_element_t
| PowerGPRegister of int
| PowerSPRegister of pwr_special_reg_t
| PowerCRField of pwr_register_field_t


type flag_t =
  | X86Flag of eflag_t
  | ARMCCFlag of arm_cc_flag_t


(** {2 Dictionary} *)

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
    method index_flag: flag_t -> int

    method get_string: int -> string
    method get_address: int -> doubleword_int
    method get_address_string: int -> string
    method get_arm_extension_register: int -> arm_extension_register_t
    method get_arm_extension_register_element:
             int -> arm_extension_register_element_t
    method get_arm_extension_register_replicated_element:
             int -> arm_extension_register_replicated_element_t
    method get_register: int -> register_t
    method get_flag: int -> flag_t

    method write_xml_register: ?tag:string -> xml_element_int -> register_t -> unit
    method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
    method read_xml_register: ?tag:string -> xml_element_int -> register_t
    method read_xml_string: ?tag:string -> xml_element_int -> string

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


(** {1 Binary I/O} *)

(** Wrapper for reading different types of data from file.*)
class type virtual stream_wrapper_int =
object

  method read: char
  method nread: int -> string
  method really_nread: int -> string
  method input: string -> int -> int -> int
  method close_in: unit

  method read_byte: int
  method read_signed_byte: int
  method virtual read_ui16: int
  method virtual read_i16: int
  method virtual read_i32: int
  method virtual read_real_i32: int32
  method virtual read_i64: int64
  method virtual read_double: float
  method read_string: string
  method read_line: string

  method virtual read_doubleword: doubleword_int
end


(** Principal class for reading in executables.*)
class type pushback_stream_int =
object
  method skip_bytes: int -> unit
  method read: char
  method nread: int -> string
  method really_nread: int -> string

  method read_byte: int
  method read_signed_byte: int
  method read_ui16: int
  method read_i16: int
  method read_i32: int
  method read_real_i32: int32
  method read_i64: int64
  method read_string: string

  method read_doubleword: doubleword_int

  method read_num_signed_byte: numerical_t
  method read_num_unsigned_byte: numerical_t
  method read_num_signed_word: numerical_t
  method read_num_signed_doubleword: numerical_t

  method read_imm_signed_byte: immediate_int
  method read_imm_signed_word: immediate_int
  method read_imm_signed_doubleword: immediate_int
  method read_imm_signed: int -> immediate_int

  method read_imm_unsigned_byte: immediate_int
  method read_imm_unsigned_word: immediate_int
  method read_imm_unsigned_doubleword: immediate_int
  method read_imm_unsigned: int -> immediate_int

  (** Return the decoded value of the unsigned DWARF Little Endian Base 128
      (LEB128) variable length data encoded value *)
  method read_dwarf_leb128: int

  (** Return the decoded value of the signed DWARF Little Endian Base 128
      (LEB128) variable length data encoded value *)
  method read_dwarf_sleb128: int -> int

  method read_null_terminated_string: string
  method read_sized_unicode_string: string

  method pushback: int -> unit

  (* accessors *)
  method pos: int
  method sub: int -> int -> string
end


(** {1 Data blocks and tables} *)

(** {2 Data block}*)

(** Represents a fragment of a code section that holds data rather than code.

    The object is mutable; only the start address is fixed; the end address
    can be changed (with the [truncate] method), as well as the name and data
    string.*)
class type data_block_int =
object ('a)
  method compare: 'a -> int

  (* setters *)
  method set_data_string: string -> unit
  method set_name: string -> unit
  method set_data_table: (string * string) list -> unit

  (** [truncate eaddr] truncates this data block such that it has end-address
      [eaddr].

      Primarily used to ensure that a data block does not cross a section
      boundary.*)
  method truncate: doubleword_int -> unit

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

(** {2 Jump table} *)

(** A jumptable generally represents a switch statement. Its external
    API exposes its extent (that is, the non-code data items that make up
    the table), and a list of target addresses together with the index value
    that activates that target.

    Internally the data of a jump table may be the list of target addresses
    itself, or it may be a list of 1- (or 2-byte) offsets that are added
    to a base address.
*)
class type jumptable_int =
object

  (** The start address can be invalidated; sometimes automatic detection
      identifies the jump instruction as part of the table (this can happed
      especially in x86.*)
  method invalidate_startaddress: unit

  (** Returns the address of the first non-code location in the code, or
      the start address of the table in another read-only section.*)
  method get_start_address: doubleword_int

  (** Returns the address of the first code location after the jump table.*)
  method get_end_address: doubleword_int

  (** Returns the length (in bytes) of the entire table (equal to the
      difference between the end address and the start address.*)
  method get_length: int

  (** Returns a list of all (unique) target addresses (de-duplicated).*)
  method get_all_targets: doubleword_int list

  (** [get_targets base lb ub] returns the list of targets are invoked
      with an index value between lowerbound [lb] and upperbound [ub]
      from base address [base]. (deprecated).*)
  method get_targets: doubleword_int -> int -> int -> doubleword_int list

  (** Returns a list of (target-address, index list) pairs where the indexes
      denote the values with which the corresponding target address is
      associated.

      Note. This is currently only supported by the ARM architecture.
      For all other architectures, the empty list is returned.

      Eventually this method will supercede [get_indexed_targets].
   *)
  method indexed_targets: (doubleword_int * int list) list

  (** [get_indexed_targets base lb ub] returns the list of targets with
      their index for index values between lowerbound [lb] and
      upperbound [ub] from base address [base]. (deprecated) *)
  method get_indexed_targets:
           doubleword_int -> int -> int -> (int * doubleword_int) list

  (** [includes_address addr] returns true if [addr] is the address
      of a location that holds a target address.

      Note that this applies only if the jumptable actually contains a
      list of addresses, which may not be the case.*)
  method includes_address: doubleword_int -> bool

  (* saving *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty:
           is_function_entry_point:(doubleword_int -> bool)
           -> get_opt_function_name:(doubleword_int -> string option)
           -> pretty_t
  method toString:
           is_function_entry_point:(doubleword_int -> bool)
           -> get_opt_function_name:(doubleword_int -> string option)
           -> string

end

(** {2 Struct tables}*)

(* Note: call-back-tables can be considered a subset of struct_tables; we
 * keep them separate for now, as they serve different purposes. *)

type struct_table_value_t =
  | STVStringAddress of string  (* char * *)
  | STVString of string         (* char[n] *)
  | STVNum of numerical_t


class type struct_table_record_int =
  object
    (* getters *)
    method address: string
    method values: (int * struct_table_value_t) list
    method stringvalue: int -> string
    method intvalue: int -> numerical_t

    (* saving *)
    method write_xml: xml_element_int -> unit

    (* printing *)
    method toPretty: pretty_t
  end


class type struct_table_int =
  object

    (* setters *)
    method add_record:
             string
             -> (int * struct_table_value_t) list
             -> unit

    (* getters *)
    method address: string
    method length: int (* number of records *)
    method record_type: btype_t
    method type_at_offset: int -> btype_t
    method fieldname_at_offset: int -> string
    method field_offset_types: (int * btype_t) list
    method record_length: int  (* number of fields in struct *)

    (* saving *)
    method write_xml: xml_element_int -> unit

  end


class type struct_tables_int =
  object

    (* setters *)
    method new_table: string -> btype_t -> struct_table_int
    method add_table_address: string -> string -> int -> unit
    (* getters *)
    method table_variables: (string * (string * int)) list   (* address, name *)
    method get_table: string -> struct_table_int

    (* predicates *)
    method has_table: string -> bool

    (* saving *)
    method write_xml: xml_element_int -> unit

  end


(** {2 Call-back tables}

    Call-back tables are arrays of structs in memory that hold function pointers
    that are selected as targets for indirect calls based on a string value
    (e.g., a submit flag in an HTML post request).

    Currently these call-back tables are constructed from the following
    information:
    - a global variable in a loaded c file, defined as a pointer to a struct;
    - a call-back-tables entry in the (json) userdata that associates the
       name with an address

    Example c definition:
    {[
    struct _cbt_cgi_setobject {
      char *tag;
      int num;
      int ( *cbp_cgi_setobject)(struct keyvaluepair_t *kvp, int len);
    } cbt_cgi_setobject;

    struct _cbt_cgi_setobject *cgi_setobject_table;
    ]}

    and associated userdata (in json):
    {[
	"call-back-tables": {
	   "0x4a5c30": "cgi_setobject_table"
	}
    ]}

    The call-back table addresses provided by the user-data are read in by
    the system_info and set in the global structure callbacktables. The
    global variable definition provided by the c-file is saved in the global
    bcfiles structure.

    Call-back table addresses are retrieved by the ELF header and matched
    (by name) with their corresponding global variable definitions, which
    provides the struct type. For each global variable a new call-back table
    is created and its struct type is used to extract the individual records
    from the array (assumed to be terminated by a null record) and added to
    the call-back table.

    The connection with the indirect call that uses a particular call-back
    table is made via another entry in the userdata, in the call-targets
    section, which identifies both the base of the call-back table and the
    particular field-offset in the struct that provides the function pointer.

    For example:
    {[
	"call-targets": [
	   {"ia": "0x40d5dc",
	    "fa": "0x40d510",
	    "tgts": [{"cba": "0x4a5c30:8"}]
	   }
         ]
    ]}
    identifies the location of the indirect call instruction by its
    instruction address (ia) in function (fa), and indicates that the
    targets to be used are available in the call-back table with base
    address 0x4a5c30, where the function pointer is located at offset 8.
    The offset of the function pointer is indicated as call-back tables
    may have multiple fields with function pointers, to be used by
    different instructions.
*)

(** Types of fields in a a call-back table. *)
type call_back_table_value_t =
  | CBAddress of string (** address, typically of a function pointer *)
  | CBTag of string   (** constant string *)
  | CBValue of numerical_t   (** constant numerical value *)


(** A single record (struct instance) in a call-back table.*)
class type call_back_table_record_int =
  object

    (** Returns the address in memory of this record (in hexadecimal).*)
    method address: string

    (** Returns the a list of (offset, field-value) pairs.*)
    method values: (int * call_back_table_value_t) list

    (** [cbtr#stringvalue n] returns the string value ([CBTag]) at offset [n].

    @raise BCH_failure if the field at offset [n] is not a [CBTag] value.*)
    method stringvalue: int -> string

    (** [cbtr#intvalue n] returns the numerical value ([CBValue]) at offset [n].

    @raise BCH_failure if the field at offset [n] is not a [CBValue] value.*)
    method intvalue: int -> numerical_t

    (** [cbtr#addrvalue n] returns the address value ([CBAddress]) at offset [n].

    @raise BCH_failure if the field at offset [n] is not a [CBAddress] value.*)
    method addrvalue: int -> string   (* address at offset *)

    (** [cbtr#write_xml xnode] writes the field values and offset to [xnode].*)
    method write_xml: xml_element_int -> unit

    method toPretty: pretty_t

  end


(** Array of call-back table records identified by a single global variable
    (base address).*)
class type call_back_table_int =
  object

    (** [cbt#add_record addr values] adds a new record to the array with
        record address [addr] and field values [values].*)
    method add_record:
             string
             -> (int * call_back_table_value_t) list
             -> unit

    (** Returns the base address of the call-back table.*)
    method address: string

    (** Returns the number of records in the table (array).*)
    method length: int

    (** Returns the struct type of the records.*)
    method record_type: btype_t

    (** [cbt#type_at_offset n] returns the type of the field at offset [n].

    @raise BCH_failure if there is no field at offset [n].*)
    method type_at_offset: int -> btype_t

    (** [cbt#fieldname_at_offset n] returns the name of the field at offset [n].

    @raise BCH_failure if there is no field at offset [n].*)
    method fieldname_at_offset: int -> string

    (** Returns a list of field-offset, field-type pairs containing all fields.*)
    method field_offset_types: (int * btype_t) list

    (** Returns the number of fields in a record.*)
    method record_length: int

    (** Returns the a list (field-name, field-type pairs containing all fields
        that are function pointers.*)
    method function_pointer_values: (string * btype_t) list

    (** [cbt#write_xml xnode] writes and xml representation of the records of
        this table to [xnode].*)
    method write_xml: xml_element_int -> unit

  end


(** Global data structure that provides access to all call-back tables.*)
class type call_back_tables_int =
  object

    (** [cbts#new_table addr type] returns a new (empty) call-back table with
        base address [addr] (in hexadecimal) and struct (record) type [type]
        and registers the table by address.*)
    method new_table: string -> btype_t -> call_back_table_int

    (** [cbts#add_table_address addr vname] associates the address of a table
        with global variable name [vname].*)
    method add_table_address: string -> string -> unit

    (** Collects the function pointers from all tables and registers the
        addresses as function entry points, and sets the function signatures.*)
    method set_function_pointers: unit

    (** Returns a list of all table base addresses as a list of pairs
        (address, name of global variable).*)
    method table_variables: (string * string) list

    (** [cbts#get_table addr] returns the call-back table with base address
        [addr].

    @raise BCH_failure if no call-back table is present at [addr].*)
    method get_table: string -> call_back_table_int

    (** [cbts#has_table addr] returns true if there is a call-back table with
        base address [addr].*)
    method has_table: string -> bool

    (** [cbts#write_xml xnode] writes an xml representation of all tables to
        xml node [xnode].*)
    method write_xml: xml_element_int -> unit

  end


(** {2 String table} *)

class type string_table_int =
object
  (* setters *)
  method add_string: doubleword_int -> string -> unit
  method add_xref    :
           doubleword_int -> string -> doubleword_int -> ctxt_iaddress_t -> unit

  (* accessors *)
  method get_string: doubleword_int -> string
  method get_strings: (doubleword_int * string) list

  (* predicates *)
  method has_string: doubleword_int -> bool

  (* saving *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

end


(** {1 System-wide data} *)

class type system_settings_int =
object
  (* setters *)
  method set_architecture: string -> unit
  method set_fileformat: string -> unit
  method set_summary_jar: string -> unit
  method add_so_library: string -> unit    (* name of so-library *)
  method set_jsignature_jar: string -> unit
  method set_verbose: unit
  method set_ssa: unit
  method set_collect_data: unit
  method set_show_function_timing: unit
  method set_gc_compact_function_interval: int -> unit
  method set_lineq_instr_cutoff: int -> unit
  method set_lineq_block_cutoff: int -> unit
  method set_vftables: unit
  method set_thumb: unit
  method set_arm_extension_registers: unit
  method enable_sideeffects_on_globals : string list -> unit
  method disable_sideeffects_on_globals: string list -> unit
  method set_no_varinvs: unit
  method set_abstract_stackvars_disabled: unit
  method set_apps_dir: string -> unit
  method set_app_summary_jars: string -> unit   (* application name *)
  method set_export_dir: string -> unit
  method exclude_debug: unit

  (* accessors *)
  method get_architecture: string
  method get_instruction_alignment: int
  method get_fileformat: string
  method get_summary_paths: (string * Zip.in_file) list
  method get_jsignature_paths: (string * Zip.in_file) list
  method get_export_dir: string
  method so_libraries: string list  (* names of so-libraries *)
  method gc_compact_function_interval: int
  method get_lineq_instr_cutoff: int
  method get_lineq_block_cutoff: int

  (* predicates *)
  method is_arm: bool
  method is_mips: bool
  method is_power: bool
  method is_x86: bool
  method is_elf: bool
  method is_pe: bool
  method is_verbose: bool
  method is_debug_excluded: bool
  method is_sideeffects_on_global_enabled: string -> bool
  method is_abstract_stackvars_disabled: bool
  method is_set_vftables_enabled: bool
  method has_thumb: bool
  method use_ssa: bool
  method collect_data: bool
  method generate_varinvs: bool
  method include_arm_extension_registers: bool
  method show_function_timing: bool
  method is_lineq_restricted: blocks:int -> instrs:int -> bool

end


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


class type user_provided_directions_int =
object
  (* setters *)
  method load_dll_ordinal_mappings: string -> unit
  method set_dll_ordinal_mappings: string -> (int * string) list -> unit

  (* getters *)
  method get_dll_ordinal_mapping: string -> int -> string

  (* predicates *)
  method are_DS_and_ES_the_same_segment: bool

  (* xml *)
  method write_xml_ordinal_table: xml_element_int -> string -> unit
end


(** {1 Function data} *)


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

    (** [add_path_context startaddr sentinels] causes path contexts to
        be created for all successors of the basic block at [startaddr],
        potentially ended by one of the basic block addresses in [sentinels]. *)
    method add_path_context: string -> string list -> unit

    (** Increments the number of call sites associated with this function. *)
    method add_callsite: unit

    (** Decrements the number of call sites associated with this function;
        returns the number of remaining call sites.*)
    method remove_callsite: int

    (* accessors *)
    method get_names: string list  (* raw names *)
    method get_function_name: string  (* demangled or combination of all names *)
    method get_inlined_blocks: doubleword_int list
    method get_function_type: btype_t
    method get_path_contexts: (string * string list) list

    (* predicates *)
    method has_function_type: bool
    method has_name: bool
    method has_class_info: bool
    method has_callsites: bool
    method has_path_contexts: bool
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
    method remove_function: doubleword_int -> unit

    (* accessors *)
    method get_functions: function_data_int list
    method get_function_entry_points: doubleword_int list
    method get_inlined_function_entry_points: doubleword_int list
    method get_library_stubs: doubleword_int list
    method get_function: doubleword_int -> function_data_int
    method get_ida_provided_functions: function_data_int list
    method get_ida_provided_function_entry_points: doubleword_int list

    (* predicates *)
    method is_function_entry_point: doubleword_int -> bool
    method is_in_function_stub: ?size:int -> doubleword_int -> bool
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


(** {1 Invariants}*)

(** {2 Variable invariants}

    Variable invariants are symbolic invariants including:
    - reaching definitions
    - flag reaching definitions (for architectures with processor flags)
    - def-use relationships
    - def-use-high relationships

    The reaching definitions are the traditional relationships between a
    variable use and all locations where that variable may have been defined.

    The def-use relationships are the traditional relationships between
    a variable definition and all locations where that variable may be used.

    The def-use-high relationships are similar to the def-use relationships,
    but are only computed for variables that would appear in a source-code
    lifting.

    The reaching definitions are computed directly by forward abstract
    interpretation in a symbolic domain with the hooks embedded in the same
    CHIF representation that is used for the regular (value) invariant
    generation.

    The def-use and def-use-high relationships (normally computed by backward
    analysis) are instead derived directly from the reaching definitions by
    recording the uses (and high-uses) in the functioninfo and using these to
    filter out the reverse relationships of the reaching definitions.
*)

(** Pairing of a variable with a set of locations represented by symbols.*)
type vardefuse_t = variable_t * symbol_t list


(** Variable invariant fact *)
type var_invariant_fact_t =
  | ReachingDef of vardefuse_t  (** reaching definitions of a variable *)
  | FlagReachingDef of vardefuse_t  (** reaching definitions of a flag variable *)
  | DefUse of vardefuse_t
  (** list of locations where a variable definition is used *)
  | DefUseHigh of vardefuse_t
  (** list of locations where a high-level variable is used *)


(** Single variable invariant at a particular location (immutable).*)
class type var_invariant_int =
  object ('a)
    method index: int
    method compare: 'a -> int

    (* accessors *)
    method get_fact: var_invariant_fact_t
    method get_variable: variable_t
    method get_reaching_defs: symbol_t list
    method get_def_uses: symbol_t list

    (* predicates *)
    method is_reaching_def: bool
    method is_flag_reaching_def: bool
    method is_def_use: bool
    method is_def_use_high: bool
    method has_multiple_reaching_defs: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


(** All variable invariants at a particular location.

    Mutable class that collects variable invariants at a particular location
    (instruction address) in the code. Reaching defs are added as complete
    facts, def-use facts are constructed one use-location at the time, as they
    are retrieved from the reaching def facts. The collect_use_facts method
    is called to package up these def-use facts when all reaching defs have
    been processed.
*)
class type location_var_invariant_int =
  object
    method reset: unit
    method add_fact: var_invariant_fact_t -> unit
    method add_use_loc: variable_t -> string -> unit
    method add_use_high_loc: variable_t -> string -> unit
    method collect_use_facts: unit

    (* accessors *)
    method get_var_facts: variable_t -> var_invariant_int list
    method get_var_reaching_defs: variable_t -> var_invariant_int list
    method get_var_flag_reaching_defs: variable_t -> var_invariant_int list
    method get_var_def_uses: variable_t -> var_invariant_int list
    method get_var_def_uses_high: variable_t -> var_invariant_int list
    method get_facts: var_invariant_int list
    method get_count: int

    (* predicates *)
    method has_facts: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


(** Access structure for all variable invariants for a single function.*)
class type var_invariant_io_int =
  object
    method add_reaching_def: string -> variable_t -> symbol_t list  -> unit
    method add_flag_reaching_def: string -> variable_t -> symbol_t list -> unit
    method add_def_use: string -> variable_t -> symbol_t list -> unit
    method add_def_use_high: string -> variable_t -> symbol_t list -> unit

    method add_use_loc: string -> variable_t -> string -> unit
    method add_use_high_loc: string -> variable_t -> string -> unit
    method collect_use_facts: unit

    (* accessors *)
    method get_location_var_invariant: string -> location_var_invariant_int
    method get_multiple_reaching_defs: (string * var_invariant_int) list

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
    method toPretty: pretty_t

  end


(** Variable invariant dictionary.*)
class type varinvdictionary_int =
  object

    method xd: xprdictionary_int
    method index_var_def_use: vardefuse_t -> int
    method index_var_invariant_fact: var_invariant_fact_t -> int

    method get_var_def_use: int -> vardefuse_t
    method get_var_invariant_fact: int -> var_invariant_fact_t

    method write_xml_var_invariant_fact:
             ?tag:string -> xml_element_int -> var_invariant_fact_t -> unit
    method read_xml_var_invariant_fact:
             ?tag:string -> xml_element_int -> var_invariant_fact_t

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t

  end


(** {2 Value invariants} *)

(** Non-relational value (symbolic or numerical constant *)
type non_relational_value_t =
| FSymbolicExpr of xpr_t
| FIntervalValue of numerical_t option * numerical_t option
| FBaseOffsetValue of symbol_t * numerical_t option * numerical_t option * bool


(** Linear equality: [c1 f1 + c2 f2 .... + cn fn = constant] *)
type linear_equality_t = {
    leq_factors: (numerical_t * variable_t) list; (** (coefficient, variable) list*)
    leq_constant: numerical_t  (** constant *)
}


(** Value invariant fact.*)
type invariant_fact_t =
  | Unreachable of string  (** name of domain that signals unreachability *)
  | NonRelationalFact of variable_t * non_relational_value_t
  (** variable equals non-relational-value *)
  | RelationalFact of linear_equality_t
  | InitialVarEquality of variable_t * variable_t
  (** variable, initial value: variable is equal to its initial value at
      function entry *)
  | InitialVarDisEquality of variable_t * variable_t
  (** variable, initial value: variable may not be equal to its initial value*)
  | TestVarEquality of variable_t * variable_t * ctxt_iaddress_t * ctxt_iaddress_t
  (** variable, test value:  *)


(** Single value invariant at a particular location.*)
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


(** All value invariants at a particular location.*)
class type location_invariant_int =
object

  (* setters *)
  method reset: unit
  method add_fact: invariant_fact_t -> unit
  method remove_initial_value_fact: variable_t -> variable_t -> unit
  method get_facts: invariant_int list
  method get_count: int

  (* accessors *)
  method get_constant: variable_t -> numerical_t
  method get_interval: variable_t -> interval_t
  method get_base_offset: variable_t -> symbol_t * interval_t
  method get_base_offset_constant: variable_t -> symbol_t * numerical_t
  method get_affine_offset: variable_t -> variable_t -> numerical_t option
  method get_interval_offset: variable_t -> variable_t -> interval_t
  method get_external_exprs: variable_t -> xpr_t list
  method get_known_variables: variable_t list
  method get_known_initial_values: variable_t list
  method get_init_disequalities: variable_t list (* initial values *)
  method get_init_equalities: variable_t list (* initial values *)
  method rewrite_expr: xpr_t ->  xpr_t

  (* predicates *)
  method is_unreachable: bool
  method is_constant: variable_t -> bool
  method is_interval: variable_t -> bool
  method is_base_offset: variable_t -> bool
  method is_base_offset_constant: variable_t -> bool
  method are_equal: variable_t -> variable_t -> bool

  method test_var_is_equal:
           variable_t -> ctxt_iaddress_t -> ctxt_iaddress_t -> bool
  method var_has_initial_value: variable_t -> bool
  method var_has_symbolic_expr: variable_t -> bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
  method toPrettyVar : (variable_t -> string) option -> pretty_t
end


(** Access structure for all value invariants for a single function.*)
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

  (* add/remove special-purpose facts *)
  method add_initial_value_fact: string -> variable_t -> variable_t -> unit
  method remove_initial_value_fact: string -> variable_t -> variable_t -> unit
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


(** Value invariant dictionary *)
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
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end



(** {1 Function summaries}*)

(** {2 Function signatures} *)

(** Location of a parameter of the function.

   The {b stack parameter} location indicates the location of the argument
   relative to the return address, in number of bytes offset.

   All function summaries assume a standard cdecl x86-based function api.
   Hence all function summaries represent parameters as stack-based. For
   architectures that use argument registers (like ARM and MIPS), these
   are converted at a later stage into the appropriate argument registers.
   This applies to both library function summaries and application function
   summaries that are constructed from preconditions.

   The {b global parameter} location indicates the address of a global
   variable that is accessed and/or modified by the function. This is not
   a true parameter of the function in the usual sense, but including it
   as a pseudo parameter allows the recording of the effects on the global
   variable in the function summary, e.g., in preconditions or postconditions.

   The size of the argument defaults to 4 bytes.

   The parameter_location_detail_t data structure provides additional
   information when a parameter is distributed over multiple registers,
   or when multiple parameters (or fields or array elements) are packed
   into a single register (i.e., a kind of serialization of a nested
   data structure over a linear list of locations).
   The pld_extract field is used to select a subset of the bytes of a
   location (0-based starting point, number of bytes) used when multiple
   distinct data entities (with their own type) are packed into a single
   location.
   The pld_position field is a list of positions that record the position
   of the data in this location in the (potentially nested) data structure
   type of the parameter to which it belongs.
 *)

type pld_position_t =
  | FieldPosition of int * int * string  (* ckey, field offset, field name *)
  | ArrayPosition of int   (* array element index (o-based) *)


type parameter_location_detail_t = {
    pld_type: btype_t;
    pld_size: int;
    pld_extract:
      (int * int) option;  (* starting byte (0-based), number of bytes *)
    pld_position: pld_position_t list
  }

type parameter_location_t =
  | StackParameter of int * parameter_location_detail_t
  (** [StackParameter(offset, _)] indicates the stack parameter that
      starts at [offset] bytes above the stackpointer at function
      entry.*)

  | RegisterParameter of register_t * parameter_location_detail_t
  | GlobalParameter of doubleword_int * parameter_location_detail_t
  | UnknownParameterLocation of parameter_location_detail_t


(** Type of format string for extracting format modifiers.*)
type formatstring_type_t =
  | NoFormat
  | PrintFormat
  | ScanFormat


(** Mode of access for a parameter.*)
type arg_io_t =
| ArgRead
| ArgReadWrite
| ArgWrite


(** Function type signature parameter.

   A parameter has the following annotation attributes:
   - desc: free form description of the parameter
   - roles: a list of (roletype, rolename) pairs that indicate the role of the
     parameter under different circumstances (primarily used in malware
     analysis; ioc stands for indicator-of-compromise)
     {[
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
      ]}
      the last two will change the representation of the values into a symbolic
      name, or list of names
   -  io : "r", "w", or "rw", depending on whether the argument provided
        is input, output or both

   Note: The api has an additional attribute for the role of the return value
   - rv-roles: a list of pairs that indicate the role of the return value
               under different circumstances,
     {[
               e.g. (ioc:filesystem, filename)
                    (ioc:network, protocol)
                    (jni, object)
     ]}
*)
type fts_parameter_t = {
    apar_index: int option;  (* 1-based parameter index, may be unknown *)
    apar_name: string;
    apar_type: btype_t;
    apar_desc: string;
    apar_roles: (string * string) list;
    apar_io: arg_io_t;
    apar_size: int;
    apar_location: parameter_location_t list;
    apar_fmt: formatstring_type_t
  }


(** Arithmetic operator used in expressions over api terms.*)
type arithmetic_op_t =
  PPlus | PMinus | PDivide | PTimes


(** Relational operator used in expressions over api terms.*)
type relational_op_t =
  PEquals | PLessThan | PLessEqual | PGreaterThan | PGreaterEqual | PNotEqual


(** Function signature

    A function signature is either directly obtained from a header file
    or function summary library (direct source perspective), or inferred
    from a list of parameter locations that are discovered during the
    analysis (inferred binary perspective).
.*)
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


(** Function interface.

    A function interface contains both a binary and a source perspective.
    The source perspective is represented by the type_signature, while the
    binary perspective is represented by the parameter_location list,
    which refer to registers, stack locations (and perhaps globals). It
    depends on the situation which perspective is known first.

    If a function signature is provided via a header file, or obtained from
    a function summary library, the type_signature
    is constructed from this type, and the type itself is kept in the bctype
    field. This is the only case where the function_interface has a bctype
    field. The fts_parameters in the type_signature are constructed with the
    default locations for the architecture, according to the ABI. Note that
    there may be some uncertainty, e.g., parameters may be packed, or parameter
    allocation may depend on the presence of floating point registers (ARM).
    The list of parameter locations is not populated during this construction.

    If no function signature is provided a priori, it can be inferred from
    references to initial values of argument registers and/or stack argument
    locations. In this case these locations are collected in the
    parameter_locations field. Only when a type signature
    is needed, a type_signature (possibly incomplete) is constructed based
    on these locations. Note that a type_signature often cannot be
    constructed on the fly, because there is no direct relationship between
    parameter locations and an ordered list of parameters.

    Even if the function signature is provided via a header or summary library,
    parameter locations are still collected in the parameter_locations field
    during analysis. These may be compared with those in the fts_parameters
    for consistency.

    A function interface is included in the call-target-infos stored in the
    function infos. To ensure that this function interface reflects the most
    recent analysis results, if inferred, each disassembler calls the
    floc#update_call_target directly after function construction.
*)
type function_interface_t = {
    fintf_name: string;
    fintf_jni_index: int option;
    fintf_syscall_index: int option;
    fintf_type_signature: function_signature_t;
    fintf_parameter_locations: parameter_location_t list;
    fintf_returntypes: btype_t list;
    fintf_bctype: btype_t option
  }


(** Api term used in expressions that describe a function's externally observable
    behavior.*)
type bterm_t =
  | ArgValue of fts_parameter_t  (** argument value (including global values) *)
  | RunTimeValue   (** unknown value *)
  | ReturnValue of bterm_t   (** return value from function identified by term *)
  | NamedConstant of string  (** macro *)
  | NumConstant of numerical_t  (** numerical constant *)
  | ArgBufferSize of bterm_t   (** size of buffer pointed to by term in bytes *)
  | IndexSize of bterm_t (** value of term, represented as size in type units *)
  | ByteSize of bterm_t  (** value of term, represented as size in bytes *)
  | ArgAddressedValue of bterm_t * bterm_t    (** [ArgAddressedValue (base, offset)]
  refers to the value at address [base + offset] *)
  | ArgNullTerminatorPos of bterm_t (** Pointer to the null-terminating byte in a
  string *)
  | ArgSizeOf of btype_t (** Size of type in bytes *)
  | ArithmeticExpr of arithmetic_op_t * bterm_t * bterm_t
  (** arithmetic expression over terms *)

(** {2 Call targets}*)

(** Function stub identification.*)
type function_stub_t =
  | SOFunction of string (** name of library function (ELF) *)
  | DllFunction of string * string (** name of library function (PE) *)
  | JniFunction of int  (** Java Native Methods, call on ( *env) where env is the
    first argument on the calling function, with the jni identification number *)
  | LinuxSyscallFunction of int (** numbers ranging from 4000 to 4999 *)
  | PckFunction of string * string list * string   (** PE, with package names *)


(** Identification of a call target in a call instruction.*)
type call_target_t =
  | StubTarget of function_stub_t (** call to dynamically linked function
  external to the executable *)
  | StaticStubTarget of doubleword_int * function_stub_t (** call to a statically
  linked library function, with its address in the executable *)
  | AppTarget of doubleword_int (** call to application function with the given address
  in the executable *)
  | InlinedAppTarget of doubleword_int * string (** [InlinedAppTarget (dw, name) is
  call to an inlined application function with address [dw] and name [name] *)
  | WrappedTarget of
      doubleword_int
      * function_interface_t
      * call_target_t
      * (fts_parameter_t * bterm_t) list
    (** [WrappedTarget (a, fapi, tgt, map)] is a call to a function that itself
        is a thin wrapper for a call to another function with address [a] and api
        [fapi], (inner) call target [tgt], with [map] a map of the parameters of
        the inner function mapped to the values given to the outer call.*)
  | VirtualTarget of function_interface_t (** call to a virtual function with a
  known type signature *)
  | IndirectTarget of bterm_t option * call_target_t list
  (** [IndirectTarget (t, tgts) is a call to a target expressed by
      term [t] (if known, must be expressible by values
      external to the function, e.g., a global variable or
      a function argument, or a return value) and a list of
      concreate call targets.*)
  | CallbackTableTarget of doubleword_int * int
  (** [CallbackTableTarget (dw, index)]
      is an indirect call where the
      target is in a table of pointers *)
  | UnknownTarget (** indirect call to an unknown target *)


(** {2 Jump targets} *)
(* Indirect jump target types:
   JumptableTarget (offset,jumptable,reg)
      jmp* offset(.,reg,4) with offset within a jump table
   OffsettableTarget (joffset, jumptable, datablock)
      x86:movzx (reg, doffset(_)) where doffset is the start of an offset table
      x86:jmp* joffset(., reg, 4) where joffset is within a jump table
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


(** {2 Preconditions} *)

type c_struct_constant_t =
| FieldValues of (int * c_struct_constant_t) list
| FieldConstant of bterm_t
| FieldString of string
| FieldCallTarget of call_target_t


(** Predicate over external terms to represent function preconditions,
    postconditions, and side effects.*)
type xxpredicate_t =
  | XXAllocationBase of bterm_t
  (** term is the start address of a dynamically allocated region*)
  | XXBlockWrite of btype_t * bterm_t * bterm_t
    (** [t1] is the start address of a memory region, [t2] is the number of
        bytes written*)
  | XXBuffer of btype_t * bterm_t * bterm_t
    (** [t1] is the start address of a memory region with at least [t2]
        bytes *)
  | XXEnum of bterm_t * string * bool
  (** term t is one of the values included in the named enumeration, if [flags]
      is true, the constant is a set of flags *)
  | XXFalse
    (** always false, used as a post condition to indicate non-returning*)
  | XXFreed of bterm_t  (** term pointed to is freed *)
  | XXFunctional  (** function has no observable side effects *)
  | XXFunctionPointer of btype_t * bterm_t  (** term is pointer to a function *)
  | XXIncludes of bterm_t * c_struct_constant_t
  | XXInitialized of bterm_t (** lval denoted is initialized *)
  | XXInitializedRange of btype_t * bterm_t * bterm_t
  (** memory region starting at [t1] is initialized for at least [t2] bytes*)
  | XXInputFormatString of bterm_t
  (** term points to format string for input (e.g., scanf)*)
  | XXInvalidated of bterm_t
  (** object pointed to may not be valid any more *)
  | XXModified of bterm_t
  (** term is modified (as a side effect of the function) *)
  | XXNewMemory of bterm_t * bterm_t
  (** [t1] points to newly allocated memory (since the start of
      the function), stack or heap with size [t2] bytes *)
  | XXStackAddress of bterm_t (** term is a stack address *)
  | XXHeapAddress of bterm_t (** term is a heap address *)
  | XXGlobalAddress of bterm_t (** term is a global address *)
  | XXNoOverlap of bterm_t * bterm_t
  (** the memory regions pointed at by [t1] and [t2] do not overlap *)
  | XXNotNull of bterm_t   (** term is not null *)
  | XXNull of bterm_t    (** term is null *)
  | XXNotZero of bterm_t   (** term is not zero *)
  | XXNonNegative of bterm_t  (** term is not negative *)
  | XXPositive of bterm_t   (** term is positive *)
  | XXNullTerminated of bterm_t  (** term points to null-terminated string *)
  | XXOutputFormatString of bterm_t
  (** term points to format string for output (e.g., sprintf) *)
  | XXRelationalExpr
    of relational_op_t * bterm_t * bterm_t  (** relational expression *)
  | XXSetsErrno
  | XXStartsThread of bterm_t * bterm_t list
  (** starts a thread with [t1] as start address and the remaining terms as
      parameters *)
  | XXTainted of bterm_t (** value of term is externally controlled *)
  | XXValidMem of bterm_t
  (** memory region pointed to be by term has not been freed *)
  | XXDisjunction of xxpredicate_t list
  | XXConditional of xxpredicate_t * xxpredicate_t


(** Informal description of the actions performed by a function, potentially
    conditional on a precondition.*)
type io_action_t = {
  iox_cat: string;
  iox_desc: string;                  (* description *)
  iox_pre: xxpredicate_t option;     (* condition for inclusion *)
}


(** {2 Function semantics} *)

(** Function semantics, combining pre- and postconditions and side effects.*)
type function_semantics_t = {
  fsem_pre: xxpredicate_t list;
  fsem_post: xxpredicate_t list;
  fsem_errorpost: xxpredicate_t list;
  fsem_postrequests: xxpredicate_t list;
  fsem_sideeffects: xxpredicate_t list;
  fsem_io_actions: io_action_t list;
  fsem_desc: string;
  fsem_throws: string list
}


(** Function documentation (from an external source).*)
type function_documentation_t = {
  fdoc_desc: string;
  fdoc_remarks: string;
  fdoc_caution: string;
  fdoc_apidoc: pretty_t;
  fdoc_xapidoc: xml_element_int
}


(** {2 Function summary} *)

(** The function summary data structure is immutable, any change creates a
    new object.*)
class type function_summary_int =
object ('a)

  (** {1 Function interface}*)

  method get_function_interface: function_interface_t

  method get_name: string

  method get_jni_index: int

  method get_syscall_index: int

  method is_jni_function: bool

  (** Modifies the types of the type signature according to the type transformer.
      Is applied primarily to Windows library functions that have a generic summary
      and can be specialized either for ASCII or Wide-string types.
   *)
  method modify_types: string -> type_transformer_t -> 'a

  (** {2 Function type signature}*)

  method get_function_signature: function_signature_t

  method get_parameters: fts_parameter_t list

  method get_parameter_for_register: register_t -> fts_parameter_t

  method get_parameter_at_stack_offset: int -> fts_parameter_t

  method get_returntype: btype_t

  (** Returns a new function summary that is identical to this summary, except
      for the return type of the type signature.*)
  method set_returntype: btype_t -> 'a

  method add_stack_parameter_location: int -> btype_t -> int -> 'a

  method add_register_parameter_location: register_t -> btype_t -> int -> 'a

  (** Returns the adjustment made by the callee to the stackpointer,
      in bytes (x86, PE only)*)
  method get_stack_adjustment: int option

  (** Returns the registers preserved by the function that deviate from the
      default registers preserved, (i.e., Eax, Ecx, Edx) (x86 only) *)
  method get_registers_preserved: register_t list

  (** {1 Function semantics}*)

  method get_function_semantics: function_semantics_t

  (** {2 Precondtiions}*)

  method get_preconditions: xxpredicate_t list

  method add_precondition: xxpredicate_t -> 'a

  (* name, specified as flags *)
  method get_enum_type: fts_parameter_t -> (btype_t * bool) option

  (** {2 Postconditions}*)

  method get_postconditions: xxpredicate_t list

  method is_nonreturning: bool

  (** {2 Error-postconditions}*)

  method get_errorpostconditions: xxpredicate_t list

  (** {2 Post-requests}*)

  method get_postrequests: xxpredicate_t list

  method add_postrequest: xxpredicate_t -> 'a

  (** {2 Side effects}*)

  method get_sideeffects: xxpredicate_t list

  method add_sideeffect: xxpredicate_t -> 'a

  method sets_errno: bool

  method has_unknown_sideeffects: bool

  method get_enums_referenced: string list

  method get_io_actions: io_action_t list

  (** {1 Function documentation}*)

  method get_function_documentation: function_documentation_t

  (** {1 Printing/saving}*)

  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end


(** Instantiated xxpredicate (or other condition) with expressions in the
    context of a function (proof obligation that can be discharged against
    invariants).*)
type xpo_predicate_t =
  | XPOAllocationBase of xpr_t
  | XPOBlockWrite of btype_t * xpr_t * xpr_t
  | XPOBuffer of btype_t * xpr_t * xpr_t
  | XPOEnum of xpr_t * string * bool
  | XPOFalse
  | XPOFreed of xpr_t
  | XPOFunctional
  | XPOFunctionPointer of btype_t * xpr_t
  | XPOIncludes of xpr_t * c_struct_constant_t
  | XPOInitialized of xpr_t
  | XPOInitializedRange of btype_t * xpr_t * xpr_t
  | XPOInputFormatString of xpr_t
  | XPOInvalidated of xpr_t
  | XPOModified of xpr_t
  | XPONewMemory of xpr_t * xpr_t
  | XPOStackAddress of xpr_t
  | XPOHeapAddress of xpr_t
  | XPOGlobalAddress of xpr_t
  | XPONoOverlap of xpr_t * xpr_t
  | XPONotNull of xpr_t
  | XPONull of xpr_t
  | XPONotZero of xpr_t
  | XPONonNegative of xpr_t
  | XPOPositive of xpr_t
  | XPONullTerminated of xpr_t
  | XPOOutputFormatString of xpr_t
  | XPORelationalExpr of relational_op_t * xpr_t * xpr_t
  | XPOSetsErrno
  | XPOStartsThread of xpr_t * xpr_t list
  | XPOTainted of xpr_t
  | XPOValidMem of xpr_t
  | XPODisjunction of xpo_predicate_t list
  | XPOConditional of xpo_predicate_t * xpo_predicate_t


(** {2 Global state}*)

(** Operator used in expressions over global terms *)
type g_arithmetic_op = GPlus | GMinus | GTimes | GDivide

(** Term in expressions over globals *)
type gterm_t =
| GConstant of numerical_t
| GReturnValue of location_int
| GSideeffectValue of location_int * string (** call site, argument name *)
| GArgValue of doubleword_int * int * int list (** function, arg index, offset *)
| GUnknownValue
| GArithmeticExpr of g_arithmetic_op * gterm_t * gterm_t


class type gv_reader_int =
object
  method get_type: btype_t
  method get_size: int option
  method get_offset: int list
  method is_function_pointer: bool
  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end


class type gv_writer_int =
  object ('a)
    method compare_x: 'a -> int

  (* accessors *)
  method get_type: btype_t
  method get_size: int option
  method get_offset: int list
  method get_value: gterm_t

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
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

  method add_precondition: location_int -> xxpredicate_t -> unit

  (* accessors *)
  method get_address: doubleword_int
  method get_values: gterm_t list
  method get_types : btype_t list

  (* predicates *)
  method is_function_pointer: bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
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

  method add_precondition:
           doubleword_int -> location_int -> xxpredicate_t -> unit

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


(** {2 Interface dictionary} *)

class type interface_dictionary_int =
  object
    method reset: unit

    (** {1 Parameter location}*)
    method index_pld_position: pld_position_t -> int
    method get_pld_position: int -> pld_position_t
    method index_pld_position_list: pld_position_t list -> int
    method get_pld_position_list: int -> pld_position_t list
    method index_parameter_location_detail: parameter_location_detail_t -> int
    method get_parameter_location_detail: int -> parameter_location_detail_t
    method index_parameter_location: parameter_location_t -> int
    method get_parameter_location: int -> parameter_location_t
    method index_parameter_location_list: parameter_location_t list -> int
    method get_parameter_location_list: int -> parameter_location_t list
    method write_xml_parameter_location:
             ?tag:string -> xml_element_int -> parameter_location_t -> unit
    method read_xml_parameter_location:
             ?tag:string -> xml_element_int -> parameter_location_t
    method write_xml_parameter_location_list:
             ?tag:string -> xml_element_int -> parameter_location_t list -> unit
    method read_xml_parameter_location_list:
             ?tag:string -> xml_element_int -> parameter_location_t list

    (** {1 Parameter role}*)

    method index_role: (string * string) -> int
    method get_role: int -> (string * string)

    (** {1 Parameter roles}*)

    method index_roles: (string * string) list -> int
    method get_roles: int -> (string * string) list

    (** {1 Fts parameters}*)

    (** {2 Fts parameter}*)

    method index_fts_parameter: fts_parameter_t -> int
    method get_fts_parameter: int -> fts_parameter_t
    method write_xml_fts_parameter:
             ?tag:string -> xml_element_int -> fts_parameter_t -> unit
    method read_xml_fts_parameter:
             ?tag:string -> xml_element_int -> fts_parameter_t

    (** {2 Fts parameter list}*)

    method index_fts_parameter_list: fts_parameter_t list -> int
    method get_fts_parameter_list: int -> fts_parameter_t list

    (** {2 Fts parameter value}*)

    method index_fts_parameter_value:  (fts_parameter_t * bterm_t) -> int
    method get_fts_parameter_value:  int -> (fts_parameter_t * bterm_t)

    (** {1 Bterm}*)

    method index_bterm: bterm_t -> int
    method get_bterm: int -> bterm_t
    method write_xml_bterm: ?tag:string -> xml_element_int -> bterm_t -> unit
    method read_xml_bterm: ?tag:string -> xml_element_int -> bterm_t

    (** {1 Gterm}*)

    method index_gterm: gterm_t -> int
    method get_gterm: int -> gterm_t
    method write_xml_gterm: ?tag:string -> xml_element_int -> gterm_t -> unit
    method read_xml_gterm: ?tag:string -> xml_element_int -> gterm_t

    (** {1 Function signature}*)

    method index_function_signature: function_signature_t -> int
    method get_function_signature: int -> function_signature_t
    method write_xml_function_signature:
             ?tag:string -> xml_element_int -> function_signature_t -> unit
    method read_xml_function_signature:
             ?tag:string -> xml_element_int -> function_signature_t

    (** {1 Function interface}*)

    method index_function_interface: function_interface_t -> int
    method get_function_interface: int -> function_interface_t
    method write_xml_function_interface:
             ?tag:string -> xml_element_int -> function_interface_t -> unit
    method read_xml_function_interface:
             ?tag:string -> xml_element_int -> function_interface_t

    (** {1 Function semantics}*)

    method index_function_semantics: function_semantics_t -> int
    method get_function_semantics: int -> function_semantics_t
    method write_xml_function_semantics:
             ?tag:string -> xml_element_int -> function_semantics_t -> unit
    method read_xml_function_semantics:
             ?tag:string -> xml_element_int -> function_semantics_t

    (** {1 XXPredicates}*)

    method index_xxpredicate: xxpredicate_t -> int
    method get_xxpredicate: int -> xxpredicate_t
    method index_xxpredicate_list: xxpredicate_t list -> int
    method get_xxpredicate_list: int -> xxpredicate_t list
    method write_xml_xxpredicate:
             ?tag:string -> xml_element_int -> xxpredicate_t -> unit
    method read_xml_xxpredicate:
             ?tag:string -> xml_element_int -> xxpredicate_t
    method write_xml_xxpredicate_list:
             ?tag:string -> xml_element_int -> xxpredicate_t list -> unit

    (** {1 Function stub}*)

    method index_function_stub: function_stub_t -> int
    method get_function_stub: int -> function_stub_t
    method write_xml_function_stub:
             ?tag:string -> xml_element_int -> function_stub_t -> unit
    method read_xml_function_stub:
             ?tag:string -> xml_element_int -> function_stub_t

    (** {1 Call target}*)

    method index_call_target: call_target_t -> int
    method get_call_target: int -> call_target_t
    method write_xml_call_target:
             ?tag:string -> xml_element_int -> call_target_t -> unit
    method read_xml_call_target: ?tag:string -> xml_element_int -> call_target_t

    (** {1 Struct constants}*)

    method index_c_struct_constant: c_struct_constant_t -> int
    method get_c_struct_constant: int -> c_struct_constant_t

    (** {1 Struct field values}*)

    method index_struct_field_value: (int * c_struct_constant_t) -> int
    method get_struct_field_value: int -> (int * c_struct_constant_t)

    (** {1 Save/restore}*)

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


(** {1 Function summary library}*)

(** Data structure for reporting statistics on shared-object library functions *)
type dm_so_metrics_t = {
    dmso_requested_summaries: int;
    dmso_so_summaries: int;
    dmso_bc_summaries: int;
    dmso_missing_summaries: int
  }


type so_import_names_t = {
    so_requested_summaries: string list;
    so_summaries: string list;
    so_bc_summaries: string list;
    so_missing_summaries: string list
  }

(** The function summary library holds
   - summaries (models) of dll/so functions, and
   - summaries (models) of jni functions

   Dll summaries are searched for by a combination of dll name, which provides
   the directory of the summary, and by name; so summaries are searched for
   by name.
   Jni summaries are obtained by index number: jni_<index> from the jni directory.

   Some Windows library functions have two versions: an ASCII version (with
   suffix A) and a Unicode version (with suffix W). The api and semantics for
   these functions are almost the same, so the models directory provides a
   neutral version (without suffix) that provides all documentation, api, and
   semantics, and an A and W version that refer to the neutral version by name
   and indicate all type changes to be made to obtain the respective version.
   The format of the referring version is, e.g., for CreateProcessA:
   {[
   <refer-to name="CreateProcess">
      <replace_type  src="STARTUPINFO" tgt="STARTUPINFOA"/>
   </refer-to>
   ]}
   Replacement of the standard types is performed automatically:
   {[
     TCHAR   -> char, wchar_t
     LPCTSTR -> LPCSTR, LPCWSTR
     LPTSTR   -> LPSTR, LPWSTR
   ]}
   and so does not need to be included.

   Some functions appear in multiple libraries. To avoid having to maintain
   multiple copies of the same model, we provide one model and references to
   this model within other libraries (directories).
   The format of the referring version is, e.g., for send in wsock32.dll:
   {[
   <libfun lib="wsock32" name="send">
      <refer-to lib="ws_32" name="send"/>
   </libfun>
   ]}

   All Jni function models are stored in the jni directory. The name of the
   file for jni function with index x is jni_x.xml .
   Several jni functions are variations of the same function, only with
   different types. E.g., there are ten jni functions of the form
   Call<type>Method, for ten different types, each with their own index.
   The model directory provides a template version, that all ten other
   model files can refer to.
   The format of the referring version is, e.g., for CallIntMethod,
   {[
   <jnifun index="49" prefix="Call" suffix="Method" typename="Int">
      <type>jint</type>
   </jnifun>
   ]}
   or for GetIntArrayElements,
   {[
   <jnifun prefix="Get" suffix="ArrayElements" typename="Int">
      <type>jint</type>
      <arrarytype>jintArray</arraytype>
   </jnifun>
   ]}

   Dll names are internally always represented with a _dll suffix unless
   the dll has an explicit different suffix (e.g., spools.drv) in which
   case the dll name is represented with the given extension (e.g.,
   spools_drv). All dllnames are internally represented in lower case.
   Windows file systems are case insensitive.

*)
class type function_summary_library_int =
  object

    (** {1 Load library function summaries} *)

    (** [load_dll_library_function dll fname] attempts to load the dll library
        function summary for the function with name [fname] from named
        dynamically loaded library [dll]. If the summary is found it is added
        to the active library and will be applied to all call sites of that
        function; if there is no function summary for this function, a message
        is logged to that effect, and no further attempts to obtain the summary
        will be made.*)
    method load_dll_library_function: string -> string -> unit

    (** [load_so_function fname] attempts to load the shared object library
        function summary for the function with name [fname]. It will first
        check if a summary is available in the [so_functions] directory. If so,
        this summary is loaded and applied to all call sites of that function.
        If no summary is found in [so_functions] it will check if a function
        prototype for this function has been provided via a header file. If so,
        the function prototype (possibly decorated with attributes) is converted
        to a function summary and applied to all call sites. If a summary could
        not be found in either source, a message is logged to that effect, and
        no further attempts to obtain the summary will be made.*)
    method load_so_function: string -> unit

    (** Reads in all summary files from the bchsummaries.jar provided.

        This provides a facility to check the (syntactic) validity of the
        summaries before they are used in analysis.*)
    method read_summary_files: unit

    (** {Query and access function summaries} *)

    (** [get_function_dll fname] returns the name of the dll that contains
        a function by this name

        @raise BCH_failure if [fname] is not an imported function
     *)
    method get_function_dll: string -> string

    (** [get_dll_function dll fname] returns the function summary for the dll
        function [fname] imported from dynamically loaded library [dll]

        @raise BCH_failure if no summary is available for [fname] from [dll].
     *)
    method get_dll_function: string -> string -> function_summary_int

    (** [get_so_function fname] returns the function summary for the shared
        object function [fname].

        @raise BCH_failure if no summary is available for [fname].
     *)
    method get_so_function: string -> function_summary_int

    (** [get_lib_function packages fname] attempts a load summary for a
        C++ function.*)
    method get_lib_function: string list -> string -> function_summary_int

    (** [search_for_library_function fname] returns the name of the dll that
        contains [fname] or None if [fname] cannot be found.*)
    method search_for_library_function: string -> string option

    (** [get_syscall_function index] returns the function summary for the
        system call with index [index].

        @raise BCH_failure if no summary is available for the system call with
        index [index].
     *)
    method get_syscall_function: int -> function_summary_int

    (** [get_jni_function index] returns the function summary for the Java
        Native Method with index [index].

        @raise BCH_failure if no summary is available for the JNI function with
        index [index].
     *)
    method get_jni_function: int -> function_summary_int

    (** Returns all dll, jni, and lib (C++) summaries available.*)
    method get_library_functions: function_summary_int list

    (** {1 Requests} *)

    (** [has_function_dll fname] returns true if [fname] has an associated dll.*)
    method has_function_dll: string -> bool

    (** [has_dllname dll] returns true if a dll with name [dll] has been
        imported and a function was loaded from it.*)
    method has_dllname: string -> bool

    (** [has_dll_function dll fname] checks if a function summary has been
        loaded for [fname] from dll [dll], or if not, if one is available from
        the provided summaries. It returns true if a summary was found, false
        otherwise.*)
    method has_dll_function: string -> string -> bool

    (** [has_so_function fname] checks if a function summary has been loaded for
        shared object function [fname], or if not, if one is available from the
        provided summaries, or from a header file. It returns true if a summary
        was found, false otherwise.*)
    method has_so_function: string -> bool

    method has_lib_function: string list -> string -> bool

    method has_syscall_function: int -> bool

    method has_jni_function: int -> bool

    (** {1 Retrieving / saving summaries} *)

    (** {2 Retrieving summaries} *)

    method read_xml_constant_file: string -> unit

    method read_xml_constants_files: xml_element_int -> unit

    method read_xml_struct_file: string -> unit

    (** {2 Saving summaries} *)

    method write_xml_requested_summaries: xml_element_int -> unit

    method write_xml_missing_summaries: xml_element_int -> unit

    (** {1 Statistics} *)

    method so_import_names: so_import_names_t

end


(** {1 Callgraph}*)

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


(** {1 C++ related types} *)

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


type demangled_name_t = {
  dm_name : tname_t;
  dm_name_space : tname_t list;
  dm_parameter_types : btype_t list;
  dm_returntype      : btype_t option;
  dm_calling_convention: string;
  dm_accessibility: string;
  dm_storage_class: string;
  dm_constructor  : bool;
  dm_destructor   : bool;
  dm_static       : bool;
  dm_virtual      : bool;
  dm_operator     : bool;
  dm_const        : bool;
  dm_vbtable      : bool;
  dm_vftable      : bool
  }


(** {1 Type inference}

    The type inference performed here is a variation on Retypd as described in:

    Noonan, M., Loginov, A., and Cok, D. (2016). Polymorphic type inference for
    machine code. In Krintz, C. and Berger, E. D., editors, Proceedings of the
    37th ACM SIGPLAN Conference on Programming Language Design and
    Implementation, PLDI 2016, Santa Barbara, CA, USA, June 13-17, 2016,
    pages 27–41. ACM.
*)

type type_base_variable_t =
  | FunctionType of string (** function hex address *)
  | DataAddressType of string  (** global hex address *)
  | GlobalVariableType of string (** global hex address *)
  | RegisterLhsType of register_t * string * string
  (** assignment (function, instruction) hex address *)

  | LocalStackLhsType of int * string * string
  (** assignment offset in bytes, (function, instruction) hex address *)


type type_cap_label_t =
  | FRegParameter of register_t
  | FStackParameter of int * int (** size, offset in bytes *)
  | FLocStackAddress of int
  (** address on local stackframe that escapes, offset in bytes *)

  | FReturn  (** for now limited to the default return register *)
  | Load
  | Store
  | Deref   (** Combination of Load and Store *)
  | LeastSignificantByte
  | LeastSignificantHalfword
  | OffsetAccess of int * int (** size in bytes, offset in bytes *)
  | OffsetAccessA of int * int
  (** array of accesses, element size in bytes, initial offset in bytes *)


type type_variable_t = {
    tv_basevar: type_base_variable_t;
    tv_capabilities: type_cap_label_t list
  }


type type_constant_t =
  | TyAsciiDigit   (** integer in the range [0x30 - 0x39] ('0' - '9')*)
  | TyAsciiCapsLetter  (** integer in the range [0x41 - 0x5a] ('A' - 'Z') *)
  | TyAsciiSmallLetter (** integer in the range [0x61 - 0x7a] ('a' - 'z') *)
  | TyAsciiControl  (** integer in the range [0x1 - 0x1f] *)
  | TyAsciiPrintable  (** integer in the range [0x20 - 0x7e] *)
  | TyAscii  (** integer in the range [0x1 - 0x7f] *)
  | TyExtendedAscii  (** integer in the range [0x1 - 0xfe] *)
  | TyZero    (** can be either a pointer or an integer *)
  | TyTInt of signedness_t * int
  | TyTStruct of int * string  (** bckey, bcname *)
  | TyTFloat of fkind_t
  | TyTUnknown  (** top in type lattice *)
  | TyBottom  (** bottom in type lattice *)


type type_term_t =
  | TyVariable of type_variable_t
  | TyConstant of type_constant_t


type type_constraint_t =
  | TyVar of type_term_t
  | TySub of type_term_t * type_term_t
  | TyGround of type_term_t * type_term_t
  | TyZeroCheck of type_term_t


class type type_constraint_dictionary_int =
  object

    method reset: unit

    method index_type_basevar: type_base_variable_t -> int
    method get_type_basevar: int -> type_base_variable_t

    method index_type_caplabel: type_cap_label_t -> int
    method get_type_caplabel: int -> type_cap_label_t

    method index_type_variable: type_variable_t -> int
    method get_type_variable: int -> type_variable_t

    method index_type_constant: type_constant_t -> int
    method get_type_constant: int -> type_constant_t

    method index_type_term: type_term_t -> int
    method get_type_term: int -> type_term_t

    method index_type_constraint: type_constraint_t -> int
    method get_type_constraint: int -> type_constraint_t

    (** {1 Save/restore} *)

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type type_constraint_graph_int =
  object ('a)

    method partition_size: int

    method typevarcount: int

    method initialize: type_term_t list -> unit

    method add_typevar: int -> unit

    method partition: CHUtils.IntCollections.set_t list

    method saturate: 'a

    method add_constraint: type_constraint_t -> unit

    method toPretty: pretty_t

  end


class type type_constraint_store_int =
  object

    method reset: unit

    method add_constraint: type_constraint_t -> unit

    method add_var_constraint: type_variable_t -> unit

    method add_term_constraint: type_term_t -> unit

    method add_zerocheck_constraint: type_variable_t -> unit

    method add_subtype_constraint: type_term_t -> type_term_t -> unit

    method add_ground_constraint: type_term_t -> type_term_t -> unit

    method get_function_type_constraints: string -> type_constraint_t list

    method get_reglhs_constraints:
             register_t -> string -> string -> type_constraint_t list

    method get_stack_lhs_constraints:
             int -> string -> type_constraint_t list

    method evaluate_reglhs_type:
             register_t
             -> string
             -> string
             -> (type_variable_t list * type_constant_t list) list

    method evaluate_stack_lhs_type:
             int
             -> string
             -> (type_variable_t list * type_constant_t list) list

    method resolve_reglhs_type:
             register_t -> string -> string -> btype_t option

    method resolve_stack_lhs_type: int -> string -> btype_t option

    method resolve_reglhs_types:
             string -> (register_t * string * btype_t option) list

    method resolve_local_stack_lhs_types: string -> (int * btype_t option) list

    method toPretty: pretty_t

  end


(** {1 Variables} *)

(** {2 Memory references} *)

(** Memory reference base: a base address for a logical region of memory.

    Note that the difference between [BaseVar v] on the one hand and
    [BaseArray (v, t)] and [BaseStruct (v, t)] on the other hand is that the
    variable [v] referenced in [BaseVar] refers to a variable that is a
    pointer, that is, its value is the address of the base, while the
    expression [x] in [BaseArray] and [BaseStruct] is a symbolic representation
    of the address itself, that is, there is no associated variable in the
    code. The latter two are applicable to global or stack-allocated arrays
    and structs that can be referenced directly via their address without
    intervention of any variables, while the former requires, e.g., a return
    variable to hold the address.
*)
type memory_base_t =
| BLocalStackFrame  (** local stack frame *)
| BRealignedStackFrame (** local stack frame after realignment *)
| BAllocatedStackFrame (** extended stack frame from alloca *)
| BGlobal  (** global data *)

| BaseVar of variable_t
(** base provided by an externally controlled variable,
    e.g., argument to the function, or return value from malloc *)

| BaseArray of xpr_t * btype_t
(** base provided by a typed array address *)

| BaseStruct of xpr_t * btype_t
(** base provided by a typed struct address *)

| BaseUnknown of string  (** address without interpretation *)


(** Memory offset: a constant or symbolic offset from a memory base.*)
type memory_offset_t =
  | NoOffset
  | ConstantOffset of numerical_t * memory_offset_t
  (** typically used when the type of the variable is not known, or for
      global offsets (the absolute address of a global variable), or for
      stack offsets (the difference between the stack pointer and the value
      of the stack pointer at function entry *)

  | FieldOffset of fielduse_t * memory_offset_t
  (** offset in a struct variable with [(fieldname, struct key)] *)

  | IndexOffset of variable_t * int * memory_offset_t  (* deprecated *)
  (** deprecated, superceded by ArrayIndexOffset *)

  | ArrayIndexOffset of xpr_t * memory_offset_t
  (** index expression is scaled by the size of the array element (assumes
      that the type of the variable is known). The index expression must
      consist solely of constants or constant-value variables.*)

  | UnknownOffset
  (** used if none of the above apply *)


(** Memory reference wrapper. *)
class type memory_reference_int =
object ('a)
  (* identification *)
  method index: int

  (* comparison *)
  method compare: 'a -> int

  (** {1 Accessors} *)

  method get_base: memory_base_t
  method get_name: string
  method get_type: btype_t option

  (** Returns the pointer variable that points to the base of this memory
      reference.

      Returns [Error] if this memory reference does not have a [Basevar] base.*)
  method get_external_base: variable_t traceresult

  (** Returns the memory address variable and type of the base address of this
      memory reference.

      Returns [Error] if this memory reference does not have a [BaseArray] base.*)
  method get_array_base: (xpr_t * btype_t) traceresult

  (** Returns the memory address variable and type of the base address of this
      memory reference.

      Returns [Error] if this memory reference does not have a [BaseStruct] base.*)
  method get_struct_base: (xpr_t * btype_t) traceresult

  (** {1 Predicates} *)

  (** Returns [true] if this reference has a [BaseVar] (pointer variable) base.*)
  method has_external_base: bool

  (** Returns [true] if this reference has a [BaseArray] (array address) base.*)
  method has_array_base: bool

  (** Returns [true] if this reference has a [BaseStruct] (struct address) base.*)
  method has_struct_base: bool

  (** Returns [true] if this reference has a local stack frame base.*)
  method is_stack_reference: bool

  method is_realigned_stack_reference: bool
  method is_global_reference: bool
  method is_unknown_reference: bool

  (** {1 Printing} *)

  method toPretty : pretty_t
end


(** Principal access points for creating and retrieving memory references.*)
class type memory_reference_manager_int =
object

  method reset: unit

  (** {1 Creating Memory references} *)

  method mk_local_stack_reference: memory_reference_int
  method mk_global_reference: memory_reference_int
  method mk_allocated_stack_reference: memory_reference_int
  method mk_realigned_stack_reference: memory_reference_int
  method mk_basevar_reference: variable_t -> memory_reference_int
  method mk_base_array_reference: xpr_t -> btype_t -> memory_reference_int
  method mk_base_struct_reference: xpr_t -> btype_t -> memory_reference_int
  method mk_unknown_reference: string -> memory_reference_int

  (** {1 Accessors} *)

  method get_memory_reference: int -> memory_reference_int traceresult
  method get_memory_reference_type: int -> btype_t option

  (** {1 Predicates} *)

  method is_unknown_reference: int -> bool traceresult
  method is_global_reference: int -> bool traceresult

  (** {1 Initialization} *)

  method initialize: unit
end


(** {2 Assembly variable} *)

(** Assembly variable denotations.*)
type assembly_variable_denotation_t =
  (* size (bytes) memory reference index *)
  | MemoryVariable of int * int * memory_offset_t
  | RegisterVariable of register_t
  | CPUFlagVariable of flag_t
  | AuxiliaryVariable of constant_value_variable_t

(** Auxiliary variables: variables that have a constant (but unknown) value
    within the function.

   A {b bridge variable} is used to carry function arguments from the point where
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
   the function is entered ([InitialRegisterValue] or [InitialMemoryValue]) or
   during the execution of the function.

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
and constant_value_variable_t =
  | InitialRegisterValue of register_t * int
  (** value of register variable at function entry *)

  | InitialMemoryValue of variable_t
  (** value of memory variable at function entry *)

  | FrozenTestValue of
      variable_t            (* variable being frozen *)
      * ctxt_iaddress_t     (* address of test instruction *)
      * ctxt_iaddress_t     (* address of jump instruction *)
  (** [FrozenTestValue (var, t_iaddr, j_iaddr)]: frozen value of variable
  [var] at the address [t_iaddr] where it participates in a test expression
  that is used as a predicate for a conditional jump instruction (or other
  condition instruction) at address [j_iaddr]*)

  | FunctionReturnValue  of ctxt_iaddress_t
  (** [FunctionReturnValue iaddr]: return value from call at instruction
      address [iaddr]*)

  | SyscallErrorReturnValue of ctxt_iaddress_t
  (** [SyscallErrorReturnValue iaddr]: error return value from system call at
      instruction address [iaddr]*)

  | FunctionPointer of
      string                (* name of function *)
      * string              (* name of creator *)
      * ctxt_iaddress_t     (* address of creation *)

  | CallTargetValue of call_target_t

  | SideEffectValue of
      ctxt_iaddress_t       (* callsite *)
      * string              (* argument description *)
      * bool                (* is-global address *)
  (** [SideEffectValue (iaddr, name, is_global) represents the value
  assigned by the callee at call site [iaddr] to the argument with
  name [name].*)

  | BridgeVariable of ctxt_iaddress_t * int      (* call site, argument index *)

  | FieldValue of string * int * string     (* struct name, offset, fieldname *)

  | SymbolicValue of xpr_t
  (** expression that consists entirely of symbolic constants *)

  | SignedSymbolicValue of xpr_t * int * int
  (** sign-extended symbolic value with the original size and new size in bits*)

  | Special of string
  | RuntimeConstant of string
  | ChifTemp


class type assembly_variable_int =
object ('a)
  (* identification *)
  method index: int

  (** {1 Comparison} *)

  method compare: 'a -> int

  (** {1 Converters} *)

  method to_basevar_reference: memory_reference_int option

  (** {1 Accessors} *)

  method get_name: string
  method get_type: btype_t option
  method get_denotation: assembly_variable_denotation_t

  (** Returns the register associated with this register variable.

      Returns [Error] if this variable is not a register variable. *)
  method get_register: register_t traceresult

  (** Returns the memory reference associated with this memory variable.

      Returns [Error] if this variable is not a memory variable. *)
  method get_memory_reference: memory_reference_int traceresult

  (** Returns the memory offset associated with this memory variable.

      Returns [Error] if this variable is not a memory variable. *)
  method get_memory_offset: memory_offset_t traceresult

  (** Returns the name of the associated function pointer.

      Returns [Error] if this variable is not a function-pointer value. *)
  method get_pointed_to_function_name: string traceresult

  (** Returns the call site of a function return value or side-effect value.

      Returns [Error] if this variable is not a function return value or
      side-effect value. *)
  method get_call_site: ctxt_iaddress_t traceresult

  (** Returns the name of the argument of a side-effect value.

      Returns [Error] if this variable is not a side-effect value. *)
  method get_se_argument_descriptor: string traceresult

  (** Returns the frozen variable and the test and jump address associated
      with this variable.

      Returns [Error] if this variable is not a frozen test variable. *)
  method get_frozen_variable:
           (variable_t * ctxt_iaddress_t * ctxt_iaddress_t) traceresult

  (** Returns the memory variable associated with this initial-value
      memory variable.

      Returns [Error] if this variable is not an initial-value memory
      variable.*)
  method get_initial_memory_value_variable: variable_t traceresult

  (** Returns the register associated with this initial-value register
      variable.

      Returns [Error] if this variable is not an initial-value register
      variable. *)
  method get_initial_register_value_register: register_t traceresult

  (** Returns the address of the global variable whose value is changed.

      Returns [Error] if this variable is not a global side-effect value. *)
  method get_global_sideeffect_target_address: doubleword_result

  (** Returns the call target associated with this variable.

      Returns [Error] if this variable is not a call-target value. *)
  method get_calltarget_value: call_target_t traceresult

  (** Returns the original (fixed-value) expression associated with this
      symbolic-valiue variable.

      Returns [Error] if this variable is not a symbolic-value variable. *)
  method get_symbolic_value_expr: xpr_t traceresult

  (** {1 Predicates} *)

  method is_auxiliary_variable: bool
  method is_register_variable: bool
  method is_stackpointer_variable: bool
  method is_mips_argument_variable: bool
  method is_arm_argument_variable: bool
  method is_arm_extension_register_variable: bool
  method is_memory_variable: bool

  (** Returns true if this variable is set by the function environment and
      does not change during the execution of the function.

      The specific types of variables for which this is true:
      - initial value of a register (upon function entry)
      - intiial value of a memory location (upon function entry)
      - function return value (from a call to that function)
      - call-target value
      - side-effect value (value set by a call to another function as a
          side effect)
      - field value
      - symbolic value: a variable representing the value of an expression
          over function-initial-values
      - signed symbolic value: idem for a sign-extended value
   *)
  method is_function_initial_value: bool    (* value from function environment *)

  method is_initial_register_value: bool
  method is_initial_mips_argument_value: bool
  method is_initial_arm_argument_value: bool
  method is_initial_stackpointer_value: bool

  method is_initial_memory_value: bool
  method is_frozen_test_value: bool

  method is_bridge_value: bool

  (** [is_bridge_value_at addr] returns true if this variable is a bridge
      value created at instruction address [addr]. *)
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

  (** [is_in_test_jump_range addr] returns [true] if this variable is a frozen
      test value and the address is in the range between the test address and
      the jump address. It returns [false] if this variable is a frozen test
      value, but the address is not in that range.

      Returns [Error] if this variable is not a frozen test value. *)
  method is_in_test_jump_range: ctxt_iaddress_t -> bool traceresult

  (* printing *)
  method toPretty: pretty_t

end


(** {2 Variable dictionary} *)

(** Ways that data can be loaded from or stored to the function stack frame.*)
type stack_access_t =
  | RegisterSpill of int * register_t
  (** stack offset *)
  | RegisterRestore of int * register_t
  (** stack offset *)
  | StackLoad of variable_t * int * int option * btype_t
  (** variable, offset, size *)
  | StackStore of variable_t * int * int option * btype_t * xpr_t option
  (** variable, offset, size, value *)
  | StackBlockRead of int * int option * btype_t
  (** offset, size *)
  | StackBlockWrite of int * int option * btype_t * xpr_t option
  (** offset, size *)


class type vardictionary_int =
  object

    method xd: xprdictionary_int
    method faddr: doubleword_int
    method reset: unit
    method get_indexed_variables: (int * assembly_variable_denotation_t) list
    method get_indexed_bases: (int * memory_base_t) list

    method index_memory_offset: memory_offset_t -> int
    method index_memory_base: memory_base_t -> int
    method index_assembly_variable_denotation: assembly_variable_denotation_t -> int
    method index_constant_value_variable: constant_value_variable_t -> int
    method index_stack_access: stack_access_t -> int

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
             ?tag:string
             -> xml_element_int
             -> assembly_variable_denotation_t
             -> unit
    method read_xml_assembly_variable_denotation:
             ?tag:string -> xml_element_int -> assembly_variable_denotation_t

    method write_xml_stack_access:
             ?tag:string -> xml_element_int -> stack_access_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


(** {2 Variable manager} *)

class type variable_manager_int =
object

  (** {1 Management}*)

  (** Resets the variable dictionary.*)
  method reset: unit

  (** Returns the address of the function to which this variable manager
      belongs.*)
  method faddr: doubleword_int

  (** Returns the variable dictionary for this function.*)
  method vard: vardictionary_int

  (** Returns the memory reference manager for this function.*)
  method memrefmgr: memory_reference_manager_int

  (** {1 Creating variables}*)

  (** {2 Registers and flags}*)

  (** [make_register_variable r] returns the register variable for [r].*)
  method make_register_variable: register_t -> assembly_variable_int

  (** [make_flag_variable f] returns the flag variable [f].*)
  method make_flag_variable: flag_t -> assembly_variable_int


  (** {2 Memory variables}*)

  (** [make_memory_variable ?size memref offset] returns the memory variable
      with base [memref] and offset [offset].*)
  method make_memory_variable:
           ?size: int ->
           memory_reference_int ->
           memory_offset_t ->
           assembly_variable_int

  method add_memvar_offset:
           variable_t
           -> memory_offset_t
           -> assembly_variable_int traceresult

  (** [make_global_variable ?size ?offset address] returns the global variable
      with address [address] and optional offset [offset].*)
  method make_global_variable:
           ?size:int
           -> ?offset:memory_offset_t
           -> numerical_t
           -> assembly_variable_int


  (** {2 Auxiliary variables}*)

  (** [make_frozen_test_value var taddr jaddr] returns a frozen test value
      for the variable [var] at test address [taddr] that is part of an
      that is used in a conditional instruction (e.g., a conditional jump) at
      address [jaddr].

      A frozen test value captures the value of a variable at the address where
      the test is evaluated. This value will be used in the predicate constructed
      for the conditional instruction, where the value of the same variable may
      have a different value.
   *)
  method make_frozen_test_value:
           variable_t
           -> ctxt_iaddress_t
           -> ctxt_iaddress_t
           -> assembly_variable_int

  (** [make_bridge_value addr argix] returns a bridge value for the
      variable [var] that is the stack argument with index [argix] (1-based)
      for a call (x86 only).*)
  method make_bridge_value: ctxt_iaddress_t -> int -> assembly_variable_int

  (** [make_initial_register_value r] returns the variable representing the
      initial value of register [r] at function entry.*)
  method make_initial_register_value: register_t -> int -> assembly_variable_int

  (** [make_initial_memory_value var] returns the variable representing the
      initial value of memory variable [var] at function entry.]*)
  method make_initial_memory_value  : variable_t -> assembly_variable_int

  (** [make_return_value addr] returns the variable representing the return
      value from the call at address [addr].*)
  method make_return_value: ctxt_iaddress_t -> assembly_variable_int

  (** [make_symbolic_value x] returns the variable representing the
      value of expression [x], which must be an expression that consists
      entirely of constant-value variables.*)
  method make_symbolic_value: xpr_t -> assembly_variable_int

  (** [make_signed_symbolic_value x oldsize newsize] returns that variable
      representing the value of expression [x] sign-extended from [oldsize] to
      [newsize] (in bits).*)
  method make_signed_symbolic_value:
           xpr_t -> int -> int -> assembly_variable_int

  (** [make_special_variable name] returns a special-purpose variable with
      name [name] (uninterpreted).*)
  method make_special_variable: string -> assembly_variable_int

  (** [make_runtime_constant name] returns a variable that represents a
      run-time constant, identified by name [name].*)
  method make_runtime_constant: string -> assembly_variable_int

  method make_calltarget_value: call_target_t -> assembly_variable_int
  method make_function_pointer_value:
           string -> string -> ctxt_iaddress_t -> assembly_variable_int
  method make_side_effect_value:
           ctxt_iaddress_t -> ?global:bool -> string -> assembly_variable_int
  method make_field_value: string -> int -> string -> assembly_variable_int

  (** {2 Memory references}*)

  (** [make_memref_from_basevar var] returns a memory reference with base
      determined by [var].

      In particular, the initial value of a stack-pointer returns a
      stack-frame base; the initial value of other registers or of a
      function return value or memory value returns a basevar reference.
      A memory address value returns either a base-array or a base-struct
      reference depending on the type provided by the memory address value.

      Returns an unknown-basevar memory variable if [var] cannot be used
      as a basevar, or if a memory address value does not have a type.

      Returns [Error] if [var] cannot be found or if [var] is not a suitable
      constant-value variable.
   *)
  method make_memref_from_basevar: variable_t -> memory_reference_int traceresult


  (** {1 Deconstructing variables} *)

  (** {2 Basic} *)

  (** [get_variable chifvar] returns the assembly variable corresponding
      to [chifvar].*)
  method get_variable: variable_t -> assembly_variable_int traceresult

  (** [get_variable_by_index index] returns the assembly variable corresponding
      to the chif variable with index [index].*)
  method get_variable_by_index: int -> assembly_variable_int traceresult

  (** [get_variable_type chifvar] returns the type of the corresponding
      assembly variable if the type can be determined without context.
      Otherwise it returns [None]. *)
  method get_variable_type: variable_t -> btype_t option


  (** {2 Memory variables}

      A memory variable consists of a size, memory reference, and
      memory offset.

      An initial-value memory variable (aka memory variable value) is a not a
      variable but a symbolic value that indicates the value of a
      corresponding memory variable at function entry.

      The base of a memory variable can be one of the following:
      - local stack frame  ([is_stack_variable])
      - realigned stack frame  ([is_realigned_stack_variable])
      - allocated stack frame
      - global   ([is_global_variable])
      - basevar  ([is_basevar_memory_variable])
      - basearray
      - basestruct
      - unknown base  ([is_unknown_base_memory_variable])
   *)

  (** Returns [true] only if [var] is a memory variable.

      Note: returns [false] if [var] is an initial_memory variable (i.e.,
      memory value variable). *)
  method is_memory_variable: variable_t -> bool

  (** Returns [true] if [var] is an initial memory value variable (i.e.,
      the initial value of a memory variable. *)
  method is_initial_memory_value: variable_t -> bool

  (** [get_memvar_reference var] returns the base memory reference of
      memory-variable [var].

      Returns [Error] if the variable is not found or the variable is
      not a memory variable. *)
  method get_memvar_reference: variable_t -> memory_reference_int traceresult

  (** [get_memvar_offset var] returns the offset of memory variable [var].

      Returns [Error] if the variable is not found or the variable is
      not a memory variable. *)
  method get_memvar_offset: variable_t -> memory_offset_t traceresult

  method has_variable_index_offset: variable_t -> bool

  (** [get_memval_reference var] returns the base memory reference of
      memory-variable value [var].

      Returns [Error] if the variable is not found or the variable is not
      a memory variable. *)
  method get_memval_reference: variable_t -> memory_reference_int traceresult

  (** [get_memval_offset var] returns the offset of the memory variable
      associated with the initial-value memory variable [var].

      Returns [Error] if the variable is not found or [var] is not
      an initial-value memory variable. *)
  method get_memval_offset: variable_t -> memory_offset_t traceresult

  (** [get_initial_memory_value_variable var] returns the variable representing
      the memory variable of which [var] is the initial value at function
      entry.

      Returns [Error] if the variable is not found or [var] is not an
      initial-value memory variable. *)
  method get_initial_memory_value_variable: variable_t -> variable_t traceresult


  (** {2 Memory offsets} *)

  (** Returns [true] if [memoff] is a known numerical value, or it is an index
      offset with constant-value index variable, idem for sub-offsets.*)
  method is_fixed_value_offset: memory_offset_t -> bool

  (** Returns [true] if [var] is a memory variable and its offset is either
      a constant numerical value or an index offset with fixed value variables. *)
  method has_fixed_value_offset: variable_t -> bool

  (** Returns [true if [var] is a memory variable and its offset is a constant
      numerical value. *)
  method has_constant_offset: variable_t -> bool

  (** Returns [true] if [var] is a memory variable and its offset is unknown. *)
  method is_unknown_offset_memory_variable: variable_t -> bool


  (** {2 Register variables} *)

  (** Returns [true] if [var] is a register variable (of any architecture). *)
  method is_register_variable: variable_t -> bool

  (** Returns [true] if [var] is a register used as a stackpointer (in the
      current architecture). *)
  method is_stackpointer_variable: variable_t -> bool

  (** Returns the register associated with [var].

      Returns [Error] if [var] is not a register variable or [var] cannot be
      found. *)
  method get_register: variable_t -> register_t traceresult

  (** Returns [true] if [var] is the initial-value variable of a register
      (of any architecture). *)
  method is_initial_register_value: variable_t -> bool

  (** Returns the register that is associated with the initial-value
      variable [var] of the register.

      Returns [Error] if [var] is not an initial register value or if [var]
      cannot be found. *)
  method get_initial_register_value_register: variable_t -> register_t traceresult

  (** Returns [true] if [var] is a register variable of one of the MIPS
      argument registers (a0, a1, a2, or a3). *)
  method is_mips_argument_variable: variable_t -> bool

  (** Returns [true] if [var] is the initial-value variable of a MIPS
      argument register variable. *)
  method is_initial_mips_argument_value: variable_t -> bool

  (** Returns [true] if [var] is a register variable of one of the ARM
      argument registers (R0, R1, R2, R3) or double argument registers
      ((R0, R1), (R2, R3)). *)
  method is_arm_argument_variable: variable_t -> bool

  (** Returns [true] if [var] is a register variable of one of the ARM
      extension registers (e.g., floating point registers). *)
  method is_arm_extension_register_variable: variable_t -> bool

  (** Returns [true] if [var] is the initial-value variable of an ARM
      argument register variable. *)
  method is_initial_arm_argument_value: variable_t -> bool

  (** Returns [true] if [var] is the initial-value variable of the
      stack pointer (of any architecture) *)
  method is_initial_stackpointer_value: variable_t -> bool


  (** {2 Global variables} *)

  (** Returns [true] if [var] is a memory variable with a global base.*)
  method is_global_variable: variable_t -> bool

  (** Returns true if [var] is a global variable with a constant offset
      (i.e., a numerical value). *)
  method has_global_variable_address: variable_t -> bool

  (** [get_global_variable_address var] returns the global address of
      variable [var].

      Returns [Error] if [var] is not a global variable with a constant
      address. *)
  method get_global_variable_address: variable_t -> doubleword_result


  (** {2 Stack variables} *)

  (** Returns [true] if [var] is a memory variable located on the stack
      (either on the local stack frame or on the argument part of the stack). *)
  method is_stack_variable: variable_t -> bool

  (** Returns [true] if [var] is a memory variable located on a realigned
      portion of the stack (x86 only). *)
  method is_realigned_stack_variable: variable_t -> bool

  (** Returns [true] if [var] is a memory variable located on the stack
      with non-negative offset from the initial value of the stack pointer.

      Note: The first stack parameter for ARM is at 0.*)
  method is_stack_parameter_variable: variable_t -> bool

  (** Returns the index of the stack parameter variable [var] assuming
      4-byte parameters starting at offset 4 (x86 only).

      Returns None if the variable is not a stack parameter variable or if
      the variable cannot be found. *)
  method get_stack_parameter_index: variable_t -> (int option)

  (** Returns [true] if [var] is either a register variable or a stack
      variable (at any offset). *)
  method is_local_variable: variable_t -> bool


  (** {2 External base variable}

      External base variables are memory variables that have a base pointer
      that is a symbolic value, which can be any function-initial value,
      that is, the value of a variable upon function entry (e.g., the
      value of an argument) or the the value of a function return value
      or side-effect value.
   *)

  (** Returns [true] if [var] is a memory variable with a base provided
      by a fixed-value pointer. *)
  method is_basevar_memory_variable: variable_t -> bool

  (** [get_memvar_basevar var] returns the base variable of memory variable
      [var].

      Returns [Error] if [var] is not a memory variable with a basevar.*)
  method get_memvar_basevar: variable_t -> variable_t traceresult

  (** Returns [true] if [var] is the initial value of a memory variable
      with a base provided by a fixed-value pointer. *)
  method is_basevar_memory_value: variable_t -> bool

  (** [get_memval_basevar var] returns the base variable of the variable
      representing the memory variable value [var]

      Returns [Error] if [var] is not the initial value of a memory
      variable with a basevar.*)
  method get_memval_basevar: variable_t -> variable_t traceresult

  (** Returns [true] if [var] is a memory variable with an unknown base
      pointer. *)
  method is_unknown_base_memory_variable: variable_t -> bool

  (** Returns [true] if [var] is a memory variable with an unknown base
      pointer or with an unknown offset. *)
  method is_unknown_memory_variable: variable_t -> bool


  (** {2 Other symbolic values} *)

  (** {3 Function-call related} *)

  (** Returns [true] if [var] is the return value of a function call. *)
  method is_return_value: variable_t -> bool

  (** Returns [true] if [var] is a side-effect value of a function call
      (that is, the variable whose address was passed as an argument to a
      call). *)
  method is_sideeffect_value: variable_t -> bool

  (** Returns the address of the call-site of a function-return value or
      a function side-effect value.

      Returns [Error] if [var] is not a function-return value or
      a function side-effect value. *)
  method get_call_site: variable_t -> ctxt_iaddress_t traceresult

  (** Returns the name of the argument associated with the side-effect
      variable [var].

      Returns [Error] if [var] is not a function side-effect value.*)
  method get_se_argument_descriptor: variable_t -> string traceresult

  (** Returns [true] if [var] is associated with a call target. *)
  method is_calltarget_value: variable_t -> bool

  (** Returns the call target associated with call-target variable [var].

      Returns [Error] if [var] is not a call-target variable or if [var]
      cannot be found. *)
  method get_calltarget_value: variable_t -> call_target_t traceresult

  (** {3 Function pointer} *)

  (** Returns [true] if [var] represents a function pointer. *)
  method is_function_pointer: variable_t -> bool

  (** Returns the name of the function pointer associated with [var].

      Returns [Error] if [var] is not a function-pointer variable or if
      [var] cannot be found. *)
  method get_pointed_to_function_name: variable_t -> string traceresult

  (** {3 Frozen variables} *)

  (** Returns [true] if [var] is the frozen variable of a variable that
      appears in a test expression. *)
  method is_frozen_test_value: variable_t -> bool

  (** Returns the variable, test-address, and jump address associated with
      the variable frozen for a test expression.

      Returns [Error] if [var] is not a frozen variable, or if [var] cannot
      be found. *)
  method get_frozen_variable:
           variable_t
           -> (variable_t * ctxt_iaddress_t * ctxt_iaddress_t) traceresult

  (** [is_in_test_jump_range addr var] returns [true] if [var] is a frozen
      test value and [addr] is in between the instruction address of the
      test and the instruction address of the user of the test (jump
      instruction or other predicated instruction.

      Returns [Error] if [var] is not a frozen test value. *)
  method is_in_test_jump_range:
           ctxt_iaddress_t -> variable_t -> bool traceresult

  (**  {3 Bridge variables} *)

  (** Returns [true] if [var] is a frozen argument value to a call. *)
  method is_bridge_value: variable_t -> bool

  (** [is_bridge_value_at addr var] returns [true] if [var] is a frozen
      argument value to a call at instruction address [addr]. *)
  method is_bridge_value_at: ctxt_iaddress_t -> variable_t -> bool

  (** {3 Global side effect} *)

  (** Returns [true] if [var] is a global variable whose value is set as
      a side-effect. *)
  method is_global_sideeffect: variable_t -> bool

  (** Returns the address of the global variable whose value is set as
      a side-effect.

      Returns [Error] if [var] does not represent a global address or if
      [var] cannot be found. *)
  method get_global_sideeffect_target_address: variable_t -> doubleword_result

  (** {3 Symbolic value} *)

  (** Returns [true] if [var] encapsulates a fixed-value expression. *)
  method is_symbolic_value: variable_t -> bool

  (** Returns [true] if [var] encapsulates a signed fixed-value expression. *)
  method is_signed_symbolic_value: variable_t -> bool

  (** Returns the symbolic (fixed-value) expression represented by [var].

      Returns [Error] if [var] is not a symbolic expression variable or if
      [var] cannot be found. *)
  method get_symbolic_value_expr: variable_t -> xpr_t traceresult

  (** {3 Other} *)

  method is_function_initial_value: variable_t -> bool

  method is_special_variable: variable_t -> bool

  method is_runtime_constant: variable_t -> bool

  (** {1 Miscellaneous} *)

  method get_assembly_variables: assembly_variable_int list

  method get_external_variable_comparator: variable_comparator_t

end

(** {1 Global Memory Map} *)

type globalvalue_t =
  | GConstantString of string
  | GScalarValue of doubleword_int


(** Reference to a global location*)
type global_location_ref_t =
  | GLoad of doubleword_int * ctxt_iaddress_t * xpr_t * int * bool
  (** address of global location, instructions address of load
      instruction, load address, size of load, signed *)

  | GStore of
      doubleword_int * ctxt_iaddress_t * xpr_t * int * numerical_t option
  (** address of global location, instruction address of store
      instruction, store address, size of store, optional numerical value
      assigned *)

  | GAddressArgument of
      doubleword_int
      * ctxt_iaddress_t
      * int
      * xpr_t
      * btype_t
      * memory_offset_t option
    (** address of global location, instruction address of call
        instruction, index of argument (1-based), value of address argument,
        type of address argument, offset of address argument.*)


type global_location_rec_t = {
    gloc_name: string;
    gloc_address: doubleword_int;
    gloc_btype: btype_t;
    gloc_size: int option;
    gloc_is_readonly: bool;
    gloc_is_initialized: bool;
    gloc_initialvalue: globalvalue_t option;
    gloc_desc: string option;
    gloc_section: string option;
  }


(** Representation of a global location that provides access to size and type
    (immutable). *)
class type global_location_int =
  object
    method grec: global_location_rec_t
    method name: string
    method address: doubleword_int
    method btype: btype_t
    method size: int option
    method is_readonly: bool
    method is_initialized: bool
    method is_typed: bool
    method is_struct: bool
    method is_array: bool
    method initialvalue: globalvalue_t option
    method desc: string option
    method contains_address: doubleword_int -> bool

    (** [address_offset addr] returns the difference between [addr] and the
        base address of the location. If [addr] is an expression that contains
        symbolic values, the global address is taken as the largest constant
        term in the expression.

        If [addr] is not contained within the location (that is, if [addr] is
        less than the base address or larger than or equal to the base address
        plus the size of the location) an Error is returned.
     *)
    method address_offset: xpr_t -> xpr_t traceresult

    (** [address_memory_offset size btype addr] returns the symbolic offset
        that corresponds to the location of [addr] within the location. An
        optional [size] or [btype] can be provided to resolve potential
        ambiguities in the offset at a given offset. For example, address
        difference 0 in the struct

        {[
        struct s {
           char a[10];
           ....
        };
        ]}

        may have either one of the following three distinct offsets:

        {[
        (1) NoOffset
        (2) FieldOffset ((a, _), NoOffset)
        (3) FieldOffset ((a, _), ArrayIndexOffset (0, NoOffset)
        ]}

        By default the minimal offset (1) is returned. Offset (2) can be
        forced by either passing in [size=10] or [btype=TArray..]. Offset
        (3) can be forced by either passing in [size=1] or [btype=TInt...].

        An Error is returned if either
        - [addr] is not contained within the location, or
        - [addr] is greater than the base address of the location and the
          location is not typed, or
        - [addr] does nor correspond to a legitimate offset, or
        - the provided type or size cannot be matched to any offset.
     *)
    method address_memory_offset:
             ?tgtsize:int option
             -> ?tgtbtype:btype_t
             -> xpr_t
             -> memory_offset_t traceresult

    method has_elf_symbol: bool

    method write_xml: xml_element_int -> unit
  end


(** Container for global locations in the system in the data sections,
    including initialized and uninitialized (.bss) data, but typically
    excluding data contained within the .text section.*)
class type global_memory_map_int =
  object

    method set_section:
             readonly:bool
             -> initialized:bool
             -> string
             -> doubleword_int
             -> doubleword_int
             -> unit

    method add_location:
             ?name:string option
             -> ?desc:string option
             -> ?btype: btype_t
             -> ?initialvalue: globalvalue_t option
             -> ?size: int option
             -> doubleword_int
             -> global_location_int traceresult

    method add_gload:
             doubleword_int
             -> ctxt_iaddress_t
             -> xpr_t
             -> int
             -> bool
             -> unit

    method add_gstore:
             doubleword_int
             -> ctxt_iaddress_t
             -> xpr_t
             -> int
             -> numerical_t option
             -> unit

    method add_gaddr_argument:
             doubleword_int
             -> ctxt_iaddress_t
             -> xpr_t
             -> int
             -> btype_t
             -> global_location_int option

    method update_named_location:
             string -> bvarinfo_t -> global_location_int traceresult

    method has_location: doubleword_int -> bool

    method get_location: doubleword_int -> global_location_int

    method containing_location: doubleword_int -> global_location_int option

    method xpr_containing_location: xpr_t -> global_location_int option

    method get_location_name: doubleword_int -> string

    method get_location_type: doubleword_int -> btype_t

    method has_location_with_name: string -> bool

    method is_global_data_address: doubleword_int -> bool

    method has_elf_symbol: doubleword_int -> bool

    method get_elf_symbol: doubleword_int -> string

    method write_xml: xml_element_int -> unit

    method write_xml_references:
             doubleword_int -> vardictionary_int -> xml_element_int -> unit
  end



(* =========================================================== Function info === *)


(** @Deprecated Currenly used only for x86 *)
class type argument_values_int =
object
  method add_argument_values : variable_t -> xpr_t list -> unit
  method get_argument_values : variable_t -> xpr_t list
  method write_xml           : xml_element_int -> unit
  method read_xml            : xml_element_int -> unit
  method toPretty            : pretty_t
end

(** {1 Functions} *)

(** {2 Function symbol table} *)

(** Function environment: function symbol table that keeps track of all
    variables known to the function.*)
class type function_environment_int =
  object

    method varmgr : variable_manager_int
    method variable_names: variable_names_int

    (* setters *)

    (** [set_variable_name var name] associates [var] with the name [name]
        in the variable_names structure for this function.*)
    method set_variable_name: variable_t -> string -> unit

    method set_class_member_variable_names:
             (string * function_interface_t * bool) list -> unit
    method set_java_native_method_signature: java_native_method_api_t -> unit
    method set_unknown_java_native_method_signature: unit

    (** [set_argument_names addr fintf] creates variable names for all of the
        known arguments of the function interface of this function, and
        registers those names in the variable_names structure for this function.*)
    method set_argument_names: function_interface_t -> unit

    method set_argument_structconstant:
             fts_parameter_t -> c_struct_constant_t -> unit

    method register_virtual_call: variable_t -> function_interface_t -> unit

    (** {1 Creating refs/vars} *)

    (** {2 Memory references} *)

    method mk_unknown_memory_reference: string -> memory_reference_int
    method mk_global_memory_reference: memory_reference_int
    method mk_local_stack_reference: memory_reference_int
    method mk_realigned_stack_reference: memory_reference_int

    (** [mk_base_variable_reference var] returns a memory reference with
        base determined by [var].

        In particular, the initial value of a stack-pointer returns a
        stack-frame base; the initial value of other registers or of a
        function return value or memory value returns a basevar reference.
        A memory-address value returns a base-array or base-struct
        reference, depending on the type of the memory-address value.

        Returns an unknown-basevar memory variable if [var] cannot be used
        as a basevar.

        Returns [Error] if [var] cannot be found. *)
    method mk_base_variable_reference:
             variable_t -> memory_reference_int traceresult

    (** [mk_base_sym_reference sym] returns the memory reference for the
        variable determined by the index of [sym]
        (see [mk_base_variable_reference].

        Returns [Error] if the variable corresponding to [var] cannot be
        found. *)
    method mk_base_sym_reference:
             symbol_t -> memory_reference_int traceresult

    (** {2 Register variables} *)

    (** {3 x86} *)

    method mk_register_variable: register_t -> variable_t
    method mk_cpu_register_variable: cpureg_t -> variable_t
    method mk_fpu_register_variable: int -> variable_t
    method mk_mmx_register_variable: int -> variable_t
    method mk_xmm_register_variable: int -> variable_t
    method mk_control_register_variable: int -> variable_t
    method mk_debug_register_variable: int -> variable_t
    method mk_double_register_variable: cpureg_t -> cpureg_t -> variable_t

    (** {3 mips} *)

    method mk_mips_register_variable: mips_reg_t -> variable_t
    method mk_mips_special_register_variable: mips_special_reg_t -> variable_t
    method mk_mips_fp_register_variable: int -> variable_t

    (** {3 arm} *)

    method mk_arm_register_variable: arm_reg_t -> variable_t
    method mk_arm_extension_register_variable:
             arm_extension_register_t -> variable_t
    method mk_arm_extension_register_element_variable:
             arm_extension_register_element_t -> variable_t
    method mk_arm_special_register_variable:
             arm_special_reg_t -> variable_t
    method mk_arm_double_register_variable: arm_reg_t -> arm_reg_t -> variable_t
    method mk_arm_double_extension_register_variable:
             arm_extension_register_t -> arm_extension_register_t -> variable_t

    (** {3 power} *)

    method mk_pwr_gp_register_variable: int -> variable_t
    method mk_pwr_sp_register_variable: pwr_special_reg_t -> variable_t
    method mk_pwr_register_field_variable: pwr_register_field_t -> variable_t

    (** {2 Memory variables} *)

    method mk_global_variable:
             ?size:int
             -> ?btype:btype_t
             -> numerical_t
             -> variable_t traceresult

    method mk_gloc_variable:
             global_location_int -> memory_offset_t -> variable_t

    method mk_initial_memory_value: variable_t -> variable_t

    method mk_memory_variable:
             ?save_name:bool
             -> ?size:int
             -> memory_reference_int
             -> numerical_t
             -> variable_t
    method mk_index_offset_memory_variable:
             ?size:int
             -> memory_reference_int
             -> memory_offset_t
             -> variable_t
    method mk_index_offset_global_memory_variable:
             ?elementsize:int
             -> numerical_t
             -> memory_offset_t
             -> variable_t traceresult
    method mk_unknown_memory_variable: string -> variable_t

    (** {2 Other variables} *)

    method mk_initial_register_value: ?level:int -> register_t -> variable_t

    method mk_flag_variable: flag_t -> variable_t
    method mk_bridge_value: ctxt_iaddress_t -> int -> variable_t

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

    method get_variable_comparator: variable_t -> variable_t -> int

    (** {1 Deconstructing variables} *)

    (** {2 Basic} *)

    (** [get_variable index] returns the chif variable with index [index].

        Returns [Error] if [index] cannot be found. *)
    method get_variable: int -> variable_t traceresult

    method get_variable_type: variable_t -> btype_t option

    (** {2 Memory variables} *)

    (** Returns [true] only if [var] is a memory variable.

        Note: returns [false] if [var] is an initial_memory variable (i.e.,
        memory value variable). *)
    method is_memory_variable: variable_t -> bool

    (** Returns [true] if [var] is an initial memory value variable (i.e.,
        the initial value of a memory variable. *)
    method is_initial_memory_value: variable_t -> bool

    (** [get_memory_reference var] returns the memory reference of a memory
        variable or initial-value memory variable [var].

        Returns [Error] if [var] is not a memory variable or an initial-value
        memory variable. *)
    method get_memory_reference: variable_t -> memory_reference_int traceresult

    (** [get_memvar_offset var] returns the offset of memory variable [var].

        Returns [Error] if the variable is not found or the variable is
        not a memory variable. *)
    method get_memvar_offset: variable_t -> memory_offset_t traceresult

    (** [get_memval_offset var] returns the offset of the memory variable
        associated with the initial-value memory variable [var].

        Returns [Error] if the variable is not found or [var] is not
        an initial-value memory variable. *)
    method get_memval_offset: variable_t -> memory_offset_t traceresult

    (** [is_unknown_reference index] returns true if [index] is the index
        of a memory reference with base Unknown.

        Returns [Error] if [index] is not a valid index of a memory reference. *)
    method is_unknown_reference: int -> bool traceresult

    method has_variable_index_offset: variable_t -> bool


    (** {2 Memory offsets} *)

    (** Returns [true if [var] is a memory variable and its offset is a constant
        numerical value. *)
    method has_constant_offset: variable_t -> bool


    method add_memory_offset:
             variable_t -> memory_offset_t -> variable_t traceresult

    (** {2 Register variables} *)

    (** Returns [true] if [var] is a register variable (of any architecture). *)
    method is_register_variable: variable_t -> bool

    (** Returns [true] if [var] is a register variable that used by the current
        architecture as a stackpointer. *)
    method is_stackpointer_variable: variable_t -> bool

    (** Returns the register associated with [var].

        Returns [Error] if [var] is not a register variable or [var] cannot be
        found. *)
    method get_register: variable_t -> register_t traceresult

    (** Returns [true] if [var] is the initial-value variable of a register
        (of any architecture). *)
    method is_initial_register_value: variable_t -> bool

    (** Returns the register that is associated with the initial-value
        variable [var] of the register.

        Returns [Error] if [var] is not an initial register value or if [var]
        cannot be found. *)
    method get_initial_register_value_register:
             variable_t -> register_t traceresult

    (** Returns [true] if [var] is the initial-value variable of a MIPS
        argument register variable. *)
    method is_initial_mips_argument_value: variable_t -> bool

    (** Returns [true] if [var] is the initial-value variable of an ARM
        argument register variable. *)
    method is_initial_arm_argument_value: variable_t -> bool

    (** Returns [true] if [var] is the initial-value variable of the
        stack pointer (of any architecture) *)
    method is_initial_stackpointer_value : variable_t -> bool


    (** {2 Global variables} *)

    (** [is_global_variable var] returns [true] if [var] is a global variable
        or if [var] is the initial value of a global variable. *)
    method is_global_variable: variable_t -> bool

    (** Returns true if [var] is a global variable with a constant offset
        (i.e., a numerical value). *)
    method has_global_variable_address: variable_t -> bool

    (** [get_global_variable_address var] returns the global address of
        global variable [var] or of the global variable associated with
        the initial-value [var]

        Returns [Error] if [var] is not a global variable or the initial
        value of a global variable. *)
    method get_global_variable_address: variable_t -> doubleword_result

    (** {2 Stack variables} *)

    (** Returns [true] if [var] is a memory variable located on the stack
        (either on the local stack frame or on the argument part of the stack). *)
    method is_stack_variable: variable_t -> bool

    (** Returns [true] if [var] is a memory variable located on the stack
        with non-negative offset from the initial value of the stack pointer.

        Note: The first stack parameter for ARM is at 0.*)
    method is_stack_parameter_variable: variable_t -> bool

    (** Returns [true] if [var] is the initial-value variable of a
        stack-parameter variable. *)
    method is_stack_parameter_value: variable_t -> bool

    (** Returns the index of the stack parameter variable [var] or of the
        initial value [var] of the stack parameter variable, assuming 4-byte
        parameters starting at offset 4.

        Returns None if the variable is not a stack parameter variable or
        initial value of a stack parameter variable, or if the variable
        cannot be found.*)
    method get_stack_parameter_index: variable_t -> int option

    (** Returns [true] if [var] is either a register variable or a stack
        variable (at any offset). *)
    method is_local_variable: variable_t -> bool


    (** {2 External base variables} *)

    (** Returns [true] if [var] is a memory variable with a base provided
        by a fixed-value pointer. *)
    method is_basevar_memory_variable: variable_t -> bool

    (** [get_memvar_basevar var] returns the base variable of memory variable
        [var].

        Returns [Error] if [var] is not a memory variable with a basevar.*)
    method get_memvar_basevar: variable_t -> variable_t traceresult

    (** Returns [true] if [var] is the initial value of a memory variable
        with a base provided by a fixed-value pointer. *)

    method is_basevar_memory_value: variable_t -> bool

    (** [get_memval_basevar var] returns the base variable of the variable
        representing the memory variable value [var]

        Returns [Error] if [var] is not the initial value of a memory
        variable with a basevar.*)
    method get_memval_basevar: variable_t -> variable_t traceresult

    method get_optreturn_value_capabilities:
             variable_t -> (ctxt_iaddress_t * type_cap_label_t list)  option


    (** {2 Other symbolic values} *)

    (** {3 Function-call related) *)

    (** Returns [true] if [var] is the return value of a function call. *)
    method is_return_value: variable_t -> bool

    (** Returns [true] if [var] is a side-effect value of a function call
        (that is, the variable whose address was passed as an argument to a
        call). *)
    method is_sideeffect_value: variable_t -> bool

    (** Returns the address of the call-site of a function-return value or
        a function side-effect value.

        Returns [Error] if [var] is not a function-return value or
        a function side-effect value. *)
    method get_call_site: variable_t -> ctxt_iaddress_t traceresult

    (** Returns the name of the argument associated with the side-effect
        variable [var].

        Returns [Error] if [var] is not a function side-effect value.*)
    method get_se_argument_descriptor: variable_t -> string traceresult

    (** Returns [true] if [var] is associated with a call target. *)
    method is_calltarget_value: variable_t -> bool

    (** Returns the call target associated with call-target variable [var].

        Returns [Error] if [var] is not a call-target variable. *)
    method get_calltarget_value: variable_t -> call_target_t traceresult

    (** {3 Function pointer} *)

    (** Returns [true] if [var] represents a function pointer. *)
    method is_function_pointer: variable_t -> bool

    (** Returns the name of the function pointer associated with [var].

        Returns [Error] if [var] is not a function-pointer variable. *)
    method get_pointed_to_function_name: variable_t -> string traceresult

    (** {3 Frozen variables} *)

    (** Returns [true] if [var] is the frozen variable of a variable that
        appears in a test expression. *)
    method is_frozen_test_value: variable_t -> bool

    (** Returns the variable, test-address, and jump address associated with
        the variable frozen for a test expression.

        Returns [Error] if [var] is not a frozen variable, or if [var] cannot
        be found. *)
    method get_frozen_variable:
             variable_t
             -> (variable_t * ctxt_iaddress_t * ctxt_iaddress_t) traceresult

    (** [is_in_test_jump_range addr var] returns [true] if [var] is a frozen
        test value and [addr] is in between the instruction address of the
        test and the instruction address of the user of the test (jump
        instruction or other predicated instruction.

        Returns [Error] if [var] is not a frozen test value. *)
    method is_in_test_jump_range:
             variable_t -> ctxt_iaddress_t -> bool traceresult

    (** {3 Bridge variables} *)

    (** Returns [true] if [var] is a frozen argument value to a call. *)
    method is_bridge_value: variable_t -> bool

    (** [is_bridge_value_at addr var] returns [true] if [var] is a frozen
        argument value to a call at instruction address [addr]. *)
    method is_bridge_value_at: ctxt_iaddress_t -> variable_t -> bool

    (** {3 Global side effect} *)

    (** Returns [true] if [var] is a global variable whose value is set as
        a side-effect. *)
    method is_global_sideeffect: variable_t -> bool

    (** Returns the address of the global variable whose value is set as
        a side-effect.

        Returns [Error] if [var] does not represent a global address. *)
    method get_global_sideeffect_target_address: variable_t -> doubleword_result

    (** {3 Symbolic expressions} *)

    (** Returns [true] if [var] encapsulates a fixed-value expression. *)
    method is_symbolic_value: variable_t -> bool

    (** Returns [true] if [var] encapsulates a signed fixed-value expression. *)
    method is_signed_symbolic_value: variable_t -> bool

    (** Returns the symbolic (fixed-value) expression represented by [var].

        Returns [Error] if [var] is not a symbolic expression variable.*)
    method get_symbolic_value_expr: variable_t -> xpr_t traceresult

    (** {3 Other} *)

    method is_function_initial_value: variable_t -> bool

    method is_initial_value: variable_t -> bool

    method get_init_value_variable: variable_t -> variable_t traceresult

    (** {1 Variable collections} *)

    method get_local_stack_variables: variable_t list
    method get_realigned_stack_variables: variable_t list
    method get_parent_stack_variables: variable_t list
    method get_mips_argument_values: variable_t list
    method get_arm_argument_values: variable_t list
    method get_bridge_values_at: ctxt_iaddress_t -> variable_t list
    method get_selected_variables: (variable_t -> bool) -> variable_t list

    method get_variables: variable_t list
    method get_sym_variables: variable_t list
    method get_domain_sym_variables: string -> variable_t list
    method get_symbolic_num_variable: variable_t -> variable_t traceresult
    method get_local_variables: variable_t list
    method get_external_memory_variables: variable_t list
    method get_virtual_target : variable_t -> function_interface_t

    method get_var_count: int
    method get_globalvar_count: int
    method get_returnvar_count: int
    method get_sideeffvar_count: int

    method get_constant_offsets: variable_t -> numerical_t list option
    method get_total_constant_offset: variable_t -> numerical_t option

    method get_argbasevar_with_offsets:
             variable_t -> (variable_t * numerical_t list) option
    method get_globalbasevar_with_offsets:
             variable_t -> (variable_t * numerical_t list) option

    method get_initialized_call_target_value: variable_t -> call_target_t
    method get_initialized_string_value: variable_t -> int -> string

    method variables_in_expr: xpr_t -> variable_t list

    (** {1 Scope and transactions} *)

    method get_scope: scope_int
    method start_transaction: unit
    method end_transaction: cmd_t list
    method mk_num_temp: variable_t
    method mk_sym_temp: variable_t
    method request_num_constant: numerical_t -> variable_t
    method mk_symbolic_variable: ?domains:string list -> variable_t -> variable_t

    (* variable manager predicates *)

    method is_unknown_base_memory_variable: variable_t -> bool
    method is_unknown_offset_memory_variable: variable_t -> bool
    method is_unknown_memory_variable: variable_t -> bool

    method is_volatile_variable: variable_t -> bool

    (** {1 Envionment data predicates} *)

    method is_virtual_call : variable_t -> bool
    method has_initialized_call_target_value: variable_t -> bool
    method has_initialized_string_value     : variable_t -> int -> bool

    (** {1 Printing} *)

    method variable_name_to_string: variable_t -> string
    method variable_name_to_pretty: variable_t -> pretty_t

  end


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

    method get_preconditions: xxpredicate_t list
    method get_postconditions: xxpredicate_t list
    method get_errorpostconditions: xxpredicate_t list
    method get_sideeffects: xxpredicate_t list
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


(** {2 Function-info} *)

class type xpodictionary_int =
  object

    method reset: unit

    method xd: xprdictionary_int

    method index_xpo_predicate: xpo_predicate_t -> int

    method write_xml_xpo_predicate:
             ?tag:string -> xml_element_int -> xpo_predicate_t -> unit

    method write_xml: xml_element_int -> unit
  end


class type stackframe_int =
  object

    method add_register_spill:
             offset:int -> register_t -> ctxt_iaddress_t -> unit
    method add_register_restore:
             offset:int -> register_t -> ctxt_iaddress_t -> unit

    method add_load:
             offset:int
             -> size:int option
             -> typ:btype_t option
             -> variable_t
             -> ctxt_iaddress_t
             -> unit

    method add_store:
             offset:int
             -> size:int option
             -> typ:btype_t option
             -> xpr:xpr_t option
             -> variable_t
             -> ctxt_iaddress_t
             -> unit

    method add_block_read:
             offset:int
             -> size:int option
             -> typ:btype_t option
             -> ctxt_iaddress_t
             -> unit
    method add_block_write:
             offset:int
             -> size:int option
             -> typ:btype_t option
             -> xpr:xpr_t option
             -> ctxt_iaddress_t
             -> unit

    method write_xml: xml_element_int -> unit

  end


type po_status_t =
  | Discharged of string
  | Delegated of xxpredicate_t
  | Requested of doubleword_int * xxpredicate_t
  | DelegatedGlobal of doubleword_int * xxpredicate_t
  | Violated of string
  | Open


class type proofobligation_int =
  object

    method xpo: xpo_predicate_t

    method loc: location_int

    method status: po_status_t

  end


class type proofobligations_int =
  object

    method faddr: doubleword_int

    method xpod: xpodictionary_int

    method add_proofobligation:
             ctxt_iaddress_t -> xpo_predicate_t -> po_status_t -> unit

    method loc_proofobligations:
             ctxt_iaddress_t -> proofobligation_int list

    method open_proofobligations: proofobligation_int list

    method discharged_proofobligations: proofobligation_int list

    method violated_proofobligations: proofobligation_int list

    method delegated_proofobligations: proofobligation_int list

    method write_xml: xml_element_int -> unit

  end

(** {b Principal access point for function characteristics and analysis results.}

    This data structure keeps track of:
    - variables known to the function
    - call targets
    - jump targets

    It also maintains a summary of the function api and semantics.
*)
class type function_info_int =
object

  (** {1 Address and symboltable}*)

  (** Returns the address of the function.*)
  method a: doubleword_int

  (** Returns the address of the function.*)
  method get_address: doubleword_int

  (** Returns the name of the function.*)
  method get_name: string

  (** Returns the function symbol table containing all variables.*)
  method env: function_environment_int

  (** Returns the local stackframe of the function *)
  method stackframe: stackframe_int

  (** Returns the xpo-dictionary to index proof obligations *)
  method xpod: xpodictionary_int

  (** Returns the object containing all active proof obligations.*)
  method proofobligations: proofobligations_int


  (** {1 Function invariants} *)

  (** {2 Accessors} *)

  (** Returns the access point for all value invariants for this function.*)
  method finv: invariant_io_int

  (** Returns the access point for all variable invariants for this function.*)
  method fvarinv: var_invariant_io_int  (* function variables invariant *)

  (** [finfo#iinv iaddr] returns the value invariant at instruction address
      [iaddr].*)
  method iinv : ctxt_iaddress_t -> location_invariant_int

  (** [finfo#ivarinv idadr] returns the variable invariant at instruction address
      [iaddr].*)
  method ivarinv: ctxt_iaddress_t -> location_var_invariant_int

  method add_reaching_def: string -> variable_t -> symbol_t list -> unit

  method add_use_loc: variable_t -> string -> unit

  method add_use_high_loc: variable_t -> string -> unit

  method is_use_loc: variable_t -> string -> bool

  method is_use_high_loc: variable_t -> string -> bool

  (** {2 Invariant reset}

   Note: currently used only for x86.
   *)

  (** Indicate change that requires invariants to be invalidated.*)
  method schedule_invariant_reset: unit

  (** Remove all invariants if there was a prior invariant reset scheduled.*)
  method reset_invariants: unit

  (** Returns true if invariants were reset.*)
  method were_invariants_reset: bool

  (** Returns true if the side effects of this function have changed since
      the beginning of the analysis round.

      Note: this is used
      (1) to determine if invariants are to be reset for callers of this
      function, and
      (2) to determine if the analysis of a function has stabilized.
   *)
  method sideeffects_changed: bool

  (** Returns true if call targets were set since the beginning of the
      analysis round. This is used in determining whether analysis has
      of the function has stabilized.*)
  method call_targets_were_set: bool


  (** {1 Function attributes} *)

  (** Declare that all relevant information about a function is known.

      In particular, this means that (1) all instructions are known, and (2) all
      indirect jumps are resolved (i.e., all code is identified). Not necessarily
      all indirect calls are resolved. This value is the default.
      If a function is not complete its summary is not used for calls to this
      function; instead a default summary is used.*)
  method set_complete: unit

  (** Declare that not all relevant information about a function is known *)
  method set_incomplete: unit

  (** Returns true if the associated function is considered complete.*)
  method is_complete: bool

  (** {2 Function return}*)

  (** Declares that this function is non-returning.*)
  method set_nonreturning: unit

  (** [finfo#record_return_value iaddr xpr] records that the function
      returns value [xpr] at return instruction [iaddr].*)
  method record_return_value: ctxt_iaddress_t -> xpr_t -> unit

  (** Returns the function return values recorded for this function.*)
  method get_return_values: xpr_t list


  (* method set_dynlib_stub: call_target_t -> unit *)

  (** {2 Instruction bytes} *)

  (** [finfo#set_instruction_bytes iaddr b] associates the hexadecimal
      representation of the instruction at address [iaddr] with that address.*)
  method set_instruction_bytes: ctxt_iaddress_t -> string -> unit

  (** finfo#get_instruction_bytes iaddr] returns the hexadecimal
      representation of the instruction bytes for the instruction at address
      [iaddr].*)
  method get_instruction_bytes: ctxt_iaddress_t -> string


  (** {2 Auxiliary variables} *)

  (** [finfo#add_constant var num] registers the fact that auxiliary
      variable [var] (usually a bridge variable representing the argument
      to a function call) has the constant value [num] in the function. *)
  method add_constant: variable_t -> numerical_t -> unit

  (** [finfo#has_constant var] returns true if auxiliary variable [var] has
      a constant value registered in the function. *)
  method has_constant: variable_t -> bool

  (** [finfo#get_constant var] returns the constant value registered
      earlier for auxiliary variable [var].

      @raise [Invocation_error] if no constant is associated with [var].
   *)
  method get_constant: variable_t -> numerical_t

  (** {2 Stack adjustment (PE only)} *)

  (** [finfo#set_stack_adjustment (Some n)] sets the number of bytes that are
      popped off the stack by this function when it returns from a call.*)
  method set_stack_adjustment: int option -> unit

  (** Returns the number of bytes that are popped off the stack by this function
      when it returns from a call, or None, if no bytes are popped off (or if the
      number is unknown).*)
  method get_stack_adjustment: int option

  (** {2 Base pointers}*)

  (** [finfo#add_base_pointer var] declares [var] to be pointer that is
      dereferenced within the function.

      [var] must be a constant-value variable (i.e., a symbolic constant in
      the function) to be a valid base pointer.

      Adding a variable as a base pointer has the effect of adding it, in the
      next analysis round, as a base to the value set domain. *)
  method add_base_pointer: variable_t -> unit

  (** Returns the list of variables that were declared to be base pointers.*)
  method get_base_pointers: variable_t list

  (** [finfo#is_base_pointer var] returns true if variable [var] is registered
      as a base pointer.*)
  method is_base_pointer: variable_t -> bool


  (** {2 Spilled registers} *)

  (** [finfo#save_register vmem iaddr reg] declares that register [reg] is saved
      (spilled) to the stack in variable [vmem] by the instruction at address
      [iaddr].*)
  method save_register: variable_t -> ctxt_iaddress_t -> register_t -> unit

  (** [finfo#restore_register memaddr iaddr reg] declares that register [reg] is
      restored from the stack at stacklocation [memaddr] by the instruction at
      address [iaddr].*)
  method restore_register: xpr_t -> ctxt_iaddress_t -> register_t -> unit


  (** {2 Auxvar types}

      The types set and retrieved are inferred variable types for constant-value
      variables. Inferences are based on their appearance in certain instructions
      or operations performed on them. Throughout the analysis different aspects
      may be revealed, and a list of these is maintained.*)

  (** [finfo#set_btype v ty] records type [ty] for variable [v].*)
  method set_btype: variable_t -> btype_t -> unit

  (** [finfo#has_btype v] returns true if at least one type has been recorded for
      variable [v].*)
  method has_btype: variable_t -> bool

  (** [finfo#get_btype v] returns the join of all types that have been recorded
      for variable [v]. If no types were recorded [t_unknown] is returned.*)
  method get_btype: variable_t -> btype_t

  (** [finfo#get_btypes v] returns all types that have been recorded for
      variable [v]. If no types were recorded the empty list is returned.*)
  method get_btypes: variable_t -> btype_t list

  (** Returns a list of indexed variable type records, where each entry
      represents (index of variable, index of joined type, indices of all
      types).*)
  method get_btype_table: (int * int * int list) list


  (** {1 Function summaries}
      Information registered to create a function summary for the application
      function represented by this function_info (possibly including global
      variables that are accessed and/or modified by the function).*)

  (** [finfo#set_bc_summary fsum] sets the app-summary to be [fsum].*)
  method set_bc_summary: function_summary_int -> unit

  (** [finfo#read_xml_user_summary xnode] extracts the user-summary from its
      xml representation in [xnode].*)
  method read_xml_user_summary: xml_element_int -> unit

  (** Returns a summary of the known, externally observable behavior of this
      function.

      Note that this information may be incomplete if it is constructed based
      on analysis results available so far. Summaries are updated in every
      round of analysis, and so tend to improve as analysis progresses.*)
  method get_summary: function_summary_int

  method update_summary: function_summary_int -> unit


  (** {2 Function signature}*)

  (** [finfo#set_java_native_method_signature api] sets the app summary
      with signature [api] and default semantics.*)
  method set_java_native_method_signature: java_native_method_api_t -> unit

  (** Creates the standard [jni$Env] parameter for a java native method.

      Note: it does not set the app summary with this signature.*)
  method set_unknown_java_native_method_signature: unit


  (** {2 Side effects}*)

  (** [finfo#record_sideeffect iaddr se] records side effect [se] (i.e.,
      an effect that is observable outside of the function, such as writing
      through a pointer provided as argument) at instruction address [iaddr].

      This method is currently called only when an assignment is performed
      with a left-hand-side that is an external memory reference.
   *)
  method record_sideeffect: ctxt_iaddress_t -> xxpredicate_t -> unit


  (** {1 Condition codes}
      The function info keeps track of test expressions and the variables used
      therein for conditional jump instructions. These methods are used mainly
      by architectures that use condition codes in the processor status word
      that are set by a test instruction and then used by a subsequent conditional
      jump instruction. However, they are also used for predicated instructions
      (as, e.g., in ARM/Thumb-2) or for the SET<cc> instructions in x86.*)

  (** {2 Test expressions}*)

  (** [set_test_expr iaddr xpr] records test expression [xpr] for the
      conditional jump instruction at [iaddr] *)
  method set_test_expr: ctxt_iaddress_t -> xpr_t -> unit

  (** Returns a list of all registered test expressions together with the
      address of the test instruction.*)
  method get_test_exprs: (ctxt_iaddress_t * xpr_t) list

  (** [get_test_expr iaddr] returns the test expression created by the test
      instruction at [iaddr].

      Returns a random constant if no test expression is found.*)
  method get_test_expr: ctxt_iaddress_t -> xpr_t

  (** [finfo#has_test_expr iaddr] returns true if a test expression is
      registered for instruction address [iaddr].*)
  method has_test_expr: ctxt_iaddress_t -> bool

  (** [finfo#set_test_variables iaddr vmap] records the variable mapping [vmap]
      between regular function variables and auxiliary variables created
      (variables frozen at a particular location) at the address of the test
      instruction [iaddr].*)
  method set_test_variables:
           ctxt_iaddress_t -> (variable_t * variable_t) list -> unit

  (** [finfo#get_test_variables iaddr] returns the mapping of test variables
      that were registered for the instruction at [iaddr].

      Returns the empty list if no test variables were registered for that
      address.*)
  method get_test_variables:
           ctxt_iaddress_t -> (variable_t * variable_t) list

  (** {2 Connections}*)

  (** [finfo#connect_cc_user u_iaddr s_iaddr] records that the instruction at
      address [u_addr] uses the test expression set by the instruction at
      address [s_addr]. Usually the user is a conditional jump and the
      setter is a test instruction (e.g., CMP) that sets the condition
      codes in the processor status word.*)
  method connect_cc_user: ctxt_iaddress_t -> ctxt_iaddress_t -> unit

  (** [finfo#has_associated_cc_setter iaddr] returns true if the instruction
      at address [iaddr] uses a test expression that is registered to have
      been set by another instruction.*)
  method has_associated_cc_setter: ctxt_iaddress_t -> bool

  (** [finfo#get_associated_cc_setter iaddr] returns the address of the
      instruction that sets the condition code used by the instruction at
      [iaddr].

      @raise [BCH_failure] if the instruction at [iaddr] does not have an
      associated setter.*)
  method get_associated_cc_setter: ctxt_iaddress_t -> ctxt_iaddress_t

  (** [finfo#has_associated_cc_user iaddr] returns true if the instruction
      at address [iaddr] sets a test expression that is registered to be
      used by another instruction.*)
  method has_associated_cc_user: ctxt_iaddress_t -> bool

  (** [finfo#get_associated_cc_user iaddr] returns the address of the instruction
      that uses the condition set by the instruction at [iaddr].

      @raise [BCH_failure] if the instruction at [iaddr] does not have an
      associated user.*)
  method get_associated_cc_user: ctxt_iaddress_t -> ctxt_iaddress_t

  (** {2 Statistics}*)

  (** Returns the number of conditions that are associated with test expressions
      in this function.*)
  method get_num_conditions_associated: int

  (** Returns the number of test expressions recorded in this function.*)
  method get_num_test_expressions: int


  (** {1 Indirect jumps}*)

  (** [finfo#set_jumptable_target iaddr base jt reg] registers jumptable [jt]
      with base address [base] to be the target of the indirect jump instruction
      at [iaddr] with the selector value in register [reg].*)
  method set_jumptable_target:
           ctxt_iaddress_t -> doubleword_int -> jumptable_int -> register_t -> unit

  method set_offsettable_target:
    ctxt_iaddress_t -> doubleword_int -> jumptable_int -> data_block_int -> unit
  method set_global_jumptarget: ctxt_iaddress_t -> variable_t -> unit

  method set_dll_jumptarget:
           ctxt_iaddress_t -> string -> string -> call_target_info_int -> unit
  method set_so_jumptarget:
           ctxt_iaddress_t -> string -> call_target_info_int -> unit
  method set_unknown_jumptarget : ctxt_iaddress_t -> unit

  method get_dll_jumptarget: ctxt_iaddress_t -> (string * string)
  method get_jump_target: ctxt_iaddress_t -> jump_target_t
  method get_jumptable_jumps: ctxt_iaddress_t list

  method is_dll_jumptarget: ctxt_iaddress_t -> bool
  method has_jump_target: ctxt_iaddress_t -> bool
  method has_unknown_jump_target : bool


  (** {2 Statistics} *)

  method get_jumptable_count: int
  method get_offsettable_count: int
  method get_global_jump_count: int
  method get_argument_jump_count: int
  method get_unknown_jumps_count: int
  method get_dll_jumps_count: int
  method get_indirect_jumps_count: int

  (** Returns the number of call targets registered for this function.*)
  method get_call_count: int

  (** [get_call_category_count name] returns the number of call targets
      in the category named [name].*)
  method get_call_category_count: string -> int

  (** {1 Call targets}*)

  (** [finfo#set_call_target iaddr cti] registers a call target [cti] at
      instruction address [iaddr].*)
  method set_call_target: ctxt_iaddress_t -> call_target_info_int -> unit

  (** [finfo#get_call_target iaddr] returns the call target registered at
      instruction address [iaddr]. [UnknownTarget] is returned if no call
      target is registered at [iaddr].*)
  method get_call_target: ctxt_iaddress_t -> call_target_info_int

  (** [finfo#has_call_target iaddr] returns true if a call target is
      registered at instruction address [iaddr].*)
  method has_call_target: ctxt_iaddress_t -> bool

  (** Returns the call targets registered in this function.*)
  method get_callees: call_target_info_int list

  (** Returns the call targets registered in this function, coupled with
      the address of the associated call instruction.*)
  method get_callees_located: (ctxt_iaddress_t * call_target_info_int) list

  (** {1 Save and restore}*)

  (** [finfo#write_xml xnode] writes the internal state of the function-info
      to xml element [xnode].*)
  method write_xml: xml_element_int -> unit

  (** [finfo#read_xml xnode] initializes the function-info with with data
      extracted from xml element [xnode].*)
  method read_xml: xml_element_int -> unit

  (** Saves the function info in [a/functions/<fname>/<fname>_finfo.xml].*)
  method save: unit

  (** {1 Printing}*)

  method state_to_pretty: pretty_t
  method summary_to_pretty: pretty_t
  method saved_registers_to_pretty: pretty_t
  method base_pointers_to_pretty: pretty_t
  method return_values_to_pretty: pretty_t

end


(** {2 Floc} *)

(** Records stack, global, or heap memory accesses performed by a
    particular instruction *)
class type memory_recorder_int =
  object

    method finfo: function_info_int

    method iaddr: ctxt_iaddress_t

    method record_assignment:
             variable_t
             -> xpr_t
             -> ?size:int option
             -> ?vtype:btype_t
             -> unit
             -> unit

    method record_argument:
             ?btype:btype_t
             -> xpr_t
             -> int
             -> global_location_int option

    method record_load:
             signed:bool
             -> addr:xpr_t
             -> var:variable_t
             -> size:int
             -> vtype:btype_t
             -> unit

    method record_store:
             addr:xpr_t
             -> var:variable_t
             -> size:int
             -> vtype:btype_t
             -> xpr:xpr_t
             -> unit

  end


(** Propagator for types encountered in a function call to the function api *)
class type argument_type_propagator_int =
  object

    method finfo: function_info_int

    method callargs: (fts_parameter_t * xpr_t) list

    (** Identifies function call arguments that are arguments of the caller
        function and propagates their types to the caller's function interface.*)
    method elevate_call_arguments: unit

  end


class type expression_externalizer_int =
  object

    method finfo: function_info_int

    method xpr_to_bterm: btype_t -> xpr_t -> bterm_t option

  end

(** Evaluator of terms used in a particular function call.*)
class type bterm_evaluator_int =
  object

    (** Return the function info in which context the term is to be evaluated.*)
    method finfo: function_info_int

    (** [bterm_xpr t] returns the expression with which [t] was instantiated
        in the call.*)
    method bterm_xpr: bterm_t -> xpr_t option

    (** [xpr_local_stack_address x] returns the stack offset (from the initial
        value of the stack pointer at function entry) if [x] is a stack address
        and None otherwise.*)
    method xpr_local_stack_address: xpr_t -> int option

    (** [bterm_stack_address t] returns the expression with which [t] was
        instantiated if that expression is a stack address, otherwise None.*)
    method bterm_stack_address: bterm_t -> xpr_t option

    (** [constant_bterm t] returns a constant-value bterm if the corresponding
        argument to [t] is a constant, or if the original term was a constant*)
    method constant_bterm: bterm_t -> bterm_t option

  end


(** Propagator for preconditions, and side effects of a function call to the
    function api.*)
class type call_semantics_propagator_int =
  object

    method termev: bterm_evaluator_int

    method propagate_precondition: xxpredicate_t -> xxpredicate_t option

    method propagate_sideeffect: xxpredicate_t -> xxpredicate_t option
  end


class type call_semantics_recorder_int =
  object

    method loc: location_int

    method termev: bterm_evaluator_int

    method calltargetinfo: call_target_info_int

    method finfo: function_info_int

    method record_precondition: xxpredicate_t -> unit

    method record_sideeffect: xxpredicate_t -> unit

    method record_callsemantics: unit

  end


(** Floc (location in a function): principal access point for information
    associated with a single instruction. *)
class type floc_int =
  object

    (** {1 Addresses and symboltable} *)

    (** Returns the address of this instruction.*)
    method ia: doubleword_int

    (** Returns the full context of the address of this instruction. *)
    method cia: ctxt_iaddress_t

    (** Returns the address of the function this instruction belongs to.*)
    method fa: doubleword_int

    (** Returns the location of this instruction. *)
    method l: location_int

    (** Returns the function-info of the function this instruction belongs to.*)
    method f: function_info_int

    method memrecorder: memory_recorder_int

    (** {2 Symbol table}*)

    (** Returns the symbol table of the function this instruction belongs to.*)
    method env: function_environment_int

    (** {2 Instruction bytes}*)

    (** Associate instruction bytes (as a hex string) with instruction *)
    method set_instruction_bytes: string -> unit

    (** Returns the bytes of the instruction as a hexstring *)
    method get_instruction_bytes: string

    (** {1 Variables} *)

    (** {1 Invariants} *)

    (** {2 Accessors} *)

    (** Returns the value invariants for this instruction.*)
    method inv: location_invariant_int

    (** Returns the variable invariants for this instruction.*)
    method varinv: location_var_invariant_int

    (** {2 Retrieve invariants/rewriting} *)

    (* rewrites the variable to an expression with external variables *)
    method rewrite_variable_to_external: variable_t -> xpr_t

    (* converts an expr into a list of expressions based on variables of
       another function *)
    method externalize_expr: doubleword_int -> xpr_t -> bterm_t list

    (* returns the constant value of a variable at this instruction *)
    method get_constant: variable_t -> numerical_t

    (* returns the interval value of a variable at this instruction *)
    method get_interval: variable_t -> interval_t

    (** {2 Resolve memory variable}*)

    (* returns the memory reference corresponding to the address in
       variable plus offset *)
    method get_memory_variable_1:
           ?align:int -> ?size:int -> variable_t -> numerical_t -> variable_t

    (* returns the memory reference corresponding to a base and index
       variable plus offset *)
    method get_memory_variable_2:
             ?size:int -> variable_t -> variable_t -> numerical_t -> variable_t

    (* returns the memory reference corresponding to a base and scaled index
       variable plus offset *)
    method get_memory_variable_3:
             ?size:int
             -> variable_t
             -> variable_t
             -> int
             -> numerical_t
             -> variable_t

    (* returns the memory reference corresponding to a global base and scaled
       index variable *)
    method get_memory_variable_4: variable_t -> int -> numerical_t -> variable_t

    (* returns the memory reference that corresponds to the address expression *)
    method decompose_address: xpr_t -> (memory_reference_int * memory_offset_t)

    (* returns the variable associated with the address expression *)
    method get_lhs_from_address: xpr_t -> variable_t

    (* returns the value of the bridge variable for a given stack
       parameter at this instruction *)
    method get_bridge_variable_value: int -> variable_t -> xpr_t

    (* returns the difference between esp and the location of the return address,
       or the difference between esp and a level of alignment indicated with the
       first returned value *)
    method get_stackpointer_offset: string -> int * interval_t

    method get_singleton_stackpointer_offset: numerical_t traceresult

    method get_var_at_address:
             ?size:int option       (** size of the argument, in bytes *)
             -> ?btype:btype_t      (** type of argument *)
             -> xpr_t               (** address value *)
             -> variable_t traceresult

    (** {2 Predicates on variables}*)

    (* returns true if the given variable evaluates to a constant at this
       location. *)
    method is_constant: variable_t -> bool

    (* returns true if the given variable evaluates to a non-trivial interval
       at this location *)
    method is_interval: variable_t -> bool

    (* returns true if the given expression is a memory address *)
    method is_address : xpr_t -> bool

    method is_base_offset: variable_t -> bool

    (* returns true if the given variable evaluates to an initial value of a
       register *)
    method has_initial_value: variable_t -> bool


    (** {1 Conditional jumps}*)

    (* sets the test expression for this instruction *)
    method set_test_expr: xpr_t -> unit

    (* sets the mapping between auxiliary variables and regular variables for a
       test expression *)
    method set_test_variables: (variable_t * variable_t) list -> unit

    (* returns the test expression for a conditional jump in this instruction *)
    method get_test_expr: xpr_t

    (* returns the auxiliary variables used in a test expression *)
    method get_test_variables: (variable_t * variable_t) list

    (* returns true if this instruction has a test expression for a conditional
       jump. *)
    method has_test_expr: bool

    (** {1 Jump targets}*)

    (** [set_jumptable_target base jt reg] registers jumptable [jt] with base
        address [base] to be target of this instruction (assumed to be an
        indirect jump instruction) with the selector value in register [reg].*)
    method set_jumptable_target:
             doubleword_int -> jumptable_int -> register_t -> unit

    (* returns the targets for the indirect jump instruction *)
    method get_jump_target: jump_target_t

    (* returns true if this instruction has jump table targets *)
    method has_jump_target: bool

    method get_jump_successors: doubleword_int list

    (** {1 Call targets}*)

    method set_call_target: call_target_info_int -> unit

    method has_call_target: bool

    method update_call_target: unit

    method get_call_target: call_target_info_int
    method get_call_args: (fts_parameter_t * xpr_t) list
    method get_call_arguments: (fts_parameter_t * xpr_t) list

    (** {1 Function summary}*)

    (* evaluates the value of eax at this location and reports it to the function
       info *)
    method record_return_value: unit

    method evaluate_summary_address_term: bterm_t -> variable_t option

    method evaluate_summary_term: bterm_t -> variable_t -> xpr_t

  (* returns the value of the nth argument (starting from 1) to this call
     instruction *)
    method get_function_arg_value: int -> xpr_t

    (* returns the value of an api parameter *)
    method get_fts_parameter_expr: fts_parameter_t -> xpr_t option


    (** {1 CHIF code generation}*)

    (** {2 Calls} *)

    (** returns the CHIF code associated with the call instruction (x86) *)
    method get_call_commands: (doubleword_int -> string option) -> cmd_t list

    (** returns the CHIF code associated with the call instruction (mips) *)
    method get_mips_call_commands: cmd_t list
    method get_mips_syscall_commands: cmd_t list

    (** returns the CHIF code associated with the call instruction (arm) *)
    method get_arm_call_commands: cmd_t list

    (** returns the CHIF code associated with the call instruction (power32) *)
    method get_pwr_call_commands: cmd_t list

    (** {2 Assignments} *)

    (** [floc#get_assign_commands var ~size ~vtype xpr] returns the CHIF commands
        representing the assignment [var := xpr].

        If [size] is not None and the left-hand side [var] is externally observable
        (e.g., it is a memory write with external base) an external block-write is
        recorded for this instruction for the enclosing function.

        If [vtype] is known type facts are added for both [var] and [xpr] for this
        instruction.
     *)
    method get_assign_commands:
             variable_t
             -> ?size:xpr_t
             -> ?vtype:btype_t
             -> xpr_t
             -> cmd_t list

    (** [floc#get_ssa_assign_commands reg ~vtype xpr] creates an ssa-register
        variable [ssavar] for the current context address and returns
        a tuple of the register-variable, and the CHIF commands representing
        the assignment and assert-equal:
        {[ reg := xpr
           assert (reg = ssavar)
        ]} *)
    method get_ssa_assign_commands:
             register_t
             -> ?vtype:btype_t
             -> xpr_t ->
             variable_t * cmd_t list

    method get_conditional_assign_commands:
             xpr_t -> variable_t -> xpr_t -> cmd_t list

    method get_sideeffect_assigns: function_semantics_t -> cmd_t list

    (** {2 Variable abstraction}*)

    (* returns the CHIF code associated with an abstraction of variables *)
    method get_abstract_commands:
             variable_t -> ?size:xpr_t -> ?vtype:btype_t -> unit -> cmd_t list

    (** floc#[get_ssa_abstract_commands reg ()] creates an ssa-register
        variable [ssavar] for the current context address and returns a tuple of
        the register-variable and the CHIF commands representing the assignment
        {[ reg := ssavar ]}*)
    method get_ssa_abstract_commands:
             register_t -> unit -> (variable_t * cmd_t list)

    method get_abstract_cpu_registers_command: cpureg_t list -> cmd_t

    method get_abstract_registers_command: register_t list -> cmd_t

    (** {2 Operations}*)

    (* returns the CHIF code associated with an unmodeled operation *)
    method get_operation_commands:
             variable_t
             -> ?size:xpr_t
             -> ?vtype:btype_t
             -> symbol_t
             -> op_arg_t list
             -> cmd_t list

    (* returns the CHIF code to set definition/use instruction addresses *)
    method get_vardef_commands:
             ?defs:variable_t list
             -> ?clobbers:variable_t list
             -> ?use:variable_t list
             -> ?usehigh:variable_t list
             -> ?flagdefs:variable_t list
             -> string
             -> cmd_t list

    (** {1 Printing}*)

    method stackpointer_offset_to_string: string -> string

end


(** {1 User data}*)

(** {2 Specializations} *)

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

(** {2 Section header info}*)

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
    method get_flags: doubleword_int
    method get_addralign: doubleword_int
    method get_entsize: doubleword_int

    (* predicates *)
    method is_new: bool
    method has_addr: bool
    method has_offset: bool
    method has_size: bool
    method has_type: bool
    method has_link: bool
    method has_info: bool
    method has_flags: bool
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
    method get_new_section_header_names: string list
    method get_section_header_info: string -> section_header_info_int

    (* predicates *)
    method has_section_header_info: string -> bool   (* section name *)
    method has_section_header_infos: bool
    method has_new_section_header_infos: bool

    (* i/o *)
    method read_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


(** {1 System info} *)

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

  method add_inlined_function: doubleword_int -> unit
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

  (** [set_arm_thumb_switch addr arch] records a switch from arm to thumb at
      address [addr] if [arch] is ['T'] and a switch from thumb to arm if [arch]
      is ['A'].*)
  method set_arm_thumb_switch: doubleword_int -> string -> unit

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

  (** [get_arm_thumb_switch addr] returns ['A'] if the architecture switches
      from thumb to arm at address [addr], returns ['T'] if the architecture
      switches from arm to thumb at address [addr], or None otherwise.*)
  method get_arm_thumb_switch: doubleword_int -> string option

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
  method get_variable_intro_name: doubleword_int -> string

  (* predicates *)
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
  method is_trampoline_payload: doubleword_int -> bool
  method is_trampoline_wrapper: doubleword_int -> bool
  method is_trampoline_fallthroughaddr: doubleword_int -> bool
  method has_variable_intro: doubleword_int -> bool
  method has_variable_intros: bool

  (** [is_thumb addr] returns true if the architecture includes (arm) thumb
      instructions and the virtual address [addr] is in a code section that
      is thumb. Otherwise returns false.*)
  method is_thumb: doubleword_int -> bool

  (* xml *)
  (* method read_xml_constant_file: string -> unit *)

  (* saving *)
  method write_xml: xml_element_int -> unit

  method dmso_metrics: dm_so_metrics_t

end


(** {1 Metrics} *)

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
  exm_count: int;     (* number of functions exported *)
  exm_cpp: int;       (* C++ functions *)
  exm_java: int       (* Java native methods *)
  }


type disassembly_metrics_t = {
  dm_unknown_instrs: int;     (* # unknown or inconsisten instructions *)
  dm_instrs: int;     (* total number of instructions from disassembly *)
  dm_functions: int;     (* # functions *)
  dm_coverage: int;      (* # instructions within functions *)
  dm_pcoverage: float;   (* percent coverage of all instructions *)
  dm_overlap: int;       (* # instructions in multiple functions *)
  dm_alloverlap: int;    (* total number of instructions in multiple functions *)
  dm_jumptables: int;    (* # jumptables identified *)
  dm_datablocks: int;    (* # datablocks provided and identified *)
  dm_imports: (string * int * int * bool) list;
  (* number of functions imported per dll, LoadLib *)

  dm_so_imports: dm_so_metrics_t;
  dm_exports: exports_metrics_t
}


type memacc_metrics_t = {
  mmem_reads : int;
  mmem_qreads: int;      (* memory reads from unknown address *)
  mmem_writes: int;
  mmem_qwrites: int;     (* memory writes to unknown address *)
  mmem_esptop : int;     (* locations where esp is unknown *)
  mmem_esprange: int     (* locations where only range is known for esp *)
}


type prec_metrics_t = {
  prec_esp : float;
  prec_reads: float;
  prec_writes: float
}


type cfg_metrics_t = {
  mcfg_instrs : int;
  mcfg_bblocks: int;
  mcfg_loops: int;
  mcfg_loopdepth: int;
  mcfg_complexity: int;
  mcfg_vc_complexity: float        (* product of cfg complexity and variable count *)
}


type vars_metrics_t = {
  mvars_count : int;
  mvars_global: int;
  mvars_args: int;
  mvars_return: int;
  mvars_sideeff: int
}


type calls_metrics_t = {
  mcalls_count: int;
  mcalls_dll: int;
  mcalls_so: int;            (* calls to so library functions *)
  mcalls_app: int;           (* known application calls *)
  mcalls_jni: int;           (* jni call-backs *)
  mcalls_arg: int;           (* calls on an argument value *)
  mcalls_arg_x: int;         (* calls on an argument value without targets *)
  mcalls_global: int;        (* calls on global variable *)
  mcalls_global_x: int;      (* calls on global variable without targets *)
  mcalls_unr: int;           (* unresolved indirect calls *)
  mcalls_nosum: int;         (* dll calls without a function summary *)
  mcalls_inlined: int;       (* inlined application calls *)
  mcalls_staticdll: int;     (* calls to statically linked dll functions *)
  mcalls_staticlib: int;     (* calls to statically linked library functions *)
  mcalls_appwrapped: int;    (* calls to a function that wraps an application call *)
  mcalls_dllwrapped: int;    (* calls to a function that wraps a dll call *)
}


type jumps_metrics_t = {
  mjumps_indirect: int;
  mjumps_unknown: int;           (* no information *)
  mjumps_dll: int;               (* indirect jump to import table *)
  mjumps_jumptable : int;        (* target is a jump table *)
  mjumps_jumptable_norange: int; (* target is a jump table, no range info on index reg *)
  mjumps_global: int;            (* target is provided in global variable *)
  mjumps_argument: int;          (* target is provided in argument variable *)
  mjumps_offsettable: int        (* target is a jump table accessed via offset table *)
}


type cc_metrics_t = {
  mcc_instrs: int;    (* instructions that depend on a condition code *)
  mcc_assoc: int;     (* cc-instructions associated with cc-setting instruction *)
  mcc_test: int       (* cc-instructions with a test expression *)
}


type invs_metrics_t = {
  minvs_table: int;       (* number of distinct invariants *)
  minvs_count: int        (* total number of invariants *)
}


type result_metrics_t = {
  mres_prec : prec_metrics_t;
  mres_memacc: memacc_metrics_t;
  mres_cfg: cfg_metrics_t;
  mres_vars: vars_metrics_t;
  mres_calls: calls_metrics_t;
  mres_jumps: jumps_metrics_t;
  mres_cc: cc_metrics_t;
  mres_invs: invs_metrics_t;
}


type function_run_t = {
  frun_index : int;
  frun_time  : float;
  frun_skip  : bool;
  frun_nonrel: bool;
  frun_reset : bool;         (* invariants were reset *)
  frun_delta_instrs: int;    (* difference in number of instrs compared to previous *)
  frun_unresolved_calls: int;
  frun_unresolved_jumps: int;
  frun_delta_vars: int;      (* difference in number of variables *)
  frun_delta_invs: int       (* difference in number of invariants *)
}


type function_results_t = {
  fres_addr   : string;
  fres_stable : bool;
  fres_time   : float;
  fres_runs   : function_run_t list;
  fres_results: result_metrics_t
}


type file_run_t = {
  ffrun_index: int;
  ffrun_ftime: float;            (* sum of function analysis times *)
  ffrun_time: float;             (* total analysis time, including disassembly *)
  ffrun_propagation_time: float; (* time to propagate arguments forward to callees *)
  ffrun_fns_analyzed: int;
  ffrun_skips: int;
  ffrun_nonrel: int;
  ffrun_resets: int;            (* number of functions for which invariants were reset *)
  ffrun_vc_complexity: float;   (* composite variable-cfg complexity measure *)
  ffrun_fns: int;               (* functions in the system *)
  ffrun_delta_instrs: int;      (* instructions added or removed during this run *)
  ffrun_unresolved_calls: int;
  ffrun_unresolved_jumps: int;
  ffrun_delta_vars: int;        (* variables added during this run *)
  ffrun_delta_invs: int         (* invariants added during this run *)
}


type aggregate_metrics_t = {
  agg_avg_function_size: float;
  agg_max_function_size: int;
  agg_avg_block_count: float;
  agg_avg_cfgc: float;
  agg_max_cfgc: int;
  agg_max_vc_complexity: float;
  agg_median_function_size: int;
  agg_median_block_count: int;
  agg_median_cfgc: int;
  agg_loop_activity: float
}


type userdata_metrics_t = {
  um_function_entry: int;
  um_data_block: int;
  um_struct: int;
  um_nonreturning: int;
  um_class: int
}


type ida_data_t = {
  ida_function_entry_points: doubleword_int list
  }


type file_results_t = {
  ffres_stable: bool;
  ffres_time: float;
  ffres_runs: file_run_t list;
  ffres_functions: function_results_t list;
  ffres_totals: result_metrics_t;
  ffres_aggregate: aggregate_metrics_t;
  ffres_disassembly: disassembly_metrics_t;
  ffres_userdata: userdata_metrics_t;
  ffres_idadata: ida_data_t;
  ffres_fns_included: string list;
  ffres_fns_excluded: string list;
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
  method write_xml: xml_element_int -> unit
  method toPretty: pretty_t
end
