(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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

(* bchlib *)
open BCHBCTypes
open BCHLibTypes

(** Utilies for creating type constraints.*)


(** {1 Type constants} *)

(** Returns a type constant for small non-negative integer constant values.

    The type constant attempts to capture the possible use of the integer
    constant in the code. The following type constants are returned
    depending on the range:
    - [0          : TyZero]
    - [0x30 - 0x39: TyAsciiDigit]
    - [0x41 - 0x5a: TyAsciiCapsLetter]
    - [0x61 - 0x7a: TyAsciiSmallLetter]
    - [0x1  - 0x1f: TyAsciiControl]
    - [0x20 - 0x7e: TyAsciiPrintable]
    - [0x0  - 0x7f: TyAscii]
    - [0x0  - 0xfe: TyExtendedAscii]
    - otherwise: None
 *)
val mk_intvalue_type_constant: int -> type_constant_t option


(** Returns an integer type constant with the size determined by ikind.*)
val mk_int_type_constant: ikind_t -> type_constant_t


(** Returns a float type constant with the size determined by fkind.*)
val mk_float_type_constant: fkind_t -> type_constant_t


(** [mk_struct_type_constant key name] returns a struct constant for the
    compinfo with key [key] and name [name].

    Note: No checks are performed if a compinfo with [key] actually exists.
*)
val mk_struct_type_constant: int -> string -> type_constant_t


val type_constant_to_btype: type_constant_t -> btype_t


(** {1 Type variables} *)

(** [mk_function_typevar faddr] returns a type variable for the function
    signature of the function (called) with address [faddr] (in hex).*)
val mk_function_typevar: string -> type_variable_t


(** mk_data_address_typevar gaddr] returns a type variable for the global
    address [gaddr] (in hex).

    Note that this address may be either the address of a global variable,
    the address of a string, or the address of a function.*)
val mk_data_address_typevar: string -> type_variable_t


(** [mk_global_variable_typevar gaddr] returns a type variable for the global
    variable at address [gaddr] (in hex).

    Note that the type of a global address is distinct from the type of the
    global variable at that address. The former is necessarily a pointer type,
    while the latter can be any type.
*)
val mk_global_variable_typevar: string -> type_variable_t


(** [mk_reglhs_typevar reg faddr iaddr] returns a type variable for the
    register [reg] lhs that is assigned in function [faddr] at instruction
    address [iaddr] (both addresses in hex). *)
val mk_reglhs_typevar: register_t -> string -> string -> type_variable_t


(** [mk_localstack_lhs_typevar offset faddr iaddr] returns a type variable
    for the local stack lhs variable at offset [offset] (non-negative value
    in bytes) that is assigned in function [faddr] at instruction address
    [iaddr] (both addresses in hex). *)
val mk_localstack_lhs_typevar: int -> string -> string -> type_variable_t


val has_reg_lhs_basevar: register_t -> string -> string -> type_term_t -> bool


val has_stack_lhs_basevar: int -> string -> type_term_t -> bool


(** {1 Capabilities} *)

val add_capability: type_cap_label_t list -> type_variable_t -> type_variable_t


(** [add_load_capability ?size ?offset tvar] returns a new type variable that
    adds a load capability to [tvar] with [size] bytes of data loaded, at offset
    [offset] (in bytes).

    The load capability on a type indicates that the variable can be dereferenced
    for reading. The default values for [size] and [offset] are 4 and 0, resp.

    Examples (from ARM32):
    - [LDR R1, \[R4\]] : add_load_capability tyvar(R4)
    - [LDR R1, \[R4, #4\]] : add_load_capability ~offset:4 tyvar(R4)
    - [LDRB R1, \[R4, #4\]] : add_load_capability ~offset:4 ~size:1 tyvar(R4)

    where tyvar(R4) refers to the type variable constructed for R4 (which would
    typically be obtained via its reaching definition).

    Note that tyvar(R4).load_4_0 represents the type of the dereferenced entity,
    that is, if tyvar(R4) is interpreted as [*int], tyvar(R4).load_4_0 is to be
    interpreted as [int].
 *)
val add_load_capability:
  ?size:int -> ?offset:int -> type_variable_t -> type_variable_t


(** [add_store_capability ?size ?offset tvar] returns a new type variable that
    adds a store capability to [tvar] with [size] bytes of data stored, at offset
    [offset] (in bytes).

    The store capability on a type indicates that the variable can be dereferenced
    for writing. The default values for [size] and [offset] are 4 and 0, resp.

    Examples (from ARM32):
    - [STR R1, \[R4\]] : add_store_capability tyvar(R4)
    - [STR R1, \[R4, #0x10\]] : add_store_capability ~offset:16 tyvar(R4)
    - [STRH R1, \[R4, #0x10\]] : add_store_capability ~offset:16 ~size:2 tyvar(R4)

    where tyvar(R4) refers to the type variable constructed for R4 (which would
    typically be obtained via its reaching definition).

    Note that tyvar(R4).store_4_0 represents the type of the dereferenced entity,
    that is, if tyvar(R4) is interpreted as [*int], tyvar(R4).store_4_0 is to be
    interpreted as [int].
 *)
val add_store_capability:
  ?size:int -> ?offset:int -> type_variable_t -> type_variable_t


val add_array_access_capability:
  ?size:int -> ?offset:int -> type_variable_t -> type_variable_t


(** Returns a new type variable that adds a capability for dereference, used
    when it is not known whether the dereference is a load or store.

    This case arises when incorporating externally provided type signatures. *)
val add_deref_capability: type_variable_t -> type_variable_t


(** Returns a new type variable that adds a return capability to a type variable
    representing a function type, indicating that the function type has a
    non-void return type, and representing that return type.
 *)
val add_return_capability: type_variable_t -> type_variable_t


(** [add_freg_param_capability register] returns a new type variable that adds a
    register parameter capability to a type variable representing a function
    type, indicating that the function type uses [register] as a parameter, and
    representing the type of that parameter.*)
val add_freg_param_capability: register_t -> type_variable_t -> type_variable_t


(** [add_fstack_param_capability offset] returns a new type variable that adds a
    stack parameter capability to a type variable representing a function type,
    indicating that the function type uses [offset] as a parameter of size [size],
    and representing the type of that parameter.*)
val add_fstack_param_capability:
  ?size:int -> int -> type_variable_t -> type_variable_t


(** [add_stack_address_capability offset] returns a new type variable that adds
    a stack address capability to a type variable representing a function type,
    indicating that the function type lets a stack address at offset [offset]
    (in bytes) escape.*)
val add_stack_address_capability: int -> type_variable_t -> type_variable_t


val drop_capability: type_cap_label_t -> type_variable_t -> type_variable_t


val drop_deref_capability: type_variable_t -> type_variable_t


val pop_capability: type_term_t -> (type_term_t * type_cap_label_t) option


(** {1 Type terms} *)

(** Returns a type-constant type-term. *)
val mk_cty_term: type_constant_t -> type_term_t


(** Returns a type-variable type-term. *)
val mk_vty_term: type_variable_t -> type_term_t


(** {1 Type constraints} *)

val type_constraint_terms: type_constraint_t -> type_term_t list

(** [ground_btype_constraint tvar ty] returns a grounded type constraint that
    equates [tvar] or a derived variable of [tvar] to [ty] or a derivative of
    [ty].

    A ground type constraint is used if external type information is incorporated
    in the type constraint. The most common form is an externally provided type
    signature for a function. *)
val mk_btype_constraint: type_variable_t -> btype_t -> type_constraint_t option


(** {1 Comparison} *)

val type_cap_label_compare: type_cap_label_t -> type_cap_label_t -> int


(** {1 Closure} *)

val type_term_prefix_closure: type_term_t -> type_term_t list


(** {1 Printing} *)

val type_cap_label_to_string: type_cap_label_t -> string

val type_base_variable_to_string: type_base_variable_t -> string

val type_variable_to_string: type_variable_t -> string

val type_constant_to_string: type_constant_t -> string

val type_term_to_string: type_term_t -> string

val type_constraint_to_string: type_constraint_t -> string
