(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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

(* Named constants *)

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


(** Storage for externally defined named constants, addresses,
    and flag constants

    These entries typically originate from user data, which is read by
    the [system_info] object from the system_u file, and further extracted
    and stored here, for later access. They
    are not saved between rounds, but instead reinitialized by
    [system_info] for every round.

    Named, but untyped, addresses may be supplemented with types obtained
    from parsed CIL files. CIL files are parsed only on the first round,
    and type updates are initiated by the CIL parser. On subsequent rounds,
    types are requested from the bcfiles data structure that saves and
    restores the CIL parsed types.
*)


(** {1 Named constants}*)

val has_symbolic_name: ?ty:btype_t option -> doubleword_int -> bool
val get_symbolic_name: ?ty:btype_t option -> doubleword_int -> string
val read_xml_symbolic_constants: xml_element_int -> unit
val constant_statistics_to_pretty: unit -> pretty_t

(** {1 Named addresses}*)

(** [has_symbolic_address name] returns true if [name] is associated with
    an address.*)
val has_symbolic_address: string -> bool

(** [get_symbolic_address name] returns the address associated with name
    [name].

    raise BCH_failure if no address exists with name [name].
 *)
val get_symbolic_address: string -> doubleword_int


val get_symbolic_address_type_by_name: string -> btype_t


(** Returns a list of names that are associated with an address without
    associated type.*)
val get_untyped_symbolic_address_names: unit -> string list


(** [update_symbolic_address_btype name ty] updates the type with type [ty]
    only if the current type is unknown. If a type already exists for the
    address associated with [name] only a message is logged. If no address
    exists with name [name] an error message is logged.*)
val update_symbolic_address_btype: string -> btype_t -> unit

(** [has_symbolic_address_name dw] returns true if the address [dw] is
    associated with a name.*)
val has_symbolic_address_name: doubleword_int -> bool

(** [get_symbolic_address_name dw] returns the name associated with address
    [dw].

    raise BCH_failure if no name is associated with address [dw]
 *)
val get_symbolic_address_name: doubleword_int -> string

(** [get_symbolic_address_type dw] returns the btype of the symbolic address
    associated with address value [dw].

    raise BCH_failure if no symbolic address is associated with address [dw].
 *)
val get_symbolic_address_type: doubleword_int -> btype_t

val is_in_global_structvar: doubleword_int -> bool

val get_structvar_base_offset: doubleword_int -> (doubleword_int * boffset_t) option

val is_in_global_arrayvar: doubleword_int -> bool

val get_arrayvar_base_offset:
  doubleword_int -> (doubleword_int * boffset_t * btype_t) option


(** Reads a symbolic address from a userdata xml element and saves it to
    storage. For untyped addresses, an attempt is made to obtain the type
    from the bcfiles structure.*)
val read_xml_symbolic_addresses: xml_element_int -> unit

(** {1 Typed flags (PE only)}*)

val has_symbolic_flags: btype_t -> bool
val get_symbolic_flags: btype_t -> doubleword_int -> string list
val get_xpr_symbolic_name:
  ?typespec:(btype_t * bool) option -> xpr_t -> string option
val read_xml_symbolic_flags: xml_element_int -> unit


(** {1 Access by name}
    Provides access by name to both named constants and named addresses.
    Note that named constants and named addresses live in the same name
    space.
*)

(** [has_constant_value ~ty name] returns true if there is any named value
    (constant value or address) associated with the name [name], optionally
    narrowed to a particular type [ty].*)
val has_constant_value: ?ty:btype_t option -> string -> bool
val get_constant_value: ?ty:btype_t option -> string -> doubleword_int


(** {1 Access for unit tests} *)

val add_address: constant_definition_t -> unit
