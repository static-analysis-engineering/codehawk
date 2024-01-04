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

(* chlib *)
open CHLanguage

(* bchlib *)
open BCHLibTypes

(** Creates and manipulates locations in assembly functions.

A base location consists of a function address ([loc_faddr]) and instruction
address ([loc_iaddr]):

[type base_location_t = {
    loc_faddr: doubleword_int;
    loc_iaddr: doubleword_int;
  }]

A base location can be wrapped into a function context if it is part of an
inlined function. The function context holds the address of the parent
(calling) function ([ctxt_faddr]), the address of the instruction that
makes the call to the inlined function ([ctxt_callsite]), and the address
of the instruction where the inlined function should return to (usually
the instruction following the call) ([ctxt_returnsite]):

[type fcontext_t = {
    ctxt_faddr: doubleword_int;
    ctxt_callsite: doubleword_int;
    ctxt_returnsite: doubleword_int
  }]

A base location can also be wrapped into a block context to facilitate
creating a delayed join by duplicating blocks. In this case the context
holds the address of the block that is duplicated.

[type context_t =
  | FunctionContext of fcontext_t
  | BlockContext of doubleword_int]

A [ctxt_iaddress_t] is a string representation of an instruction address with
context, with spec

[   i  ( [], { faddr,iaddr } ) = iaddr
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
]

where [fa], [faddr] stand for function address, [cs] stands for call-site address,
[rs] stands for return-site address, [js] stands for jump-site address (the
address of the basic block), and [iaddr] stands for instruction address. All
addresses are represented in hex.
 *)


(** [mk_function_context] returns a context_t data structure with function
    address [faddr], callsite [callsite] and returnsite [returnsite].*)
val mk_function_context:
  faddr:doubleword_int
  -> callsite:doubleword_int
  -> returnsite:doubleword_int
  -> context_t


(** [mk_base_location [faddr] [iaddr] creates a base_location from function
    address [faddr] and instruction address [iaddr] *)
val mk_base_location: doubleword_int -> doubleword_int -> base_location_t


(** [make_location ctxt:ctxts bloc] creates a location from a base location
    [bloc] and zero or more contexts [ctxts] with outer context first and inner
    context last *)
val make_location:
  ?ctxt:context_t list  (* context: outer context first *)
  -> base_location_t    (* address of inner function, instruction address *)
  -> location_int


(** [make_location_by_address faddr iaddr] returns a context-free location
    for instruction address [iaddr] in the function with address [faddr]*)
val make_location_by_address: doubleword_int -> doubleword_int -> location_int


(** [make_i_location loc iaddr] creates a new location that is identical to
    [loc] except that the instruction address of [loc] is replaced by [iaddr],
    that is, the new location has the same context, but a (potentially) different
    instruction address *)
val make_i_location:
  location_int          (* original location *)
  -> doubleword_int     (* new instruction address *)
  -> location_int


(** [make_c_location loc ctxt] creates a new location by prepending [ctxt] to
    [loc] *)
val make_c_location:
  location_int           (* original location *)
  -> context_t           (* new context to be prepended *)
  -> location_int        (* new location with new context prepended *)


(** [make_function_context_location] returns a location that represents
    the entry point of an inlined call with function address calltgt into a
    function with address faddr.*)
val make_function_context_location:
  faddr:doubleword_int
  -> callsite:doubleword_int
  -> returnsite:doubleword_int
  -> calltgt:doubleword_int
  -> location_int


(** [ctxt_string_to_location faddr ctxt_iaddr] converts a string representation
    of a context address [ctxt_iaddr] with outer function address [faddr] to a
    location. *)
val ctxt_string_to_location:
  doubleword_int      (* outer function address *)
  -> ctxt_iaddress_t  (* string that represents the base location and context *)
  -> location_int


val add_ctxt_to_ctxt_string:
  doubleword_int      (* outer function address *)
  -> ctxt_iaddress_t  (* string that represents the context, outer context first *)
  -> context_t        (* new context to be prepended *)
  -> ctxt_iaddress_t


(** [ctxt_string_to_string ctxt_iaddr] converts [ctxt_iaddr] to a string (which,
    currently, is the identity function, as ctxt_iaddress_t is already represented by
    a string) *)
val ctxt_string_to_string: ctxt_iaddress_t -> string


(** [is_iaddress ctxt_iaddr] returns [true] if [ctxt_iaddr] is a bare instruction
    address (without any wrapping contexts) *)
val is_iaddress: ctxt_iaddress_t -> bool


(** [is_same_address iaddr ctxt_iaddr] returns true if ctxt_iaddr is a bare
    instruction address that is the same as [iaddr] *)
val is_same_iaddress: doubleword_int -> ctxt_iaddress_t -> bool


(** [has_false_condition_context ctxt_iaddr] returns true if ctxt_iaddr is
    wrapped in a condition context that is false (i.e., the instruction's
    semantics is NOP and the guarding condition is false).*)
val has_false_condition_context: ctxt_iaddress_t -> bool


(** [has_true_condition_context ctxt_iaddr] returns true if ctxt_iaddr is
    wrapped in a condition context that is true (i.e., the instruction's
    semantics is its own semantics and the guarding condition is true).*)
val has_true_condition_context: ctxt_iaddress_t -> bool


val symbol_to_ctxt_string: symbol_t -> ctxt_iaddress_t


val ctxt_string_to_symbol:
  string -> ?atts:string list -> ctxt_iaddress_t -> symbol_t


(** [ssa_register_value_reg name faddr iaddr] returns a name for the
    variable created as part of an ssa register assignment or abstraction
    to the register [reg] at address [iaddr] in function [faddr].

    Note: the case where [iaddr] has a context may produce a name that
    is not a valid variable name in C.*)
val ssa_register_value_name:
  register_t -> doubleword_int -> ctxt_iaddress_t -> string
