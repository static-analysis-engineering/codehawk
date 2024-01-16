(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(** Utility to parse C-style format strings *)

(* chlib *)
open CHPretty

type fieldwidth_t =
  | NoFieldwidth
  | FieldwidthArgument
  | FieldwidthConstant of int

type precision_t =
  | NoPrecision
  | PrecisionArgument
  | PrecisionConstant of int

type conversion_t =
  | IntConverter
  | DecimalConverter   (* synonymous with IntConverter for printf, but not for scanf *)
  | UnsignedOctalConverter
  | UnsignedDecimalConverter
  | UnsignedHexConverter of bool                  (* true is caps *)
  | FixedDoubleConverter of bool                  (* true is caps *)
  | ExpDoubleConverter of bool                    (* true is caps *)
  | FlexDoubleConverter of bool                   (* true is caps *)
  | HexDoubleConverter of bool                    (* true is caps *)
  | UnsignedCharConverter
  | StringConverter
  | PointerConverter
  | OutputArgument

type lengthmodifier_t =
  | NoModifier
  | CharModifier
  | ShortModifier
  | LongModifier
  | LongLongModifier
  | IntMaxModifier
  | SizeModifier
  | PtrDiffModifier
  | LongDoubleModifier

class type argspec_int =
  object
    method add_flag: int -> unit
    method set_fieldwidth_arg: unit
    method set_precision_arg: unit
    method set_fieldwidth: int -> unit
    method set_precision: int -> unit
    method set_lengthmodifier: string -> unit
    method set_conversion: int -> unit
    method set_scanset: unit

    method get_flags: int list
    method get_fieldwidth: fieldwidth_t
    method get_precision: precision_t
    method get_conversion: conversion_t
    method get_lengthmodifier: lengthmodifier_t

    method has_fieldwidth: bool
    method has_precision : bool
    method has_lengthmodifier: bool
    method is_well_defined: bool
    method is_scanset: bool

    method toPretty: pretty_t
  end

class type formatstring_spec_int =
  object
    method start_argspec: unit
    method add_flag: int -> unit
    method set_fieldwidth_arg: unit
    method set_precision_arg: unit
    method set_precision: int -> unit
    method set_fieldwidth: int -> unit
    method set_lengthmodifier: string -> unit
    method set_conversion: int -> unit
    method set_literal_length: int -> unit
    method set_scanset: unit

    method get_arguments: argspec_int list
    method get_literal_length: int (* length of literal part of the format string *)

    method has_arguments: bool
    method is_well_defined: bool

    method toPretty: pretty_t
  end

class type formatstring_parser_int =
  object
    method get_result: formatstring_spec_int
    method get_literal_length: int
    method parse: unit
  end

val conversion_table: (int,conversion_t) Hashtbl.t
val invconversion_table: (conversion_t,int) Hashtbl.t
val parse_formatstring: string -> bool -> formatstring_spec_int
