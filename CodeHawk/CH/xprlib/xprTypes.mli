(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
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

(* chlib *)
open CHBounds
open CHIntervals
open CHLanguage
open CHNumerical
open CHPEPRTypes
open CHPretty

(* chutil *)
open CHNestedCommands
open CHXmlDocument


type xop_t =
  | XNeg
  | XBNot
  | XLNot
  | XPlus
  | XMinus
  | XMult
  | XDiv
  | XMod
  | XPow
  | XShiftlt
  | XShiftrt
  | XLsr      (* Logical shift right; currently in binary only *)
  | XAsr      (* Arithmetic shift right; idem *)
  | XLsl      (* Logical shift left; currently in binary only *)
  | XLt
  | XGt
  | XLe
  | XGe
  | XEq
  | XNe
  | XSubset
  | XDisjoint
  | XBAnd
  | XBXor
  | XBOr
  | XBNor
  | XLAnd 
  | XLOr
  | XNumJoin
  | XNumRange
  | XXlsb  (* extract least significant byte *)
  | XXlsh  (* extract least significant halfword (2 bytes) *)
  | XXbyte  (* extract one byte from a word: XXbyte [index, word] *)
  | Xf of string   (* uninterpreted function *)

type xcst_t = 
  | SymSet of symbol_t list
  | IntConst of numerical_t
  | BoolConst of bool
  | XRandom
  | XUnknownInt
  | XUnknownSet

type xpr_t =
    XVar of variable_t
  | XConst of xcst_t
  | XOp of xop_t * xpr_t list
  | XAttr of string * xpr_t


class type xpr_pretty_printer_int =
  object
    method pr_expr: xpr_t -> pretty_t
  end

type substitution_t = variable_t -> xpr_t

type tmp_provider_t = unit -> variable_t
type cst_provider_t = numerical_t -> variable_t 

type code_var_t  = (nested_cmd_t * variable_t)
type code_num_t  = (nested_cmd_t * numerical_exp_t)
type code_bool_t = (nested_cmd_t * boolean_exp_t)

type pepr_xpr_extract = {
    pepr_n: numerical_t option ;
    pepr_i: interval_t option ;
    pepr_equalities: xpr_t list ;
    pepr_bounds: (bound_type_t * xpr_t list list) list
  }



class type xprdictionary_int =
  object

    method index_numerical: numerical_t -> int
    method index_bound: bound_t -> int
    method index_interval: interval_t -> int
    method index_symbol: symbol_t -> int
    method index_variable: variable_t -> int
    method index_xcst: xcst_t -> int
    method index_xpr: xpr_t -> int
    method index_xpr_list: xpr_t list -> int
    method index_xpr_list_list: xpr_t list list -> int

    method get_numerical: int -> numerical_t
    method get_bound: int -> bound_t
    method get_interval: int -> interval_t
    method get_symbol: int -> symbol_t
    method get_variable: int -> variable_t
    method get_xcst: int -> xcst_t
    method get_xpr: int -> xpr_t
    method get_xpr_list: int -> xpr_t list
    method get_xpr_list_list: int -> xpr_t list list

    method write_xml_numerical: ?tag:string -> xml_element_int -> numerical_t -> unit
    method read_xml_numerical: ?tag:string -> xml_element_int -> numerical_t

    method write_xml_symbol: ?tag:string -> xml_element_int -> symbol_t -> unit
    method read_xml_symbol: ?tag:string -> xml_element_int -> symbol_t

    method write_xml_variable: ?tag:string -> xml_element_int -> variable_t -> unit
    method read_xml_variable: ?tag:string -> xml_element_int -> variable_t

    method write_xml_xcst: ?tag:string -> xml_element_int -> xcst_t -> unit
    method read_xml_xcst: ?tag:string -> xml_element_int -> xcst_t

    method write_xml_xpr: ?tag:string -> xml_element_int -> xpr_t -> unit
    method read_xml_xpr: ?tag:string -> xml_element_int -> xpr_t

    method write_xml_xpr_list: ?tag:string -> xml_element_int -> xpr_t list -> unit
    method read_xml_xpr_list: ?tag:string -> xml_element_int -> xpr_t list

    method write_xml_xpr_list_list: ?tag:string -> xml_element_int -> xpr_t list list -> unit
    method read_xml_xpr_list_list: ?tag:string -> xml_element_int -> xpr_t list list

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty : pretty_t

  end
