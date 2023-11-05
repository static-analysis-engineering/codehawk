(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
  ============================================================================== *)

type num_cst_t = NUM_BOTTOM | NUM_CST of CHNumerical.numerical_t | NUM_TOP

class numerical_constant_t :
  num_cst_t ->
  object ('a)
    val cst : num_cst_t
    method add : 'a -> 'a
    method div : 'a -> 'a
    method equal : 'a -> bool
    method getCst : num_cst_t
    method isBottom : bool
    method isTop : bool
    method join : 'a -> 'a
    method leq : 'a -> bool
    method meet : 'a -> 'a
    method mkBottom : 'a
    method private mkNew : num_cst_t -> 'a
    method mkTop : 'a
    method mult : 'a -> 'a
    method narrowing : 'a -> 'a
    method sub : 'a -> 'a
    method toPretty : CHPretty.pretty_t
    method widening : 'a -> 'a
  end

type sym_cst_t = SYM_BOTTOM | SYM_CST of CHLanguage.symbol_t | SYM_TOP

class symbolic_constant_t :
  sym_cst_t ->
  object ('a)
    val cst : sym_cst_t
    method equal : 'a -> bool
    method getCst : sym_cst_t
    method isBottom : bool
    method isTop : bool
    method join : 'a -> 'a
    method leq : 'a -> bool
    method meet : 'a -> 'a
    method mkBottom : 'a
    method private mkNew : sym_cst_t -> 'a
    method mkTop : 'a
    method narrowing : 'a -> 'a
    method toPretty : CHPretty.pretty_t
    method widening : 'a -> 'a
  end

type bool_cst_t = BOOL_BOTTOM | BOOL_CST of bool | BOOL_TOP

class boolean_constant_t :
  bool_cst_t ->
  object ('a)
    val cst : bool_cst_t
    method equal : 'a -> bool
    method getCst : bool_cst_t
    method isBottom : bool
    method isTop : bool
    method join : 'a -> 'a
    method leq : 'a -> bool
    method meet : 'a -> 'a
    method mkBottom : 'a
    method private mkNew : bool_cst_t -> 'a
    method mkTop : 'a
    method narrowing : 'a -> 'a
    method toPretty : CHPretty.pretty_t
    method widening : 'a -> 'a
  end


(** Partially ordered set of symbolic constants, with the partial order
    induced by the name of the symbol.*)
type ordered_sym_cst_t =
  | ORDERED_SYM_BOTTOM
  | ORDERED_SYM_CST of CHLanguage.symbol_t
  | ORDERED_SYM_TOP

class ordered_symbolic_constant_t :
  ordered_sym_cst_t ->
  object ('a)
    val cst : ordered_sym_cst_t
    method equal : 'a -> bool
    method getCst : ordered_sym_cst_t
    method isBottom : bool
    method isTop : bool
    method join : 'a -> 'a
    method leq : 'a -> bool
    method meet : 'a -> 'a
    method mkBottom : 'a
    method private mkNew : ordered_sym_cst_t -> 'a
    method mkTop : 'a
    method narrowing : 'a -> 'a
    method toPretty : CHPretty.pretty_t
    method widening : 'a -> 'a
  end


val mkNumericalConstant : CHNumerical.numerical_t -> numerical_constant_t

val topNumericalConstant : numerical_constant_t

val bottomNumericalConstant : numerical_constant_t

val mkSymbolicConstant : CHLanguage.symbol_t -> symbolic_constant_t

val topSymbolicConstant : symbolic_constant_t

val bottomSymbolicConstant : symbolic_constant_t

val mkBooleanConstant : bool -> boolean_constant_t

val trueBooleanConstant : boolean_constant_t

val falseBooleanConstant : boolean_constant_t

val topBooleanConstant : boolean_constant_t

val bottomBooleanConstant : boolean_constant_t

val mkOrderedSymbolicConstant: CHLanguage.symbol_t -> ordered_symbolic_constant_t

val topOrderedSymbolicConstant: ordered_symbolic_constant_t

val bottomOrderedSymbolicConstant: ordered_symbolic_constant_t

val ordered_sym_leq: CHLanguage.symbol_t -> CHLanguage.symbol_t -> bool

val ordered_sym_join:
  CHLanguage.symbol_t -> CHLanguage.symbol_t -> CHLanguage.symbol_t option
