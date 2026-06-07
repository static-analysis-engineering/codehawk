(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024-2026 Aarno Labs LLC

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

(* chutil *)
open CHTraceResult

(* cchlib *)
open CCHBasicTypes

(** The Usual Arithmetic Conversions (C Standard 6.3.1.8)

    All of the usual arithmetic conversions applied to expressions in the C
    source code are supplied by the CIL parser in the form of casts.

    The implementation in this file serves to determine the result type of an
    expression constructed to serve as a precondition or side effect to a
    function.
 *)


(** {1 Integer promotion: C Standard 6.3.1.1}

    The following may be used in an expression wherever an int or unsigned
    int may be used:
    - an object or expression with an integer type whose integer conversion
    rank is less than or equal to the rank of int and unsigned int.
    - a bit-field of type _Bool, int, signed int, unsigned int.

    If an int can represent all values of the original type, the value is
    converted to an int; otherwise it is converted to an unsigned int. These
    are called the integer promotions. All other types are unchanged by the
    integer promotions.

    The integer promotions preserve value including sign.
 *)

val get_integer_promotion: typ -> typ


(** {1 Usual arithmetic conversions: C Standard 6.3.1.8}
    
    Many operators that expect operands of arithmetic type cause conversions
    and yield result types in a similar way. The purpose is to determine a
    common real type for the operands and result. For the specified operands,
    each operand is converted, without change of type domain, to a type whose
    corresponding real type is the common real type. Unless explicitly stated
    otherwise, the common real type is also the corresponding real type of
    the result, whose type domain is the type domain of the operands if they
    are the same, and complex otherwise. This pattern is called 'the usual
    arithmetic conversions'.

    First, if the corresponding real type of either operand is long double,
    the other operand is converted, without change of type domain, to a type
    whose corresponding real type is long double.

    Otherwise, if the corresponding real type of either operand is double, the
    other operand is converted, without change of type domain, to a type
    whose corresponding real type is double.

    Otherwise, if the corresponding real type of either operand is float, the
    other operand is converted, without change of type domain, to a type whose
    corresponding type is float.

    Other, the integer promotions are performed on both operands. Then the
    following rules are applied to the promoted operands:

    If both operands have the same type, then no further conversion is needed.

    Otherwise, if both operands have signed integer types or both have unsigned
    integer types, the operand with the type of lesser integer conversion rank
    is converted to the type of the operand with greater rank.

    Otherwise, if the operand that has unsigned integer type has rank greater
    or equal to the rank of the type of the other operand, then the operand
    with signed integer type is converted to the type of the operand with
    unsigned integer type.

    Otherwise, if the type of the operand with signed integer type can represent
    all of the values of the type of the operand with unsigned integer type, then
    the operand with unsigned integer type is converted to the type of the operand
    with signed integer type.

    Otherwise, both operands are converted to the unsigned integer type
    corresponding  to the type of the operand with signed integer type.
 *)

val usual_arithmetic_conversion: typ -> typ -> typ traceresult
