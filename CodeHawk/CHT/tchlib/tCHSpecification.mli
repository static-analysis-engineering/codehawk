(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* tchlib *)
open TCHTestApi


(** Provides type definitions, base functions, and combinators allowing to
    encode specifications *)


(** [implies p1 p2] is equivalent to [{ precond = p1; postcond = p2 }]. *)
val implies: 'a predicate_t -> ('a * 'b) predicate_t -> ('a, 'b) specification_t


(** Shorthand for [implies]. *)
val (=>): 'a predicate_t -> ('a * 'b) predicate_t -> ('a, 'b) specification_t


(** [implies' p1 p2] is a simplified version of [implies] where the predicate of
    the postcondition is only applied to the function result. *)
val implies': 'a predicate_t -> 'b predicate_t -> ('a, 'b) specification_t


(** Shorthand for [implies'] *)
val (==>): 'a predicate_t -> 'b predicate_t -> ('a, 'b) specification_t


(** [is_result p] returns a predicate that ensures that the outcome is a result
    satisfying predicate [p]. *)
val is_result: 'a predicate_t -> 'a outcome_t predicate_t


(** Predicate that always evaluates to [true] *)
val always: 'a predicate_t


(** Predicate testing whether the [int] argument is greater than or equal to zero. *)
val is_pos_int: int predicate_t

              
