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


(** Provides the functions for creating and running tests.
    
    There are three kinds of tests:
    - {i assertion-based} tests, inspired by the {i x}Unit tools, are basic
    unit tests where the developer explicitly writes input values and
    checks that output values satisfy given assertions;
    - {i generator-based} tests, inspired by the QuickCheck tool, are unit
    tests where the developer builds specifications (using combinators)
    and then requests the framework to generate random values to be tested
    against the specification;
    - {i enumeration-based} tests, that are akin to {i generator-based} ones
    except that values are enumerated rather than randomly generated;
 *)


(** [return x] returns the function always returning [x]. *)
val return: 'a -> (unit -> 'a)


(** {6 Assertion-based tests} *)


(** [make_assert_test ~title:t set_up f tear_down] constructs a test running the
    function [f]. The function is fed by the result of a call to [set_up], and
    the value returned by the function is passed to [tear_down].
    The function is intended to use functions from the [TCHAssertion] module to
    check if computed values are equal to waited ones. *)
val make_assert_test:
  ?title:string -> (unit -> 'a) -> ('a -> 'b) -> ('b -> unit) -> testcase_t


(** [make_simple_test ~title:t f] constructs a test running the function [f].
    It is equivalent to [make_assert_test ~title:t (return ()) f ignore].
    The function is intended to use functions from the [TCHAssertion] module to
    check if computed values are equal to waited ones. *)
val make_simple_test: ?title:string -> (unit -> unit) -> testcase_t
  
  
(** {6 Generator-based tests} *)

(** [make_random_test ~title:t ~nb_runs:nb ~nb_tries:nt ~classifier:c ~reducer:red
    ~random_src:rnd gen f spec] constructs a random test. [f] is the function to
    be tested; when run the framework will generate [nb] input values for [f]
    satisfying [spec] using [gen] (an input value satisifies [spec] if it makes
    one of the preconditions evaluate to [true]). As it is possible to find no
    such input value, [nt] defines the maximum number of tries when generating
    a value.
    
    The function[f] is then fed with those values, and the output is passed to
    the associated postcondition to check if it evaluates to [true] (otherwise,
    a counterexample has been found). The reducer is used to try to produce a
    smaller counterexample. The classifier [c] is used to group generated
    elements into categories to have a better understanding of what the random
    elements actually tested.
    
    The default values are:
    - an auto-generated ["untitled no X"] string
    ("X" being the value of a counter) for [title];
    - [100] for [nb_runs]
    - [10 * nb_runs] for [nb_tries];
    - [default_classifier] for [classifier];
    - [default-reducer] for [reducer];
    - [TCHGenerator.make_random ()] for [random_src].
    
    Raises [Invalid_arg] if either [nb] or [nt] is not strictly positive *)
val make_random_test:
  ?title:string
  -> ?nb_runs:int
  -> ?nb_tries:int
  -> ?classifier:'a classifier_t
  -> ?reducer:'a reducer_t
  -> ?reduce_depth:int
  -> ?reduce_smaller:('a -> 'a -> bool)
  -> ?random_src:random_t
  -> 'a generator_t
  -> ('a -> 'b)
  -> (('a, 'b) specification_t) list
  -> testcase_t
