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


(** Provides a framework for creating and running tests.
    
    There are two types of tests:
    - {i assertion-based} tests, similar to JUnit tests; these are basic unit
    tests with explicit input values and checks on the output values. Output
    is provided in text format (printed to console) and xml format, compatible
    with JUnit.
    - {i generator-based} tests; these are unit tests based on random values,
    generated based on input specifications, and checked against an input-output
    (precondition, postcondition) specification.
    
    The framework has been adapted from Kaputt (https://kaputt.x9c.fr/index.html).
 *)


(** [new_testsuite name] sets up a new test suite with the given name and an
    empty set of tests *)   
val new_testsuite: string -> unit


(** [add_simple_test ~title:t f] adds a test with name [t] to the test suite that
    will perform the function [f]. Names of tests are required to be unique. 
    If the name is omitted the default name [test <x>] will be created with 
    sequence number x. *)
val add_simple_test: ?title:string -> (unit -> unit) -> unit


(** [make_random_test ~title:t ~nb_runs:nb ~nb_tries:nt ~classifier:c 
    ~reducer:red ~random_src:rnd gen f spec] constructs a random test and adds
    it to the testsuite.
    [f] is the function to be tested; when run the framework will generate [nb] 
    input values for [f] satisfying [spec] using [gen] (an input value 
    satisifies [spec] if it makes one of the preconditions evaluate to [true]).
    As it is possible to find no such input value, [nt] defines the maximum number 
    of tries when generating a value.
    
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
val add_random_test:
  ?title:string
  -> ?nb_runs:int
  -> ?nb_tries: int
  -> ?classifier:'a classifier_t
  -> ?reducer:'a reducer_t
  -> ?reduce_depth:int
  -> ?reduce_smaller:('a -> 'a -> bool)
  -> ?random_src:random_t
  -> 'a generator_t
  -> ('a -> 'b)
  -> (('a, 'b) specification_t) list
  -> unit


val launch_tests: unit -> unit
