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


type failure_t = {
    expected_value: string; (** expected value converted to string *)
    actual_value: string;   (** actual value converted to string *)
    fmessage: string        (** short message associated with failure *)
  }


type testresult_t =
  | Passed of float  (** test passed, time used to run the test *)
  | Failed of failure_t   (** test failed *)
  | Uncaught of exn * string  (** assertion-based test raised an exception *)
  | Report of int * int * int * (string list) * ((string * int) list) * float
  (** indication of generator-based test performance with
      - number of cases that passed
      - total number of cases
      - number of uncaught exceptions
      - list of counterexamples found
      - map from categories to number of occurrences
      - time used to run all tests
   *)
  | Exit_code of int  (** currently not supported *)


(** classifying function to categorize generated elements for random tests *)               
type 'a classifier_t = 'a -> string


(** name of testcase and application of test function *)
type testcase_t = string * (unit -> testresult_t)


(* ------------------------------------------------------ generator --- *)                

type random_t = Random.State.t

(** generator of input values, with
    - a function to generate random values of a given type
    - a function that converts values of this type to strings 
 *)
type 'a generator_t = (random_t -> 'a) * ('a -> string)


(** reducer of counterexamples that returns a list of some smaller elements *)
type 'a reducer_t = 'a -> 'a list


(* --------------------------------------------------- sepcification --- *)

(** unary predicate *)
type 'a predicate_t = 'a -> bool


(** specification for generator-based tests:
    - ['a] type of domain of function to be tested
    - ['b] type of range of function to be tested
    The precondition is evaluated over values of the domain; the postcondition
    is evaluated over pairs with the first element the input value and the 
    second element the test function result.
 *)
type ('a, 'b) specification_t = {
    s_pre: 'a predicate_t;
    s_post: ('a * 'b) predicate_t
  }


(** The type used to model partial functions, that is, functions that
    may either return a value or raise an exception. *)
type 'a outcome_t =
  | Result of 'a  (** Encodes the result returned by the function. *)
  | Exception of exn  (** Encodes the exception raised by the function. *)
