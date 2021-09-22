(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
  ------------------------------------------------------------------------------ *)

(* chlib *)
open CHCommon
open CHLanguage
open CHNumerical   
open CHPretty


class type graph_t =
  object
    method getRootNode: symbol_t
    method getNextNodes: symbol_t -> symbol_t list
  end
  
module IntCollections =
  CHCollections.Make
    (struct
      type t = int
      let compare = Stdlib.compare
      let toPretty n = INT n
    end)
  
module StringCollections =
  CHCollections.Make
    (struct
      type t = string
      let compare = Stdlib.compare
      let toPretty s = STR s
    end)
  
module SymbolCollections =
  CHCollections.Make
    (struct
      type t = symbol_t
      let compare s1 s2 = s1#compare s2
      let toPretty s = s#toPretty
    end)
  
module VariableCollections =
  CHCollections.Make
    (struct
      type t = variable_t
      let compare s1 s2 = s1#compare s2
      let toPretty s = s#toPretty
    end)
  
module NumericalCollections =
  CHCollections.Make
    (struct
      type t = numerical_t
      let compare s1 s2 = s1#compare s2
      let toPretty s = s#toPretty
    end)
