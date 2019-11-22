(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

class virtual local_iteration_sigma_combinator_with_threshold_t :
  domain_1:CHUtils.StringCollections.ObjectSet.elt ->
  domain_2:CHUtils.StringCollections.ObjectSet.elt ->
  threshold:int ->
  object
    val domain_a : CHUtils.StringCollections.ObjectSet.elt
    val domain_b : CHUtils.StringCollections.ObjectSet.elt
    val max_iterations : int
    method private loop :
      int ->
      CHDomain.domain_int * CHDomain.domain_int ->
      CHDomain.domain_int * CHDomain.domain_int
    method reduce : CHAtlas.atlas_t -> CHAtlas.atlas_t
    method private virtual sigma :
      CHDomain.domain_int * CHDomain.domain_int ->
      CHDomain.domain_int * CHDomain.domain_int
  end

class virtual local_iteration_sigma_combinator_t :
  domain_1:CHUtils.StringCollections.ObjectSet.elt ->
  domain_2:CHUtils.StringCollections.ObjectSet.elt ->
  object
    val domain_a : CHUtils.StringCollections.ObjectSet.elt
    val domain_b : CHUtils.StringCollections.ObjectSet.elt
    val max_iterations : int
    method private loop :
      int ->
      CHDomain.domain_int * CHDomain.domain_int ->
      CHDomain.domain_int * CHDomain.domain_int
    method reduce : CHAtlas.atlas_t -> CHAtlas.atlas_t
    method private virtual sigma :
      CHDomain.domain_int * CHDomain.domain_int ->
      CHDomain.domain_int * CHDomain.domain_int
  end
