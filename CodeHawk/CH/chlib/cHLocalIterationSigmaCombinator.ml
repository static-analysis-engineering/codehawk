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

(* chlib *)
open CHAtlas
open CHDomain

class virtual local_iteration_sigma_combinator_with_threshold_t
                ~(domain_1: string)
                ~(domain_2: string)
                ~(threshold: int) =
object (self: 'a)
     
  val domain_a = domain_1
               
  val domain_b = domain_2
               
  val max_iterations = threshold
  (** if threshold is equal to -1 the number of local iterations is left unbounded *)
                     
  method virtual private sigma: (domain_int * domain_int) -> (domain_int * domain_int)
                       
  method private loop n (dom_a, dom_b) =
    if (threshold < 0) || (n <= threshold) then
      let (red_a, red_b) = self#sigma (dom_a, dom_b) in
      if red_a#isBottom || red_b#isBottom then
	(red_a#mkBottom, red_b#mkBottom)
      else if (dom_a#leq red_a) && (dom_b#leq red_b) then
	(red_a, red_b)
      else
	self#loop (n + 1) (red_a, red_b)
    else
      (dom_a, dom_b)
    
  method reduce (atlas: atlas_t) =
    let domains = atlas#getDomains in
    if List.mem domain_a domains && List.mem domain_b domains then
      let dom_a = atlas#getDomain domain_a in
      let dom_b = atlas#getDomain domain_b in
      let (red_a, red_b) = self#loop 1 (dom_a, dom_b) in
      if red_a#isBottom || red_b#isBottom then
	atlas#mkBottom
      else
	atlas#setDomains [(domain_a, red_a); (domain_b, red_b)]
    else
      atlas
    
end
        
class virtual local_iteration_sigma_combinator_t
                ~(domain_1: string)
                ~(domain_2: string) =
object (_self: 'a)
             
  inherit local_iteration_sigma_combinator_with_threshold_t
            ~domain_1:domain_1 ~domain_2:domain_2 ~threshold:(-1)
        
end
