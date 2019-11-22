(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
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
open CHPEPRTypes
open CHPretty

module H = Hashtbl
module P = Pervasives

class indexed_htable_t (name:string):indexed_htable_int =
object (self)

  val mutable next = 1
  val table = H.create 3

  method add (k:(string list * int list)) =
    if H.mem table k then
      H.find table k
    else
      let index = next in
      begin
        H.add table k index ;
        next <- next + 1 ;
        index
      end

  method reset = begin H.clear table ; next <- 1 end

  method toPretty =
    let pairs = H.fold (fun k v acc -> (k,v) :: acc) table [] in
    let pairs = List.sort (fun (_,v) (_,v') -> P.compare v v') pairs in
    let pr_key (tags,args) =
      LBLOCK [ pretty_print_list tags (fun t -> STR t) "[" "," "]" ; STR " ; " ;
               pretty_print_list args (fun a -> INT a) "[" "," "]" ] in
    LBLOCK [ STR name ; NL ;
             LBLOCK (List.map (fun (k,v) ->
                         LBLOCK [ INT v ; STR ": " ; pr_key k ; NL ]) pairs) ]

end

let mk_indexed_htable = new indexed_htable_t
