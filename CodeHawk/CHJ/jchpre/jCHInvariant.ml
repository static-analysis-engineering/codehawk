(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* chlib *)
open CHPretty
open CHLanguage
open CHSymbolicSets
open CHAtlas

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

module H = Hashtbl

let null_symbol = new symbol_t "null"
let not_null_symbol = new symbol_t "not_null"

let null_domain = "null"
let type_domain = "type"

let get_symbols s = 
  match s#toSymbolicSet#getSymbols with SET s -> s#toList | _ ->
    raise (JCH_failure (STR "internal error in j_invariant"))

class j_invariant_t:j_invariant_int =
object (self:'a)

  val store = H.create 3

  method set_domain (name:string) (invariant:atlas_t) = H.replace store name invariant

  method get_domains = H.fold (fun k v a -> (k,v) :: a) store []

  method get_domain (name:string) =
    try
      H.find store name 
    with Not_found ->
      begin
	ch_error_log#add "invocation error"
	  (LBLOCK [ STR "Invariant does not have domain " ; STR name ]) ;
	raise (JCH_failure (STR "j_invariant_int#get_domain"))
      end

  method has_domain (name:string) = H.mem store name

  method is_bottom = List.exists (fun (_, invariant) -> invariant#isBottom) self#get_domains

  method is_not_null (var:variable_t) =
    if self#is_bottom then false
    else if self#has_domain null_domain then
      let nullInv = self#get_domain null_domain in
      let varInv = ((nullInv#getDomain null_domain)#observer#getNonRelationalVariableObserver) var in
      not (varInv#isTop || (List.exists (fun s -> s#equal null_symbol) (get_symbols varInv)))
    else
      false

  method is_null (var:variable_t) =
    if self#is_bottom then false
    else if self#has_domain null_domain then
      let nullInv = self#get_domain null_domain in
      let varInv = ((nullInv#getDomain null_domain)#observer#getNonRelationalVariableObserver) var in
      not (varInv#isTop || (List.exists (fun s -> s#equal not_null_symbol) (get_symbols varInv)))
    else
      false

  method can_be_null (var:variable_t) = not (self#is_not_null var)

  method toPretty = H.fold (fun k v a -> LBLOCK [ a ; NL ; v#toPretty ]) store (STR "")

end

class type invariants_int =
object
  (* setters *)
  method add_invariant: string -> symbol_t -> symbol_t -> string -> atlas_t -> unit

  (* accessors *)
  method get_invariant: ?mode:string -> bytecode_location_int -> j_invariant_int
end

class invariants_t:invariants_int =
object


  val invariants = H.create 111

  method add_invariant (mode:string) (procName:symbol_t) (opName:symbol_t) (domainName:string)
    (domainInvariant:atlas_t) =
    let index = (mode,procName#getSeqNumber, opName#getSeqNumber) in
    let invariant = 
      if H.mem invariants index then
	H.find invariants index
      else
	let invariant = new j_invariant_t in
	begin H.add invariants index invariant ; invariant end in
    invariant#set_domain domainName domainInvariant

  method get_invariant ?(mode="base") (loc:bytecode_location_int) =
    let index = (mode,loc#get_method_index, loc#get_pc) in
    if H.mem invariants index then
      H.find invariants index
    else
      new j_invariant_t

end

let invariants = new invariants_t
      
