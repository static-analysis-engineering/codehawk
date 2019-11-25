(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
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
   ============================================================================= *)

(* chutil *)
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

(* cchpre *)
open CCHPreTypes

val join_dependencies: dependencies_t -> dependencies_t -> dependencies_t

val mk_ppo: podictionary_int -> ppo_type_t -> proof_obligation_int

val mk_returnsite_spo: podictionary_int -> spo_type_t -> proof_obligation_int
  
val mk_local_spo: podictionary_int -> spo_type_t -> proof_obligation_int

val read_xml_ppo: xml_element_int -> podictionary_int -> proof_obligation_int
  
val read_xml_callsite_spo:
  xml_element_int -> podictionary_int -> proof_obligation_int
  
val read_xml_returnsite_spo:
  xml_element_int -> podictionary_int -> proof_obligation_int
  
val read_xml_local_spo:
  xml_element_int -> podictionary_int -> proof_obligation_int
