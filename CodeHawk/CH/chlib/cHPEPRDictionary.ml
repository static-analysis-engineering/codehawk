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
open CHBounds
open CHCommon
open CHIndexedHTable
open CHIntervals
open CHNumerical
open CHPEPRTypes
open CHPretty

class pepr_dictionary_t:pepr_dictionary_int =
object (self)

  val coeff_vector_table = mk_indexed_htable "coeff-vector"
  val param_constraint_table = mk_indexed_htable "param-constraint"
  val param_constraint_set_table = mk_indexed_htable "param-constraint-set"
  val pex_table = mk_indexed_htable "pex"
  val pex_set_table = mk_indexed_htable "pex-set"
  val pex_pset_table = mk_indexed_htable "pex-pset"
  val pepr_bound_table = mk_indexed_htable "pepr-bound"
  val mutable tables = []

  initializer
    tables <- [
      coeff_vector_table ;
      param_constraint_table ;
      param_constraint_set_table ;
      pex_table ;
      pex_set_table ;
      pex_pset_table ;
      pepr_bound_table 
    ]

  method reset = List.iter (fun t -> t#reset) tables

  method index_coefficients (v:numerical_t list) =
    try
      coeff_vector_table#add ([],List.map (fun c -> c#toInt) v)
    with
    | CHFailure p ->
       raise (CHDomainFailure
                ("pepr",
                 (LBLOCK [ STR "Coefficients or offset too large when indexing: " ; p ])))

  method index_coeff_vector (v:coeff_vector_int) =
    self#index_coefficients v#get_k

  method index_param_constraint_data (k:coeff_vector_int) (n:numerical_t) (pt:param_dep_type_t) =
    let pti = match pt with P_EQ -> 0 | P_INEQ -> 1 in
    try
      param_constraint_table#add ([], [ self#index_coeff_vector k ; n#toInt ; pti ])
    with
    | CHFailure p ->
       raise (CHDomainFailure
                ("pepr",
                 (LBLOCK [ STR "Coefficients or offset too large when indexing: " ; p ])))

  method index_param_constraint (p:param_constraint_int) =
    self#index_param_constraint_data p#get_k p#get_n p#get_pt

  method index_param_constraint_set_data (s:param_constraint_int list) =
    param_constraint_set_table#add([], List.map (fun x -> x#index) s)

  method index_param_constraint_set (s:param_constraint_set_int) =
    self#index_param_constraint_set_data s#get_s

  method index_pex_data (k:coeff_vector_int) (n:numerical_t) (bt:bound_type_t) =
    let bti = match bt with LB -> 0 | UB -> 1 in
    try
      pex_table#add ([], [ self#index_coeff_vector k ; n#toInt ; bti ])
    with
    | CHFailure p ->
       raise (CHDomainFailure
                ("pepr",
                 (LBLOCK [ STR "Coefficients or offset too large when indexing: " ; p ])))

  method index_pex (p:pex_int) = self#index_pex_data p#get_k p#get_n p#get_bt

  method index_pex_set_data (s:pex_int list) =
    pex_set_table#add ([], List.map (fun x -> x#index) s)

  method index_pex_set (s:pex_set_int) = self#index_pex_set_data s#get_s

  method index_pex_pset_data (p:pex_set_int list) =
    pex_pset_table#add ([], List.map (fun s -> s#index) p)

  method index_pex_pset (p:pex_pset_int) = self#index_pex_pset_data p#get_p

  method index_pepr_bound_data (p:pepr_bounds_t) =
    let (tags,args) =
      match p with
      | XTOP -> (["t"],[])
      | XPSET p -> ([], [ self#index_pex_pset p ]) in
    pepr_bound_table#add (tags,args)

  method index_pepr_bound (p:pepr_bound_int) = self#index_pepr_bound_data p#get_bound

  method toPretty =
    LBLOCK (List.map (fun t -> LBLOCK [ t#toPretty ; NL ; NL ]) tables)

end
    
let pepr_dictionary = new pepr_dictionary_t
