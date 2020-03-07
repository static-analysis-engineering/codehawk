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

(* chlib  *)
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI
open JCHBasicTypes

(* jchfeatures *)
open JCHFeaturesAPI


module H = Hashtbl


class ['a] sumtype_string_converter_t
           (name:string) (pairs:('a * string) list):['a] sumtype_string_converter_int =
object
  
  val tstable = H.create (List.length pairs)
  val sttable = H.create (List.length pairs)
              
  initializer
    List.iter (fun (t,s) -> begin H.add tstable t s ; H.add sttable s t end) pairs
  
  method to_string (t:'a) =
    if H.mem tstable t then
      H.find tstable t
    else
      raise (JCH_failure (LBLOCK [ STR "Type not found for sumtype " ; STR name ]))
    
  method from_string (s:string) =
    if H.mem sttable s then
      H.find sttable s
    else
      raise (JCH_failure (LBLOCK [ STR "No sumtype " ; STR name ;
                                   STR " for string " ; STR s ]))
    
end

let mk_sumtype_string_converter = new sumtype_string_converter_t
        
(* Converter that can be used when only a few types have
   additional data, which can be encoded into and decoded
   from the strin
 *)
class ['a] fn_sumtype_string_converter_t
           (name:string)
           (pairs:('a * string) list)
           (f:'a -> string)
           (g:string -> 'a):['a] sumtype_string_converter_int =
object

  inherit ['a] sumtype_string_converter_t name pairs as super

  method to_string (t:'a) =
    try
      super#to_string t
    with
    | JCH_failure _ -> f t

  method from_string (s:string) =
    try
      super#from_string s
    with
    | JCH_failure _ -> g s

end

let mk_fn_sumtype_string_converter = new fn_sumtype_string_converter_t                                

class virtual ['a] complextyp_string_converter_t (name:string) =
  object
    
    method virtual to_string: 'a -> string
                 
    method from_string (s:string):'a =
      raise
        (JCH_failure
           (LBLOCK [ STR "No reverse construction possible for " ; STR name ]))
            
  end

class fxpr_converter_t:[fxpr_t] sumtype_string_converter_int =
object

  inherit [ fxpr_t ] complextyp_string_converter_t "fxpr_t"

  method to_string (x:fxpr_t) =
    match x with
    | FXVar _ -> "v"
    | FXField _ -> "f"
    | FXArrayElem _ -> "a"
    | FXConst _ -> "c"
    | FXOp _ -> "x"
    | FXFunctionCall _ -> "fc"
    | FXAttr _ -> "s"
    | FXMultiple _ -> "m"
    | FXException -> "e"
    | FXNull -> "n"
    | FXUnknown -> "u"

end

let fxpr_serializer:fxpr_t sumtype_string_converter_int =
  new fxpr_converter_t

class fxfeature_converter_t:[fxfeature_t] sumtype_string_converter_int =
object

  inherit [ fxfeature_t ] complextyp_string_converter_t "fxfeature_t"

  method to_string (f:fxfeature_t) =
    match f with
    | FXCondition _ -> "c"
    | FXAssignment _ -> "a"
    | FXProcedureCall _ -> "p"
    | FXReturn _ -> "r"
    | FXThrow _ -> "t"

end

let fxfeature_serializer:fxfeature_t sumtype_string_converter_int =
  new fxfeature_converter_t

