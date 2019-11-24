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

(* chlib *)
open CHPretty
   
(* cchlib *)
open CCHLibTypes
open CCHBasicTypes
open CCHUtilities

class system_settings_t:system_settings_int =
object

  val mutable verbose = false
  val mutable filterabspathfiles = true
  val mutable wordsize = None
  val mutable use_unreachability = false
  val mutable path = ""
  val mutable cfilename = ""
  val mutable application_name = ""
  val mutable contractpath = ""
  val mutable analysis_level = ImplementationDefinedBehavior
  val mutable source_path = ""

  method set_path (p:string) = path <- p
  method set_cfilename (c:string) = cfilename <- c
  method set_application_name (n:string) = application_name <- n
  method set_contractpath (p:string) = contractpath <- p

  method set_analysis_level s = analysis_level <- s
                           
  method set_verbose (v:bool) = verbose <- v
  method set_filterabspathfiles (v:bool) = filterabspathfiles <- v
  method set_wordsize (v:int) = wordsize <- Some v
  method set_use_unreachability = use_unreachability <- true

  method get_path = path
  method get_cfilename = cfilename
  method get_application_name = application_name
  method get_contractpath = contractpath

  method get_wordsize =
    match wordsize with
    |Some v -> v
    | _ -> raise (CCHFailure (STR "No wordsize specified in settings"))

  method is_undefined_only = analysis_level = UndefinedBehavior
  method is_implementation_defined = analysis_level = ImplementationDefinedBehavior
  method is_value_wrap_around = analysis_level = ValueWrapAround

  method use_unreachability = use_unreachability
  method verbose = verbose
  method filterabspathfiles = filterabspathfiles
  method has_wordsize = match wordsize with Some _ -> true | _ -> false
  method has_contractpath = not (contractpath = "")
                                                                
end

let system_settings = new system_settings_t
