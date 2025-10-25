(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CCHUtilities


class system_settings_t:system_settings_int =
object

  val mutable projectpath = ""
  val mutable projectname = ""
  val mutable cfilepath = ""
  val mutable cfilename = ""
  val mutable targetpath = ""
  val mutable contractpath = ""

  val mutable verbose = false
  val mutable keep_system_includes = false
  val mutable wordsize = Some 32
  val mutable use_unreachability = false
  val mutable analysis_level = ImplementationDefinedBehavior

  method set_projectpath (p: string) = projectpath <- p
  method get_projectpath = projectpath

  method set_projectname (n: string) = projectname <- n
  method get_projectname = projectname

  method set_cfilepath (p: string) = cfilepath <- p
  method get_cfilepath = cfilepath
  method has_cfilepath = cfilepath != ""

  method set_cfilename (n: string) = cfilename <- n
  method get_cfilename = cfilename

  method set_targetpath (p: string) = targetpath <- p
  method get_targetpath = targetpath

  method set_contractpath (p:string) =
    contractpath <- p

  method get_contractpath = contractpath

  method has_contractpath = not (contractpath = "")

  method set_analysis_level s = analysis_level <- s

  method set_verbose (v:bool) = verbose <- v

  method set_keep_system_includes (v:bool) = keep_system_includes <- v
  method keep_system_includes = keep_system_includes

  method set_wordsize (v:int) = wordsize <- Some v

  method set_use_unreachability = use_unreachability <- true

  method get_wordsize =
    match wordsize with
    |Some v -> v
    | _ -> raise (CCHFailure (STR "No wordsize specified in settings"))

  method is_undefined_only = analysis_level = UndefinedBehavior

  method is_implementation_defined =
    analysis_level = ImplementationDefinedBehavior

  method is_value_wrap_around = analysis_level = ValueWrapAround

  method use_unreachability = use_unreachability
  method verbose = verbose

  method has_wordsize = match wordsize with Some _ -> true | _ -> false


end

let system_settings = new system_settings_t
