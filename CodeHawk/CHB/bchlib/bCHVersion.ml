(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* chutil *)
open CHPrettyUtil

class type version_info_int =
object
  method get_version: string
  method get_description: string
  method get_date: string
  method get_licensee: string option
  method toPretty:pretty_t
end


class version_info_t 
  ?(maxfilesize=None)
  ?(licensee=None)
  ~(version:string)
  ~(date:string)
  () =
object (self)

  method get_version = version

  method get_date = date

  method get_licensee = licensee

  method get_maxfilesize = maxfilesize

  method toPretty =
    LBLOCK [
        STR (string_repeat "=" 80); NL ;
	STR "* CodeHawk Binary Analyzer. Version ";
        STR self#get_version; NL ;
	STR "* Date: ";
        STR self#get_date ; NL ;
	(match self#get_licensee with
	 | Some u ->
            LBLOCK [
                STR "* ";
                STR (string_repeat "-" 78); NL;
		STR "* Licensed to: "; STR u; NL]
	 | _ -> STR "");
	(match self#get_maxfilesize with
	 | Some v ->
            LBLOCK [
                STR "* Maximum file size allowed: ";
                INT v;
		STR " bytes"; NL]
	 | _ -> STR "");
	STR (string_repeat "-" 80); NL;
        STR "* Major changes since version 0.5.0;"; NL;
        STR "* - add option to import summaries written as parseable C code ";
        STR "(using CIL);"; NL;
        STR "* - integration of CIL-based types."; NL;
        STR "* Major changes since version 0.4.0:"; NL;
        STR "* - remove external libraries extlib and camlzip"; NL;
	STR "* Major changes since version 0.3.0:"; NL;
	STR "* - support for arm32/thumb2"; NL;
	STR (string_repeat "=" 80); NL]

end


let version = new version_info_t 
  ~version:"0.6.0_20241111"
  ~date:"2024-11-11"
  ~licensee: None
  ~maxfilesize: None
  ()
