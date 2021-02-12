(* =============================================================================
   CodeHawk Binary Analyzer 
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
  ~(version:string) 
  ~(date:string) 
  ?(maxfilesize=None)
  ?(licensee=None) =
object (self)

  method get_version = version

  method get_date = date

  method get_licensee = licensee

  method get_maxfilesize = maxfilesize

  method toPretty =
    LBLOCK [ STR (string_repeat "=" 80) ; NL ;
	     STR "* CodeHawk Binary Analyzer. Version " ; STR self#get_version ; NL ;
	     STR "* Date: " ; STR self#get_date ; NL ;
	     (match self#get_licensee with
	     | Some u -> LBLOCK [ STR "* " ; STR (string_repeat "-" 78) ; NL ;
				  STR "* Licensed to: " ; STR u ; NL ]
	     | _ -> STR "") ;
	     (match self#get_maxfilesize with
	     | Some v -> LBLOCK [ STR "* Maximum file size allowed: " ; INT v ;
				  STR " bytes" ; NL ]
	     | _ -> STR "") ;
	     STR (string_repeat "-" 80) ; NL ; 
	     STR "* Changes since version 0.2.0:" ; NL ;
	     STR "* - enhanced MIPS functionality" ; NL ;
	     STR (string_repeat "=" 80) ; NL ]

end


let version = new version_info_t 
  ~version:"0.3.0"
  ~date:"Feb 12, 2021"
  ~licensee: None
  ~maxfilesize: None
