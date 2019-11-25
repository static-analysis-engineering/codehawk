(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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

(** Utility to extract garbage collector settings *)

open Gc

(* chlib *)
open CHPretty

(* chutil *)
open CHPrettyUtil

let garbage_collector_settings_to_pretty () =
  let gc = Gc.get () in
  LBLOCK 
    [ STR "Garbage Collector Settings" ; NL ;
      STR (string_repeat "-" 80) ; NL ;
      STR "minor_heap_size       : " ; INT gc.minor_heap_size ; NL ;
      STR "major_heap_increment  : " ; INT gc.major_heap_increment ; NL ;
      STR "space_overhead        : " ; INT gc.space_overhead ; NL ;
      STR "max_overhead          : " ; INT gc.max_overhead ; NL ;
      STR (string_repeat "=" 80) ; NL ; NL ]
