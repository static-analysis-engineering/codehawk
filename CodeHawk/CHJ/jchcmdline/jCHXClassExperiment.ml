(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
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
open CHCommon
open CHPretty

(* jchlib *)
open JCHBasicTypes
open JCHDictionary
open JCHFile

(* jchpre *)
open JCHClassLoader
open JCHIFSystem
open JCHSystemSettings


let classname = ref ""
let speclist = [
    ("-classpath",
     Arg.String system_settings#add_classpath_unit, "sets java classpath");
  ]


let usage_msg = "chj_experiment classname"

let read_args () = Arg.parse speclist (fun s -> classname := s) usage_msg


let main () =
  try
    let _ = read_args () in
    let cn = make_cn !classname in
    begin
      load_class (get_class system_settings#get_classpath cn);
      ignore(translate_base_system ());
      pr_debug [chif_system#toPretty base_system; NL]
    end
  with
  | CHFailure p | JCH_failure p ->
    pr_debug [STR "Error in processing class: "; p; NL]
  | JCH_runtime_type_error p ->
    pr_debug [STR "Runtime type error in byte code: "; p; NL]


let _ = Printexc.print main ()
