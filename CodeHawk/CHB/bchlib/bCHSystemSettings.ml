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
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHUtilities

class system_settings_t:system_settings_int =
object (self)

  val mutable jsignature_paths = []
  val mutable summary_paths = []
  val mutable exportdir = ""
  val mutable verbose = false
  val mutable jni_enabled = false
  val mutable sideeffects_on_globals_disabled = []
  val mutable sideeffects_on_globals_enabled = true
  val mutable abstract_stackvars_disabled = false
  val mutable apps_dir = None
  val mutable app_name = None

  method set_verbose = verbose <- true

  method set_apps_dir s = 
    begin
      apps_dir <- Some s ;
      chlog#add "applications directory" (LBLOCK [ STR "Set to " ; STR s])
    end

  method set_export_dir s = exportdir <- s

  method get_export_dir = exportdir

  method set_abstract_stackvars_disabled =
    begin
      abstract_stackvars_disabled <- true ;
      chlog#add "settings" (STR "disable abstraction of stackvars when esp is unknown")
    end

  method set_sideeffects_on_globals_disabled (l:string list) =
    match l with
    | [] -> 
      begin
	sideeffects_on_globals_enabled <- false ;
	chlog#add "settings" (STR "disable sideeffects on globals")
      end
    | _ ->
      begin
	sideeffects_on_globals_disabled <- l ;
	chlog#add "settings" 
	  (LBLOCK [ STR "disable sideeffects on globals on " ;
		    pretty_print_list l (fun a -> STR a) " [" "; " "]" ])
      end

  method set_summary_jar s = 
    match open_path s with Some p -> summary_paths <- summary_paths @ [ p ] | _ -> ()

  method set_app_summary_jars (appname:string) =
    match apps_dir with
    | Some dir ->
      let sumDir = dir ^ "/summaries/" in
      let appDir = sumDir ^ "appsummaries/" ^ appname ^ "/" in
      let appJDir = sumDir ^ "appjsignatures/" in
      let jSigFilename = sumDir ^ "jsignatures.jar" in
      let sumFilename  = sumDir ^ "bcodesummaries.jar" in
      let appjSigFilename = appJDir ^ appname ^ "_jsignatures.jar" in
      let appSumFilename = appDir ^ appname ^ "_summaries.jar" in 
      begin
	app_name <- Some appname ;
	self#set_summary_jar appSumFilename  ;
	self#set_summary_jar sumFilename ;
	self#set_jsignature_jar appjSigFilename ;
	self#set_jsignature_jar jSigFilename ;
	chlog#add "applications directory" (LBLOCK [ STR "application name: " ; STR appname ])
      end
    | _ -> chlog#add "applications directory" (STR "Not set")

  method set_jsignature_jar s =
    match open_path s with Some p -> jsignature_paths <- jsignature_paths @ [ p ] | _ -> ()

  method get_summary_paths = summary_paths

  method get_jsignature_paths = jsignature_paths

  method is_verbose = verbose

  method is_sideeffects_on_globals_enabled = sideeffects_on_globals_enabled

  method is_abstract_stackvars_disabled = abstract_stackvars_disabled

  method is_sideeffects_on_global_disabled (gv:string) =
    (not sideeffects_on_globals_enabled) ||
    (List.mem gv sideeffects_on_globals_disabled)
        
end
  
let system_settings = new system_settings_t
  
let pverbose l = if system_settings#is_verbose then pr_debug l else ()
