(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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


let fns_included = ref []
let include_function (s: string) = fns_included := s :: !fns_included
let included_functions () = !fns_included


let fns_excluded = ref []
let exclude_function (s: string) = fns_excluded := s :: !fns_excluded
let excluded_functions () = !fns_excluded


(* -------------------------------------------------------------------------
 * Command-line switches:
 * - set_vftables: for all jump tables, if one of the targets is a function entry
 *       then declare all targets to be function entry points, if enabled
 *       default setting: disabled
 *)

(* --------------------------------------------------------------------------
 * System_user_data settings:
 * - sideeffects-on-globals:
 *      disable <list>
 *        disable sideeffects for global variables in list:
 *          <disable name="sideeffects-on-globals">
 *              <gv a="hex-address"/>
 *              ......
 *          side effects on listed globals are not recorded
 *      enable <list>
 *        enable sideeffects for global variables in list:
 *          <enable name="sideeffects-on-globals">
 *               <gv a="hex-address"/>
 *               ......
 *           side effects only on listed globals are recorded
 *
 *   One effect of recording side effects on globals is that, as long
 *   as there are new side effects, analysis does not stabilize, which
 *   in some cases may lead to performance problems.
 *)

class system_settings_t:system_settings_int =
object (self)

  val mutable jsignature_paths = []
  val mutable summary_paths = []
  val mutable so_libraries = []    (* names of so-libraries *)
  val mutable exportdir = ""
  val mutable verbose = false
  val mutable show_function_timing = false
  val mutable gc_compact_function_interval = 0
  val mutable lineq_instr_cutoff = 0
  val mutable lineq_block_cutoff = 0
  val mutable thumb = false
  val mutable arm_extension_registers = false
  val mutable jni_enabled = false
  val mutable set_vftables_enabled = false
  val mutable record_sideeffects_on_globals = []
  val mutable not_record_sideeffects_on_globals = []
  val mutable sideeffects_on_globals_enabled = false
  val mutable abstract_stackvars_disabled = false
  val mutable apps_dir = None
  val mutable app_name = None
  val mutable exclude_debug = false
  val mutable ssa = false

  method set_verbose = verbose <- true

  method set_show_function_timing = show_function_timing <- true

  method show_function_timing = show_function_timing

  method set_gc_compact_function_interval (count: int) =
    gc_compact_function_interval <- count

  method gc_compact_function_interval = gc_compact_function_interval

  method set_lineq_instr_cutoff (n: int) = lineq_instr_cutoff <- n

  method get_lineq_instr_cutoff = lineq_instr_cutoff

  method set_lineq_block_cutoff (n: int) = lineq_block_cutoff <- n

  method get_lineq_block_cutoff = lineq_block_cutoff

  method is_lineq_restricted ~(blocks: int) ~(instrs: int): bool =
    let icutoff = self#get_lineq_instr_cutoff in
    let bcutoff = self#get_lineq_block_cutoff in
    match (bcutoff > 0, icutoff > 0) with
    | (false, false) -> false
    | (false, true) -> instrs > icutoff
    | (true, false) -> blocks > bcutoff
    | _ -> (blocks > bcutoff) || (instrs > icutoff)

  method set_arm_extension_registers = arm_extension_registers <- true

  method include_arm_extension_registers = arm_extension_registers

  method exclude_debug = exclude_debug <- true

  method set_ssa = ssa <- true

  method use_ssa = ssa

  method set_thumb =
    begin
      chlog#add "settings" (STR "set thumb");
      thumb <- true
    end

  method has_thumb = thumb

  method set_vftables =  set_vftables_enabled <- true

  method is_set_vftables_enabled = set_vftables_enabled

  method set_apps_dir s = 
    begin
      apps_dir <- Some s ;
      chlog#add "applications directory" (LBLOCK [STR "Set to "; STR s])
    end

  method set_export_dir s = exportdir <- s

  method get_export_dir = exportdir

  method set_abstract_stackvars_disabled =
    begin
      abstract_stackvars_disabled <- true;
      chlog#add
        "settings"
        (STR "disable abstraction of stackvars when esp is unknown")
    end

  method enable_sideeffects_on_globals (l:string list) =
    match l with
    | [] ->
       begin
         sideeffects_on_globals_enabled <- false;
         chlog#add "settings" (STR "disable sideeffects on globals")
       end
    | _ ->
       begin
         sideeffects_on_globals_enabled <- true;
         not_record_sideeffects_on_globals <- [];
         record_sideeffects_on_globals <- l;
	 chlog#add
           "settings"
	   (LBLOCK [
                STR "enable sideeffects on globals on ";
		pretty_print_list l (fun a -> STR a) " [" "; " "]"])
       end

  method disable_sideeffects_on_globals (l:string list) =
    match l with
    | [] -> 
      begin
	sideeffects_on_globals_enabled <- true;
	chlog#add "settings" (STR "disable sideeffects on globals")
      end
    | _ ->
       begin
         sideeffects_on_globals_enabled <- true;
	 not_record_sideeffects_on_globals <- l;
         record_sideeffects_on_globals <- [];
	 chlog#add
           "settings"
	   (LBLOCK [
                STR "disable sideeffects on globals on ";
		pretty_print_list l (fun a -> STR a) " [" "; " "]"])
       end

  method set_summary_jar s = 
    match open_path s with
    | Some p -> summary_paths <- summary_paths @ [ p ] | _ -> ()

  method add_so_library l =
    let _ = chlog#add "so-library" (STR l) in
    so_libraries <- l :: so_libraries

  method so_libraries = so_libraries

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
	app_name <- Some appname;
	self#set_summary_jar appSumFilename;
	self#set_summary_jar sumFilename;
	self#set_jsignature_jar appjSigFilename;
	self#set_jsignature_jar jSigFilename ;
	chlog#add
          "applications directory"
          (LBLOCK [STR "application name: "; STR appname])
      end
    | _ ->
       chlog#add "applications directory" (STR "Not set")

  method set_jsignature_jar s =
    match open_path s with
    | Some p -> jsignature_paths <- jsignature_paths @ [ p ]
    | _ -> ()

  method get_summary_paths = summary_paths

  method get_jsignature_paths = jsignature_paths

  method is_verbose = verbose

  method is_debug_excluded = exclude_debug

  method is_abstract_stackvars_disabled = abstract_stackvars_disabled

  method is_sideeffects_on_global_enabled (gv:string) =
    sideeffects_on_globals_enabled
    && (match record_sideeffects_on_globals with
        | [] -> not (List.mem gv not_record_sideeffects_on_globals)
        | l -> List.mem gv l)

end


let system_settings = new system_settings_t


let pverbose l = if system_settings#is_verbose then pr_debug l else ()
