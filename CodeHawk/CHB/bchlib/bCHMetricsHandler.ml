(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs

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
open CHFileIO
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes
open BCHSystemSettings
open BCHUtilities

module TR = CHTraceResult


class ['a] metrics_handler_t (name:string):['a] metrics_handler_int =
object (self)

  method name = name

  method init_value =
    raise (BCH_failure (LBLOCK [ STR "not implemented for " ;
                                 STR self#name ]))

  method add (v1:'a) (v2:'a):'a =
    raise (BCH_failure (LBLOCK [ STR "not implemented for " ;
                                 STR self#name ]))

  method calc (i:int):'a =
    raise (BCH_failure (LBLOCK [ STR "not implemented for " ;
                                 STR self#name ]))

  method write_xml (node:xml_element_int) (v:'a) =
    raise (BCH_failure (LBLOCK [ STR "not implemented for " ;
                                 STR self#name ]))

  method read_xml (node:xml_element_int) =
    raise (BCH_failure (LBLOCK [ STR "not implemented for " ;
                                 STR self#name ]))

  method toPretty (v:'a) = STR self#name
end


(* ------------------------------------------------------- export metrics --- *)

class exports_metrics_handler_t: [ exports_metrics_t ] metrics_handler_int =
object

  inherit [ exports_metrics_t ] metrics_handler_t "exports_metrics_t"

  method init_value = {
      exm_count = 0 ;
      exm_cpp = 0 ;
      exm_java = 0
    }

  method write_xml (node:xml_element_int) (d:exports_metrics_t) =
    let seti tag i = if i = 0 then () else node#setIntAttribute tag i in
    begin
      seti "count" d.exm_count ;
      seti "cpp" d.exm_cpp ;
      seti "java" d.exm_java
    end

  method read_xml (node:xml_element_int):exports_metrics_t =
    let has = node#hasNamedAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    { exm_count = geti "count" ;
      exm_cpp = geti "cpp" ;
      exm_java = geti "java"
    }

  method toPretty (d:exports_metrics_t) =
    if d.exm_count = 0 then STR "" else
      LBLOCK [ STR "Exports: " ; INT d.exm_count ; 
	       (if d.exm_cpp + d.exm_java > 0 then
		  LBLOCK [ STR " (" ;
			   (if d.exm_cpp > 0 then 
			      LBLOCK [ STR "c++ : " ; INT d.exm_cpp ; STR "; " ]
			    else STR "" ) ;
			   (if d.exm_java > 0 then
			      LBLOCK [ STR "java: " ; INT d.exm_java ; STR "; " ]
			    else STR "" ) ; STR ")" ]
	        else
		  STR "") ; NL ]
end

let exports_metrics_handler = new exports_metrics_handler_t

(* -------------------------------------------------- disassembly metrics --- *)

class disassembly_metrics_handler_t: [ disassembly_metrics_t ] metrics_handler_t =
object

  inherit [ disassembly_metrics_t ] metrics_handler_t "disassembly_metrics_t"

  method init_value = {
      dm_unknown_instrs = 0 ;
      dm_instrs = 0 ;
      dm_functions = 0 ;
      dm_coverage = 0 ;
      dm_pcoverage = 0.0 ;
      dm_overlap = 0 ;
      dm_alloverlap = 0 ;
      dm_jumptables = 0 ;
      dm_datablocks = 0 ;
      dm_imports = [] ;
      dm_exports = exports_metrics_handler#init_value
    }

  method write_xml (node:xml_element_int) (d:disassembly_metrics_t) =
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setf tag f = set tag (Printf.sprintf "%.2f" f) in
    let iiNode = xmlElement "imports" in
    let eNode = xmlElement "exports" in
    begin
      iiNode#appendChildren
        (List.map (fun (name,count,summaries,loaded) ->
             let iNode = xmlElement "import" in
             let set = iNode#setAttribute in
             let seti = iNode#setIntAttribute in
             let setb tag b = if b then set tag "yes" else () in
             let safename =
               if has_control_characters name then
                 "__xx__" ^ (hex_string name)
               else
                 name in
             begin 
	       set "name" safename ; 
	       seti "count" count ;
	       seti "summaries" summaries ;
	       setb "loaded" loaded ;
	       iNode 
             end) d.dm_imports) ;
      exports_metrics_handler#write_xml eNode d.dm_exports ;
      append [ iiNode ; eNode ] ;
      seti "unknown-instrs" d.dm_unknown_instrs ;
      seti "instrs" d.dm_instrs ;
      seti "functions" d.dm_functions ;
      seti "coverage" d.dm_coverage ;
      setf "pcoverage" d.dm_pcoverage ;
      seti "overlap" d.dm_overlap ;
      seti "alloverlap" d.dm_alloverlap ;
      seti "datablocks" d.dm_datablocks ;
      seti "jumptables" d.dm_jumptables ;
    end
    
  method read_xml (node:xml_element_int):disassembly_metrics_t =
    let has = node#hasNamedAttribute in
    let get = node#getAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    let getc = node#getTaggedChild in
    let getf tag = float_of_string (get tag) in
    let hasc = node#hasOneTaggedChild in
    { dm_unknown_instrs = geti "unknown-instrs" ;
      dm_instrs = geti "instrs" ;
      dm_functions = geti "functions" ;
      dm_coverage = geti "coverage" ;
      dm_pcoverage = getf "pcoverage" ;
      dm_overlap = geti "overlap" ;
      dm_alloverlap = geti "alloverlap" ;
      dm_jumptables = geti "jumptables" ;
      dm_datablocks = geti "datablocks" ;
      dm_imports =
        List.map (fun iNode -> 
            let chas = iNode#hasNamedAttribute in
            let cget = iNode#getAttribute in
            let cgeti = iNode#getIntAttribute in
            let cgetb tag = (chas tag) && (cget tag) = "yes" in
            (cget "name", cgeti "count", cgeti "summaries",cgetb "loaded")) 
                 (getc "imports")#getChildren ;
      dm_exports =
        if hasc "exports" then 
	  exports_metrics_handler#read_xml (getc "exports")
        else
	  exports_metrics_handler#init_value
  }
    
  method toPretty (d:disassembly_metrics_t) =
    let prf f = STR (Printf.sprintf "%5.2f" f) in
    let imports_to_pretty (imports:(string * int * int * bool) list) =
      if (List.length imports) > 0 then  
        let pri i = fixed_length_pretty ~alignment:StrRight (INT i) 5 in
        let dlls =
          LBLOCK
            (List.map (fun (name,count,summ,loaded) ->
                 LBLOCK [ pri count ; pri summ ; STR "   " ; STR name ; 
	                  (if loaded then STR " (loaded)" else STR "") ;
                          NL ]) imports) in
        LBLOCK [  STR " fns   summ   DLL" ; NL ; dlls  ]
      else
        STR "" in
    let csv = LBLOCK [
                  STR "CSV:";
                  INT d.dm_instrs;
                  STR ",";
                  INT d.dm_unknown_instrs;
                  STR ",";
                  INT d.dm_functions;
                  STR ",";
                  prf d.dm_pcoverage;
                  STR ",";
                  INT d.dm_overlap;
                  STR ",";
                  INT d.dm_alloverlap;
                  NL] in

    LBLOCK [ 
        STR "Instructions         : " ; INT d.dm_instrs ; NL ;
        STR "Unknown instructions : " ; INT d.dm_unknown_instrs ; NL ;
        STR "Functions            : " ; INT d.dm_functions ; 
        STR " (coverage: " ; prf d.dm_pcoverage ; STR "%)" ; NL ;
        STR "Function overlap     : " ; INT d.dm_overlap ; 
        STR " (counting multiples: " ; INT d.dm_alloverlap ; STR ")" ; NL ;
        STR "Jumptables           : " ; INT d.dm_jumptables ; NL ;
        STR "Data blocks          : " ; INT d.dm_datablocks ; NL ; NL ;
        STR "Imports" ; NL ; imports_to_pretty d.dm_imports ; NL ; 
        exports_metrics_handler#toPretty d.dm_exports ; NL;
        csv; NL
    ]

end

let disassembly_metrics_handler = new disassembly_metrics_handler_t

(* -------------------------------------------------------- memacc_metrics --- *)

class memacc_metrics_handler_t: [ memacc_metrics_t ] metrics_handler_int =
object

  inherit [ memacc_metrics_t ] metrics_handler_t "memacc_metrics_t"

  method init_value = {
      mmem_reads = 0 ;
      mmem_qreads = 0 ;
      mmem_writes = 0 ;
      mmem_qwrites = 0 ;
      mmem_esptop = 0 ;
      mmem_esprange = 0 
    }

  method add (d1:memacc_metrics_t) (d2:memacc_metrics_t) = {
      mmem_reads = d1.mmem_reads + d2.mmem_reads ;
      mmem_qreads = d1.mmem_qreads + d2.mmem_qreads ;
      mmem_writes = d1.mmem_writes + d2.mmem_writes ;
      mmem_qwrites = d1.mmem_qwrites + d2.mmem_qwrites ;
      mmem_esptop = d1.mmem_esptop + d2.mmem_esptop ;
      mmem_esprange = d1.mmem_esprange + d2.mmem_esprange
    }

  method write_xml (node:xml_element_int) (m:memacc_metrics_t) =
    let seti tag i = if i = 0 then () else node#setIntAttribute tag i in
    begin
      seti "reads" m.mmem_reads ;
      seti "qreads" m.mmem_qreads ;
      seti "writes" m.mmem_writes ;
      seti "qwrites" m.mmem_qwrites ;
      seti "esptop" m.mmem_esptop ;
      seti "esprange" m.mmem_esprange
    end

  method read_xml (node:xml_element_int):memacc_metrics_t =
    let has = node#hasNamedAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    { mmem_reads = geti "reads" ;
      mmem_qreads = geti "qreads" ;
      mmem_writes = geti "writes" ;
      mmem_qwrites = geti "qwrites" ;
      mmem_esptop = geti "esptop" ;
      mmem_esprange = geti "esprange"
    }
    
  method toPretty (d:memacc_metrics_t) =
    LBLOCK [
        STR "Esp top   : " ; INT d.mmem_esptop ; NL ;
        (if d.mmem_esprange > 0 then 
	   LBLOCK [ STR "Esp range : " ; INT d.mmem_esprange ; NL ] else STR "") ;
        STR "Reads     : " ; INT d.mmem_reads ; 
        (if d.mmem_qreads > 0 then
	   LBLOCK [ STR " (" ; INT d.mmem_qreads ; STR " at unknown address)"  ]
         else STR "") ; NL ;
        STR "Writes    : " ; INT d.mmem_writes ;
        (if d.mmem_qwrites > 0 then
	   LBLOCK [ STR " (" ; INT d.mmem_qwrites ; STR " at unknown address)" ]
         else STR "") ; NL ]
end

let memacc_metrics_handler = new memacc_metrics_handler_t

  
(* ---------------------------------------------------- precision metrics --- *)

class prec_metrics_handler_t
        (m:memacc_metrics_t): [ prec_metrics_t ] metrics_handler_int =
object

  inherit [ prec_metrics_t ] metrics_handler_t "prec_metrics_t"

  method init_value = {
      prec_esp = 0.0 ;
      prec_reads = 0.0 ;
      prec_writes = 0.0
    }

  method calc (instrs:int) = 
    let prec x y = if y = 0 then 100.0 else
                     100.0 *. (float_of_int (y - x)) /. (float_of_int y) in
    { prec_esp = prec (m.mmem_esprange + m.mmem_esptop) instrs ;
      prec_reads = prec m.mmem_qreads m.mmem_reads ;
      prec_writes = prec m.mmem_qwrites m.mmem_writes
    }

  method write_xml (node:xml_element_int) (p:prec_metrics_t) =
    let set = node#setAttribute in
    let setp tag p = set tag (Printf.sprintf "%.2f" p) in
    begin
      setp "esp" p.prec_esp ;
      setp "reads" p.prec_reads ;
      setp "writes" p.prec_writes
    end

  method read_xml (node:xml_element_int):prec_metrics_t =
    let get = node#getAttribute in
    let getf tag = float_of_string (get tag) in
    { prec_esp = getf "esp" ;
      prec_reads = getf "reads" ;
      prec_writes = getf "writes"
    }

  method toPretty (d:prec_metrics_t) =
    let prf f = LBLOCK [ STR (Printf.sprintf "%5.2f" f) ; STR "%" ] in
    LBLOCK [
        STR "Esp   : " ; prf d.prec_esp ; NL ;
        STR "Reads : " ; prf d.prec_reads ; NL ;
        STR "Writes: " ; prf d.prec_writes ; NL ]
end

let mk_prec_metrics_handler = new prec_metrics_handler_t
                         
(* --------------------------------------------------------- cfg metrics --- *)

class cfg_metrics_handler_t: [ cfg_metrics_t ] metrics_handler_int =
object

  inherit [ cfg_metrics_t ] metrics_handler_t "cfg_metrics_t"
  
  method init_value = {
      mcfg_instrs = 0 ;
      mcfg_bblocks = 0 ;
      mcfg_loops = 0 ;
      mcfg_loopdepth = 0 ;
      mcfg_complexity = 0 ;
      mcfg_vc_complexity = 0.0
    }

  method add (d1:cfg_metrics_t) (d2:cfg_metrics_t) = {
      mcfg_instrs = d1.mcfg_instrs + d2.mcfg_instrs ;
      mcfg_bblocks = d1.mcfg_bblocks + d2.mcfg_bblocks ;
      mcfg_loops = d1.mcfg_loops + d2.mcfg_loops ;
      mcfg_loopdepth =
        if d1.mcfg_loopdepth > d2.mcfg_loopdepth then
          d1.mcfg_loopdepth else d2.mcfg_loopdepth ;
      mcfg_complexity = d1.mcfg_complexity + d2.mcfg_complexity ;
      mcfg_vc_complexity = d1.mcfg_vc_complexity +. d2.mcfg_vc_complexity
    }
                                                   
  method write_xml (node:xml_element_int) (c:cfg_metrics_t) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setf tag f = set tag (Printf.sprintf "%.2f" f) in
    begin
      seti "instrs" c.mcfg_instrs ;
      seti "bblocks" c.mcfg_bblocks ;
      seti "loops" c.mcfg_loops ;
      seti "loopdepth" c.mcfg_loopdepth ;
      seti "cfgc" c.mcfg_complexity ;
      setf "vc-complexity" c.mcfg_vc_complexity ;
    end
    
  method read_xml (node:xml_element_int):cfg_metrics_t =
    let get = node#getAttribute in
    let geti = node#getIntAttribute in
    let getf tag = float_of_string (get tag) in
    { mcfg_instrs = geti "instrs" ;
      mcfg_bblocks = geti "bblocks" ;
      mcfg_loops = geti "loops" ;
      mcfg_loopdepth = geti "loopdepth" ;
      mcfg_complexity = geti "cfgc" ;
      mcfg_vc_complexity = getf "vc-complexity" 
    }
    
  method toPretty (d:cfg_metrics_t) =
    let prf f = STR (Printf.sprintf "%.2f" f) in
    LBLOCK [
        STR "Instructions : " ; INT d.mcfg_instrs ; NL ;
        STR "Blocks       : " ; INT d.mcfg_bblocks ; NL ;
        STR "Loops        : " ; INT d.mcfg_loops ; NL ;
        STR "Loop-depth   : " ; INT d.mcfg_loopdepth ; NL ;
        STR "Complexity   : " ; INT d.mcfg_complexity ; NL ;
        STR "VC-complexity: " ; prf d.mcfg_vc_complexity ; NL ]
end

let cfg_metrics_handler = new cfg_metrics_handler_t

(* ------------------------------------------------------ variable metrics --- *)

class vars_metrics_handler_t: [ vars_metrics_t ] metrics_handler_int =
object

  inherit [ vars_metrics_t ] metrics_handler_t "vars_metrics_t"
        
  method init_value = {
      mvars_count = 0 ;
      mvars_global = 0 ;
      mvars_args   = 0 ;
      mvars_return = 0 ;
      mvars_sideeff = 0
    }

  method add (d1:vars_metrics_t) (d2:vars_metrics_t) = {
      mvars_count = d1.mvars_count + d2.mvars_count ;
      mvars_global = d1.mvars_global + d2.mvars_global ;
      mvars_args = d1.mvars_args + d2.mvars_args ;
      mvars_return = d1.mvars_return + d2.mvars_return ;
      mvars_sideeff = d1.mvars_sideeff + d2.mvars_sideeff
    }

  method write_xml (node:xml_element_int) (v:vars_metrics_t) =
    let seti = node#setIntAttribute in
    begin
      seti "count" v.mvars_count ;
      seti "global" v.mvars_global ;
      seti "args" v.mvars_args ;
      seti "return" v.mvars_return ;
      seti "sideeff" v.mvars_sideeff
    end

  method read_xml (node:xml_element_int):vars_metrics_t =
    let geti = node#getIntAttribute in
    { mvars_count = geti "count" ;
      mvars_global = geti "global" ;
      mvars_args = geti "args" ;
      mvars_return = geti "return" ;
      mvars_sideeff = geti "sideeff"
    }

      method toPretty (d:vars_metrics_t) =
        let e tag v =
          if v > 0 then
            LBLOCK [ STR tag ; INT v ; NL ]
          else
            STR "" in
        LBLOCK [
            STR "Variables            : " ; INT d.mvars_count ; NL ;
            (e  "Global variables     : " d.mvars_global) ;
            (e  "Argument variables   : " d.mvars_args) ;
            (e  "Return variables     : " d.mvars_return) ;
            (e  "Side-effect variables: " d.mvars_sideeff) ; NL ]
end

let vars_metrics_handler = new vars_metrics_handler_t
  
(* ------------------------------------------------------------ calls metrics *)

class calls_metrics_handler_t: [ calls_metrics_t ] metrics_handler_int =
object

  inherit [ calls_metrics_t ] metrics_handler_t "calls_metrics_t"

  method init_value = {
      mcalls_count = 0 ;
      mcalls_dll = 0 ;
      mcalls_app = 0 ;
      mcalls_jni = 0 ;
      mcalls_arg = 0 ;
      mcalls_arg_x = 0 ;
      mcalls_global = 0 ;
      mcalls_global_x = 0 ;
      mcalls_unr = 0 ;
      mcalls_nosum = 0 ;
      mcalls_inlined = 0 ;
      mcalls_staticdll = 0 ;
      mcalls_staticlib = 0 ;
      mcalls_appwrapped = 0 ;
      mcalls_dllwrapped = 0
    }

  method add (d1:calls_metrics_t) (d2:calls_metrics_t) = {
      mcalls_count = d1.mcalls_count + d2.mcalls_count ;
      mcalls_dll = d1.mcalls_dll + d2.mcalls_dll ;
      mcalls_app = d1.mcalls_app + d2.mcalls_app ;
      mcalls_jni = d1.mcalls_jni + d2.mcalls_jni ;
      mcalls_arg = d1.mcalls_arg + d2.mcalls_arg ;
      mcalls_arg_x = d1.mcalls_arg_x + d2.mcalls_arg_x ;
      mcalls_global = d1.mcalls_global + d2.mcalls_global ;
      mcalls_global_x = d1.mcalls_global_x + d2.mcalls_global_x ;
      mcalls_unr = d1.mcalls_unr + d2.mcalls_unr ;
      mcalls_nosum = d1.mcalls_nosum + d2.mcalls_nosum ;
      mcalls_inlined = d1.mcalls_inlined + d2.mcalls_inlined ;
      mcalls_staticdll = d1.mcalls_staticdll + d2.mcalls_staticdll ;
      mcalls_staticlib = d1.mcalls_staticlib + d2.mcalls_staticlib ;
      mcalls_appwrapped = d1.mcalls_appwrapped + d2.mcalls_appwrapped ;
      mcalls_dllwrapped = d1.mcalls_dllwrapped + d2.mcalls_dllwrapped 
    }

  method write_xml (node:xml_element_int) (c:calls_metrics_t) =
    let seti tag c = if c > 0 then node#setIntAttribute tag c in
    begin
      seti "count" c.mcalls_count ;
      seti "dll" c.mcalls_dll ;
      seti "app" c.mcalls_app ;
      seti "jni" c.mcalls_jni ;
      seti "arg" c.mcalls_arg ;
      seti "arg-x" c.mcalls_arg_x ;
      seti "global" c.mcalls_global ;
      seti "global-x" c.mcalls_global_x ;
      seti "unr" c.mcalls_unr ;
      seti "no-sum" c.mcalls_nosum ;
      seti "inlined" c.mcalls_inlined ;
      seti "staticdll" c.mcalls_staticdll ;
      seti "staticlib" c.mcalls_staticlib ;
      seti "wraps-app" c.mcalls_appwrapped ;
      seti "wraps-dll" c.mcalls_dllwrapped
    end
    
  method read_xml (node:xml_element_int):calls_metrics_t =
    let has = node#hasNamedAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    { mcalls_count = geti "count" ;
      mcalls_dll = geti "dll" ;
      mcalls_app = geti "app" ;
      mcalls_jni = geti "jni" ;
      mcalls_arg = geti "arg" ;
      mcalls_arg_x = geti "arg-x" ;
      mcalls_global = geti "global" ;
      mcalls_global_x = geti "global-x" ;
      mcalls_unr = geti "unr" ;
      mcalls_nosum = geti "no-sum" ;
      mcalls_inlined = geti "inlined" ;
      mcalls_staticdll = geti "staticdll" ;
      mcalls_staticlib = geti "staticlib" ;
      mcalls_appwrapped = geti "wraps-app" ;
      mcalls_dllwrapped = geti "wraps-dll"
    }

  method toPretty (d:calls_metrics_t) =
    let e tag v = if v > 0 then LBLOCK [ STR tag ; INT v ; NL ] else STR "" in
    let dllEntry =
      if d.mcalls_dll > 0 then
        LBLOCK [ STR "Dll calls                : " ; INT d.mcalls_dll ;
	         (if d.mcalls_nosum > 0 then
		    LBLOCK [ STR " (" ; INT d.mcalls_nosum ; STR " without summary)" ]
	          else STR "") ; NL ]
      else STR "" in
    let argEntry =
      if d.mcalls_arg > 0 then
        LBLOCK [ STR "Calls on argument      : " ; INT d.mcalls_arg ;
	         (if d.mcalls_arg_x > 0 then
		    LBLOCK [ STR " (" ; INT d.mcalls_arg_x ; STR " without targets)" ]
		  else STR "") ; NL ] 
      else STR "" in
    let globalEntry =
      if d.mcalls_global > 0 then
        LBLOCK [ STR "Calls on global variable: " ; INT d.mcalls_global ;
	         (if d.mcalls_global_x > 0 then
		    LBLOCK [ STR " (" ; INT d.mcalls_global_x ; STR " without targets)" ]
		  else STR "") ; NL ]
      else STR "" in
    LBLOCK [
        STR "Calls                    : " ; INT d.mcalls_count ; NL ; dllEntry ; 
        (e  "Application calls        : " d.mcalls_app) ;
        (e  "Jni calls                : " d.mcalls_jni) ; argEntry ; globalEntry ;
        (e  "Unresolved indirect calls: " d.mcalls_unr) ]
end

let calls_metrics_handler = new calls_metrics_handler_t
                          
(* ------------------------------------------------------------ jumps metrics *)

class jumps_metrics_handler_t: [ jumps_metrics_t ] metrics_handler_int =
object

  inherit [ jumps_metrics_t ] metrics_handler_t "jumps_metrics_t"

  method init_value = {
      mjumps_indirect = 0 ;
      mjumps_unknown = 0 ;
      mjumps_dll = 0 ;
      mjumps_jumptable = 0 ;
      mjumps_jumptable_norange = 0 ;
      mjumps_global = 0 ;
      mjumps_argument = 0 ;
      mjumps_offsettable = 0 ;
    }
                    
  method add (d1:jumps_metrics_t) (d2:jumps_metrics_t)  = {
      mjumps_indirect = d1.mjumps_indirect + d2.mjumps_indirect ;
      mjumps_unknown = d1.mjumps_unknown + d2.mjumps_unknown ;
      mjumps_dll = d1.mjumps_dll + d2.mjumps_dll ;
      mjumps_jumptable = d1.mjumps_jumptable + d2.mjumps_jumptable ;
      mjumps_jumptable_norange = d1.mjumps_jumptable_norange + d2.mjumps_jumptable_norange ;
      mjumps_global = d1.mjumps_global + d2.mjumps_global ;
      mjumps_argument = d1.mjumps_argument + d2.mjumps_argument ;
      mjumps_offsettable = d1.mjumps_offsettable + d2.mjumps_offsettable
    }

  method write_xml (node:xml_element_int) (j:jumps_metrics_t) =
    let seti tag i = if i = 0 then () else node#setIntAttribute tag i in
    let get_unresolved (d:jumps_metrics_t) =
      d.mjumps_jumptable_norange + d.mjumps_global + d.mjumps_argument + d.mjumps_unknown in
    begin
      seti "indirect" j.mjumps_indirect ;
      seti "unknown" j.mjumps_unknown ;
      seti "dll" j.mjumps_dll ;
      seti "jt" j.mjumps_jumptable ;
      seti "jt-x" j.mjumps_jumptable_norange ;
      seti "global" j.mjumps_global ;
      seti "argument" j.mjumps_argument ;
      seti "ot-jt" j.mjumps_offsettable ;
      seti "unr" (get_unresolved j)
    end

  method read_xml (node:xml_element_int):jumps_metrics_t =
    let has = node#hasNamedAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    { mjumps_indirect = geti "indirect" ;
      mjumps_unknown = geti "unknown" ;
      mjumps_dll = geti "dll" ;
      mjumps_jumptable = geti "jt" ;
      mjumps_jumptable_norange = geti "jt-x" ;
      mjumps_global = geti "global" ;
      mjumps_argument = geti "argument" ;
      mjumps_offsettable = geti "ot-jt"
    }
    
  method toPretty (d:jumps_metrics_t) =
    let get_unresolved (d:jumps_metrics_t) =
      d.mjumps_jumptable_norange + d.mjumps_global + d.mjumps_argument + d.mjumps_unknown in
    let jtEntry =
      if d.mjumps_jumptable > 0 then
        LBLOCK [ STR "Jumptable jumps : " ; INT d.mjumps_jumptable ;
	         (if d.mjumps_jumptable_norange > 0 then
		    LBLOCK [ STR " (" ; INT d.mjumps_jumptable_norange ; 
			     STR " unresolved due to unknown range)" ]
		  else STR "") ; NL ]
      else
        STR "" in
    let otEntry =
      if d.mjumps_offsettable > 0 then
        LBLOCK [ STR "Offsettable jumps: " ; INT d.mjumps_offsettable ; NL ]
      else
        STR "" in
    let gvEntry =
      if d.mjumps_global > 0 then
        LBLOCK [ STR "Jumps on global  : " ; INT d.mjumps_global ; NL ]
      else
        STR "" in
    let avEntry =
      if d.mjumps_argument > 0 then
        LBLOCK [ STR "Jumps on argument: " ; INT d.mjumps_argument ; NL ]
      else
        STR "" in
    let unresolved = 
      let unresolved = get_unresolved d in
      if unresolved > 0 then
        LBLOCK [ STR "Total unresolved: " ; INT unresolved ; NL ]
      else
        STR "" in
    LBLOCK [
        STR "Indirect jumps  : " ; INT d.mjumps_indirect ; NL ;
        jtEntry ; otEntry ; gvEntry ; avEntry ; unresolved ; NL ]
end

let jumps_metrics_handler = new jumps_metrics_handler_t

(* --------------------------------------------------------------- cc metrics *)

class cc_metrics_handler_t: [ cc_metrics_t ] metrics_handler_int =
object

  inherit [ cc_metrics_t ] metrics_handler_t "cc_metrics_t"

  method init_value = {
      mcc_instrs = 0 ;
      mcc_assoc = 0 ;
      mcc_test = 0 
    }

  method add (d1:cc_metrics_t) (d2:cc_metrics_t) = {
      mcc_instrs = d1.mcc_instrs + d2.mcc_instrs ;
      mcc_assoc = d1.mcc_assoc + d2.mcc_assoc ;
      mcc_test = d1.mcc_test + d2.mcc_test
    }

  method write_xml (node:xml_element_int) (d:cc_metrics_t) =
    let seti = node#setIntAttribute in
    begin
      seti "instrs" d.mcc_instrs ;
      seti "assoc" d.mcc_assoc ;
      seti "test" d.mcc_test
    end

  method read_xml (node:xml_element_int):cc_metrics_t =
    let geti = node#getIntAttribute in
    { mcc_instrs = geti "instrs" ;
      mcc_assoc = geti "assoc" ;
      mcc_test = geti "test"
    }
end

let cc_metrics_handler = new cc_metrics_handler_t

(* ---------------------------------------------------------- invs metrics --- *)

class invs_metrics_handler_t: [ invs_metrics_t ] metrics_handler_int =
object

  inherit [ invs_metrics_t ] metrics_handler_t "invs_metrics_t"

  method init_value = {
      minvs_table = 0 ;
      minvs_count = 0
    }

  method add (d1:invs_metrics_t) (d2:invs_metrics_t) = {
      minvs_table = d1.minvs_table + d2.minvs_table ;
      minvs_count = d1.minvs_count + d2.minvs_count
    }

  method write_xml (node:xml_element_int) (d:invs_metrics_t) =
    let seti = node#setIntAttribute in
    begin
      seti "table" d.minvs_table ;
      seti "count" d.minvs_count
    end

  method read_xml (node:xml_element_int):invs_metrics_t =
    let geti = node#getIntAttribute in
    { minvs_table = geti "table" ;
      minvs_count = geti "count"
    }

  method toPretty (d:invs_metrics_t) =
    LBLOCK [
        STR "table:  " ; INT d.minvs_table ; NL ;
        STR "count:  " ; INT d.minvs_count ; NL ]
end

let invs_metrics_handler = new invs_metrics_handler_t


(* ------------------------------------------------------- result metrics --- *)

class result_metrics_handler_t: [ result_metrics_t ] metrics_handler_int =
object

  inherit [ result_metrics_t ] metrics_handler_t "result_metrics_t"

  method init_value = 
      let prec_metrics_handler =
        mk_prec_metrics_handler memacc_metrics_handler#init_value in
      { mres_prec = prec_metrics_handler#init_value ;
        mres_memacc = memacc_metrics_handler#init_value ;
        mres_cfg = cfg_metrics_handler#init_value ;
        mres_vars = vars_metrics_handler#init_value ;
        mres_calls = calls_metrics_handler#init_value ;
        mres_jumps = jumps_metrics_handler#init_value ;
        mres_cc = cc_metrics_handler#init_value ;
        mres_invs = invs_metrics_handler#init_value ;
      }
                        
  method add (d1:result_metrics_t) (d2:result_metrics_t) = {
      mres_prec = d1.mres_prec ;            (* adjust later *)
      mres_memacc = memacc_metrics_handler#add d1.mres_memacc d2.mres_memacc ;
      mres_cfg = cfg_metrics_handler#add d1.mres_cfg d2.mres_cfg ;
      mres_vars = vars_metrics_handler#add d1.mres_vars d2.mres_vars ;
      mres_calls = calls_metrics_handler#add d1.mres_calls d2.mres_calls ;
      mres_jumps = jumps_metrics_handler#add d1.mres_jumps d2.mres_jumps ;
      mres_cc = cc_metrics_handler#add d1.mres_cc d2.mres_cc ;
      mres_invs = invs_metrics_handler#add d1.mres_invs d2.mres_invs ;
    }
                                                         
  method write_xml (node:xml_element_int) (d:result_metrics_t) =
    let append = node#appendChildren in
    let pNode = xmlElement "prec" in
    let mNode = xmlElement "memacc" in
    let gNode = xmlElement "cfg" in
    let vNode = xmlElement "vars" in
    let cNode = xmlElement "calls" in
    let jNode = xmlElement "jumps" in
    let ccNode = xmlElement "cc" in
    let iNode = xmlElement "invs" in
    let prec_metrics_handler =
      mk_prec_metrics_handler memacc_metrics_handler#init_value in
    begin
      prec_metrics_handler#write_xml pNode d.mres_prec ;
      memacc_metrics_handler#write_xml mNode d.mres_memacc ;
      cfg_metrics_handler#write_xml gNode d.mres_cfg ;
      vars_metrics_handler#write_xml vNode d.mres_vars ;
      calls_metrics_handler#write_xml cNode d.mres_calls ;
      jumps_metrics_handler#write_xml jNode d.mres_jumps ;
      cc_metrics_handler#write_xml ccNode d.mres_cc ;
      invs_metrics_handler#write_xml iNode d.mres_invs ;
      append [ pNode ; mNode ; gNode ; vNode ; cNode ; jNode ; ccNode ; iNode ]
    end
    
  method read_xml (node:xml_element_int):result_metrics_t =
    let getc = node#getTaggedChild in
    let prec_metrics_handler =
      mk_prec_metrics_handler memacc_metrics_handler#init_value in
    { mres_prec = prec_metrics_handler#read_xml (getc "prec") ;
      mres_memacc = memacc_metrics_handler#read_xml (getc "memacc") ;
      mres_cfg = cfg_metrics_handler#read_xml (getc "cfg") ;
      mres_vars = vars_metrics_handler#read_xml (getc "vars") ;
      mres_calls = calls_metrics_handler#read_xml (getc "calls") ;
      mres_jumps = jumps_metrics_handler#read_xml (getc "jumps") ;
      mres_cc = cc_metrics_handler#read_xml (getc "cc") ;
      mres_invs = invs_metrics_handler#read_xml (getc "invs") ;
    }

  method toPretty (d:result_metrics_t) =
    let prec_metrics_handler =
      mk_prec_metrics_handler memacc_metrics_handler#init_value in
    LBLOCK [
        STR "Precision" ; NL ;
        INDENT (3, prec_metrics_handler#toPretty d.mres_prec) ;
        STR "Memory accesses" ; NL ;
        INDENT (3, memacc_metrics_handler#toPretty d.mres_memacc) ;
        STR "Control flow graph" ; NL ;
        INDENT (3, cfg_metrics_handler#toPretty d.mres_cfg) ;
        STR "Variables" ; NL ;
        INDENT (3, vars_metrics_handler#toPretty d.mres_vars) ;
        STR "Calls" ; NL ;
        INDENT (3, calls_metrics_handler#toPretty d.mres_calls) ;
        STR "Jumps" ; NL ;
        INDENT (3, jumps_metrics_handler#toPretty d.mres_jumps) ;
        STR "Invariants" ; NL ;
        INDENT (3, invs_metrics_handler#toPretty d.mres_invs) ; NL ]
end

let result_metrics_handler = new result_metrics_handler_t


(* ----------------------------------------------------- function run --- *)

class function_run_handler_t: [ function_run_t ] metrics_handler_int =
object

  inherit [ function_run_t ] metrics_handler_t "function_run_t"

  method write_xml (node:xml_element_int) (d:function_run_t) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setci tag v = if v = 0 then () else seti tag v in
    let setf tag f = set tag (Printf.sprintf "%.4f" f) in
    let setb tag b = if b then set tag "yes" in
    begin
      seti "index" d.frun_index ;
      setf "time" d.frun_time ;
      setb "skip" d.frun_skip ;
      setb "nonrel" d.frun_nonrel ;
      setb "reset" d.frun_reset ;
      setci "dinstrs" d.frun_delta_instrs ;
      setci "unrcalls" d.frun_unresolved_calls ;
      setci "unrjumps" d.frun_unresolved_jumps ;
      setci "dvars" d.frun_delta_vars ;
      setci "dinvs" d.frun_delta_invs ;
    end

  method read_xml (node:xml_element_int):function_run_t =
    let has = node#hasNamedAttribute in
    let get = node#getAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    let getf tag = float_of_string (get tag) in
    let getb tag = (has tag) && ((get tag) = "yes") in
    { frun_index = geti "index" ;
      frun_time = getf "time" ;
      frun_skip = getb "skip" ;
      frun_nonrel = getb "nonrel" ;
      frun_reset = getb "reset" ;
      frun_delta_instrs = geti "dinstrs" ;
      frun_unresolved_calls = geti "unrcalls" ;
      frun_unresolved_jumps = geti "unrjumps" ;
      frun_delta_vars = geti "dvars" ;
      frun_delta_invs = geti "dinvs"
    }
end

let function_run_handler = new function_run_handler_t

(* ------------------------------------------------------ function results --- *)

class function_results_handler_t (addr:string): [ function_results_t ] metrics_handler_int =
object

  inherit [ function_results_t ] metrics_handler_t "function_results_t"

  method init_value = {
      fres_addr = addr ;
      fres_stable = false ;
      fres_time = 0.0 ;
      fres_runs = [] ;
      fres_results = result_metrics_handler#init_value
    }
                                        
  method write_xml (node:xml_element_int) (d:function_results_t) =
    let set = node#setAttribute in
    let setf tag f = set tag (Printf.sprintf "%.4f" f) in
    let append = node#appendChildren in
    let rrNode = xmlElement "runs" in
    let mNode = xmlElement "fmetrics" in
    let faddr = TR.tget_ok (string_to_doubleword d.fres_addr) in
    begin
      rrNode#appendChildren
        (List.map (fun r ->
             let rNode = xmlElement "run" in
             begin
               function_run_handler#write_xml rNode r;
               rNode
             end) d.fres_runs);
      result_metrics_handler#write_xml mNode d.fres_results;
      append [rrNode; mNode];
      set "a" d.fres_addr;
      setf "time" d.fres_time;
      (if d.fres_stable then set "stable" "yes");
      (if functions_data#has_function_name faddr then
         let name = (functions_data#get_function faddr)#get_function_name in
         let name = if has_control_characters name then
                      "__xx__" ^ (hex_string name)
                    else
                      name in
         set "name" name)
    end
    
  method read_xml (node:xml_element_int):function_results_t =
    let get = node#getAttribute in
    let getc = node#getTaggedChild in
    let has = node#hasNamedAttribute in
    let getf tag = float_of_string (get tag) in
    { fres_addr = get "a" ;
      fres_stable = if has "stable" then (get "stable") = "yes" else false ;
      fres_time = getf "time" ;
      fres_runs = List.map function_run_handler#read_xml ((getc "runs")#getTaggedChildren "run") ;
      fres_results = result_metrics_handler#read_xml (getc "fmetrics")
    }
  
  method toPretty (d:function_results_t) =
    let prf f = fixed_length_pretty ~alignment:StrRight (STR (Printf.sprintf "%5.2f" f)) 8  in
    let pri i = fixed_length_pretty ~alignment:StrRight (INT i) 8 in
    let rprec = d.fres_results.mres_prec in
    let rcfg = d.fres_results.mres_cfg in
    let j = d.fres_results.mres_jumps in
    let get_unresolved (d:jumps_metrics_t) =
      d.mjumps_jumptable_norange + d.mjumps_global + d.mjumps_argument + d.mjumps_unknown in
    let unresolved = get_unresolved j in
    let incomplete = if unresolved > 0 then
                       LBLOCK [ STR " (unresolved jumps: " ; INT unresolved ; STR ")" ]
                     else STR "" in
    LBLOCK [ fixed_length_pretty (STR d.fres_addr) 12 ; STR "  " ; 
	     pri rcfg.mcfg_instrs ; STR "  " ; 
	     pri rcfg.mcfg_bblocks ; STR "  " ; 
	     prf rcfg.mcfg_vc_complexity ; STR "  " ; 
	     prf rprec.prec_esp ; STR "  " ;
	     prf rprec.prec_reads ; STR "  " ;
	     prf rprec.prec_writes ; STR "  " ;
	     prf d.fres_time ; 
	     incomplete ; NL ]
  (*
    let function_results_to_pretty (d:function_results_t) =
    result_metrics_to_pretty d.fres_results
   *)
end

let mk_function_results_handler = new function_results_handler_t
  
(* ------------------------------------------------------------ file run --- *)

class file_run_handler_t: [ file_run_t ] metrics_handler_t =
object

  inherit [ file_run_t ] metrics_handler_t "file_run_t"

  method write_xml (node:xml_element_int) (d:file_run_t) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setci tag c = if c = 0 then () else seti tag c in
    let setf tag f = set tag (Printf.sprintf "%.4f" f) in
    begin
      seti "index" d.ffrun_index ;
      setf "time" d.ffrun_time ;
      setf "propagation-time" d.ffrun_propagation_time ;
      setf "ftime" d.ffrun_ftime ;
      seti "fns-analyzed" d.ffrun_fns_analyzed ;
      setf "vc-complexity" d.ffrun_vc_complexity ;
      setci "skips" d.ffrun_skips ;
      setci "nonrel" d.ffrun_nonrel ;
      setci "resets" d.ffrun_resets ;
      setci "fns" d.ffrun_fns ;
      setci "dinstrs" d.ffrun_delta_instrs ;
      setci "unrcalls" d.ffrun_unresolved_calls ;
      setci "unrjumps" d.ffrun_unresolved_jumps ;
      setci "dvars" d.ffrun_delta_vars ;
      setci "dinvs" d.ffrun_delta_invs 
    end
    
  method read_xml (node:xml_element_int):file_run_t =
    let has = node#hasNamedAttribute in
    let get = node#getAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    let getf tag = float_of_string (get tag) in
    { ffrun_index = geti "index" ;
      ffrun_time = getf "time" ;
      ffrun_propagation_time = getf "propagation-time" ;
      ffrun_ftime = getf "ftime" ;
      ffrun_fns_analyzed = geti "fns-analyzed" ;
      ffrun_vc_complexity = getf "vc-complexity" ;
      ffrun_skips = geti "skips" ;
      ffrun_nonrel = geti "nonrel" ;
      ffrun_resets = geti "resets" ;
      ffrun_fns = geti "fns" ;
      ffrun_delta_instrs = geti "dinstrs" ;
      ffrun_unresolved_calls = geti "unrcalls" ;
      ffrun_unresolved_jumps = geti "unrjumps" ;
      ffrun_delta_vars = geti "dvars" ;
      ffrun_delta_invs = geti "dinvs"
    }
end

let file_run_handler = new file_run_handler_t
    
(* ---------------------------------------------------- aggregate metrics --- *)

class aggregate_metrics_handler_t: [ aggregate_metrics_t ] metrics_handler_int =
object

  inherit [ aggregate_metrics_t ] metrics_handler_t "aggregate_metrics_t"

  method init_value = {
      agg_avg_function_size = 0.0 ;
      agg_max_function_size = 0 ;
      agg_avg_block_count = 0.0 ;
      agg_avg_cfgc = 0.0 ;
      agg_max_cfgc = 0 ;
      agg_max_vc_complexity = 0.0 ;
      agg_median_function_size = 0 ;
      agg_median_block_count = 0 ;
      agg_median_cfgc = 0 ;
      agg_loop_activity = 0.0 ; 
    }

  method write_xml (node:xml_element_int) (d:aggregate_metrics_t) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setf1 tag f = set tag (Printf.sprintf "%.1f" f) in
    let setf4 tag f = set tag (Printf.sprintf "%.4f" f) in
    begin
      setf1 "avg-fn-size" d.agg_avg_function_size ;
      seti "max-fn-size" d.agg_max_function_size ;
      setf1 "avg-block-count" d.agg_avg_block_count ;
      setf1 "avg-cfgc" d.agg_avg_cfgc ;
      seti "max-cfgc" d.agg_max_cfgc ;
      setf1 "max-vc-complexity" d.agg_max_vc_complexity ;
      seti "median-fn-size" d.agg_median_function_size ;
      seti "median-block-count" d.agg_median_block_count ;
      seti "median-cfgc" d.agg_median_cfgc ;
      setf4 "loop-activity" d.agg_loop_activity ;
    end

  method read_xml (node:xml_element_int):aggregate_metrics_t =
    let get = node#getAttribute in
    let geti = node#getIntAttribute in
    let getf tag = float_of_string (get tag) in
    { agg_avg_function_size = getf "avg-fn-size" ;
      agg_max_function_size = geti "max-fn-size" ;
      agg_avg_block_count = getf "avg-block-count" ;
      agg_avg_cfgc = getf "avg-cfgc" ;
      agg_max_cfgc = geti "max-cfgc" ;
      agg_max_vc_complexity = getf "max-vc-complexity" ;
      agg_median_function_size = geti "median-fn-size" ;
      agg_median_block_count = geti "median-block-count" ;
      agg_median_cfgc = geti "median-cfgc" ;
      agg_loop_activity = getf "loop-activity"
    }
    
  method toPretty (d:aggregate_metrics_t) =
    let prf f = STR (Printf.sprintf "%.2f" f) in
    LBLOCK [
        STR "median function size  : " ; INT d.agg_median_function_size ; NL ;
        STR "average function size : " ; prf d.agg_avg_function_size ; NL ;
        STR "maximum function size : " ; INT d.agg_max_function_size ; NL ;
        STR "median block count    : " ; INT d.agg_median_block_count ; NL ;
        STR "median cfg complexity : " ; INT d.agg_median_cfgc ; NL ;
        STR "average block count   : " ; prf d.agg_avg_block_count ; NL ;
        STR "average cfg complexity: " ; prf d.agg_avg_cfgc ; NL ;
        STR "maximum cfg complexity: " ; INT d.agg_max_cfgc ; NL ;
        STR "maximum vc complexity : " ; prf d.agg_max_vc_complexity ; NL ;
        STR "loop activity         : " ; prf d.agg_loop_activity ; NL ]
end

let aggregate_metrics_handler = new aggregate_metrics_handler_t
                              
(* ---------------------------------------------------- user data metrics --- *)

class userdata_metrics_handler_t: [ userdata_metrics_t ] metrics_handler_int =
object

  inherit [ userdata_metrics_t ] metrics_handler_t "userdata_metrics_t"
        
  method init_value = {
      um_function_entry = 0 ;
      um_data_block  = 0 ;
      um_struct = 0 ;
      um_nonreturning = 0 ;
      um_class = 0
    }

  method write_xml (node:xml_element_int) (d:userdata_metrics_t) =
    let seti tag i = if i = 0 then () else node#setIntAttribute tag i in
    begin
      seti "fe" d.um_function_entry ;
      seti "db" d.um_data_block ;
      seti "struct" d.um_struct ;
      seti "nr" d.um_nonreturning ;
      seti "class" d.um_class
    end

  method read_xml (node:xml_element_int):userdata_metrics_t =
    let has = node#hasNamedAttribute in
    let geti tag = if has tag then node#getIntAttribute tag else 0 in
    { um_function_entry = geti "fe" ;
      um_data_block = geti "db" ;
      um_struct = geti "struct" ;
      um_nonreturning = geti "nr" ;
      um_class = geti "class"
    }
end

let userdata_metrics_handler = new userdata_metrics_handler_t

(* ------------------------------------------------------------- ida data --- *)

class ida_data_handler_t: [ ida_data_t ] metrics_handler_int =
object

  inherit [ ida_data_t ] metrics_handler_t "ida_data_t"

  method init_value = { ida_function_entry_points = [] }

  method write_xml (node:xml_element_int) (d:ida_data_t) =
    begin
      node#appendChildren
        (List.map (fun a ->
             let fNode = xmlElement "fe" in
             begin
               fNode#setAttribute "a" a#to_hex_string ;
               fNode end) d.ida_function_entry_points) ;
      node#setIntAttribute "count" (List.length d.ida_function_entry_points)
    end

  method read_xml (node:xml_element_int):ida_data_t =
    { ida_function_entry_points = 
        List.map
          (fun fNode ->
            TR.tget_ok (string_to_doubleword (fNode#getAttribute "a")))
	  (node#getTaggedChildren "fe")
    }
end

let ida_data_handler = new ida_data_handler_t

(* --------------------------------------------------------- file results --- *)

class file_results_handler_t: [ file_results_t ] metrics_handler_int =
object

  inherit [ file_results_t ] metrics_handler_t "file_results_t"

  method init_value = {
      ffres_stable = false;
      ffres_time = 0.0;
      ffres_runs = [];
      ffres_functions = [];
      ffres_totals = result_metrics_handler#init_value;
      ffres_aggregate = aggregate_metrics_handler#init_value;
      ffres_disassembly = disassembly_metrics_handler#init_value;
      ffres_userdata = userdata_metrics_handler#init_value;
      ffres_idadata = ida_data_handler#init_value;
      ffres_fns_included = included_functions ();
      ffres_fns_excluded = excluded_functions ()
    }

  method write_xml (node:xml_element_int) (d:file_results_t) =
    let set = node#setAttribute in
    let setf tag f = set tag (Printf.sprintf "%.2f" f) in
    let append = node#appendChildren in
    let rrNode = xmlElement "runs" in
    let ffNode = xmlElement "functions" in
    let ftNode = xmlElement "function-totals" in
    let aNode = xmlElement "aggregates" in
    let dNode = xmlElement "disassembly" in
    let uNode = xmlElement "userdata" in
    let iNode = xmlElement "idadata" in
    let incNode = xmlElement "fns-included" in
    let excNode = xmlElement "fns-excluded" in
    begin
      rrNode#appendChildren
        (List.map (fun r ->
             let rNode = xmlElement "run" in
             begin
               file_run_handler#write_xml rNode r;
               rNode
             end) d.ffres_runs);
      ffNode#appendChildren
        (List.map (fun f ->
             let function_results_handler =
               mk_function_results_handler f.fres_addr in
             let fNode = xmlElement "fn" in
             begin
               function_results_handler#write_xml fNode f;
               fNode
             end) d.ffres_functions);
      result_metrics_handler#write_xml ftNode d.ffres_totals;
      aggregate_metrics_handler#write_xml aNode d.ffres_aggregate;
      disassembly_metrics_handler#write_xml dNode d.ffres_disassembly;
      userdata_metrics_handler#write_xml uNode d.ffres_userdata;
      ida_data_handler#write_xml iNode d.ffres_idadata;
      append [rrNode; ffNode; ftNode; aNode; dNode; uNode; iNode];
      (if (List.length d.ffres_fns_included) > 0 then
        begin
          incNode#setAttribute "addrs" (String.concat "," d.ffres_fns_included);
          append [incNode]
        end);
      (if (List.length d.ffres_fns_excluded) > 0 then
         begin
           excNode#setAttribute "addrs" (String.concat "," d.ffres_fns_excluded);
           append [excNode]
         end);
      (if d.ffres_stable then set "stable" "yes");
      setf "time" d.ffres_time 
    end

  method read_xml (node:xml_element_int):file_results_t =
    let get = node#getAttribute in
    let getc = node#getTaggedChild in
    let getf tag = float_of_string (get tag) in
    let has = node#hasNamedAttribute in
    { ffres_stable = if has "stable" then (get "stable") = "yes" else false;
      ffres_time = getf "time";
      ffres_runs =
        List.map
          file_run_handler#read_xml
          ((getc "runs")#getTaggedChildren "run");
      ffres_functions = 
        List.map
          (fun n ->
            let faddr = n#getAttribute "a" in
            let function_results_handler =
              mk_function_results_handler faddr in
            function_results_handler#read_xml n)
          ((getc "functions")#getTaggedChildren "fn");
      ffres_totals = result_metrics_handler#read_xml (getc "function-totals");
      ffres_aggregate = aggregate_metrics_handler#read_xml (getc "aggregates");
      ffres_disassembly = disassembly_metrics_handler#read_xml (getc "disassembly");
      ffres_userdata = userdata_metrics_handler#read_xml (getc "userdata");
      ffres_idadata = ida_data_handler#read_xml (getc "idadata");
      ffres_fns_included =
        if has "fns-included" then nsplit ',' (get "addrs") else [];
      ffres_fns_excluded =
        if has "fns-excluded" then nsplit ',' (get "addrs") else [];
    }

  method toPretty (d:file_results_t) =
    LBLOCK [
        STR "Disassembly information: " ; NL ; 
        INDENT (3, disassembly_metrics_handler#toPretty d.ffres_disassembly) ; NL ;
        result_metrics_handler#toPretty d.ffres_totals ; NL ;
        STR "Aggregate analysis results: " ; NL ; 
        INDENT (3, aggregate_metrics_handler#toPretty d.ffres_aggregate) ; NL ; NL ;
        STR "function         instrs    blocks     cfgc      esp     reads     writes    time" ;
        NL ; LBLOCK
               (List.map
                  (fun f ->
                    let function_results_handler =
                      mk_function_results_handler f.fres_addr in
                    function_results_handler#toPretty f) d.ffres_functions) ; NL ]
        end

let file_results_handler = new file_results_handler_t
