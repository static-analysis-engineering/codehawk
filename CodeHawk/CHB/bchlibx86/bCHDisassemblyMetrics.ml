(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes

(* bchlibx86 *)
open BCHAssemblyInstructions
open BCHAssemblyFunctions


class type disassembly_metrics_int =
object
  method collect  : unit
  method write_xml: xml_element_int -> unit
  method toPretty : pretty_t
end

class type disassembly_stats_int =
object
  method collect  : unit
  method write_xml: xml_element_int -> unit
  method toPretty : pretty_t
end

type metrics_data_t = {
  unkinstrs : int ;           (* # unknown or inconsisten instructions *)
  instrs    : int ;           (* total number of instructions *)
  functions : int ;           (* # functions *)
  coverage  : int ;           (* # instructions within functions *)
  overlap   : int ;           (* # instructions in multiple functions *)
  alloverlap: int ;           (* total number of instructions in multiple functions *)
}

class disassembly_metrics_t =
object (self)

  val mutable data = None 

  method collect =
    match data with Some _ -> () | _ ->
      let (ccoverage,coverlap,cmultiple) = assembly_functions#get_function_coverage in
      (* let (ccinstrs,ccacc,cctest) = assembly_functions#get_num_conditional_instructions in *)
      let d = {
	unkinstrs = !assembly_instructions#get_num_unknown_instructions ;
	instrs    = !assembly_instructions#get_num_instructions ;
	functions = assembly_functions#get_num_functions ;
	coverage  = ccoverage ;
	overlap   = coverlap ;
	alloverlap = cmultiple
      } in
      data <- Some d

  method private get_data = match data with Some d -> d | _ ->
    raise (BCH_failure (STR "Disassembly metrics have not been initialized"))

  method write_xml (node:xml_element_int) =
    let d = self#get_data in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let setp tag n d = 
      let p = 100.0 *. (float_of_int n) /. (float_of_int d) in
      set tag (Printf.sprintf "%5.2f" p) in
    begin
      seti "unkinstrs" d.unkinstrs ;
      seti "instrs" d.instrs ;
      seti "functions" d.functions ;
      seti "coverage" d.coverage ;
      setp "pcoverage" d.coverage d.instrs ;
      seti "overlap" d.overlap ;
      seti "alloverlap" d.alloverlap
    end

  method toPretty =
    let d = self#get_data in
    let perc n d = 
      let p = 100.0 *. (float_of_int n) /. (float_of_int d) in
      STR (Printf.sprintf "%5.2f" p) in
    LBLOCK [
      STR (string_repeat "= " 25) ; NL ; 
      STR "Instructions        : " ; INT d.instrs ; NL ;
      STR "Unknown instructions: " ; INT d.unkinstrs ; NL ;
      STR "Functions           : " ; INT d.functions ; NL ;
      STR "Coverage            : " ; INT d.coverage ; 
      STR " (" ; perc d.coverage d.instrs ; STR ")" ; NL ;
      STR "Overlap             : " ; INT d.overlap ; 
      STR " (including multiple: " ; INT d.alloverlap ; STR ")" ; NL ;
      STR (string_repeat "= " 25) ; NL  ]

end

let disassembly_metrics = new disassembly_metrics_t

class disassembly_stats_t =
object

  val mutable opcode_groups = []
  val mutable opcode_stats  = []
  val mutable opcode_fun_groups = []
  val mutable opcode_fun_stats  = []

  method reset =
    begin
      opcode_groups <- [] ;
      opcode_stats <- [] ;
      opcode_fun_groups <- [] ;
      opcode_fun_stats <- []
    end

  method collect =
    let sort l = List.sort (fun (_,i1) (_,i2) -> Stdlib.compare i2 i1) l in
    begin
      opcode_groups <- sort !assembly_instructions#get_opcode_group_stats ;
      opcode_stats <- sort !assembly_instructions#get_opcode_stats ;
      opcode_fun_groups <- sort assembly_functions#get_opcode_group_stats ;
      opcode_fun_stats  <- sort assembly_functions#get_opcode_stats 
    end

  method write_xml (node:xml_element_int) =
    let gNode = xmlElement "groups" in
    let oNode = xmlElement "opcodes" in
    let fgNode = xmlElement "fgroups" in
    let foNode = xmlElement "fopcodes" in
    let collectdata l =
      let total = List.fold_left (fun a (_,i) -> a + i) 0  l in
      List.map (fun (s,i) ->
          let snode = xmlElement "pct" in
          begin
            snode#setAttribute "k" s ;
            snode#setAttribute "v" (string_of_float (100.0 *. ((float i) /. (float total)))) ;
            snode
          end) l in
    begin
      gNode#appendChildren (collectdata opcode_groups) ;
      oNode#appendChildren (collectdata opcode_stats) ;
      fgNode#appendChildren (collectdata opcode_fun_groups) ;
      foNode#appendChildren (collectdata opcode_fun_stats) ;
      node#appendChildren [ gNode ; fgNode ; oNode ; foNode ]
    end

  method toPretty = 
    let len l = LBLOCK [ STR " (" ; INT (List.length l) ; STR ")" ] in
    let pr l = 
      let total = List.fold_left (fun a (_,i) -> a + i) 0 l in
      pretty_print_list
        l 
	(fun (s,i) ->
          LBLOCK [ STR (fixed_length_string ~alignment:StrLeft s 30) ; 
                   STR (fixed_length_string ~alignment:StrRight (string_of_int i) 8) ; 
		   STR (fixed_length_string
                          ~alignment:StrRight 
			  (Printf.sprintf "   %5.2f" (100.0 *. ((float i) /. (float total)))) 
			  12) ; NL ] )  "" "" ""  in
    LBLOCK [
      STR "All assembly instructions, by groups" ; 
      len opcode_groups ; NL ; pr opcode_groups ; NL ; NL ;
      STR "Assembly instructions within functions" ; 
      len opcode_fun_groups ; NL ; pr opcode_fun_groups ; NL ; NL ;
      STR "All assembly instructions" ; 
      len opcode_stats ; NL ; pr opcode_stats ; NL ; NL ;
      STR "Assembly instructions within functions"  ; 
      len opcode_fun_stats ;	NL ; pr opcode_fun_stats ; NL ]
    
end

let get_disassembly_stats () =
  let stats = new disassembly_stats_t in
  begin
    stats#collect ;
    stats#toPretty
  end

let write_xml_disassembly_stats (node:xml_element_int) =
  let stats = new disassembly_stats_t in
  begin
    stats#collect ;
    stats#write_xml node
  end
