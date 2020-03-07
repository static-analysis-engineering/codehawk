(* =============================================================================
   CodeHawk Java Analyzer
   Author: Cody Schuffelen and Anca Browne and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* gtk *)
open Gobject.Data

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHJTerm
open JCHTranslateToCHIF


(* jchpre *)
open JCHAnnotationsPre
open JCHApplication
open JCHBytecodeLocation
open JCHFunctionSummary
open JCHPreAPI
open JCHAnalysisResults

(* jchstacgui *)
open JCHBCFunctions
open JCHGuiUtil
open JCHSystemDisplay

module P = Pervasives

module LF = CHOnlineCodeSet.LanguageFactory

let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p

let relational_expr_to_pretty mInfo pc x =
  relational_expr_to_pretty ~varname:(mInfo#get_varname_mapping pc) x

let pp_tainto (pvar:variable_t -> string) t =
  match t with
  | T_ORIG_VAR (cmsix,v) ->
     LBLOCK [ STR "M:" ; INT cmsix ;  STR " :" ; STR (pvar v) ]
  | T_ORIG_FIELD(cfsix,s,_,_) -> 
    LBLOCK [ STR "F:" ; STR s ; STR " - " ; INT cfsix ]
  | T_ORIG_CALL (cmsix,s,_,_) ->
     let cms = retrieve_cms cmsix in
     LBLOCK [ STR "C:" ; STR s ; STR ": " ; cms#toPretty ]
  | T_ORIG_TOP_TARGET (tgt,caller_cmsix,i) ->
     LBLOCK [ STR "TOP:" ; tgt#toPretty ; STR " (" ;
	      INT caller_cmsix ; STR "), " ; INT i ; STR ")" ]
  | T_ORIG_STUB (tgt_cmsix,_,_) ->
     let cms = retrieve_cms tgt_cmsix in
     LBLOCK [ STR "L:" ; cms#toPretty ]

let tainto_to_pretty (pvar:variable_t -> string) (v,deftaint,toptaint) =
  match (deftaint,toptaint) with
  | ([],[]) -> LBLOCK [ STR (pvar v) ; STR ": not tainted" ; NL ]
  | (_::_,_) ->
    LBLOCK [ STR (pvar v) ; STR ":" ; NL ;
	     INDENT(3,LBLOCK [ STR "Tainted: " ; 
			       pretty_print_list deftaint (pp_tainto pvar) "" ", " "" ;
			       NL ]) ]
  | _ -> 
    LBLOCK [ STR (pvar v) ; STR ":" ; NL ;
	     INDENT (3,LBLOCK [ STR "Potentially tainted: " ; 
				pretty_print_list toptaint (pp_tainto pvar) "" ", " "" ;
				NL ]) ]

let show_chif_dialog (cmsix:int) (parent:GWindow.window) =
  try
    let cms = retrieve_cms cmsix in
    let mInfo = app#get_method cms in
    let procname = make_procname cmsix in
    let system = LF.mkSystem (new symbol_t "_") in
    let _ =
      try
        translate_method
          ~proc_filter:(fun _ -> true)
          ~simplify:false
          ~transform:false
          ~java_method:mInfo#get_method
          ~code_set:system
          ~exn_infos_fn:(defaultExnInfoFn mInfo#get_method)
          ()
      with
      | JCH_failure p ->
         begin
	   ch_error_log#add "failure"
			    (LBLOCK [ STR "failure in translate method " ;
                                      cms#toPretty ; STR ": " ; p ]) ;
	   raise (JCH_failure (LBLOCK [ STR "failure in translate method: " ; p ]))
         end in
    let proc = system#getProcedure procname in
    let title = "CHIF for " ^ cms#name in
    let dialog =
      GWindow.dialog
        ~title
        ~parent
        ~modal:false 
        ~show:true
        ~width:800
        ~height:480
        () in
    let window =
      GBin.scrolled_window 
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:dialog#vbox#add
        () in
    let view = GText.view () in
    let _ = view#set_pixels_above_lines 5 in
    let _ = view#set_left_margin 10 in
    let buffer = view#buffer in
    let iter = buffer#get_iter `START in
    let _ = buffer#insert ~iter (pp_str proc#toPretty) in
    let contents = view#coerce in
    let _ = window#add contents in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun () -> ()) in
    let _ = dialog#connect#response
              ~callback:(fun resp -> dialog#destroy ()) in
    ()
  with
  | JCH_failure p ->
     pr_debug [ STR "Failure in CHIF dialog: " ; p ; NL ]
    

let show_invariant_dialog (cmsId:int) (pc:int) (parent:GWindow.window) =
  try
    let cms = retrieve_cms cmsId in
    let mInfo = app#get_method cms in
    let invs =
      (application_analysis_results#get_invariants cmsId)#get_invariants pc in
    let pPcTaints =
      (application_analysis_results#get_taints cmsId)#pc_to_pretty pc in
    let pSlots =
      (mInfo#get_method_stack_layout#get_stack_layout pc)#toPretty in
    let pPcInvs =
      List.map (relational_expr_to_pretty mInfo pc) invs in
    let pPcInvs =
      LBLOCK (List.map (fun p -> INDENT (3, LBLOCK [ p ; NL ])) pPcInvs) in
    let pTgtInfo = 
      match mInfo#get_opcode pc with
      | OpInvokeVirtual _ | OpInvokeInterface _ ->
         let loc = get_bytecode_location mInfo#get_index pc in
         if app#has_instruction loc then
	   let iInfo = app#get_instruction loc in
	   if iInfo#has_method_target then
	     Some (iInfo#get_method_target ())#toPretty
	   else
	     Some (STR "no method target found")
         else
	   Some (STR "no instruction info found") 
      | _ -> None in
    let pPc =
      LBLOCK [ STR "Local invariants" ; NL ; 
	       STR (string_repeat "=" 80) ; NL ; pPcInvs ; NL ; 
	       STR "Taint status of local variables" ; NL ; 
	       STR (string_repeat "=" 80) ; NL ; pPcTaints ; NL ;
	       (match pTgtInfo with
		| Some pTgtInfo ->
		   LBLOCK [ STR "Method target" ; NL ;
			    STR (string_repeat "=" 80) ; NL ; pTgtInfo ; NL ; NL]
		| _ -> STR "") ;
	       STR "Expr stack layout" ; NL ;
	       STR (string_repeat "=" 80) ; NL ; pSlots ; NL ] in
    let title = "Invariant at pc = " ^ (string_of_int pc) in
    let dialog =
      GWindow.dialog
        ~title
        ~parent
        ~modal:false 
        ~show:true
        ~width:800
        ~height:480
        () in
    let window =
      GBin.scrolled_window 
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:dialog#vbox#add
        () in
    let view = GText.view () in
    let _ = view#set_pixels_above_lines 5 in
    let _ = view#set_left_margin 10 in
    let buffer = view#buffer in
    let iter = buffer#get_iter `START in
    let _ = buffer#insert ~iter (pp_str pPc) in
    let contents = view#coerce in
    let _ = window#add contents in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun () -> ()) in
    let _ = dialog#connect#response
              ~callback:(fun resp -> dialog#destroy ()) in
    ()
  with JCH_failure p ->
    pr_debug [ STR "Failure in invariant dialog: " ; p ; NL ]
       
let get_callees (mInfo:method_info_int) =
  let callees = ref [] in
  let add pc ty name ms =
    callees := (pc,ty,name ^ "." ^ ms#to_string) :: !callees in
  let _ = mInfo#bytecode_iteri (fun pc opc ->
    match opc with
    | OpInvokeVirtual (TClass cn,ms) ->
       add pc "virtual" cn#name ms
    | OpInvokeVirtual (TArray vt,ms) ->
       add pc "array" (value_type_to_string vt) ms
    | OpInvokeSpecial (cn,ms) ->
       add pc "special" cn#name ms
    | OpInvokeStatic (cn,ms) ->
       add pc "static" cn#name ms
    | OpInvokeInterface (cn,ms) ->
       add pc "interface" cn#name ms 
    | _ -> ()) in
  !callees
			       
      
let show_callees_dialog (cmsId:int) (parent:GWindow.window) =
  let cms = retrieve_cms cmsId in
  let mInfo = app#get_method cms in
  let mname = cms#method_name_string in
  let title = "Calls made by " ^ mname in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let callees = get_callees mInfo in
  let count  = List.length callees in
  let table =
    GPack.table
      ~col_spacings:25
      ~row_spacings:5
      ~columns:3
      ~rows:(count+1)
      () in
  let _ = window#add_with_viewport table#coerce in
  let _ =
    GMisc.label
      ~text:"pc"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~text:"kind"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:1)
      () in
  let _ = GMisc.label ~text:"instruction" ~xalign:0.0 
    ~packing:(table#attach ~top:0 ~left:2) () in
  let row = ref 1 in
  let _ =
    List.iter (fun (pc,kind,call) ->
        let _ =
          GMisc.label
            ~text:(string_of_int pc)
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:0)
            () in
        let _ =
          GMisc.label
            ~text:kind
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:1)
            () in
        let _ =
          GMisc.label
            ~text:call
            ~xalign:0.0 
            ~packing:(table#attach ~top:!row ~left:2)
            () in
        row := !row + 1) (List.rev callees) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response
            ~callback:(fun resp -> dialog#destroy ()) in
  ()
    
let show_callers_dialog (cmsId:int) (parent:GWindow.window) =
  let cms = retrieve_cms cmsId in
  let mInfo = app#get_method cms in
  let mname = cms#method_name_string in
  let title = "Calls made to " ^ mname in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let callers = mInfo#get_callers in
  let count  = List.length callers in
  let table =
    GPack.table
      ~col_spacings:25
      ~row_spacings:5
      ~columns:1
      ~rows:(count+1)
      () in
  let _ = window#add_with_viewport table#coerce in
  let _ =
    GMisc.label
      ~text:"callers"
      ~xalign:0.0 
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let row = ref 1 in
  let _ =
    List.iter (fun cms ->
        let _ =
          GMisc.label
            ~text:(pp_str cms#toPretty)
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:0)
            () in
        row := !row + 1) callers in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response
            ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_conditions_dialog (cmsId:int) (parent:GWindow.window) =
  let cms = retrieve_cms cmsId in
  let mInfo = app#get_method cms in
  let (name,bcfunction) = bcfunctions#get_bc_function mInfo in
  let conditions = bcfunction#get_conditions in
  let title = "Conditions in " ^ name in
  let dialog  =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let count = List.length conditions in
  let table =
    GPack.table
      ~col_spacings:25
      ~row_spacings:5
      ~columns:2
      ~rows:(count+1)
      () in
  let _ = window#add_with_viewport table#coerce in
  let _ =
    GMisc.label
      ~text:"pc"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~text:"condition"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:1)
      () in
  let row = ref 1 in
  let _ =
    List.iter (fun (pc,c) ->
        let _ =
          GMisc.label
            ~text:(string_of_int pc)
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:0)
            () in
        let _ =
          GMisc.label
            ~text:c
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:1)
            () in
    row := !row + 1) conditions in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response
            ~callback:(fun resp -> dialog#destroy ()) in
  ()
  
let show_handlers_dialog (cmsId:int) (parent:GWindow.window) =
  let cms = retrieve_cms cmsId in
  let mInfo = app#get_method cms in
  let mname = cms#method_name_string in
  let title = "Exception handlers in " ^ mname in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let pHandlers = if mInfo#has_handlers then
      mInfo#get_exception_handlers#toPretty else STR "" in
  let view = GText.view () in
  let _ = view#set_pixels_above_lines 5 in
  let _ = view#set_left_margin 10 in
  let buffer = view#buffer in
  let iter = buffer#get_iter `START in
  let _ = buffer#insert ~iter (pp_str pHandlers) in
  let contents = view#coerce in
  let _ = window#add contents in 
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response
            ~callback:(fun resp -> dialog#destroy ()) in
  ()
    
let display_assignments
      (mInfo:method_info_int)
      (varindex:int)
      (startpc:int)
      (endpc:int)
      (parent:GWindow.window)
      () =
  let title = "Assignments for variable " ^ (string_of_int varindex) in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let assignments = get_assignments mInfo varindex startpc endpc in
  let count = List.length assignments in
  let table =
    GPack.table
      ~col_spacings:25
      ~row_spacings:5
      ~columns:2
      ~rows:(count+1)
      () in
  let _ = window#add_with_viewport table#coerce in
  let _ =
    GMisc.label
      ~text:"offset"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~text:"assignment"
      ~xalign:0.0 ~packing:(table#attach ~top:0 ~left:1)
      () in
  let row = ref 1 in
  let _ =
    List.iter (fun (pc,assign) ->
        let _ =
          GMisc.label
            ~text:(string_of_int pc)
            ~xalign:1.0
            ~packing:(table#attach ~top:!row ~left:0)
            () in
        let _ =
          GMisc.label
            ~text:(pp_str assign)
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:1)
            () in
    row := !row + 1) assignments in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response
            ~callback:(fun resp -> dialog#destroy ()) in
  ()
    

let show_variable_table_dialog (cmsId:int) (parent:GWindow.window) =
  let cms = retrieve_cms cmsId in
  let mInfo = app#get_method cms in
  let mname = cms#method_name_string in
  let title = "Variable table for " ^ mname in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let vartable = if mInfo#has_local_variable_table then
      mInfo#get_local_variable_table 
    else [] in
  let vartable =
    List.sort (fun (_,_,_,_,i1) (_,_,_,_,i2) -> P.compare i1 i2) vartable in
  let count = List.length vartable in
  let table =
    GPack.table
      ~col_spacings:25
      ~row_spacings:5
      ~columns:5
      ~rows:(count+1)
      () in
  let _ = window#add_with_viewport table#coerce in
  let _ =
    GMisc.label
      ~text:"slot"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~text:"name"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:1)
      () in
  let _ =
    GMisc.label
      ~text:"type"
      ~packing:(table#attach ~top:0 ~left:2)
      () in
  let _ =
    GMisc.label
      ~text:"start-pc"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:3)
      () in
  let _ =
    GMisc.label
      ~text:"end-pc"
      ~xalign:0.0
      ~packing:(table#attach ~top:0 ~left:4)
      () in
  let row = ref 1 in
  let _ =
    List.iter (fun (startpc, length, name, ty, index) ->
        let _ =
          GMisc.label
            ~text:(string_of_int index)
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:0)
            () in
        let varButton =
          GButton.button
            ~label:name
            ~packing:(table#attach ~top:!row ~left:1)
            () in
        let _ = varButton#connect#clicked 
                  ~callback:(display_assignments
                               mInfo index startpc (startpc+length) parent) in
        let _ =
          GMisc.label
            ~text:(pp_str (value_type_to_pretty ty))
            ~packing:(table#attach ~top:!row ~left:2)
            () in
        let _ =
          GMisc.label
            ~text:(string_of_int startpc)
            ~packing:(table#attach ~top:!row ~left:3)
            () in
        let _ =
          GMisc.label
            ~text:(string_of_int (startpc + length))
            ~packing:(table#attach ~top:!row ~left:4)
            () in
    row := !row + 1) vartable in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response
            ~callback:(fun resp -> dialog#destroy ()) in
  ()
