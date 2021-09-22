(* =============================================================================
   CodeHawk C Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma and Andrew McGraw
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
open CHLogger
open CHPrettyUtil

(* cchlib *)
open CCHBasicTypes
open CCHDeclarations
open CCHCodewalker
open CCHExternalPredicate
open CCHFileContract
open CCHFileEnvironment
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHApiAssumption
open CCHFunctionAPI
open CCHInterfaceDictionary
open CCHPOPredicate
open CCHPreFileIO
open CCHPreTypes
open CCHProofObligation
open CCHProofScaffolding

(* cchgui *)
open CCHSystemDisplay
open CCHGuiRequests
open CCHGuiUtils

module H = Hashtbl


let stri = string_of_int
let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p
let p2s p = string_printer#print p
let e2s e = pp_str (exp_to_pretty e)
let x2s e = pp_str (exp_to_pretty e)
let c2xfile f = (Filename.chop_extension f) ^ ".xml"

let fenv = CCHFileEnvironment.file_environment

let show_library_summary fname summary parent  =
  let title = "Library summary for " ^ fname in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480 () in
  let addframe label lst =
    let rows = if List.length lst = 0 then 1 else List.length lst in
    let frame  =
      GBin.frame
        ~label
        ~label_xalign:1.0
        ~height:60
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~rows
        ~columns:1
        ~col_spacings:20
        ~row_spacings:10
        ~packing:window#add_with_viewport
        () in
    let row = ref 0 in
    let xalign = 0.0 in
    let _ =
      List.iter (fun p ->
          let _ =
            GMisc.label
              ~xalign
              ~text:(annotated_xpredicate_to_string p)
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          row := !row + 1) lst in
    () in
  let _ = addframe "postconditions" summary.fs_postconditions in
  let _ = addframe "error-postconditions" summary.fs_error_postconditions in
  let _ = addframe "side-effects" summary.fs_sideeffects in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()


let show_function_contract fname fncontract parent =
  let title = "Function contract for " ^ fname in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480
      () in
  let addframe label (lst:xpredicate_t list) =
    let rows = if List.length lst = 0 then 1 else List.length lst  in
    let frame  =
      GBin.frame
        ~label
        ~label_xalign:1.0
        ~height:60
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~rows
        ~columns:1
        ~col_spacings:20
        ~row_spacings:10
        ~packing:window#add_with_viewport
        () in
    let row = ref 0 in
    let xalign = 0.0 in
    let _ =
      List.iter (fun p ->
          let _ =
            GMisc.label
              ~xalign
              ~text:(pp_str (xpredicate_to_pretty p))
              ~packing:(table#attach ~top:!row  ~left:0)
              () in
          row := !row + 1) lst in
    () in
  let _ = addframe "preconditions" fncontract#get_preconditions in
  let _ = addframe "postconditions" fncontract#get_postconditions in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_proof_obligations (fname:string) ?(is_spo=false) (pos:int list) (parent:GWindow.window) =
  let pos =
    if is_spo then
      let spomanager = proof_scaffolding#get_spo_manager fname in
      List.map spomanager#get_spo pos
    else
      let ppomanager = proof_scaffolding#get_ppo_manager fname  in
      List.map ppomanager#get_ppo pos in
  let pos = List.sort (fun p1 p2 -> Stdlib.compare p1#get_location.line p2#get_location.line) pos in
  let title = "Dependent proof obligations for " ^  fname in
  let dialog = GWindow.dialog ~title ~parent ~modal:false ~show:true ~width:650 ~height:480 () in
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~packing:dialog#vbox#add
      () in
  let table =
    GPack.table
      ~rows:(List.length pos)
      ~columns:3
      ~col_spacings:20
      ~row_spacings:5
      ~packing:window#add_with_viewport
      () in
  let _ =
    GMisc.label
      ~text:"id"
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~text:"line"
      ~packing:(table#attach ~top:0 ~left:1)
      () in
  let _ =
    GMisc.label
      ~text:"proof obligation"
      ~packing:(table#attach ~top:0 ~left:2)
      () in
  let row = ref 1 in
  let _ =
    List.iter (fun po ->
        let _ =
          GMisc.label
            ~text:(string_of_int po#index)
            ~xalign:1.0
            ~packing:(table#attach ~top:!row ~left:0)
            () in
        let _ =
          GMisc.label
            ~text:(string_of_int po#get_location.line)
            ~xalign:1.0
            ~packing:(table#attach ~top:!row ~left:1)
            () in
        let _ =
          GMisc.label
            ~text:(pp_str (po_predicate_to_pretty po#get_predicate))
            ~xalign:0.0
            ~packing:(table#attach ~top:!row ~left:2)
            () in
        let  _ = row := !row + 1 in
        ()) pos in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
 
    
      
  
let show_file_precondition_request_dialog (cfilename:string) (parent:GWindow.window) =
  let title = "Function precondition requests for " ^ cfilename in
  let assumptionRequests =
    List.fold_left (fun acc fn ->
        let fnApi = proof_scaffolding#get_function_api fn.vname in
        let requests = fnApi#get_assumption_requests in
        if List.length requests > 0 then
          (fn.vname, requests)::acc
        else acc) [] fenv#get_application_functions in
  if List.length  assumptionRequests = 0 then
    log_message ("No precondition requests found for "  ^ cfilename)
  else
    let requestcount =
      List.fold_left (fun acc (_,l) ->
          acc + List.length l) 0 assumptionRequests in
    let activerequests = ref [] in
    let spq i s p = if i = 1 then s else p in
    let add_checked_conditions () =
      let count = ref 0 in
      let functionnames = new CHUtils.StringCollections.set_t in
      begin
        List.iter (fun (b,fname,a) ->
            if b#active then
              begin
                functionnames#add fname ;
                file_contract#add_precondition fname a#get_predicate ;
                count := !count + 1
              end) !activerequests ;
        save_cfile_contract () ;
        (let fns = functionnames#size in
         guilog#add
           "preconditions added"
           (LBLOCK [ STR "File: " ; STR cfilename ;
                     STR "; conditions added: " ; INT !count ;
                     STR "; for " ; INT fns ; STR (spq fns " function" " functions") ])) ;
        log_message_pp
          (LBLOCK [ STR "Added " ; INT !count ; 
                    STR " global api preconditions for: " ;
                    STR cfilename ; STR ";  " ;
                    STR " saved contracts to file" ])
      end in
    let check_all_conditions () =
      List.iter  (fun (b,_,_) -> b#set_active true) !activerequests in
    let dialog =
      GWindow.dialog
        ~title
        ~parent
        ~modal:false
        ~show:true
        ~width:650 ~height:480
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:dialog#vbox#add
        () in    
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:20
        ~columns:5
        ~rows:(requestcount + 1)
        ~packing:window#add_with_viewport
        () in
    let row = ref 1 in
    let _ =
      GMisc.label
        ~text:"add"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"function"
        ~packing:(table#attach ~top:0 ~left:1)
        () in
    let _ =
      GMisc.label
        ~text:"assumption"
        ~packing:(table#attach ~top:0 ~left:2)
        () in
    let _ =
      GMisc.label
        ~text:"ppos"
        ~packing:(table#attach ~top:0 ~left:3)
        () in
    let _ =
      GMisc.label
        ~text:"spos"
        ~packing:(table#attach ~top:0 ~left:4)
        () in
    let _  =
      List.iter (fun (fname,l) ->
          let _ =
            List.iter (fun a ->
                let ppos = a#get_dependent_ppos in
                let spos = a#get_dependent_spos in
                let addButton =
                  GButton.check_button
                    ~label:""
                    ~packing:(table#attach ~top:!row ~left:0)
                    () in
                let _ = activerequests := (addButton,fname,a) :: !activerequests in
                let _ =
                  GMisc.label
                    ~xalign:0.0
                    ~text:fname
                    ~packing:(table#attach ~left:1 ~top:!row)
                    () in
                let _ =
                  GMisc.label
                    ~xalign:0.0
                    ~text:(pp_str a#toPretty)
                    ~packing:(table#attach ~left:2 ~top:!row)
                    () in
                let _ =
                  if List.length ppos > 0 then
                    let ppobutton =
                      GButton.button
                        ~label:(string_of_int (List.length ppos))
                        ~packing:(table#attach ~top:!row ~left:3)
                        () in
                    let _ =
                      ppobutton#connect#clicked
                        ~callback:(fun () -> show_proof_obligations fname ppos parent) in
                    () in
                let _ =
                  if List.length spos > 0 then
                    let spobutton =
                      GButton.button
                        ~label:(string_of_int (List.length spos))
                        ~packing:(table#attach ~top:!row ~left:4)
                        () in
                    let _ =
                      spobutton#connect#clicked
                        ~callback:(fun () ->
                          show_proof_obligations
                            ~is_spo:true fname spos parent) in
                    () in
                let _ =
                  if file_contract#has_function_contract fname then
                    let fncontract = file_contract#get_function_contract fname in
                    let button =
                      GButton.button
                        ~label:"function contract"
                        ~packing:(table#attach ~top:!row ~left:5)
                        () in
                    let _ =
                      button#connect#clicked
                        ~callback:(fun () ->
                          show_function_contract fname fncontract parent) in
                    ()  in
                row := !row + 1) l in
          ()) assumptionRequests in
    let checkAllButton =
      GButton.button
        ~label:"check all"
        ~packing:dialog#action_area#add
        () in
    let _ =
      checkAllButton#connect#clicked
        ~callback:(fun () -> check_all_conditions ()) in
    let addCheckedButton =
      GButton.button
        ~label:"add checked conditions"
        ~packing:dialog#action_area#add
        () in
    let _ =
      addCheckedButton#connect#clicked
        ~callback:(fun () -> add_checked_conditions ()) in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun ()->()) in
    let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
    ()
    

let show_file_postcondition_request_dialog (cfilename:string) (parent:GWindow.window) =
  let title = "Function postcondition requests for " ^ cfilename in
  let get_callee_name fdecls index =
    if index >= 0 then (fdecls#get_varinfo_by_vid index).vname else "global" in
  let is_local index = (index >= 0) && (fenv#is_application_function index) in
  let is_preserves_all_memory x =
    match x with XPreservesAllMemory -> true | _ -> false  in
  let get_callee_file fdecls index =
    if index >= 0 then
      let vname = (fdecls#get_varinfo_by_vid index).vname in
      if fenv#has_external_header vname then
        fenv#get_external_header vname ^ ".h"
      else if function_summary_library#has_builtin_summary vname then
        "__builtin__"
      else if fenv#is_application_function index then
        cfilename
      else
         "?"
    else
      "global" in
  let has_function_summary fdecls index =
    if index >= 0 then
      let vname = (fdecls#get_varinfo_by_vid index).vname  in
      if fenv#has_external_header vname then
        let header = fenv#get_external_header vname in
        function_summary_library#has_summary header vname
      else
        function_summary_library#has_builtin_summary vname
    else
      false in
  let get_function_summary fdecls index =
    let vname = (fdecls#get_varinfo_by_vid index).vname  in
    function_summary_library#get_summary vname in
  let is_active_request ppomgr spomgr (r:postcondition_request_int) =
    let fp p = not (ppomgr#get_ppo p)#is_closed in
    let fs s = not (spomgr#get_spo s)#is_closed in
    let ppos = List.filter fp r#get_dependent_ppos in
    let spos = List.filter fs r#get_dependent_spos in
    (List.length ppos) + (List.length spos) > 0 in
  let assumptionRequests =
    List.fold_left (fun acc fn ->
        let fnApi = proof_scaffolding#get_function_api fn.vname in
        let ppomgr = proof_scaffolding#get_ppo_manager fn.vname in
        let spomgr = proof_scaffolding#get_spo_manager fn.vname in
        let requests = fnApi#get_postcondition_requests in
        let requests = List.filter (is_active_request ppomgr spomgr) requests in
        if List.length requests > 0 then
          (fn.vname, requests)::acc
        else acc) [] fenv#get_application_functions in
  if List.length  assumptionRequests = 0 then
    log_message ("No postcondition requests found for "  ^ cfilename)
  else
    let activerequests = ref [] in
    let add_checked_conditions () =
      let count = ref 0 in
      let functionnames = new CHUtils.StringCollections.set_t in
      begin
        List.iter (fun (b,callee,r) ->
            if b#active then
              let fncontract = file_contract#get_function_contract callee in
              begin
                functionnames#add callee ;
                fncontract#add_postcondition r#get_postcondition ;
                count := !count + 1
              end) !activerequests ;
        save_cfile_contract () ;
        guilog#add "postconditions added"
                   (LBLOCK [ STR "File: " ; STR cfilename ;
                             STR "; conditions added: " ; INT !count ;
                             STR "; for " ; INT functionnames#size ; STR " functions" ]) ;
        log_message_pp
          (LBLOCK [ STR "Added " ; INT !count ;
                    STR " postconditions to function contracts for: " ;
                    STR cfilename ; STR "; " ;
                    STR " saved contracts to file" ])
      end in            
    let requestcount =
      List.fold_left (fun acc (_,l) ->
          acc + List.length l) 0 assumptionRequests in
    let dialog =
      GWindow.dialog
        ~title ~parent
        ~modal:false
        ~show:true
        ~width:1200
        ~height:850
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:dialog#vbox#add
        () in    
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:20
        ~columns:10
        ~rows:(requestcount + 1)
        ~packing:window#add_with_viewport
        () in
    let row = ref 1 in
    let _ =
      GMisc.label
        ~text:"add"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"function"
        ~packing:(table#attach ~top:0 ~left:1)
        () in
    let _ =
      GMisc.label
        ~text:"callee"
        ~packing:(table#attach ~top:0 ~left:2)
        () in
    let _ =
      GMisc.label
        ~text:"callee file"
        ~packing:(table#attach ~top:0 ~left:3)
        () in
    let _ =
      GMisc.label
        ~text:"condition request"
        ~packing:(table#attach ~top:0 ~left:4)
        ()  in
    let _ =
      GMisc.label
        ~text:"ppos"
        ~packing:(table#attach ~top:0 ~left:5)
        () in
    let _ =
      GMisc.label
        ~text:"spos"
        ~packing:(table#attach ~top:0 ~left:6)
        () in
    let _ =
      GMisc.label
        ~text:"library"
        ~packing:(table#attach ~top:0 ~left:7)
        () in
    let _ =
      GMisc.label
        ~text:"contract"
        ~packing:(table#attach ~top:0 ~left:8)
        () in
    let _ =
      GMisc.label
        ~text:"additional info"
        ~packing:(table#attach ~top:0 ~left:9)
        () in
    let _  =
      List.iter (fun (fname,l) ->
          let _ =
            List.iter (fun r->
                let fundec = read_function_semantics fname in
                let fdecls = fundec.sdecls in
                let calleename = get_callee_name fdecls r#get_callee in
                let calleefile = get_callee_file fdecls r#get_callee in
                let ppos = r#get_dependent_ppos in
                let spos = r#get_dependent_spos in
                let _ =
                  if is_local r#get_callee
                     && file_contract#has_function_contract calleename then
                    let addButton =
                      GButton.check_button
                        ~label:""
                        ~packing:(table#attach ~top:!row ~left:0)
                        () in
                    activerequests := (addButton,calleename,r) :: !activerequests
                  else
                    () in
                let _ =
                  GMisc.label
                    ~xalign:0.0
                    ~text:fname
                    ~packing:(table#attach ~left:1 ~top:!row)
                    () in
                let _ =
                  GMisc.label
                    ~xalign:0.0 ~text:calleename
                    ~packing:(table#attach ~left:2 ~top:!row)
                    () in
                let _ =
                  GMisc.label
                    ~xalign:0.0
                    ~text:calleefile
                    ~packing:(table#attach ~left:3 ~top:!row)
                    () in
                let _ =
                  GMisc.label
                    ~xalign:0.0
                    ~text:(pp_str r#toPretty)
                    ~packing:(table#attach ~left:4 ~top:!row)
                    () in
                let _ =
                  if List.length ppos > 0 then
                    let ppobutton =
                      GButton.button
                        ~label:(string_of_int (List.length ppos))
                        ~packing:(table#attach ~top:!row ~left:5)
                        () in
                    let _ =
                      ppobutton#connect#clicked
                        ~callback:(fun () ->
                          show_proof_obligations fname ppos parent) in
                    () in
                let _ =
                  if List.length spos > 0 then
                    let spobutton =
                      GButton.button
                        ~label:(string_of_int (List.length spos))
                        ~packing:(table#attach ~top:!row ~left:6)
                        () in
                    let _ =
                      spobutton#connect#clicked
                        ~callback:(fun () ->
                          show_proof_obligations ~is_spo:true fname spos parent) in
                    () in
                let _ =
                  if List.mem calleename [ "free"; "realloc" ;  "regfree" ]
                     && is_preserves_all_memory r#get_postcondition then
                    let _ =
                      GMisc.label
                        ~xalign:0.0
                        ~text:("PRQ:preserves-all-memory-x")
                        ~packing:(table#attach ~top:!row  ~left:7)
                        () in
                    ()
                  else if has_function_summary fdecls r#get_callee then
                    let summary = get_function_summary fdecls r#get_callee in
                    let button =
                      GButton.button
                        ~label:"view summary"
                        ~packing:(table#attach ~top:!row ~left:7)
                        () in
                    let _ =
                      button#connect#clicked
                        ~callback:(fun () ->
                          show_library_summary calleename summary parent) in
                    ()
                  else if file_contract#has_function_contract calleename then
                    let fncontract = file_contract#get_function_contract calleename in
                    let xtag = xpredicate_tag r#get_postcondition in
                    let notes = fncontract#get_tagged_notes xtag in
                    let label =
                      match notes with
                      | [] -> "view contract"
                      | l ->
                         String.concat
                           ";" (List.map (fun n -> n.cn_txt ^ ";PRQ:" ^ n.cn_prq) l) in
                    let button =
                      GButton.button
                        ~label
                        ~packing:(table#attach ~top:!row ~left:8)
                        () in
                    let _ =
                      button#connect#clicked
                        ~callback:(fun () ->
                          show_function_contract calleename fncontract parent) in
                    ()
                  else
                    let button =
                      GButton.button
                        ~label:"record missing"
                        ~packing:(table#attach ~top:!row ~left:7)
                        () in
                    let nppos = List.length ppos in
                    let nspos = List.length spos in
                    let _ =
                      button#connect#clicked
                        ~callback:(fun () ->
                          record_missing_summary calleefile calleename nppos nspos) in
                    () in
                let _ =
                  let button =
                    GButton.button
                      ~label:"request"
                      ~packing:(table#attach ~top:!row ~left:9)
                      () in
                  let nppos = List.length ppos in
                  let nspos = List.length spos in
                  let _ =
                    button#connect#clicked
                      ~callback:(fun () ->
                        record_postcondition_request
                          calleefile calleename (pp_str r#toPretty) nppos nspos) in
                  () in
                    
                row := !row + 1) l in
          ()) assumptionRequests in
    let addCheckedButton =
      GButton.button
        ~label:"add checked conditions"
        ~packing:dialog#action_area#add
        () in
    let _ = addCheckedButton#connect#clicked
          ~callback:(fun () -> add_checked_conditions ()) in
    let _ = dialog#add_button_stock `CLOSE `CLOSE in
    let _ = dialog#connect#close ~callback:(fun ()->()) in
    let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
    ()

let show_function_assumptions_dialog cfilename fname parent =
  let title = "Assumptions for " ^ fname  in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480 () in
  let fundec = read_function_semantics fname in
  let fnApi = proof_scaffolding#get_function_api fname in
  let get_callee index =
    if index >= 0 then (fundec.sdecls#get_varinfo_by_vid index).vname else "global" in
  let _ =
    let lst = fnApi#get_api_assumptions in
    let lst =
      List.map (fun a ->
          (a, List.map snd (collect_indexed_predicate_expressions a#get_predicate))) lst in
    let lst =
      List.concat
        (List.map
           (fun (a,el) ->
             List.fold_left
               (fun acc e ->
                 match e with
                 | Const _ | CastE (_,Const _) -> acc
                 | _ -> (a,e)::acc) [] el) lst) in                     
    let lst = List.map (fun (a,e) -> (a, e2s e)) lst in
    let lst = List.sort (fun (_,e1) (_,e2) -> Stdlib.compare e1 e2) lst in
    let rows = List.length lst + 1 in
    let frame =
      GBin.frame
        ~label:"api assumptions"
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        ()  in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:15
        ~rows
        ~columns:3
        ~packing:window#add_with_viewport
        () in
    let _ =
      GMisc.label
        ~text:"parameter"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"api condition imposed"
        ~packing:(table#attach  ~top:0 ~left:2)
        () in
    let row = ref 1 in
    let _ =
      List.iter (fun (a,e) ->
          let xalign = 0.0 in
          let _ =
            GMisc.label
              ~xalign
              ~text:e
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:":"
              ~packing:(table#attach ~top:!row ~left:1)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(p2s a#toPretty)
              ~packing:(table#attach ~top:!row ~left:2)
              () in
          row := !row + 1) lst in
    () in
  let _ =
    let lst = fnApi#get_contract_assumptions in
    let rows = List.length lst + 1 in
    let frame =
      GBin.frame
        ~label:"contract assumptions"
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT ~packing:dialog#vbox#add
        ()  in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:15
        ~rows
        ~columns:3
        ~packing:window#add_with_viewport
        () in
    let _ =
      GMisc.label
        ~text:"callee"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"postcondition assumed"
        ~packing:(table#attach ~top:0 ~left:2)
        () in
    let row = ref 1 in
    let _ =
      List.iter (fun a ->
          let xalign = 0.0 in
          let _ =
            GMisc.label
              ~xalign
              ~text:(get_callee a#get_callee)
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:":"
              ~packing:(table#attach ~top:!row ~left:1)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(p2s a#toPretty)
              ~packing:(table#attach ~top:!row ~left:2)
              () in
          row := !row + 1) lst in
    () in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_function_guarantees_dialog cfilename fname parent =
  let title = "Guarantees for " ^ fname in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480 () in
  let fnApi  = proof_scaffolding#get_function_api fname in
  let add_function_contract () =
    let fundec = read_function_semantics fname in
    let fdecls = fundec.sdecls in
    let formals = List.map (fun v -> v.vname) fdecls#get_formals in
    begin
      file_contract#add_function_contract fname formals ;
      save_cfile_contract ()
    end in
  let addframe label (lst:xpredicate_t  list) =
    let rows = (List.length lst) + 1 in
    let frame =
      GBin.frame
        ~label
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:15
        ~rows
        ~columns:1
        ~packing:window#add_with_viewport
        () in
    let row = ref 1 in
    let _ =
      List.iter (fun x ->
          let xalign = 0.0 in
          let _ =
            GMisc.label
              ~text:(pp_str (xpredicate_to_pretty x))
              ~xalign
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          row := !row + 1) lst in
    () in
  let _ = addframe "postcondition guarantees" fnApi#get_postcondition_guarantees in
  let _ =
    if file_contract#has_function_contract fname then
      let fncontract = file_contract#get_function_contract fname in
      let _ = addframe "contract postconditions" fncontract#get_postconditions in
      ()
    else
      let button =
        GButton.button
          ~label:"add function\n  contract"
          ~packing:dialog#action_area#add
          ()  in
      let _ =
        button#connect#clicked
          ~callback:(fun () -> add_function_contract ()) in
      () in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  
  
let show_function_requests_dialog cfilename fname parent =
  let title = "Requests for " ^ fname in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480
      () in
  let fundec = read_function_semantics fname in
  let fnApi  = proof_scaffolding#get_function_api fname in
  let get_callee index =
    if index >= 0 then
      (fundec.sdecls#get_varinfo_by_vid index).vname
    else
      "global" in
  let _ =
    let lst = fnApi#get_assumption_requests in
    let lst =
      List.map (fun a ->
          (a,get_xpredicate_global_variables a#get_predicate)) lst in
    let lst =
      List.concat
        (List.map
           (fun (a,gl) ->
             List.fold_left (fun acc g -> (a,g) :: acc) [] gl) lst) in
    let lst = List.sort (fun (_,g1) (_,g2) -> Stdlib.compare g1 g2) lst in
    let rows = List.length lst in
    let frame =
      GBin.frame
        ~label:"global api assumption requests"
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:15
        ~rows
        ~columns:3
        ~packing:window#add_with_viewport
        () in
    let _ =
      GMisc.label
        ~text:"global variable"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"api condition requested"
        ~packing:(table#attach  ~top:0 ~left:2)
        () in
    let row = ref 1 in
    let _ =
      List.iter (fun (a,g) ->
          let xalign = 0.0 in
          let _ =
            GMisc.label
              ~xalign
              ~text:g
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:":"
              ~packing:(table#attach ~top:!row ~left:1)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(p2s a#toPretty)
              ~packing:(table#attach ~top:!row ~left:2)
              () in
          row := !row + 1) lst in
    () in
  let _ =
    let lst = fnApi#get_postcondition_requests in
    let lst = List.map (fun pc -> (pc,get_callee  pc#get_callee)) lst in
    let lst = List.sort (fun (_,c1) (_,c2) -> Stdlib.compare c1 c2) lst in
    let rows = List.length lst + 1 in
    let frame =
      GBin.frame
        ~label:"postcondition requests"
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        ()  in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:15
        ~rows
        ~columns:3
        ~packing:window#add_with_viewport
        () in
    let _ =
      GMisc.label
        ~text:"callee"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"postcondition assumed"
        ~packing:(table#attach ~top:0 ~left:2)
        () in
    let row = ref 1 in
    let _ =
      List.iter (fun (a,c) ->
          let xalign = 0.0 in
          let _ =
            GMisc.label
              ~xalign
              ~text:c
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:":"
              ~packing:(table#attach ~top:!row ~left:1)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(p2s a#toPretty)
              ~packing:(table#attach ~top:!row ~left:2)
              () in
          row := !row + 1) lst in
    () in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_function_variables_dialog cfilename fname parent =
  let title = "Variables of " ^ fname in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let fundec = read_function_semantics fname in
  let fdecls = fundec.sdecls in
  let mkTable label variables =
    let rows = (List.length variables) + 1 in
    let columns = 3 in
    let frame =
      GBin.frame
        ~label
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:15
        ~columns ~rows
        ~packing:window#add_with_viewport
        () in
    let _ =
      GMisc.label
        ~text:"name"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"type"
        ~packing:(table#attach ~top:0 ~left:1)
        () in
    let row = ref 1 in
    let xalign = 0.0 in
    let _ =
      List.iter (fun f ->
          let _ =
            GMisc.label
              ~xalign
              ~text:f.vname
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(pp_str (typ_to_pretty f.vtype))
              ~packing:(table#attach ~top:!row ~left:1)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(pp_str (typ_to_pretty (fenv#get_type_unrolled f.vtype)))
              ~packing:(table#attach ~top:!row ~left:2)
              () in
          row := !row + 1) variables in
    () in
  let _ = mkTable "parameters" fdecls#get_formals in
  let _ = mkTable "local variables" fdecls#get_locals in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  

let show_global_variables_dialog cfilename parent =
  let title = "Global variables of " ^ cfilename in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let mkTable label variables =
    let rows = (List.length variables) + 1 in
    let columns = 6 in
    let frame =
      GBin.frame
        ~label
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    let table =
      GPack.table
        ~row_spacings:5
        ~col_spacings:15
        ~columns
        ~rows
        ~packing:window#add_with_viewport
        () in
    let _ =
      GMisc.label
        ~text:"name"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~text:"type"
        ~packing:(table#attach ~top:0 ~left:1)
        () in
    let _ =
      GMisc.label
        ~text:"basic type"
        ~packing:(table#attach ~top:0 ~left:2)
        () in
    let _ =
      GMisc.label
        ~text:"storage"
        ~packing:(table#attach ~top:0  ~left:3)
        () in
    let _ =
      GMisc.label
        ~text:"attributes"
        ~packing:(table#attach ~top:0 ~left:4)
        () in
    let _ =
      GMisc.label
        ~text:"initializer"
        ~packing:(table#attach ~top:0 ~left:5)
        () in
    let row = ref 1 in
    let xalign = 0.0 in
    let _ =
      List.iter (fun v ->
          try
          let storage = storage_to_string v.vstorage in
          let volatile = if is_volatile_type v.vtype then "volatile" else "" in
          let vinit = match v.vinit with
            | None -> ""
            | Some (SingleInit e) -> e2s e
            | Some _ -> "compound" in
          let _ =
            GMisc.label
              ~xalign
              ~text:v.vname
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(pp_str (typ_to_pretty v.vtype))
              ~packing:(table#attach ~top:!row ~left:1)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:(pp_str (typ_to_pretty (fenv#get_type_unrolled v.vtype)))
              ~packing:(table#attach ~top:!row ~left:2)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:storage
              ~packing:(table#attach ~top:!row ~left:3)
              () in
          let _ =
            GMisc.label
              ~xalign ~text:volatile
              ~packing:(table#attach ~top:!row ~left:4)
              () in
          let _ =
            GMisc.label
              ~xalign
              ~text:vinit
              ~packing:(table#attach ~top:!row ~left:5)
              () in
          row := !row + 1
          with
          | CCHFailure p ->
             ch_error_log#add
               "opaque" (LBLOCK [ STR "Error: " ; p ; NL])) variables in
    () in
  let gvars = fenv#get_globalvars in
  let gvars =
    List.filter (fun v ->
        match v.vtype with TFun _ -> false | _ -> true) gvars in
  let gvars = List.sort (fun v1 v2 -> Stdlib.compare v1.vname v2.vname) gvars in
  let _ = mkTable "global variables" gvars in
  let opaquevars =
    try
      cdeclarations#get_opaque_varinfos
    with
    |  CCHFailure  p ->
        begin
          ch_error_log#add
            "opaque"
            (LBLOCK [ STR "Error in get-opaque vars: " ; p ; NL ]) ;
          []
        end in
  let _ =
    write_message_pp
      (LBLOCK [ STR "Opaque variables: " ;
                pretty_print_list opaquevars  (fun v -> STR v.vname) "[" "," "]" ; NL ]) in
  let _ =
    if (List.length opaquevars) > 0 then
      mkTable "opaque variables" opaquevars in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let show_callees_dialog cfilename fname parent = 
  let title = "Callees of " ^ fname in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let mkTable label rows columns =
    let frame =
      GBin.frame
        ~label
        ~label_xalign:1.0
        ~shadow_type:`ETCHED_OUT
        ~packing:dialog#vbox#add
        () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        ~packing:frame#add
        () in
    GPack.table
      ~row_spacings:5
      ~col_spacings:5
      ~columns
      ~rows 
      ~packing:window#add_with_viewport
      () in
  let rec indirect_calls_to_string indirect_callees =
  let rec build_string indirect_callees =
    match indirect_callees with
      | [] -> ""
      | [x] -> x
      | hd :: l -> (build_string l) ^ hd ^ ", " in
    build_string indirect_callees in
  let directCalls = proof_scaffolding#get_direct_callsites fname in
  let indirectCalls = proof_scaffolding#get_indirect_callsites fname in
  let directTable = mkTable "direct calls"  ((List.length directCalls) + 1) 3 in
  let indirectTable = mkTable "indirect calls" ((List.length indirectCalls) + 1) 3 in
  let entry (table:GPack.table) row text xalign n =
    GMisc.label
      ~xalign
      ~text 
      ~packing:(table#attach ~top:row ~left:n)
      () in
  let args2s args = "(" ^ (String.concat "," (List.map x2s args)) ^ ")" in
  let row = ref 1 in
  let _ = List.iter (fun d ->
    let entry text xalign n = entry directTable !row text xalign n in
    let _ = entry (string_of_int d#get_location.line) 0.0 1 in
    let _ = entry (d#get_callee).vname 0.0 2 in
    let _ = entry (args2s d#get_arguments) 0.0 3 in
    row := !row + 1) directCalls in
  let row = ref 1 in
  let _ = List.iter (fun d ->
    let entry text xalign n = entry indirectTable !row text xalign n in
    let _ = entry (string_of_int d#get_location.line) 0.0 1 in
    let indirect_callees = List.map (fun x -> x.vname) d#get_callees in
    let _ = entry (indirect_calls_to_string indirect_callees) 0.0 2 in
    let _ = entry (args2s d#get_arguments) 0.0 3 in
    row := !row + 1) indirectCalls in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun () -> ()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
