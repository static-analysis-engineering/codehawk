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

(* cchlib *)
open CCHBasicTypes
open CCHUtilities

(* cchpre *)
open CCHPOPredicate
open CCHInvariantFact
open CCHPOExplanations
open CCHPreFileIO
open CCHPreTypes
open CCHProofObligation
open CCHProofScaffolding

(* cchgui *)
open CCHSystemDisplay
open CCHGuiRequests
open CCHGtkUtils

module H = Hashtbl


let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p
let stri = string_of_int

let read_xpm_file name =
  let xpmpath = get_xpm_path () in
  let file = xpmpath ^ "/" ^ name ^ ".xpm" in
  GDraw.pixmap_from_xpm ~file ()

let ppo_pixmaps = H.create 7  

let set_ppo_pixmaps () =
  begin
    H.add ppo_pixmaps "check-valid" (read_xpm_file "checkvalid") ;
    H.add ppo_pixmaps "invariants" (read_xpm_file "invariants") ;
    H.add ppo_pixmaps "rv" (read_xpm_file "rv") ;
    H.add ppo_pixmaps "api" (read_xpm_file "api") ;
    H.add ppo_pixmaps "ds" (read_xpm_file "ds") ;
    H.add ppo_pixmaps "reduced" (read_xpm_file "reduced") ;
    H.add ppo_pixmaps "global" (read_xpm_file "global") ; 
    H.add ppo_pixmaps "open" (read_xpm_file "openpo") ;
    H.add ppo_pixmaps "opendiag" (read_xpm_file "openwithdiags") ;
    H.add ppo_pixmaps "opaque" (read_xpm_file "opaque") ;
    H.add ppo_pixmaps "violation" (read_xpm_file "violation") ;
    H.add ppo_pixmaps "unreachable" (read_xpm_file "unreachable") ;
  end

let get_ppo_pixmap tag =
  if H.mem ppo_pixmaps tag then H.find ppo_pixmaps tag else
    begin
      write_message ("No pixmap found for " ^ tag) ;
      raise (CCHFailure (LBLOCK [ STR "No pixmap found for " ; STR tag ]))
    end

let c2xfile f = (Filename.chop_extension f) ^ ".xml"

let add_diagnostic_window invio diagnostic dialog =
  let window = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~height:320
    ~packing:dialog#vbox#add () in
  let view = GText.view () in
  let buffer = view#buffer in
  let invs = diagnostic#get_invariants in
  let invmsgs = LBLOCK (List.map  (fun p -> LBLOCK [ p ; NL ]) (get_invariant_messages invio invs)) in
  let iter = buffer#get_iter `START in
  let _ =
    if diagnostic#is_empty then
      (buffer#insert
         ~iter (pp_str (LBLOCK [ STR "No diagnostic message to show" ; NL ])))
    else
      (buffer#insert
         ~iter (pp_str (LBLOCK [ diagnostic#toPretty ; invmsgs 
                                 ; diagnostic#arg_messages_to_pretty 
                                 ; diagnostic#key_messages_to_pretty ; NL]))) in
  let contents = view#coerce in
  let _ = window#add contents in
  ()

let add_invariants_window invariants dialog =
  let window =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC
      ~vpolicy:`AUTOMATIC
      ~height:320
      ~packing:dialog#vbox#add
      () in
  let view = GText.view () in
  let buffer = view#buffer in
  let iter = buffer#get_iter `START in
  let _ =
    List.iter (fun inv ->
        let _ = buffer#insert ~iter (pp_str (LBLOCK [ inv#toPretty ; NL ])) in
        ()) invariants in
  let contents = view#coerce in
  let _ = window#add contents in 
  ()

let add_predicate_frame predicate dialog =
  let frame =
    GBin.frame
      ~label:"predicate"
      ~label_xalign:1.0
      ~height:60
      ~shadow_type:`ETCHED_OUT
      ~packing:dialog#vbox#add
      () in
  let text = pp_str (po_predicate_to_pretty predicate) in
  let _ =
    GMisc.label
      ~xalign:0.1
      ~text
      ~packing:frame#add
      () in
  ()

let add_explanation_frame explanation dialog = 
  let frame =
    GBin.frame
      ~label:"explanation"
      ~label_xalign:1.0
      ~height:60
      ~shadow_type:`ETCHED_OUT
      ~packing:dialog#vbox#add
      () in
  let _ =
    GMisc.label
      ~xalign:0.1
      ~text:explanation
      ~packing:frame#add
      () in
  ()

let add_assumptions_frame fnApi assumptions dialog =
  let get_assumption (sym,id) =
    match sym#getBaseName with
    | "api" -> (fnApi#get_api_assumption id)#toPretty 
    | "rv" -> (fnApi#get_rv_assumption id)#toPretty
    | "global" -> (fnApi#get_global_assumption id)#toPretty
    | _ -> STR "unknown" in
  match assumptions with
  | [] -> ()
  | l ->
     let frame =
       GBin.frame
         ~label:"assumptions"
         ~label_xalign:1.0
         ~height:60
         ~shadow_type:`ETCHED_OUT
         ~packing:dialog#vbox#add
         () in
     let text =
       String.concat
         "\n" (List.map (fun a -> pp_str (get_assumption a)) l) in
     let _ =
       GMisc.label
         ~xalign:0.1
         ~text
         ~packing:frame#add
         () in
    ()


let show_explanation predicate explanation parent =
  let title = "Evidence for ppo TODO" in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480
      () in
  let _ = add_predicate_frame predicate dialog in
  let _ = add_explanation_frame explanation dialog in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()


let show_invariants id predicate invariants parent =
  let title = "Invariants for ppo " ^ (string_of_int id) in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480
      () in
  let _ = add_predicate_frame predicate dialog in
  let _ = add_invariants_window invariants dialog in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()

let report_diagnostic filename fname id predicate invio diagnostic =
  let invs = diagnostic#get_invariants in
  let invs = List.map pp_str (get_invariant_messages invio invs) in
  let diag = pp_str diagnostic#toPretty in
  let darg = pp_str diagnostic#arg_messages_to_pretty in
  let dkey = pp_str diagnostic#key_messages_to_pretty in
  report_rfi
    {
      dr_filename = filename ;
      dr_fname = fname ;
      dr_isppo = true ;
      dr_po_id = id ;
      dr_predicate_tag = po_predicate_tag predicate ;
      dr_predicate = pp_str (po_predicate_to_pretty predicate) ;
      dr_diagnostics = invs @ [ diag ; darg ; dkey ]
    }

let investigate filename fname id predicate invio diagnostic =
  let invs = diagnostic#get_invariants in
  let invs = List.map pp_str (get_invariant_messages invio invs) in
  let diag = pp_str diagnostic#toPretty in
  let darg = pp_str diagnostic#arg_messages_to_pretty in
  let dkey = pp_str diagnostic#key_messages_to_pretty in
  report_investigate
    {
      dr_filename = filename ;
      dr_fname = fname ;
      dr_isppo = true ;
      dr_po_id = id ;
      dr_predicate_tag = po_predicate_tag predicate ;
      dr_predicate = pp_str (po_predicate_to_pretty predicate) ;
      dr_diagnostics = invs @ [ diag ; darg ; dkey ]
    }

let show_diagnostic filename fname id predicate invio diagnostic parent =
  let title = "Diagnostic for ppo " ^ (string_of_int id) in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:650
      ~height:480
      () in
  let _ = add_predicate_frame predicate dialog in
  let _ = add_diagnostic_window invio diagnostic dialog in
  let _ =
    let button =
      GButton.button
        ~label:"report"
        ~packing:dialog#action_area#add
        () in
    let _ =
      button#connect#clicked
        ~callback:(fun () ->
          report_diagnostic filename fname id predicate invio diagnostic) in
    () in
  let _ =
    let button =
      GButton.button
        ~label:"investigate"
        ~packing:dialog#action_area#add
        () in
    let _ =
      button#connect#clicked
        ~callback:(fun () ->
          investigate filename fname id predicate invio diagnostic) in
    () in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  

let get_ppo_button filename fname  invio ppo packing parent =
  let id = ppo#index in
  let predicate = ppo#get_predicate in
  let explanation = ppo#get_explanation in
  let diagnostic = ppo#get_diagnostic in
  let dependencies = ppo#get_dependencies in
  let button = GButton.button ~packing () in
  let bbutton = GPack.hbox ~border_width:2 ~packing:button#add () in
  if not ppo#is_closed then
    let piximage =
      if ppo#is_opaque then
        "opaque"
      else if diagnostic#is_empty then
        "open"
      else
        "opendiag" in
    let _ =
      GMisc.pixmap
        (get_ppo_pixmap piximage)
        ~packing:(bbutton#pack ~padding:2)
        () in 
    let _ =
      button#event#connect#button_press
        ~callback:(fun e ->
          show_diagnostic filename fname id predicate invio diagnostic parent ; true) in
    ()
  else 
    let piximage =
      if ppo#is_violation then
        "violation"
      else
        match dependencies with
        | None -> let _ = pr_debug [ STR "No dependency" ; NL ] in "violation"
        | Some DStmt -> "check-valid"
        | Some (DLocal _) -> "invariants"
        | Some (DReduced _) -> "reduced"
        | Some (DEnvC (_, assumptions)) -> 
           let contract_assumes =
             List.filter (fun x ->
                 match x with
                 | GlobalAssumption (_)
                   | PostAssumption (_,_) -> true
                 | _ -> false
               ) assumptions in
           if List.length contract_assumes > 0 then "rv" else "api"
        | Some DUnreachable (_) -> "unreachable" in
    let _ =
      GMisc.pixmap
        (get_ppo_pixmap piximage)
        ~packing:(bbutton#pack ~padding:2)
        () in
    let labels =
      [ ("predicate: " ^ (pp_str (po_predicate_to_pretty predicate))) ;
        ("reason   : " ^ explanation) ] in
    let _ = attach_popup_menu button labels in
    let _ =
      button#event#connect#button_press
        ~callback:(fun a ->
          show_explanation predicate explanation parent ; true) in
    ()

let show_po_explanation g (parent:GWindow.window) =
  let title = "Explanation for proof obligation predicate " ^ g in
  let dialog =
    GWindow.dialog
      ~title
      ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let _ =
    if has_po_explanation g  then
      let explanation = get_po_explanation g in
      let hbox =
        GPack.hbox
          ~homogeneous:false
          ~packing:dialog#vbox#add
          () in
      let frame1 =
        GBin.frame
          ~shadow_type:`ETCHED_OUT
          ~height:20
          ~packing:hbox#add
          () in
      let _ =
        GMisc.label
          ~text:(pp_str (prototype_to_pretty  explanation))
          ~ypad:5
          ~packing:frame1#add
          () in
      let frame2 =
        GBin.frame
          ~shadow_type:`ETCHED_OUT
          ~height:20
          ~packing:hbox#add
          () in      
      let _ =
        GMisc.label
          ~text:"severity: undefined behavior"
          ~ypad:5
          ~packing:frame2#add
          () in
      let _ =
        let rows = (List.length explanation.pox_arguments) + 1 in
        let frame =
          GBin.frame
            ~label:"parameters"
            ~height:40
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
            ~columns:4 ~rows
            ~packing:window#add_with_viewport
            () in
        let _ =
          GMisc.label
            ~text:"index"
            ~packing:(table#attach ~top:0 ~left:0)
            () in
        let _ =
          GMisc.label
            ~text:"name"
            ~packing:(table#attach ~top:0 ~left:1)
            () in
        let _ =
          GMisc.label
            ~text:"type"
            ~packing:(table#attach ~top:0 ~left:2)
            () in
        let _ =
          GMisc.label
            ~text:"description"
            ~xalign:0.0
            ~packing:(table#attach ~top:0 ~left:3)
            () in
        let row = ref 1 in
        let _ =
          List.iter (fun (index,name,vtype,desc) ->
              let _ =
                GMisc.label
                  ~text:(stri index)
                  ~packing:(table#attach ~top:!row ~left:0)
                  () in
              let _ =
                GMisc.label
                  ~text:name
                  ~packing:(table#attach ~top:!row ~left:1)
                  () in
              let _ =
                GMisc.label
                  ~text:vtype
                  ~packing:(table#attach ~top:!row ~left:2)
                  () in
              let _ =
                GMisc.label
                  ~text:desc
                  ~xalign:0.0
                  ~packing:(table#attach ~top:!row ~left:3)
                  () in
              row := !row + 1) explanation.pox_arguments in
        () in
      let _ =
        let frame =
          GBin.frame
            ~label:"description"
            ~height:20
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
        let view = GText.view ~packing:window#add_with_viewport () in
        let buffer = view#buffer in
        let iter = buffer#get_iter `START in
        let _ = buffer#insert ~iter explanation.pox_desc in
        () in
      let _ =
        List.iter (fun cref ->
            let label = "C99: " ^ cref.por_section ^ "; item: " ^ cref.por_item  in
            let txt = get_cref_section cref.por_section cref.por_item in
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
            let view = GText.view ~packing:window#add_with_viewport () in
            let _ = view#misc#modify_font_by_name "Monospace 12" in
            let buffer = view#buffer in
            let iter = buffer#get_iter `START  in
            let _ = buffer#insert ~iter (pp_str txt) in
            ()) explanation.pox_cstandard_refs in
      ()
    else
      let _ =
        GMisc.label
          ~text:"no explanation available"
          ~packing:dialog#vbox#add
          () in
      () in
      
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  

let show_ppo_group_dialog
      source_table (cfilename:string) (fname:string) (parent:GWindow.window) =
  let title = "Primary proof obligations for " ^ fname in
  let dialog =
    GWindow.dialog
      ~title ~parent
      ~modal:false
      ~show:true
      ~width:800
      ~height:480
      () in
  let fundec = read_function_semantics fname in
  let fdecls = fundec.sdecls in
  let varmgr = read_vars fname fdecls in
  let invio = read_invs fname varmgr#vard in
  let ppos = (proof_scaffolding#get_ppo_manager fname)#get_ppos in
  let pposelection = ref false in
  let set_pposelection s = pposelection := s in
  let display_ppos dialogwindow contents =
    let _ = match contents with Some s -> dialogwindow#vbox#remove s | _ -> () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC () in
    let ppos =
      if !pposelection then
        ppos
      else
        List.filter (fun p -> p#is_violation || (not p#is_closed)) ppos in
    let groups = H.create 5 in
    let add_group ppo =
      let group = po_predicate_tag ppo#get_predicate in
      if H.mem groups group then
        H.replace groups group (ppo :: (H.find groups group))
      else
        H.add groups group [ ppo ] in 
    let _ = List.iter add_group ppos in
    let groupList = H.fold (fun i l acc -> (i,l) :: acc) groups [] in
    let groupList = List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) groupList in
    let maxLine =
      List.fold_left (fun acc (_,l) ->
          let len = List.length l in if len > acc then len else acc) 0 groupList in
    let table =
      GPack.table
        ~row_spacings:1
        ~col_spacings:5
        ~columns:(maxLine+1)
        ~rows:(List.length groupList)
        ~packing:window#add_with_viewport
        () in
    let get_status packing ppo =
      get_ppo_button cfilename fname invio ppo packing parent in
    
    let row = ref 1 in
    let _ =
      List.iter (fun (g,l) ->
          let button =
            GButton.button
              ~label:g
              ~packing:(table#attach ~top:!row ~left:0)
              () in
          let _ =
            button#connect#clicked
              ~callback:(fun () -> show_po_explanation g parent) in
          let col = ref 1 in
          let _ =
            List.iter (fun ppo ->
                let _ = get_status (table#attach ~top:(!row) ~left:(!col)) ppo in
                col := !col + 1) l in
          row := !row + 1) groupList in
    let newcontents = window#coerce in
    let _ = dialogwindow#vbox#add newcontents in
    Some newcontents in
  let windowcontents = ref (display_ppos dialog None) in
  let checkButton =
    GButton.check_button
      ~label:"show all"
      ~packing:(dialog#action_area#add)
      () in
  let _ =
    checkButton#connect#clicked
      ~callback:(fun () -> set_pposelection checkButton#active) in
  let refreshButton =
    GButton.button
      ~stock:`REFRESH
      ~packing:dialog#action_area#add
      () in
  let _ =
    refreshButton#connect#clicked
      ~callback:(fun () ->
        windowcontents := display_ppos dialog !windowcontents) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  

let show_ppo_line_dialog
      source_table (cfilename:string) (fname:string) (parent:GWindow.window) = 
  let title = "Primary proof obligations for " ^ fname in
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
  let varmgr = read_vars fname fdecls in
  let invio = read_invs fname varmgr#vard in
  let get_source_line i =
    if H.mem source_table i then H.find source_table i else "" in
  let ppos = (proof_scaffolding#get_ppo_manager fname)#get_ppos in
  let pposelection = ref false  in
  let showcode = ref false in
  let set_pposelection s = pposelection := s in
  let set_showcode s = showcode := s in
  let display_ppos dialogwindow contents  =
    let _ = match contents with Some s -> dialogwindow#vbox#remove s | _ -> () in
    let window =
      GBin.scrolled_window
        ~hpolicy:`AUTOMATIC
        ~vpolicy:`AUTOMATIC
        () in
    let ppos =
      if !pposelection then
        ppos
      else
        List.filter (fun p -> p#is_violation || (not p#is_closed)) ppos in
    let lines = H.create 5 in
    let add_line ppo =
      let line = ppo#get_location.line in
      if H.mem lines line then
        H.replace lines line (ppo :: (H.find lines line))
      else
        H.add lines line [ ppo ] in 
    let _ = List.iter add_line ppos in
    let lineList = H.fold (fun i l acc -> (i,l) :: acc) lines [] in
    let lineList = List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) lineList in
    let rows =
      if !showcode then
        2 * (List.length lineList)
      else
        List.length lineList in
    let maxLine =
      List.fold_left (fun acc (_,l) ->
          let len = List.length l in
          if len > acc then len else acc) 0 lineList in
    let table =
      GPack.table
        ~row_spacings:1
        ~col_spacings:5
        ~columns:(maxLine+2)
        ~rows
        ~packing:window#add_with_viewport
        () in
    let get_status packing ppo =
      get_ppo_button cfilename fname invio ppo packing parent in
    let _ =
      GMisc.label
        ~xalign:0.5
        ~text:"line"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      if (not !showcode) && maxLine > 1 then
        ignore (GMisc.label
                  ~xalign:0.0
                  ~text:"proof obligations"
                  ~packing:(table#attach ~top:0 ~left:1 ~right:maxLine)
                  ()) in
    let row = ref 1 in
    if List.length lineList > 0 then
      let currentline = ref (fst (List.hd lineList) - 1) in
      let _ =
        List.iter (fun (i,l) ->
            let sourceLine = get_source_line i in
            let _ =
              if not !showcode then
                let lineButton =
                  GButton.button
                    ~label:(string_of_int i)
                    ~packing:(table#attach ~top:(!row) ~left:0)
                    () in
                let _ =
                  if sourceLine = "" then
                    ()
                  else
                    attach_popup_menu lineButton [ sourceLine ] in
                () in
            let _ =
              if !showcode then
                begin
                  for k = !currentline + 1 to i do
                    begin
                      ignore (GMisc.label
                                ~text:(string_of_int k)
                                ~packing:(table#attach ~top:(!row) ~left:0)
                                ()) ;
                      ignore (GMisc.label
                                ~text:(get_source_line k)
                                ~xalign:0.0
                                ~packing:(table#attach
                                            ~ypadding:10
                                            ~top:(!row)
                                            ~left:1
                                            ~right:(maxLine+2))
                                ()) ;
                      row := !row + 1
                    end ;
                  done;
                  currentline :=  i
                end in
            let col = ref 1 in
            let _ =
              if not !showcode then
                begin
                  List.iter (fun ppo ->
                      let _ = get_status (table#attach ~top:(!row) ~left:(!col)) ppo in
                      col := !col + 1) l ;
                  row := !row + 1
                end
              else
                List.iter (fun ppo ->
                    let _ = get_status (table#attach ~top:(!row) ~left:1) ppo in
                    let _ = GMisc.label
                              ~text:(pp_str (po_predicate_to_pretty ppo#get_predicate))
                              ~xalign:0.0
                              ~packing:(table#attach ~top:(!row) ~left:2 ~right:(maxLine+2))
                              () in
                    row := !row+1) l in
            ()) lineList in
      let newcontents = window#coerce in
      let _ = dialogwindow#vbox#add newcontents in
      Some newcontents
    else
      let newcontents = window#coerce in
      let _ = dialogwindow#vbox#add newcontents in
      Some newcontents in
  let windowcontents = ref (display_ppos dialog None) in
  let checkButton =
    GButton.check_button
      ~label:"show all"
      ~packing:dialog#action_area#add
      () in
  let _ =
    checkButton#connect#clicked
      ~callback:(fun () -> set_pposelection checkButton#active) in
  let showcodeButton =
    GButton.check_button
      ~label:"show code"
      ~packing:dialog#action_area#add
      () in
  let _ =
    showcodeButton#connect#clicked
      ~callback:(fun () -> set_showcode showcodeButton#active) in
  let refreshButton =
    GButton.button
      ~stock:`REFRESH
      ~packing:dialog#action_area#add
      () in
  let _ =
    refreshButton#connect#clicked
      ~callback:(fun () ->
        windowcontents := display_ppos dialog !windowcontents) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
  
let show_ppo_dialog
      source_table (cfilename:string) (fname:string) (parent:GWindow.window) =
  let title = "Primary proof obligations for " ^ fname in
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
  let varmgr = read_vars fname fdecls in
  let invio = read_invs fname varmgr#vard in
  let ppos = (proof_scaffolding#get_ppo_manager fname)#get_ppos in
  let sortpposbyid ppos =
    List.sort (fun p1 p2 -> Stdlib.compare p1#index p2#index) ppos in
(*  let sortpposbylinenumber ppos =
    List.sort (fun p1 p2 ->
        Stdlib.compare p1#get_location.line p2#get_location.line) ppos in *)
  let ppos = sortpposbyid ppos in
  let sortpposbypredicate ppos =
    List.sort (fun p1 p2 ->
        Stdlib.compare (pp_str (po_predicate_to_pretty p1#get_predicate))
                  (pp_str (po_predicate_to_pretty p2#get_predicate))) ppos in
  let pposelection = ref false in
  let set_pposelection s = pposelection := s in
  let display_ppos dialogwindow contents =
    let _ = match contents with Some s -> dialogwindow#vbox#remove s | _ -> () in
    let window =
      GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC () in
    let ppos =
      if !pposelection
      then
        ppos
      else
        (List.filter (fun p ->
             p#is_violation || (not p#is_closed)) (sortpposbypredicate ppos)) in
    let ppoCount = List.length ppos in
    let table =
      GPack.table
        ~row_spacings:2
        ~col_spacings:10
        ~columns:6
        ~rows:(ppoCount+2)
        ~packing:window#add_with_viewport
        () in
    let get_status packing ppo =
      get_ppo_button cfilename fname invio ppo packing parent in
    let row = ref 1 in
    let xalign = 0.5 in
    let _ =
      GMisc.label
        ~xalign
        ~text:"ppo-id"
        ~packing:(table#attach ~top:0 ~left:0)
        () in
    let _ =
      GMisc.label
        ~xalign
        ~text:"line"
        ~packing:(table#attach ~top:0 ~left:1)
        () in
    let _ =
      GMisc.label
        ~xalign
        ~text:"status"
        ~packing:(table#attach ~top:0 ~left:2)
        () in
    let _ =
      GMisc.label
        ~xalign
        ~text:"proof obligation"
        ~packing:(table#attach ~top:0 ~left:3)
        () in
    let _ =
      List.iter (fun ppo -> 
          let _ = get_status (table#attach ~top:(!row) ~left:2) ppo in
          let _ =
            GMisc.label
              ~xalign:0.0
              ~text:(string_of_int ppo#get_location.line)
              ~packing:(table#attach ~top:(!row) ~left:1)
              () in
          let _ =
            GMisc.label
              ~xalign:0.0
              ~text:(string_of_int ppo#index)
              ~packing:(table#attach ~top:(!row) ~left:0)
              () in
          let _ =
            GMisc.label
              ~xalign:0.0
              ~text:(pp_str (po_predicate_to_pretty (ppo#get_predicate)))
              ~packing:(table#attach ~top:(!row) ~left:3)
              () in
          row := !row + 1) ppos in
    let newcontents = window#coerce in
    let _ = dialogwindow#vbox#add newcontents in
    Some newcontents in
  let windowcontents = ref (display_ppos dialog None) in
  let checkButton  =
    GButton.check_button
      ~label:"show all"
      ~packing:dialog#action_area#add
      () in
  let _ =
    checkButton#connect#clicked
      ~callback:(fun () -> set_pposelection checkButton#active) in
  let refreshButton =
    GButton.button
      ~stock:`REFRESH
      ~packing:dialog#action_area#add
      () in
  let _ =
    refreshButton#connect#clicked 
      ~callback:(fun () ->
        windowcontents := display_ppos dialog !windowcontents) in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()  
  
let show_spo_post_dialog (cfilename:string) (fname:string) (parent:GWindow.window) =
  let title = "Secondary postcondition proof obligations for " ^ fname in
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
  let fundec = read_function_semantics fname in
  let fdecls = fundec.sdecls in
  let varmgr = read_vars fname fdecls in
  let invio = read_invs fname varmgr#vard in
  let spos = (proof_scaffolding#get_spo_manager fname)#get_spos in
  let directCalls = proof_scaffolding#get_direct_callsites fname in
  let indirectCalls = proof_scaffolding#get_indirect_callsites fname in
  (* TODO : This looks inefficient, someone should fix that *)
  let find_spo_callers spo = 
    let directCallers = List.filter ( fun directCall -> 
      List.exists ( fun other_spo -> 
        other_spo == spo
      ) directCall#get_spos
    ) directCalls in
    let indirectCallers = List.filter ( fun indirectCall ->
      List.exists ( fun other_spo ->
        other_spo == spo
      ) indirectCall#get_spos
    ) indirectCalls in
    let directCallers =
      List.map (fun f -> (f#get_callee).vname) directCallers in
    let indirectCallers =
      List.concat
        (List.map (fun f -> 
             (List.map (fun callee -> callee.vname)) (f#get_callees))
                  indirectCallers) in
    List.append directCallers indirectCallers in
  let spoCount = List.length spos in
  let table =
    GPack.table
      ~row_spacings:2
      ~col_spacings:10
      ~columns:7
      ~rows:(spoCount+2)
      ~packing:window#add_with_viewport
      () in
  let get_status packing spo =
    get_ppo_button cfilename fname invio spo packing parent in
  let row = ref 1 in
  let _ =
    GMisc.label
      ~xalign:0.5
      ~text:"spo-id"
      ~packing:(table#attach ~top:0 ~left:0)
      () in
  let _ =
    GMisc.label
      ~xalign:0.5
      ~text:"line"
      ~packing:(table#attach ~top:0 ~left:1)
      () in
  let _ =
    GMisc.label
      ~xalign:0.5
      ~text:"callers"
      ~packing:(table#attach ~top:0 ~left:2)
      () in
  let _ =
    GMisc.label
      ~xalign:0.5
      ~text:"status"
      ~packing:(table#attach ~top:0 ~left:3)
      () in
  let _ =
    GMisc.label
      ~xalign:0.5
      ~text:"predicate"
      ~packing:(table#attach ~top:0 ~left:4)
      () in
  let _ = List.iter (fun spo -> 
    let _ = get_status (table#attach ~top:(!row) ~left:3) spo in
    let _ =
      GMisc.label
        ~xalign:0.0
        ~text:(string_of_int spo#get_location.line)
        ~packing:(table#attach ~top:(!row) ~left:1) () in
    (* TODO : Replace with callers with something that works *)
    let button =
      GButton.button
        ~label:(string_of_int (List.length (find_spo_callers spo)))
        ~packing:(table#attach ~top:(!row) ~left:2)
        () in
    let _ = attach_popup_menu button (find_spo_callers spo) in
    let _ =
      GMisc.label
        ~xalign:0.0
        ~text:(string_of_int spo#index)
        ~packing:(table#attach ~top:(!row) ~left:0)
        () in
    let _ =
      GMisc.label
        ~xalign:0.0
        ~text:(pp_str (po_predicate_to_pretty spo#get_predicate))
        ~packing:(table#attach ~top:(!row) ~left:4)
        () in
    row := !row + 1) spos in
  let _ = dialog#add_button_stock `CLOSE `CLOSE in
  let _ = dialog#connect#close ~callback:(fun ()->()) in
  let _ = dialog#connect#response ~callback:(fun resp -> dialog#destroy ()) in
  ()
