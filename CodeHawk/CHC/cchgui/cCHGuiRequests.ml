(* =============================================================================
   CodeHawk C Analyzer 
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

(* cchlib *)
open CHPretty

(* chutil *)
open CHPrettyUtil

(* cchgui *)
open CCHSystemDisplay

module H = Hashtbl
module P = Pervasives

let flp = CHPrettyUtil.fixed_length_pretty
let fls = CHPrettyUtil.fixed_length_string


(* --------------------------------------------------- missing library summaries *)
let missing_summaries = H.create 3
                      
let record_missing_summary filename fname nppos nspos=
  let key = (filename,fname) in
  let (lcount,ppocount,spocount) =
    if H.mem missing_summaries key then
      H.find missing_summaries key
    else (0,0,0) in
  H.replace missing_summaries key (lcount+1,ppocount+nppos,spocount+nspos)

let display_missing_summaries () =
  let txt = H.fold (fun k v a ->  (k,v) :: a) missing_summaries [] in
  let txt = List.sort (fun (k1,_) (k2,_) -> P.compare k1 k2) txt in
  let ptitle  =
    LBLOCK [ STR (fls "count" 7) ;
             STR (fls "ppos" 7) ;
             STR (fls "spos" 7) ;
             STR (fls "header file" 20) ;
             STR "function" ] in
  let pline = LBLOCK [ STR (string_repeat "-" 80) ] in             
  let p =
    LBLOCK (List.map (fun ((filename,fname),(lcount,ppocount,spocount)) ->
                LBLOCK [
                    flp ~alignment:StrRight (INT lcount) 4 ; STR "   " ;
                    flp ~alignment:StrRight (INT ppocount) 4 ; STR "   " ;
                    flp ~alignment:StrRight (INT spocount) 4 ; STR "   " ; 
                    STR (fls filename 20) ;
                    STR (fls fname 20) ; NL ]) txt) in
  let (ltotal,ppototal,spototal) =
    H.fold (fun _ (l,p,s) (lt,pt,st) -> (l+lt,p+pt,s+st)) missing_summaries (0,0,0) in
  let ptotal =
    LBLOCK [ flp ~alignment:StrRight (INT ltotal) 4  ; STR "   " ;
             flp ~alignment:StrRight (INT ppototal) 4 ; STR "   " ;
             flp ~alignment:StrRight (INT spototal) 4 ; STR "   " ] in
  let ptxt = LBLOCK [ ptitle ; NL ; pline ; NL ; p ; pline ; NL ; ptotal ; NL ] in
  begin
    write_to_system_display_pp "missing_summaries" ptxt ;
    goto_system_page ()
  end


(* --------------------------------------- external postcondition requests *)
let postcondition_requests = H.create 3

let record_postcondition_request filename fname pc nppos nspos =
  let key = (filename,fname)  in
  let keyentry =
    if H.mem postcondition_requests key then
      H.find postcondition_requests key
    else
      let t = H.create 3 in
      begin
        H.add postcondition_requests key t ;
        t
      end in
  let (pccount,ppocount,spocount) =
    if H.mem keyentry pc then
      H.find keyentry pc
    else
      (0,0,0) in
  H.replace keyentry pc (pccount + 1,ppocount+nppos,spocount+nspos)

let display_postcondition_requests () =
  let txt = H.fold (fun k v a -> (k,v) :: a)  postcondition_requests [] in
  let txt = List.sort  (fun (k1,_) (k2,_) -> P.compare k1 k2) txt in
  let txt =
    List.concat
      (List.map (fun (k,t) ->
           H.fold (fun pc v a -> (k,pc,v) :: a) t []) txt) in
  let maxfnname =
    List.fold_left (fun acc ((_,n),_,_) ->
        let len = String.length n in
        if len > acc then len else acc) 0 txt in
  let maxpc =
    List.fold_left (fun acc (_,pc,_) ->
        let len  =  String.length pc in
        if len > acc then len else acc) 0 txt in
  let fnlen = if maxfnname > 13 then maxfnname else 13 in
  let pclen = if maxpc > 10 then maxpc else 10 in
  let ptitle =
    LBLOCK [ STR (fls "count" 7) ;
             STR (fls "ppos" 7) ;
             STR (fls "spos" 7) ;
             STR (fls "condition" (pclen+2)) ;
             STR (fls "function name" (fnlen+2)) ;
             STR "filename" ; NL ] in
  let (pctotal,ppototal,spototal) =
    List.fold_left (fun (pct,pt,st) (_,_,(pc,ppo,spo)) ->
        (pct+pc,pt+ppo,st+spo)) (0,0,0) txt in
  let pline = LBLOCK [ STR (string_repeat "-" 80) ; NL ] in             
  let p =
    LBLOCK
      (List.map (fun ((filename,fname),pc,(pccount,ppocount,spocount)) ->
           LBLOCK [ flp ~alignment:StrRight (INT pccount) 4 ; STR "   " ;
                    flp ~alignment:StrRight (INT ppocount) 4 ; STR "   " ;
                    flp ~alignment:StrRight (INT spocount) 4 ; STR "   " ;
                    STR (fls pc (pclen+2)) ;
                    STR (fls fname (maxfnname + 2)) ;
                    STR (fls filename 20) ; NL ]) txt) in
  let ptotal =
    LBLOCK [ flp ~alignment:StrRight (INT pctotal)  4 ; STR "   " ;
             flp ~alignment:StrRight (INT ppototal) 4 ; STR "   " ;
             flp ~alignment:StrRight (INT spototal) 4 ; STR "   " ; NL ] in
  let p = LBLOCK [ ptitle ; pline ; p ; pline ; ptotal ] in
  begin
    write_to_system_display_pp "postcondition_requests" p ;
    goto_system_page ()
  end


    (* ---------------------------------------------- diagnostic reports *)

type diagnostic_report_t = {
    dr_filename: string ;
    dr_fname: string ;
    dr_isppo: bool ;
    dr_po_id: int ;
    dr_predicate_tag: string ;
    dr_predicate: string ;
    dr_diagnostics: string list
  }

let taggedreports = H.create 3
let investigations = H.create 3

let report_diagnostic table (r:diagnostic_report_t) =
  let tagentry =
    if H.mem table r.dr_predicate_tag then
      H.find table r.dr_predicate_tag
    else
      let t = H.create 3 in
      begin H.add table r.dr_predicate_tag t ; t end in
  let fkey = (r.dr_filename,r.dr_fname) in
  let fentry =
    if H.mem tagentry fkey then
      H.find tagentry fkey
    else
      let t = H.create  3 in
      begin H.add tagentry fkey t ; t end in
  if H.mem fentry (r.dr_isppo,r.dr_po_id) then
    log_message "duplicate diagnostic report"
  else
    H.add fentry (r.dr_isppo,r.dr_po_id) r

let diagnostic_report_to_pretty r =
  LBLOCK [ INT r.dr_po_id ; STR (if r.dr_isppo then " " else " (spo) ") ;
           STR r.dr_predicate ; NL ;
           LBLOCK (List.map (fun d ->
                       LBLOCK [ INDENT (3,STR d) ; NL ]) r.dr_diagnostics) ; NL ]

let diagnostic_fentry_to_pretty fentry t =
  let (filename,fname) = fentry in
  let pos = H.fold (fun k v a -> (k,v)::a) t [] in
  let pos = List.sort (fun (k1,_) (k2,_) -> P.compare k1 k2) pos in
  let p = LBLOCK (List.map (fun (_,r) -> diagnostic_report_to_pretty r) pos) in
  LBLOCK [ STR filename ; STR " : " ; STR fname ; NL ; p ]

let diagnostic_tag_to_pretty tag t =
  let fentries = H.fold (fun k v a -> (k,v)::a) t [] in
  let fentries = List.sort (fun (k1,_) (k2,_) -> P.compare k1 k2) fentries in
  let p = LBLOCK (List.map (fun (k,v) -> diagnostic_fentry_to_pretty k v) fentries) in
  LBLOCK [ STR tag ; NL ; STR (string_repeat "-" 80) ; NL ; p ; NL ]

let display_reports table =
  let tags = H.fold (fun k v a -> (k,v)::a) table [] in
  let tags = List.sort (fun (k1,_) (k2,_) -> P.compare k1 k2) tags in
  let p = LBLOCK (List.map (fun (k,v) -> diagnostic_tag_to_pretty k v) tags) in
  begin
    write_to_system_display_pp "diagnostic_reports" p ;
    goto_system_page ()
  end
  
let report_rfi (r:diagnostic_report_t) =
  report_diagnostic taggedreports r

let report_investigate (r:diagnostic_report_t) =
  report_diagnostic investigations r

let display_diagnostic_reports () = display_reports taggedreports

let display_investigations () = display_reports investigations
