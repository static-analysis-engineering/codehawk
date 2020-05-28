(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
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

(* chlib *)
open CHCommon
open CHPretty
open CHUtils

(* chutil *)
open CHXmlDocument
open CHXmlReader
open CHFileIO
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHFile
open JCHJTerm
open JCHJTDictionary

(* jchpre *)
open JCHCHAUtil
open JCHClassSummary
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHFunctionSummaryXmlDecoder
open JCHPreAPI
open JCHPreSumTypeSerializer
open JCHSystemSettings

(* standalone main program to parse all summary files and collect statistics *)

module H = Hashtbl
module P = Pervasives

module ClassNameCollections = CHCollections.Make (
  struct
    type t = class_name_int
    let compare n1 n2 = n1#compare n2
    let toPretty n = n#toPretty
  end)

module SummaryCollections = CHCollections.Make (
  struct
    type t = function_summary_int
    let compare s1 s2 = s1#get_cms#compare s2#get_cms
    let toPretty s = s#toPretty
  end)

module ClassMethodSignatureCollections = CHCollections.Make (
  struct
    type t = class_method_signature_int
    let compare cms1 cms2 = cms1#compare cms2
    let toPretty cms = cms#toPretty
  end)

let showinvalid = ref false
let showinvalidfinal = ref false
let showimmutable = ref false
let showranges = ref false
let showstringsinks = ref false
let showinputsources = ref false
let name = ref ""
let cn = make_cn "java.lang.Object"

let allsummaries = ref []

let dynamically_dispatched_methods = ref 0
let default_implementations = H.create 3

let check_dependents
      (filename:string)
      (cn:class_name_int)
      (summary:class_summary_int) =
  let dependents = summary#get_interfaces in
  let dependents =
    if summary#has_super_class then
      summary#get_super_class :: dependents
    else
      dependents in
  if List.exists (fun d -> d#equal cn) dependents then
    raise
      (JCH_failure
         (LBLOCK [ STR "Class name is equal to one of its dependents. Filename: " ;
		   STR filename ; STR ". Dependents: " ; 
		   pretty_print_list dependents (fun cn -> cn#toPretty) "[" "; " "]" ]))
  else ()

let nPost = ref 0 
let nGuards= ref 0 
let nStringSinks = ref 0 
let nResourceSinks = ref 0
let nSideEffects = ref 0
let nPatterns = ref 0
let patterns = ref []

let default_implementations_to_pretty () =
  let lst = ref [] in
  let _ = H.iter (fun k v -> lst := (k,v) :: !lst) default_implementations in
  let lst = List.sort (fun (k1,_) (k2,_) -> P.compare k1 k2) !lst in
  LBLOCK (List.map (fun (k,v) ->
    LBLOCK [ fixed_length_pretty (STR k) 32 ; STR ": " ; 
	     pretty_print_list v (fun s -> s#toPretty) "" ", " "" ; NL ]) lst)

type pkg_rec_t = {
    class_count: int ;
    method_count: int ;
    pre_count: int ;
    post_count: int ;
    stringsink_count: int ;
    resourcesink_count: int
  }

let zero_pkg_rec = {
    class_count = 0 ;
    method_count = 0 ;
    pre_count = 0 ;
    post_count = 0 ;
    stringsink_count = 0 ;
    resourcesink_count = 0
  }

let update_pkg_rec (pkgrec:pkg_rec_t) (methods:function_summary_int list) =
  let getpre (m:function_summary_int) =
    let exninfos = m#get_exception_infos in
    List.fold_left
      (fun acc x -> acc + List.length x#get_safety_condition) 0 exninfos in
  { class_count = pkgrec.class_count + 1 ;
    method_count = pkgrec.method_count + List.length methods ;
    pre_count =
      pkgrec.pre_count + List.fold_left (fun acc m -> acc + getpre m) 0 methods ;
    post_count =
      pkgrec.post_count
        + List.fold_left (fun acc m -> acc + (List.length m#get_post)) 0 methods ;
    stringsink_count =
      pkgrec.stringsink_count
      + List.fold_left (fun acc m -> acc + (List.length m#get_string_sinks)) 0 methods ;
    resourcesink_count =
      pkgrec.resourcesink_count
      + List.fold_left (fun acc m -> acc + (List.length m#get_resource_sinks)) 0 methods
  }

let packages = H.create 3  

let add_class_to_package (name:string) (methods:function_summary_int list) =
  let pkgrec =
    if H.mem packages name then
      H.find packages name
    else
      zero_pkg_rec in  
  H.replace packages name (update_pkg_rec pkgrec methods)

let pkg_recs_to_pretty () =
  let pkg_header =
    LBLOCK [ STR "| package | classes | methods | preconditions | postconditions " ;
             STR "| string sinks | resource sinks | " ; NL ;
             STR "| :--- | ---: | ---: | ---: | ---: | ---: | ---: | " ; NL ] in
  let pkg_rec_to_pretty (r:pkg_rec_t) =
    LBLOCK [ STR " | " ; INT r.class_count ;
             STR " | " ; INT r.method_count ;
             STR " | " ; INT r.pre_count ;
             STR " | " ; INT r.post_count ;
             STR " | " ; INT r.stringsink_count ;
             STR " | " ; INT r.resourcesink_count ;
             STR " | " ] in
  let recs = H.fold (fun k v a -> (k,v) :: a) packages [] in
  let recs = List.sort (fun (p1,_) (p2,_) -> P.compare p1 p2) recs in
  let totals =
    List.fold_left (fun acc (_,r) ->
        { class_count = acc.class_count + r.class_count ;
          method_count = acc.method_count + r.method_count ;
          pre_count = acc.pre_count + r.pre_count ;
          post_count = acc.post_count + r.post_count ;
          stringsink_count = acc.stringsink_count + r.stringsink_count ;
          resourcesink_count = acc.resourcesink_count + r.resourcesink_count
      } ) zero_pkg_rec recs in
  let totals_pretty =
    LBLOCK [ STR "| total "  ;
             STR " | " ; INT totals.class_count ;
             STR " | " ; INT totals.method_count ;
             STR " | " ; INT totals.pre_count ;
             STR " | " ; INT totals.post_count ;
             STR " | " ; INT totals.stringsink_count ;
             STR " | " ; INT totals.resourcesink_count ;
             STR " | " ; NL ] in
  LBLOCK [ pkg_header ;
           LBLOCK
             (List.map (fun (p,r) ->
                  LBLOCK [ STR p ; pkg_rec_to_pretty r ; NL ]) recs) ;
           totals_pretty ]


let exception_guards = H.create 3
let exception_info_exns = H.create 3

let add_guard name =
  if H.mem exception_guards name then
    H.replace exception_guards name ((H.find exception_guards name) + 1)
  else
    H.add exception_guards name 1

let classify_exception_guards (s:function_summary_int) =
  let infos = s#get_exception_infos in
  let conditions =
    List.fold_left (fun acc i -> i#get_safety_condition @ acc) [] infos in
  begin
    List.iter
      (fun c ->
        match c with
        | PreRelationalExpr _ -> add_guard "numeric"
        | PreNull _ -> add_guard "null"
        | PreNotNull _ -> add_guard "not-null" 
        | PreValidString _ -> add_guard "valid string") conditions ;
    List.iter
      (fun info ->
        if (List.length info#get_safety_condition) > 0 then
          let exn = info#get_exception#name in
          let entry =
            if H.mem exception_info_exns exn then
              H.find exception_info_exns exn
            else
              0 in
          H.replace
            exception_info_exns
            exn
            (entry + (List.length info#get_safety_condition))) infos
  end
  
let stringforms = H.create 5
let stringdests = H.create 5
let stringexceptions = H.create 5

let categorize_string_sinks
      (cms:class_method_signature_int) (sinks:string_sink_int list) =
  let add_form form dest  =
    let entry = if H.mem stringforms form then H.find stringforms form else [] in
    H.replace stringforms form ((dest,cms)::entry) in
  let add_dest dest form  =
    let entry = if H.mem stringdests dest then H.find stringdests dest else [] in
    H.replace stringdests dest ((form,cms)::entry) in
  let add_exn exn form =
    let entry = if H.mem stringexceptions exn then H.find stringexceptions exn else [] in
    H.replace stringexceptions exn ((form,cms)::entry) in
  List.iter (fun sink ->
      begin
        add_form sink#get_form sink#get_dest;
        add_dest sink#get_dest sink#get_form;
        List.iter (fun exn -> add_exn exn#name sink#get_form) sink#get_exceptions
      end) sinks

let print_string_sinks () =
  let forms = H.fold (fun k v a -> (k,v)::a) stringforms [] in
  let dests = H.fold (fun k v a -> (k,v)::a) stringdests [] in
  let exns = H.fold (fun k v a -> (k,v)::a) stringexceptions [] in
  let sort l = List.sort (fun (s1,_) (s2,_) -> P.compare s1 s2) l in
  let pl l =
    List.map (fun (s,cms)  ->
        LBLOCK [ STR s  ; STR "  " ; cms#toPretty ; NL ])
             (List.sort (fun (s1,_) (s2,_) -> P.compare s1 s2) l) in
  pr_debug [
      STR "Forms:" ; NL ;
      LBLOCK (List.map (fun (s,l)  ->
                  LBLOCK  [ STR s ; NL ; INDENT (3, LBLOCK (pl l)) ]) (sort forms)) ;
      NL ; NL ;
      STR "Destinations:" ; NL ;
      LBLOCK (List.map (fun (s,l) ->
                  LBLOCK [ STR s ; NL ; INDENT (3, LBLOCK (pl  l)) ]) (sort dests)) ;
      NL ; NL ;
      STR "Exceptions:" ; NL ;
      LBLOCK (List.map (fun (s,l) ->
                  LBLOCK [ STR s ; NL ; INDENT (3, LBLOCK  (pl l)) ]) (sort exns)) ]


let exception_guards_to_pretty () =
  let exns =  H.fold (fun k v a -> (k,v) :: a) exception_info_exns [] in
  let exns = List.sort (fun (x1,_) (x2,_) -> P.compare x1 x2) exns in
  LBLOCK
    (List.map (fun (k,v) ->
         LBLOCK [ STR "| " ; STR k ; STR " | " ; INT v ; STR " | " ; NL ]) exns)

let get_input_sources summaries =
  let sources = ref [] in
  begin
    List.iter (fun (cms,_,summary) ->
        List.iter (fun taintelement ->
            match taintelement with
            | TDefPut term ->
               sources := (cms,term) :: !sources
            | _ -> ()) summary#get_taint_elements) summaries ;
    !sources
  end

let print_input_sources sources =
  let packages = H.create 11 in
  let add_pkg pkg =
    let entry =
      if H.mem packages pkg then
        H.find packages pkg
      else
        0 in
    H.replace packages pkg (entry + 1) in
  begin
    pr_debug [ NL ; STR "Input sources (" ; INT (List.length sources) ; STR ")" ; NL ;
               STR "------------------------------------------------------------" ; NL  ] ;
    List.iter (fun (cms,term) ->
        add_pkg cms#class_name#package_name ;
        pr_debug [ cms#toPretty ; STR ": " ; jterm_to_pretty term ; NL ]) sources ;
    let packages =
      List.sort
        (fun (_,c1) (_,c2) -> P.compare c2 c1)
        (H.fold (fun k v a -> (k,v)::a) packages []) in
    pr_debug [ NL ; STR "Input sources per package: " ; NL ;
               STR "------------------------------------------------------------" ; NL  ] ;
    List.iter (fun (pkg,count) ->
        pr_debug [ fixed_length_pretty ~alignment:StrRight (INT count) 5 ; STR "  " ;
                   STR pkg ; NL ]) packages
  end

let get_statistics summaries =
  List.iter (fun (cms,_,summary) ->
    begin
      (match summary#get_exception_infos with
       | [] -> ()
       | l ->
	  if List.exists (fun eInfo ->
                 eInfo#has_safety_condition) l then nGuards := !nGuards + 1) ;
      nSideEffects := !nSideEffects + (List.length summary#get_sideeffects) ;
      nStringSinks := !nStringSinks + (List.length summary#get_string_sinks) ;
      categorize_string_sinks cms summary#get_string_sinks ;
      nResourceSinks := !nResourceSinks + (List.length summary#get_resource_sinks) ;
      nPost := !nPost + (List.length summary#get_post) ;
      (if summary#has_pattern then
         begin
           patterns := summary#get_pattern :: !patterns ;
           nPatterns := !nPatterns + 1
         end)
    end) summaries

let rangepostconditions = H.create 11
let get_range_postconditions () =
  H.fold (fun k v a  -> (k,v)::a) rangepostconditions []

let collect_range_postconditions summaries  =
  let add classname r =
    let entry =
      if H.mem rangepostconditions classname then
        H.find rangepostconditions classname
      else
        [] in
    H.replace rangepostconditions classname (r::entry) in

  List.iter (fun (cms,_,summary) ->
      let classname = cms#class_name#name in
      List.iter (fun post ->
          match post#get_predicate with
          | PostRelationalExpr r -> add classname r
          | _ -> ()) summary#get_post) summaries

let costexprs = H.create 3
let constantcost = ref 0
let rangecost = ref 0
let symboliccost = ref 0

let categorize_cost (c:jterm_range_int) =
  if c#is_constant then
    constantcost := !constantcost + 1
  else if c#is_interval then
    rangecost := !rangecost + 1
  else if c#is_top then
    ()
  else
    symboliccost := !symboliccost + 1

let add_cost_expr
      (cn:class_name_int)
      (cms:class_method_signature_int)
      (cost:jterm_range_int) =
  let _ = categorize_cost cost in
  let package = String.concat "." cn#package in
  let cnname = cn#simple_name in
  let pkgentry =
    if H.mem costexprs package then
      H.find costexprs package
    else
      let e = H.create 3 in
      begin
        H.add costexprs package e ;
        e
      end in
  let cnentry =
    if H.mem pkgentry cnname then
      H.find pkgentry cnname
    else
      let e = H.create 3 in
      begin
        H.add pkgentry cnname e ;
        e
      end in
  H.add cnentry cms#class_method_signature_string cost

let cost_exprs_to_pretty () =
  let cost_to_pretty cms cost =
    LBLOCK [ STR cms ; NL ; INDENT (3, cost#toPretty) ; NL ] in
  let cn_to_pretty cn cnentry =
    let entry_to_pretty =
      H.fold (fun cms cost acc ->
          LBLOCK [ acc ; cost_to_pretty cms cost ]) cnentry (STR "") in
    LBLOCK [ STR cn ; STR " (" ; INT (H.length cnentry) ; STR ")" ;
             NL ; entry_to_pretty ; NL ] in
  let pkg_to_pretty pkg pkgentry =
    H.fold (fun cn cnentry acc ->
        LBLOCK [ acc ; cn_to_pretty cn cnentry ; NL ]) pkgentry (STR "") in
  H.fold (fun pkg pkgentry acc ->
      let pkg_count = H.fold (fun _ v a -> a + (H.length v)) pkgentry 0 in
      LBLOCK [ acc ; STR (string_repeat "=" 80) ; NL ;
               STR pkg ; STR " (" ; INT (H.length pkgentry) ; STR " classes; " ;
               INT pkg_count ; STR " methods)" ; NL ;
               STR (string_repeat "=" 80) ;
               NL ;  pkg_to_pretty pkg pkgentry ])
         costexprs (STR "")

let cost_exprs_count () =
  let cncount cn = H.length cn in
  let pkgcount pkg = H.fold (fun _ v a -> a + (cncount v)) pkg 0 in
  H.fold (fun _ v a -> a + (pkgcount v)) costexprs 0
  

let inspect_summaries (name:string) =
  let cnSet = new ClassNameCollections.set_t in
  let nameSet = new StringCollections.set_t in
  let arrayArgumentSummaries = new ClassNameCollections.table_t in
  let classpath = system_settings#get_classpath in
  let arrayArgumentCounter = ref 0 in
  let increment_counter () = arrayArgumentCounter := !arrayArgumentCounter + 1 in
  let iSummaries = ref [] in
  let classes_with_length = ref [] in
  let add_array_argument_summaries cn summary =
    let arguments = summary#get_cms#method_signature#descriptor#arguments in
    if List.exists (fun a ->
           match a with (TObject (TArray _)) -> true | _ -> false) arguments
       && (not summary#is_inherited)
       && summary#is_valid
       && (match summary#get_sideeffects with [] -> true | _ -> false) then
      let _ = increment_counter () in
      match arrayArgumentSummaries#get cn with
	Some s -> s#add summary
      | _ ->
	let s = new SummaryCollections.set_t in
	begin s#add summary ; arrayArgumentSummaries#set cn s end
    else
      () in
  let abstractedArguments = new ClassMethodSignatureCollections.set_t in
  let add_abstract_argument summary =
    if List.exists 
         (fun se ->
           match se with
           | NumericAbstract _ -> true | _ -> false) summary#get_sideeffects then
      abstractedArguments#add summary#get_cms in
  let print_summaries () =
    let p = ref [] in
    let _ = arrayArgumentSummaries#iter (fun cn s ->
      let pp = ref [] in
      let _ = s#iter (fun summary -> pp := (LBLOCK [ summary#toPretty ; NL ; NL ]) :: !pp) in
      p := (LBLOCK [ cn#toPretty ; NL ; INDENT (3, LBLOCK !pp)  ]) :: !p) in
    LBLOCK !p in
  let has_interesting_feature summary = 
    (match summary#get_exception_infos with
     | [] -> false
     | l -> List.exists (fun eInfo -> eInfo#has_safety_condition) l)
    || (match summary#get_sideeffects with [] -> false | _ -> true)
    || (match summary#get_string_sinks with [] -> false | _ -> true)
    || (match summary#get_resource_sinks with [] -> false | _ -> true) in
  begin
    
    apply_to_xml_jar (fun name s ->
        if name = "jdk_jar_version.xml" || name = "chjlib_jar_version.xml" then
          ()
        else
	  let summary = read_xml_class_file_from_string name s in
	  let ((cn,classSummary),_,methodSummaries) = summary in
	  let filename = Filename.basename name in
	  let filename = Filename.chop_extension filename in
	  let _ =
            if cn#simple_name = filename then () else
	      raise (JCH_failure
                       (LBLOCK [
                            STR "Filename is not the same as the classname. Filename: " ; 
			    STR filename ; STR "; classname: " ; cn#toPretty ; NL ])) in
	  let _ = check_dependents filename cn classSummary in
	  let (classesReferenced,unrecognizedNames) =
            get_classes_referenced_in_summary classpath summary in
          let _ = match classSummary#get_class_properties with
            | [] -> ()
            | (LogicalSize (MethodAccessor ms))::_ ->
               classes_with_length := (cn,ms) :: !classes_with_length in
	  begin
	    function_summary_library#add_class_summary summary ;
	    cnSet#addList classesReferenced ;
	    nameSet#addList unrecognizedNames ;
	    (if classSummary#is_dispatch then
               dynamically_dispatched_methods :=
                 !dynamically_dispatched_methods + (List.length methodSummaries)) ;
	    (if classSummary#is_interface then
	       H.add default_implementations cn#name classSummary#get_default_implementations) ;
	    add_class_to_package
              cn#package_name 
              (List.fold_left
                 (fun acc (_,_,s) ->
                   if (not s#is_inherited) && s#is_valid then
                     s :: acc
                   else
                     acc) [] methodSummaries) ;

            allsummaries := methodSummaries @ !allsummaries ;
	    List.iter (fun (_,_,s) -> classify_exception_guards s) methodSummaries ;
	    List.iter (fun (_,_,m) -> add_array_argument_summaries cn m) methodSummaries ;
	    List.iter (fun (_,_,m) -> add_abstract_argument m) methodSummaries ;
	    List.iter (fun (_,_,m) -> if has_interesting_feature m then
	                                iSummaries := m#toPretty :: !iSummaries) methodSummaries ;
            List.iter (fun (_,_,m) ->
                let  cost = m#get_time_cost in
                if not cost#is_top then
                   add_cost_expr cn m#get_cms cost) methodSummaries ;
                (*  costexprs := (m#get_cms,cost) :: !costexprs) methodSummaries ;  *)
	    get_statistics methodSummaries ;
            collect_range_postconditions methodSummaries ;
	  end) (fun _ _ -> ()) name ;
    
    file_output#saveFile "jdk_summaries.ch_array_arguments" (print_summaries ()) ;
    file_output#saveFile
      "jdk_summaries.ch_abstracted_arguments"
      (pretty_print_list
         abstractedArguments#toList (fun cms -> LBLOCK [ cms#toPretty  ; NL ]) "" "" "") ;
    file_output#saveFile "jdk_summaries.ch_some_summaries" (LBLOCK !iSummaries) ; 
    file_output#saveFile "jdk_package_statistics" (pkg_recs_to_pretty ()) ;
    file_output#saveFile "jdk_exception_guard_statistics" (exception_guards_to_pretty ()) ;
    pr_debug [ function_summary_library#statistics_to_pretty ; NL ;
	       STR "Number of distinct classes referenced: " ; INT cnSet#size ; NL ;
	       STR "Names not recognized: " ; 
	       pretty_print_list nameSet#toList (fun s -> STR s) "[" "; " "]" ; NL ] ;
    pr_debug [ STR "Number of summaries with array arguments: " ;
               INT !arrayArgumentCounter ; NL ; NL ] ;
    pr_debug [ STR "Post:         " ; INT !nPost ; NL ;
	       STR "Side effects: " ; INT !nSideEffects ; NL ;
	       STR "String sinks: " ; INT !nStringSinks ; NL ;
	       STR "Resource sinks: " ; INT !nResourceSinks ; NL ;
               STR "Patterns:     " ; INT !nPatterns ; NL ;
	       STR "Guards:       " ; INT !nGuards ; NL ] ;
    pr_debug [ NL ; STR "Classes with length: " ; NL ] ;
    List.iter (fun (cn,ms) ->
        pr_debug [ STR "   " ; cn#toPretty ;
                   STR " (" ; ms#toPretty ; STR ")" ; NL ]) !classes_with_length ;
               
    pr_debug [ NL ; STR "Cost expressions (" ;
               INT (cost_exprs_count ()) ; STR "; " ;
               INT !constantcost ; STR " constants, " ;
               INT !rangecost ; STR " ranges, " ;
               INT !symboliccost ; STR " symbolic):" ; NL ;
               STR (string_repeat "-" 80) ; NL  ; cost_exprs_to_pretty () ];
    (* List.iter (fun (cms,x) ->
        pr_debug [ cms#toPretty ; NL ; INDENT (3,x#toPretty) ; NL ]) !costexprs ;  *)

    (if !showinvalid || !showinvalidfinal then
       let comparesummaries s1 s2 =
         P.compare
           s1#get_cms#class_method_signature_string
           s2#get_cms#class_method_signature_string in
       let summaries = function_summary_library#get_invalid_methods in
       let summaries =
         List.filter (fun v ->
             (not v#is_abstract)
             && (match v#get_visibility with
                 | Private | Default -> false
                 |  _ -> true)) summaries in
       (* let summaries =
         if !showinvalidfinal then
           List.filter (fun v -> v#is_final || v#is_static) summaries
         else
           summaries in *)
       let summaries = List.sort comparesummaries summaries in
       let numSummaries = List.length summaries in
       begin
         pr_debug [ NL ; STR "Public methods not yet summarized (" ;
                    INT numSummaries ; STR  "): " ;  NL ;
                    STR (string_repeat "-" 80) ; NL ] ;
         pr_debug
           (List.map (fun s ->
                let f =
                  if s#is_final then
                    LBLOCK [ STR " (final)" ]
                  else
                    STR "" in
                LBLOCK [ s#get_cms#toPretty ; f ; NL ]) summaries)
       end) ;
    
    (if !showimmutable then
       let cns =
         List.sort
           (fun cn1 cn2 -> P.compare cn1#name cn2#name)
           function_summary_library#get_immutable_classes in
       pr_debug [ NL ; STR "Immutable classes: " ; NL ;
                  LBLOCK (List.map (fun cn -> LBLOCK [ STR "  " ; cn#toPretty ; NL ]) cns) ]);

    (if !showranges then
       let rangepost = get_range_postconditions () in
       let rangepost =
         List.sort
           (fun (cn1,_) (cn2,_) -> P.compare cn1 cn2) rangepost in
       pr_debug [ NL ; STR "Range post conditions: " ; NL ;
                  LBLOCK (List.map (fun (cn,l) ->
                              LBLOCK [ NL ; STR "  " ; STR cn ; STR " (" ;
                                       INT (List.length l) ; STR ")" ; NL ;
                                         LBLOCK (List.map (fun r ->
                                                     LBLOCK [ STR "    " ;
                                                              relational_expr_to_pretty r ;
                                                              NL  ]) l)  ]) rangepost) ] ) ;

    (if !showstringsinks then print_string_sinks ()) ;
    (if !showinputsources then print_input_sources (get_input_sources !allsummaries))

  end

let speclist =
  [("-classpath",Arg.String system_settings#add_classpath_unit,
    "sets java classpath") ;
   ("-showinvalid", Arg.Set showinvalid,
    "shows methods that have not been summarized yet");
   ("-showinvalidfinal", Arg.Set showinvalidfinal,
    "shows final methods that have not been summarized yet");
   ("-showimmutable", Arg.Set showimmutable,
    "prints list of classes that are immutable");
   ("-showranges", Arg.Set showranges,
    "prints list of range post conditions");
   ("-showstringsinks", Arg.Set showstringsinks,
    "prints list of string sinks");
   ("-showinputsources", Arg.Set showinputsources,
    "prints list of input sources")]

let usage_msg = "inspect_summaries filename"
let read_args () = Arg.parse speclist   (fun s -> name := s) usage_msg

let main () =
  let _ = JCHBasicTypes.set_permissive true in
  try
    read_args () ;
    inspect_summaries !name ;
    file_output#saveFile "jdk_summaries.ch_log" chlog#toPretty
  with
    CHFailure p
  | JCH_failure p ->
     pr_debug [ NL ; STR "Error in summaries: " ; p  ; NL ]
  | JCH_class_structure_error p ->
     pr_debug [ NL ; STR "Class structure error: " ; p ; NL ]
  | CHXmlReader.XmlParseError (l,c,p) ->
    pr_debug [ NL ; STR "Xml parse error at (" ; INT l ; STR "," ; INT c ; STR "): " ; p ; NL ]
  | XmlDocumentError(line, col, p) ->
    pr_debug [ NL ; STR "XML document error at (" ; INT line; STR ","; INT col; STR "): "; p; NL]

let _ = Printexc.print main ()
