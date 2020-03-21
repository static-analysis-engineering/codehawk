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
let name = ref ""
let cn = make_cn "java.lang.Object"

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

let packages = H.create 3

let default_implementations_to_pretty () =
  let lst = ref [] in
  let _ = H.iter (fun k v -> lst := (k,v) :: !lst) default_implementations in
  let lst = List.sort (fun (k1,_) (k2,_) -> P.compare k1 k2) !lst in
  LBLOCK (List.map (fun (k,v) ->
    LBLOCK [ fixed_length_pretty (STR k) 32 ; STR ": " ; 
	     pretty_print_list v (fun s -> s#toPretty) "" ", " "" ; NL ]) lst)

let add_package (name:string) (methods:int) =
  if H.mem packages name then
    let (numClasses,numMethods) = H.find packages name in
    H.replace packages name (numClasses + 1, numMethods + methods)
  else
    H.add packages name (1,methods)

let exception_guards = H.create 3

let add_guard name =
  if H.mem exception_guards name then
    H.replace exception_guards name ((H.find exception_guards name) + 1)
  else
    H.add exception_guards name 1

let classify_exception_guards (s:function_summary_int) =
  let infos = s#get_exception_infos in
  let conditions =
    List.fold_left (fun acc i -> i#get_safety_condition @ acc) [] infos in
  List.iter
    (fun c ->
      match c with
      | PreRelationalExpr _ -> add_guard "numeric"
      | PreNull _ -> add_guard "null"
      | PreNotNull _ -> add_guard "not-null" 
      | PreValidString _ -> add_guard "valid string") conditions

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


let print_exception_guards () =
  let pp = ref [] in
  let _ =
    H.iter (fun name num ->
        pp := (LBLOCK [ STR name ; STR ": " ; INT num ; NL ]) :: !pp) exception_guards in
  LBLOCK [ STR "Exception guards" ; NL ; LBLOCK !pp ]

let print_package_statistics () =
  let results = ref [] in
  let _ = H.iter (fun name (nC,nM) -> results := (name,nC,nM) :: !results) packages in
  let results = List.sort (fun (_,nC1,_) (_,nC2,_) -> Pervasives.compare nC1 nC2) !results in
  let pp = ref [] in
  let _ =
    List.iter (fun (name,nC,nM) ->
        let p =
          LBLOCK [ STR (fixed_length_string name 30) ; STR "  " ; 
		   fixed_length_pretty ~alignment:StrRight (INT nC) 8 ; STR "  " ;
		   fixed_length_pretty ~alignment:StrRight (INT nM) 8 ; NL ] in
        pp := p :: !pp) results in
  LBLOCK [ STR "Package statistics: " ; NL ; LBLOCK !pp ; NL ]

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
  

let inspect_summaries (name:string) =
  let cnSet = new ClassNameCollections.set_t in
  let nameSet = new StringCollections.set_t in
  let arrayArgumentSummaries = new ClassNameCollections.table_t in
  let classpath = system_settings#get_classpath in
  let arrayArgumentCounter = ref 0 in
  let increment_counter () = arrayArgumentCounter := !arrayArgumentCounter + 1 in
  let iSummaries = ref [] in
  let costexprs = ref [] in
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
	    add_package cn#package_name 
	                (List.length
                           (List.filter
                              (fun (_,_,s) ->
                                (not s#is_inherited) && s#is_valid) methodSummaries)) ;
	    List.iter (fun (_,_,s) -> classify_exception_guards s) methodSummaries ;
	    List.iter (fun (_,_,m) -> add_array_argument_summaries cn m) methodSummaries ;
	    List.iter (fun (_,_,m) -> add_abstract_argument m) methodSummaries ;
	    List.iter (fun (_,_,m) -> if has_interesting_feature m then
	                                iSummaries := m#toPretty :: !iSummaries) methodSummaries ;
            List.iter (fun (_,_,m) ->
                let  cost = m#get_time_cost in
                if not cost#is_top then
                  costexprs := (m#get_cms,cost) :: !costexprs) methodSummaries ;       
	    get_statistics methodSummaries ;
            collect_range_postconditions methodSummaries ;
	  end) (fun _ _ -> ()) name ;
    
    file_output#saveFile "jdk_summaries.ch_array_arguments" (print_summaries ()) ;
    file_output#saveFile
      "jdk_summaries.ch_abstracted_arguments"
      (pretty_print_list
         abstractedArguments#toList (fun cms -> LBLOCK [ cms#toPretty  ; NL ]) "" "" "") ;
    file_output#saveFile "jdk_summaries.ch_some_summaries" (LBLOCK !iSummaries) ; 
    file_output#saveFile "jdk_package_statistics" (print_package_statistics ()) ;
    file_output#saveFile "jdk_exception_guard_statistics" (print_exception_guards ()) ;
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
               INT (List.length !costexprs) ; STR "):" ; NL ;
               STR (string_repeat "-" 80) ; NL ];
    List.iter (fun (cms,x) ->
        pr_debug [ cms#toPretty ; NL ; INDENT (3,x#toPretty) ; NL ]) !costexprs ;

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
       let summaries =
         if !showinvalidfinal then
           List.filter (fun v -> v#is_final) summaries
         else
           summaries in
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

    (if !showstringsinks then print_string_sinks ())

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
    "prints list of string sinks") ]

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
