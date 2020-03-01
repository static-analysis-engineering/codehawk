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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* cchlib *)
open CCHBasicTypes
open CCHExternalPredicate
open CCHLibTypes
open CCHTypesToPretty
open CCHUtilities

module H = Hashtbl

let p2s = pretty_to_string
  
let get_freed_terms fs =
  List.fold_left (fun acc (se,_) ->
    match se with XFreed t -> t::acc | _ -> acc) [] fs.fs_sideeffects

let get_repositioned_terms fs =
  List.fold_left (fun acc (se,_) ->
    match se with XRepositioned t -> t::acc | _ -> acc) [] fs.fs_sideeffects

let is_const_parameter fs (index:int) =       (* use index starting at 1 *)
  List.fold_left (fun acc (se,_) ->
    acc || 
      (match se with 
      | XConstTerm (ArgValue (ParFormal i,ArgNoOffset)) -> index = i
      | XFunctional -> true
      | _ -> acc)) false fs.fs_sideeffects

let preserves_memory_parameter fs (index:int) =    (* use index starting at 1 *)
  List.fold_left (fun acc (se,_) ->
    acc || 
      (match se with 
      | XConstTerm (ArgValue (ParFormal i,ArgNoOffset)) -> index = i 
      | XPreservesAllMemory
      | XFunctional -> true
      | _ -> acc)) false fs.fs_sideeffects

let preserves_null_termination fs (index:int) =      (* use index starting at 1 *)
  List.fold_left (fun acc (se,_) ->
    acc ||
      (match se with
      | XConstTerm (ArgValue (ParFormal i,ArgNoOffset)) -> index = i
      | XFunctional -> true
      | _ -> acc)) false fs.fs_sideeffects

exception XmlReaderError of int * int * pretty_t

let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, error_msg))
  end

let summary_annotation_to_string (a:summary_annotation_t) (name:string) =
  match a with
  | ExternalCondition s -> "EC (" ^ name ^ "): " ^ s
  | EnvironmentCondition s -> "Env (" ^ name ^ "): " ^ s
  | UnmodeledArgumentDependency s -> "UAD (" ^ name ^ "): " ^ s
  | NoAnnotation -> "explanation missing"

let get_summary_annotation_type (a:summary_annotation_t) =
  match a with
  | ExternalCondition _ -> "EC"
  | EnvironmentCondition _ -> "Env"
  | UnmodeledArgumentDependency _ -> "UAD"
  | NoAnnotation -> "none"

let get_summary_annotation_string (a:summary_annotation_t) =
  match a with
  | ExternalCondition s
    | EnvironmentCondition s
    | UnmodeledArgumentDependency s -> s
  | NoAnnotation -> "?"

let annotated_xpredicate_to_string (a:annotated_xpredicate_t) =
  let (p,a) = a in
  match a with
  | NoAnnotation -> p2s (xpredicate_to_pretty p)
  | _ -> (p2s (xpredicate_to_pretty p))  ^  " [" ^ (get_summary_annotation_string a) ^ "]"

let read_xml_summary_annotation (node:xml_element_int):summary_annotation_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  if has "env" then EnvironmentCondition (get "env")
  else if has "ec" then ExternalCondition (get "ec")
  else if has "uad" then UnmodeledArgumentDependency (get "uad")
  else NoAnnotation


let read_xml_ds_condition (node:xml_element_int) : ds_condition_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let getcc = node#getTaggedChildren in
  { dsc_ckey = geti "ckey" ;
    dsc_name = get "name" ;
    dsc_fields = List.concat (List.map (fun n -> read_xml_xpredicate n []) (getcc "post")) 
  }
    
let read_xml_precondition_list 
    (node:xml_element_int) ?(gvars=[]) params: annotated_xpredicate_t list =
  List.concat
    (List.map (fun pNode ->
         let a = read_xml_summary_annotation pNode in
         List.map (fun p -> (p,a)) (read_xml_xpredicate pNode ~gvars params))
              (List.map (fun n ->
                   n#getTaggedChild "math") (node#getTaggedChildren "pre")))
  
let read_xml_postcondition_list 
      (node:xml_element_int)
      ?(gvars=[]) params :(annotated_xpredicate_t list * annotated_xpredicate_t list) =
  let zero_val = NumConstant numerical_zero in
  let negone_val = NumConstant numerical_one#neg in
  let predefined =
    List.filter (fun p ->
        not (p#getTag = "post" || p#getTag = "error-post")) node#getChildren in
  let noa p = (p, NoAnnotation) in
  let (predefinedPost,predefinedErrorpost) = 
    List.fold_left (fun (accP,accE) pNode ->
      match pNode#getTag with
      | "notnull-null" -> 
	((noa (XNotNull ReturnValue))::accP, (noa )(XNull ReturnValue)::accE)
      | "zero-negone" -> 
	((noa (XRelationalExpr (Eq,ReturnValue,zero_val))):: accP,
	 (noa (XRelationalExpr (Eq,ReturnValue,negone_val))) :: accE)
      | "zero-notzero" -> 
	((noa (XRelationalExpr (Eq,ReturnValue,zero_val))) :: accP,
	 (noa (XRelationalExpr (Ne,ReturnValue,zero_val))) :: accE)
      | "notzero-zero" -> 
	((noa (XRelationalExpr (Ne,ReturnValue,zero_val))) :: accP,
	 (noa (XRelationalExpr (Eq,ReturnValue,zero_val))) :: accE)
      | s -> raise_error pNode 
	(LBLOCK [ STR "Unknown predefined postcondition predicate: " ; 
		  STR s ])) ([],[]) predefined in
  let postNodes = List.filter (fun p -> p#getTag = "post") node#getChildren in
  let errorpostNodes =
    List.filter (fun p -> p#getTag = "error-post") node#getChildren in
  let post = 
    List.concat
      (List.map (fun pNode ->
           let a = read_xml_summary_annotation pNode in
           let pNode = pNode#getTaggedChild "math" in
           List.map (fun p -> (p,a)) (read_xml_xpredicate pNode ~gvars params)) postNodes) in
  let errorpost =
    List.concat
      (List.map (fun pNode ->
           let a = read_xml_summary_annotation  pNode in
           let pNode = pNode#getTaggedChild "math" in
           List.map (fun p -> (p,a)) (read_xml_xpredicate pNode ~gvars params)) errorpostNodes) in
  ((predefinedPost @ post), (predefinedErrorpost @ errorpost))
    
let read_xml_sideeffect_list
      (node:xml_element_int) ?(gvars=[]) params: annotated_xpredicate_t list =
  let sidenodes =
    List.map (fun s -> s#getTaggedChild "math") (node#getTaggedChildren "sideeffect") in
  List.concat
    (List.map
       (fun sNode ->
         let a = read_xml_summary_annotation sNode in
         List.map (fun s -> (s,a)) (read_xml_xpredicate sNode ~gvars params)) sidenodes)
  
let read_xml_parameter_list 
      (fname:string)
      (node:xml_element_int):(annotated_xpredicate_t list * (string * int) list) =
  let paramList = ref [] in
  let preList = ref [] in
  let deref_read t  = XInitializedRange (t, IndexSize (NumConstant numerical_one)) in
  let deref_write t = XBuffer (t, IndexSize (NumConstant numerical_one)) in
  let deref_read_nt t = XInitializedRange (t, IndexSize (ArgNullTerminatorPos t)) in
  let _ = List.iter (fun xpar ->
    let get = xpar#getAttribute in
    let get_int = xpar#getIntAttribute in
    let hasc = xpar#hasTaggedChild in
    let getc = xpar#getTaggedChild in
    let name = get "name" in
    let seqnr = get_int "nr" in
    let arg = ArgValue (ParFormal seqnr,ArgNoOffset) in
    let _ =
      if hasc "pre" then
	List.iter (fun xpre ->
	    let prec = match xpre#getTag with
	      | "deref-read" -> [ deref_read arg ; XNotNull arg ]
	      | "deref-read-null" -> [ deref_read arg ]
	      | "deref-write" -> [ deref_write arg ; XNotNull arg ]
	      | "deref-write-null" -> [ deref_write arg ]
	      | "deref-read-nt" -> [ deref_read_nt arg ; XNotNull arg ]
	      | "deref-read-nt-null" -> [ deref_read_nt arg ]
	      | "not-null" -> [ XNotNull arg ]
	      | "allocation-base" -> [ XAllocationBase arg ]
	      | "null" -> [ XNull arg ]
	      | "format-string" ->
                 if xpre#hasNamedAttribute "input"
                    && (xpre#getAttribute "input") = "yes" then
                   [ XInputFormatString arg ]
                 else
                   [ XOutputFormatString arg ]
	      | s ->
                 raise_error
                   xpre 
	           (LBLOCK [ STR "read_xml_parameter: " ; STR s ;
			     STR " not recognized as shortcut precondition" ]) in
	    preList := prec @ !preList) (getc "pre")#getChildren in
    paramList := (name,seqnr) :: !paramList) (node#getTaggedChildren "par") in
  (List.map (fun p -> (p,NoAnnotation)) !preList, !paramList)
    
let read_xml_function_summary (node:xml_element_int) : function_summary_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasTaggedChild in
  let fname = get "name" in
  let domainref =
    if hasc "domainref" then
      let dnode = getc "domainref" in
      Some (dnode#getAttribute "name", dnode#getAttribute "desc")
    else
      None in
  let (parpre,params) = read_xml_parameter_list fname (getc "parameters") in
  let preconditions =
    if hasc "preconditions" then 
      read_xml_precondition_list (getc "preconditions") params 
    else [] in
  let (postconditions,errorpostconditions) = 
    if hasc "postconditions" then 
      read_xml_postcondition_list (getc "postconditions") params 
    else ([],[]) in
  let sideeffects = 
    if hasc "sideeffects" then 
      read_xml_sideeffect_list (getc "sideeffects") params
    else [] in
  { fs_fname = fname ;
    fs_domainref = domainref ;
    fs_params = params ;
    fs_preconditions = parpre @  preconditions ;
    fs_postconditions = postconditions;
    fs_error_postconditions = errorpostconditions;
    fs_sideeffects = sideeffects
  }
    	
class function_summary_library_t:function_summary_library_int =
object (self)
  
  val mutable summary_jars = []
  val mutable paths = []
  val table = H.create 13
    
  method add_summary_jar (s:string) =
    begin
      summary_jars <- s :: summary_jars ;
      match open_path s with 
      | Some p -> 
	begin pr_debug [ STR "Opening " ; STR s ; NL ] ; paths <- p :: paths end
      | _ -> ()
    end
      
  method get_summary (name:string) = 
    try
      H.find table name
    with
      Not_found -> raise (Invalid_argument ("get_summary: " ^ name))
	
  method read_function_summary_string (name:string) (s:string) =
    try
      let xmlDoc = readXmlDocumentString s in
      let root = xmlDoc#getRoot in
      let xsummary = root#getTaggedChild "function-summary" in
      let summary = read_xml_function_summary xsummary in
      H.add table name summary
    with 
    | XmlParseError (line,col,p)
    | XmlReaderError (line,col,p)
    | XmlDocumentError (line,col,p) ->
      let msg = LBLOCK [ STR name  ; STR ": " ; p ] in
      begin
	raise (XmlDocumentError (line,col,msg))
      end

  method read_xml_substitute_summary (node:xml_element_int) (name:string) =
    try
      let summary  = read_xml_function_summary node in
      let _ = chlog#add "substitute library summary"  (STR name) in
      H.add table name summary
    with
    | XmlDocumentError (line,col,p) ->
      let msg = LBLOCK [ STR name  ; STR ": " ; p ] in
      begin
	raise (XmlDocumentError (line,col,msg))
      end      

  method has_summary (header:string) (name:string) =
    if H.mem table name then true else
      try
	let filename = header ^ "/" ^ name in
	if has_summary_file paths filename then
	  let xmlString = get_summary_file paths filename in
	  begin
	    self#read_function_summary_string name xmlString ;
            let summary = H.find table name in
            chlog#add
              "function summary"
              (LBLOCK [ STR name ; STR " -- " ; STR "post: " ;
                        INT (List.length summary.fs_postconditions) ;
                        STR "; error-post: " ;
                        INT (List.length summary.fs_error_postconditions) ]) ;
	    true
	  end
	else
	  false
      with
	XmlDocumentError (line,col,msg) -> 
	begin
          ch_error_log#add
            "function summary"
            (LBLOCK [ STR header ; STR "/" ; STR name ; STR ": Xml error: (" ;
                      INT line ; STR "," ; INT col ; STR "): " ; msg ]);
	  false
	end

  method has_builtin_summary (name:string) = self#has_summary "builtins" name
	    
  method statistics_to_pretty =
    let nRef = H.fold (fun _ s acc ->
                   match s.fs_domainref with Some _ -> acc + 1 | _ -> acc) table 0 in
    let nPre = H.fold (fun _ s acc -> 
                   acc + (List.length s.fs_preconditions)) table 0 in
    let nPost = H.fold (fun _ s acc -> 
      acc + (List.length s.fs_postconditions)) table 0 in
    let nErrorPost = H.fold (fun _ s acc -> 
      acc + (List.length s.fs_error_postconditions)) table 0 in
    let nSideEffects = H.fold (fun _ s acc -> 
                           acc + (List.length s.fs_sideeffects)) table 0 in
    let pr_right n = fixed_length_pretty ~alignment:StrRight (INT n) 5 in
    LBLOCK [ STR "Summaries           : " ; pr_right (H.length table) ; NL ;
             STR "Domain references   : " ; pr_right nRef ; NL ;
	     STR "Preconditions       : " ; pr_right nPre ; NL ;
	     STR "Postconditions      : " ; pr_right nPost ; NL ;
	     STR "Error-postconditions: " ; pr_right nErrorPost ; NL ;
	     STR "Side effects        : " ; pr_right nSideEffects ; NL ]
      
end
  

let function_summary_library = new function_summary_library_t

let application_summary_library = H.create 3

let has_application_summary (gvid:int) = H.mem application_summary_library gvid

let get_application_summary (gvid:int) = 
  try
    H.find application_summary_library gvid
  with
    Not_found -> 
      raise (CCHFailure 
	       (LBLOCK [ STR "No application summary found for " ; INT gvid ]))

let set_application_summary (gvid:int) (summary:function_summary_t) =
  H.replace application_summary_library gvid summary

let application_ds_library = H.create 3

let has_application_ds_summary (gkey:int) = H.mem application_ds_library gkey

let get_application_ds_summary (gkey:int) =
  try
    H.find application_ds_library gkey
  with
   Not_found ->
     raise (CCHFailure 
	      (LBLOCK [ STR "No application data structure summary found for " ;
			INT gkey ]))

let set_application_ds_summary (gkey:int) (ds:ds_condition_t) =
  H.replace application_ds_library gkey ds


let gac_datastructures = ref []
let set_gac_datastructures l = gac_datastructures := l
let is_gac_datastructure i = List.mem i !gac_datastructures
