(* =============================================================================
   CodeHawk Java Analyzer
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
open CHPretty
open CHCommon
open CHLanguage

(* chutil *)
open CHXmlReader
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHPreAPI
open JCHSystemSettings
open JCHFunctionSummaryXmlDecoder

module H = Hashtbl
module P = Pervasives

module ClassMethodSignatureCollections = CHCollections.Make (
  struct
    type t = class_method_signature_int
    let compare m1 m2 = m1#compare m2
    let toPretty m = m#toPretty
  end)

module ClassFieldSignatureCollections = CHCollections.Make (
  struct
    type t = class_field_signature_int
    let compare f1 f2 = f1#compare f2
    let toPretty f = f#toPretty
  end)

let method_name cms =
  cms#class_method_signature_data#class_name#name ^ "." ^
  cms#class_method_signature_data#method_signature#name


let hashtable_to_pretty t =
  H.fold 
    (fun k v a -> LBLOCK [ a ; NL ; INT k ; STR " - " ; v#toPretty ]) t (STR "")
  
class function_summary_library_t:function_summary_library_int =
object (self)

  val mutable final_classes = []
  val mutable classes_to_be_excluded = []
  val method_library = H.create 3
  val class_library = H.create 3
  val field_library = H.create 3

  method size = H.length method_library

  method exclude_class (s:string) =
    classes_to_be_excluded <- (make_cn s) :: classes_to_be_excluded

  method private is_excluded (cn:class_name_int) =
    List.exists (fun cne -> cne#equal cn) classes_to_be_excluded


  method add_class_summary 
    (summary:(class_name_int * class_summary_int) * 
       (class_field_signature_int * field_stub_int) list *
       (class_method_signature_int * loop_info_t list * function_summary_int) list) =
    let ((cn,classSummary), fieldSummaries, methodSummaries) = summary in
    begin
      H.add class_library cn#index classSummary ;
      List.iter (fun (cfs,s) -> H.add field_library cfs#index s) fieldSummaries ;
      List.iter (fun (cms,_,s) -> H.add method_library cms#index s) methodSummaries ;
      chlog#add "method summaries"
	(let numInherited = 
	   List.length (List.filter (fun (m,_,s) -> 
	     s#is_inherited) methodSummaries) in
	 let numValidSummaries = 
	   List.length (List.filter (fun (m,_,s) -> 
	     s#is_valid) methodSummaries) in
	 LBLOCK [ fixed_length_pretty ~alignment:StrRight cn#toPretty 50 ; STR ": " ;
		  pp_quantity numValidSummaries ~numwidth:4
		    "method summary  " "method summaries" ; STR ", " ;
		  pp_quantity (List.length fieldSummaries) ~numwidth:4 "field " "fields" ;
		  (if numInherited > 0 then 
		      LBLOCK [ STR " (" ; 
			       pp_quantity numInherited ~numwidth:4 "inherited method "
			"inherited methods" ; STR ")" ] else STR "") ])
    end


  method private add_inherited_fields (cs:class_summary_int) =
    let cn = cs#get_class_name in
    let get_fields_from_class (cn:class_name_int) =
      H.fold 
	(fun _ v a -> 
	  if v#get_class_name#equal cn && not v#is_inherited then v::a else a) 
	field_library [] in
    let rec get_fields (cn:class_name_int) =
      let cs = try H.find class_library cn#index with 
	  Not_found -> 
	    raise (JCH_failure 
		     (LBLOCK [ STR "Class " ; cn#toPretty ; STR " (" ; 
			       INT cn#index ; STR ")" ;
			       STR " not found in class library" ; NL ;
			       hashtable_to_pretty class_library ; NL ])) in
      let super_fields =  
	if cs#has_super_class then get_fields cs#get_super_class else [] in
      (get_fields_from_class cn) @ super_fields in
    let all_interface_fields:field_stub_int list =
      H.fold (fun _ v a -> 
	if v#is_interface_field then v::a else a) field_library [] in
    let inherited_fields_from_super:field_stub_int list =
      if cs#has_super_class then get_fields cs#get_super_class else [] in
    let inherited_fields_from_interfaces:field_stub_int list =
      List.concat 
	(List.map 
	   (fun interface ->
	     List.filter (fun f -> 
	       f#get_class_name#equal interface) all_interface_fields)
	   cs#get_interfaces) in
    let inherited_fields = List.map
      (fun f ->
	let new_cfs = 
	  common_dictionary#make_class_field_signature cn f#get_signature in
	f#set_inherited new_cfs) 
      (inherited_fields_from_super @ inherited_fields_from_interfaces) in
    List.iter (fun f -> 
      H.add field_library f#get_class_signature#index f) inherited_fields
    
  method has_method_summary ?(anysummary=false) cms = 
    if H.mem method_library cms#index then
      let summary = H.find method_library cms#index in
      (summary#is_valid || anysummary)
      && ((not summary#is_inherited)
          || ((summary#has_defining_method)
              && (let dcms = summary#get_defining_method in
                  self#has_method_summary dcms)))
    else
      false
      
  method get_method_summary ?(anysummary=false) cms =
    try
      let summary = H.find method_library cms#index in
      if summary#is_valid || anysummary then
        summary
      else 
	raise (JCH_failure (LBLOCK [ STR "Function summary for " ; cms#toPretty ; 
				     STR " is not valid " ]))
    with
      Not_found ->
	raise (JCH_failure 
		 (LBLOCK [ STR "No function summary found for " ; cms#toPretty ]))
	  
  method has_class_summary cn = H.mem class_library cn#index
    
  method get_class_summary cn =
    try
      H.find class_library cn#index
    with
      Not_found ->
	raise (JCH_failure 
		 (LBLOCK [ STR "No class summary found for " ; cn#toPretty ]))
	  
  method iter f = H.iter (fun _ summary -> f summary) method_library
    
  method has_field_summary cfs = H.mem field_library cfs#index
    
  method get_field_summary cfs =
    try
      H.find field_library cfs#index
    with
      Not_found ->
	raise (JCH_failure 
		 (LBLOCK [ STR "No field summary found for " ; cfs#toPretty ]))
	  
  method private get_summaries (cn:class_name_int) =
    H.fold (fun _ v a -> if v#get_cms#class_name#equal cn then v :: a else a)
      method_library []
      
  method get_final_summaries (cn:class_name_int) =
    if self#has_class_summary cn then
      let cnSummary = self#get_class_summary cn in
      let scSummaries = if cnSummary#has_super_class then
	  let sc = cnSummary#get_super_class in
	  self#get_final_summaries sc
	else
	  [] in
      let cnSummaries = self#get_summaries cn in
      let cnSummaries = if cnSummary#is_final then 
	  cnSummaries
	else 
	  List.filter (fun summary -> summary#is_final) cnSummaries in
      (List.map (fun s -> s#get_cms) cnSummaries) @ scSummaries
    else
      []

  method get_invalid_methods =
    let invalidMethods =
      H.fold (fun k v a ->
          if v#is_valid then a else
            let cn = v#get_cms#class_name in
            try
              let classSummary = H.find class_library cn#index in
              if classSummary#is_dispatch || v#is_abstract then a else
                v#get_cms :: a
            with
              Not_found ->
              raise (JCH_failure (LBLOCK [ STR "class summary for " ; cn#toPretty ;
                                           STR " not found" ]))) method_library [] in
    List.sort (fun cms1 cms2 -> P.compare cms1#class_name#name cms2#class_name#name)
              invalidMethods
	
  method statistics_to_pretty =
    let numClasses = H.length class_library in
    let numInterfaces = H.fold (fun k v a -> 
      if v#is_interface then a+1 else a) class_library 0 in
    let numAbstractClasses =
      H.fold (fun k v a -> 
	if v#is_abstract && not v#is_interface then a+1 else a) class_library 0 in
    let numRegularClasses = numClasses - (numInterfaces + numAbstractClasses) in
    let numMethods = H.length method_library in
    let numInheritedMethods = 
      H.fold (fun k v a -> if v#is_inherited then a+1 else a) method_library 0 in
    let numInvalidMethods =
      H.fold (fun k v a -> if v#is_valid then a else a+1) method_library 0 in
    let numSummarizedMethods = numMethods - ( numInheritedMethods + numInvalidMethods ) in
    let numFields = H.length field_library in
    let numInheritedFields = 
      H.fold (fun k v a -> if v#is_inherited then a+1 else a) field_library 0 in
    let numFieldsWithValue =
      H.fold (fun k v a -> if v#has_value then a+1 else a) field_library 0 in
    LBLOCK
      [ STR (string_repeat "~" 80) ; NL ; 
	STR "Number of classes           : " ; 
	fixed_length_pretty ~alignment:StrRight (INT numClasses) 5 ; NL ;
	STR "   Regular classes          : " ; 
	fixed_length_pretty ~alignment:StrRight (INT numRegularClasses) 15 ; NL ;
	STR "   Interfaces               : " ; 
	fixed_length_pretty ~alignment:StrRight (INT numInterfaces) 15 ; NL ;
	STR "   Abstract classes         : " ; 
	fixed_length_pretty ~alignment:StrRight (INT numAbstractClasses) 15 ; NL ; NL ;
	STR "Number of methods           : " ; 
	fixed_length_pretty ~alignment:StrRight (INT numMethods) 5 ; NL ;
	STR "   Summarized methods       : " ;
	fixed_length_pretty ~alignment:StrRight (INT numSummarizedMethods) 15 ; NL ;
	STR "   Inherited methods        : " ;
	fixed_length_pretty ~alignment:StrRight (INT numInheritedMethods) 15 ; NL ;
	STR "   Not yet summarized       : " ; 
	fixed_length_pretty ~alignment:StrRight (INT numInvalidMethods) 15 ; NL ; NL ;
	STR "Number of fields            : " ;
	fixed_length_pretty ~alignment:StrRight (INT numFields) 5 ; NL ;
	STR "   Fields with a value      : " ;
	fixed_length_pretty ~alignment:StrRight (INT numFieldsWithValue) 15 ; NL ;
	STR "   Inherited fields         : " ;
	fixed_length_pretty ~alignment:StrRight (INT numInheritedFields) 15 ; NL ;
	STR (string_repeat "~" 80) ; NL ; NL ]
      
      
  method toPretty =
    H.fold 
      (fun _ v a -> LBLOCK [ a ; NL ; v#toPretty ]) method_library
      (STR "Function Library")
      
end
  
  
let function_summary_library = new function_summary_library_t
  
let mk_function_summary_library () = new function_summary_library_t
