(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFunctionInterface
open BCHFunctionData
open BCHLibTypes
open BCHMakeCallTargetInfo
open BCHSystemInfo

(* bchlibx86 *)
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHPredefined64bitEDKSemantics
open BCHPredefinedAllocaSemantics
open BCHPredefinedDelphiRTLSemantics
open BCHPredefinedDelphiRTLClassSemantics
open BCHPredefinedDelphiRTLSysUtilsSemantics
open BCHPredefinedDelphiRTLTypesSemantics
open BCHPredefinedELFSemantics
open BCHPredefinedErrnoSemantics
open BCHPredefinedFPSemantics
open BCHPredefinedGettersSemantics
open BCHPredefinedLibInternalCRTSemantics
open BCHPredefinedLibMemSemantics
open BCHPredefinedLibMiscSemantics
open BCHPredefinedLibStrSemantics
open BCHPredefinedLibWcsSemantics
open BCHPredefinedPredicatesSemantics
open BCHPredefinedProlog3Semantics
open BCHPredefinedProlog4Semantics
open BCHPredefinedSettersSemantics
open BCHPredefinedUpdatersSemantics
open BCHPredefinedWrappedCallSemantics
open BCHPredefinedUtil
open BCHOperand

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory


let callsemantic_definitions = H.create 3        (*  fnhash -> callsemantics *)
let callsemantics = H.create 3                   (*  faddr -> callsemantics *)

let register_hashed_functions () = 
  begin
    load_mem_functions () ;
    load_misc_functions () ;
    load_str_functions () ;
    load_wcs_functions () ;
    load_rtl_functions () ;
    load_rtl_sysutils_functions () ;
    load_rtl_tobject_functions () ;
    List.iter (fun flist ->
      List.iter (fun sem -> H.add callsemantic_definitions sem#get_md5hash sem) flist)
      [ alloca_functions ;
	delphi_rtl_functions () ;
	delphi_rtl_class_functions () ;
	delphi_rtl_sysutils_functions () ;
	delphi_rtl_types_functions ;
	edk64_functions ;
	fp_functions ;
	eh3_functions ;
	seh4_functions ;
	getter_functions ;
	internalcrt_functions ;
	libmem_functions () ;
	libmisc_functions () ;
	libstr_functions () ;
	libwcs_functions () ;
	setter_functions
      ]
  end

let register_hashed_elf_functions () =
  List.iter (fun flist ->
      List.iter
        (fun sem -> H.add callsemantic_definitions sem#get_md5hash sem) flist)
            [ thunk_functions
            ]
    
let patterns =
  List.concat [ 
      alloca_patterns ;
      delphi_rtl_patterns ;
      delphi_rtl_class_patterns ;
      delphi_rtl_sysutils_patterns ;
      delphi_rtl_types_patterns ;
      errno_patterns ;
      fp_patterns ;
      getter_patterns ;
      eh3_patterns ;
      seh4_patterns ;
      internalcrt_patterns ;
      libmem_patterns ;
      libmisc_patterns ;
      predicate_patterns ;
      setter_patterns ;
      updater_patterns ;
      wrapper_patterns
    ]


let get_templated_function faddr fnbytes fnhash =
  List.fold_left (fun result p ->
    match result with Some _ -> result | _ ->
      if Str.string_match p.regex_s fnbytes 0 then
	p.regex_f faddr fnbytes fnhash
      else
	None) None patterns

let register_predefined_callsemantics 
    (fnbytes:string) (fnhash:string) (instrs:int) (faddr:doubleword_int) =
  let add_semantics s =
    begin
      H.add callsemantics faddr#index s ;
      (functions_data#add_function faddr)#add_name s#get_name ;
      chlog#add "register function with predefined semantics"
	(LBLOCK [ faddr#toPretty ; STR ": " ; STR s#get_name ])
    end in
  if H.mem callsemantic_definitions fnhash then
    let semantics = H.find callsemantic_definitions fnhash in
    if semantics#get_instrcount = instrs then 
      add_semantics semantics
    else
      ch_error_log#add "inconsistent hash" 
	(LBLOCK [ faddr#toPretty ; STR " has " ; INT instrs ; STR ", but " ;
		  STR semantics#get_name ; STR " expects " ;
                  INT semantics#get_instrcount ])
  else
    match get_templated_function faddr fnbytes fnhash with
    | Some semantics -> add_semantics semantics
    | _ -> ()

let has_callsemantics (faddr:doubleword_int) = H.mem callsemantics faddr#index

let get_callsemantics (faddr:doubleword_int):predefined_callsemantics_int =
  try
    H.find callsemantics faddr#index
  with
  | Not_found ->
    raise (BCH_failure (LBLOCK [ STR "No call semantics found for " ; faddr#toPretty ]))

let get_callsemantics_target (faddr:doubleword_int):call_target_info_int =
  (get_callsemantics faddr)#get_call_target faddr
