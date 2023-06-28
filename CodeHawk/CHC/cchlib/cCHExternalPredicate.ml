(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
open CCHLibTypes
open CCHSettings
open CCHSumTypeSerializer
open CCHTypesToPretty
open CCHUtilities

module H = Hashtbl


let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, error_msg))
  end


let macroconstants = H.create 11


let _ =
  List.iter (fun (name,tval) ->
      H.add  macroconstants name (NumConstant (mkNumericalFromString tval)))
            [ ("MININT8", "-128") ;
              ("MAXINT8", "127") ;
              ("MAXUINT8", "255") ;
              ("MININT16", "-32768") ;
              ("MAXINT16", "32767") ;
              ("MAXUINT16", "65535") ;
              ("MININT32", "-2147483648") ;
              ("MAXINT32", "2147483647") ;
              ("MAXUINT32", "4294967295") ;
              ("MININT64", "-9223372036854775808") ;
              ("MAXINT64", "9223372036854775807") ;
              ("MAXUINT64", "18446744073709551615") ]

let is_macro_constant (name:string) = H.mem macroconstants name

let get_macro_constant (name:string):s_term_t =
  if H.mem macroconstants name then
    H.find macroconstants name
  else
    raise (CCHFailure (LBLOCK [ STR "Macro constant " ; STR name ; STR " not found" ]))

let macrovalues32 = H.create 11
let macrovalues64 = H.create 11
let macrovalues = H.create  3


let _ =
  List.iter (fun (name,tmacro) ->
      H.add macrovalues32 name tmacro)
            [ ("MININT", "MININT32");
              ("MAXINT", "MAXINT32");
              ("MAXUINT", "MAXUINT32");
              ("MINLONG", "MININT32");
              ("MAXLONG", "MAXINT32");
              ("MAXULONG", "MAXUINT32");
              ("MAXULONGLONG", "MAXUINT64");
              ("MAXLONGLONG", "MAXINT64");
              ("MINLONGLONG", "MININT64")
            ]

let _ =
  List.iter (fun (name,tmacro) ->
      H.add macrovalues64 name tmacro)
            [ ("MININT", "MININT32");
              ("MAXINT", "MAXINT32");
              ("MAXUINT", "MAXUINT32");
              ("MINLONG", "MININT64");
              ("MAXLONG", "MAXINT64");
              ("MAXULONG", "MAXUINT64");
              ("MAXULONGLONG", "MAXUINT64");
              ("MAXLONGLONG", "MAXINT64");
              ("MINLONGLONG", "MININT64")
            ]

let _ = H.add macrovalues 32 macrovalues32
let _ = H.add macrovalues 64 macrovalues64


let get_macro_value_size name wordsize =
  let default () =
    let _ =
      chlog#add
        "symbolic name in function summary"
        (LBLOCK [STR name; STR " (wordsize: "; INT wordsize]) in
    NamedConstant name in
  if  H.mem macrovalues wordsize then
    let values = H.find macrovalues wordsize in
    if H.mem values name then
      get_macro_constant (H.find values name)
    else
      default ()
  else
    default ()


let is_generic_macro_constant (name:string) =
  List.mem name
    ["MININT";
     "MAXINT";
     "MAXUINT";
     "MINLONG";
     "MAXLONG";
     "MAXULONG";
     "MAXULONGLONG";
     "MINLONGLONG";
     "MAXLONGLONG"]


let is_macro_value (name:string) =
  (is_macro_constant name) || (is_generic_macro_constant name)


let get_macro_value (name:string):s_term_t =
  let default () =
    let _ = chlog#add "symbolic name in function summary" (STR name) in
    NamedConstant name in
  if is_macro_constant name then
    get_macro_constant name
  else if is_generic_macro_constant name then
    if system_settings#has_wordsize then
      get_macro_value_size name system_settings#get_wordsize
    else
      default ()
  else
    default ()


let xpredicate_tag p =
  match p with
  | XAllocationBase _ -> "allocation-base"
  | XBlockWrite _ -> "block-write"
  | XBuffer _ -> "buffer"
  | XConstTerm _ -> "const"
  | XControlledResource _ -> "controlled-resource"
  | XFalse -> "false"
  | XFormattedInput _  -> "fomatted-input"
  | XFreed _ -> "freed"
  | XFunctional -> "functional"
  | XGlobalAddress _ -> "global-address"
  | XHeapAddress _ -> "heap-address"
  | XInitialized _ -> "initialized"
  | XInitializedRange _ -> "initialized-range"
  | XInvalidated _ -> "invalidated"
  | XInputFormatString _ -> "input-formatstring"
  | XNewMemory _ -> "new-memory"
  | XNoOverlap _ -> "no-overlap"
  | XNotNull _ -> "not-null"
  | XNotZero _ -> "not-zero"
  | XNonNegative _ -> "non-negative"
  | XNull _ -> "null"
  | XNullTerminated _ -> "nt"
  | XOutputFormatString _ -> "output-formatstring"
  | XPreservesAllMemory -> "preserves-all-memory"
  | XPreservesAllMemoryX _ -> "preserves-all-memory-x"
  | XPreservesMemory _ -> "preserves-memory"
  | XPreservesNullTermination -> "preserves-null-termination"
  | XPreservesValidity _ -> "preserves-validity"
  | XPreservesValue _ -> "preserves-value"
  | XRepositioned _ -> "repositioned"
  | XRelationalExpr _ -> "relational-expr"
  | XRevBuffer _ -> "rev-buffer"
  | XStackAddress _ -> "stack-address"
  | XConfined _ -> "confined"
  | XTainted _ -> "tainted"
  | XUniquePointer _ -> "unique-pointer"
  | XValidMem _ -> "valid-memory"
  | XPolicyPre _ -> "policy-pre"
  | XPolicyValue _ -> "policy-value"
  | XPolicyTransition _ -> "policy-transition"


class s_term_walker_t =
object (self)

  method walk_api_parameter (p:api_parameter_t) = ()

  method walk_s_offset (o:s_offset_t) =
    let toff = self#walk_s_offset in
    match o with
    | ArgNoOffset -> ()
    | ArgFieldOffset (_,ss) -> toff ss
    | ArgIndexOffset (_,ss) -> toff ss

  method walk_s_term (t:s_term_t) =
    let toff = self#walk_s_offset in
    let tp = self#walk_api_parameter in
    let tt = self#walk_s_term in
    match t with
    | ArgValue (p,o) -> begin tp p ; toff o end
    | IndexSize t -> tt t
    | ByteSize t -> tt t
    | ArgAddressedValue (t1,o) -> begin tt t1 ;  toff o end
    | ArgNullTerminatorPos t -> tt t
    | ArgSizeOfType t -> tt t
    | ArithmeticExpr (_,t1,t2) -> begin tt t1 ; tt t2 end
    | FormattedOutputSize t -> tt t
    | Region t -> tt t
    | ChoiceValue (optt1,optt2) ->
       begin
         (match optt1 with Some t1 -> tt t1 | _ -> ()) ;
         (match optt2 with Some t2 -> tt t2 | _ -> ())
       end
    | _ -> ()

end


class xpredicate_walker_t =
object (self)

  method walk_s_term (index:int) (t:s_term_t) = ()

  method walk_api_parameter (index:int) (p:api_parameter_t) = ()

  method walk_xpredicate (p:xpredicate_t) =
    let wt = self#walk_s_term in
    match p with
    | XAllocationBase t -> wt 1 t
    | XControlledResource (_,t) -> wt 2 t
    | XBlockWrite (t1,t2) ->  begin  wt 1 t1 ;  wt 2 t2 end
    | XBuffer (t1,t2) -> begin wt 1 t1 ; wt 2 t2 end
    | XConfined t -> wt 1 t
    | XConstTerm t -> wt 1 t
    | XFormattedInput t -> wt 1 t
    | XFalse -> ()
    | XFreed t -> wt 1 t
    | XFunctional ->  ()
    | XInitialized t -> wt 1  t
    | XInitializedRange (t1,t2) -> begin wt 1 t1 ; wt 2 t2 end
    | XInputFormatString t -> wt 1 t
    | XInvalidated t -> wt 1 t
    | XNewMemory t -> wt 1 t
    | XStackAddress t -> wt 1 t
    | XHeapAddress t -> wt 1 t
    | XGlobalAddress t -> wt 1 t
    | XNoOverlap (t1,t2) -> begin  wt 1 t1 ; wt 2 t2 end
    | XNotNull t -> wt 1 t
    | XNull t -> wt 1 t
    | XNotZero t -> wt 1 t
    | XNonNegative t -> wt 1 t
    | XNullTerminated t -> wt 1 t
    | XOutputFormatString t -> wt 1 t
    | XPreservesAllMemory -> ()
    | XPreservesAllMemoryX l -> List.iteri wt l
    | XPreservesMemory t -> wt 1 t
    | XPreservesValue t -> wt 1 t
    | XPreservesNullTermination -> ()
    | XPreservesValidity t -> wt 1 t
    | XRelationalExpr (_,t1,t2) -> begin wt 1 t1 ; wt 2 t2 end
    | XRepositioned t -> wt 1 t
    | XRevBuffer (t1,t2) -> begin wt 1 t1 ; wt 2 t2 end
    | XTainted (t1,optt2,optt3) ->
       begin
         wt 1 t1 ;
         (match optt2 with Some t2 -> wt 2 t2 | _ -> ()) ;
         (match optt3 with Some t3 -> wt 3 t3 | _ -> ())
       end
    | XUniquePointer t -> wt 1 t
    | XValidMem t -> wt 1 t
    | XPolicyPre (t,_,_) -> wt 1 t
    | XPolicyValue (t,_,_) -> wt 1 t
    | XPolicyTransition (t,_,_) -> wt 1 t

end


class  find_global_walker_t =
object

  inherit s_term_walker_t as super

  val mutable result = []

  method walk_api_parameter (p:api_parameter_t) =
    match p with
    | ParGlobal g -> result <- g :: result
    | _ -> ()

  method get_result = result

end


class xpredicate_get_term_walker_t  (walker:find_global_walker_t) =
object

  inherit xpredicate_walker_t as super

  method walk_term (index:int) t = walker#walk_s_term t

  method get_result = walker#get_result

end


let find_xpredicate_global_vars (p:xpredicate_t) =
  let w = new find_global_walker_t in
  let walker = new xpredicate_get_term_walker_t w in
  let _ = walker#walk_xpredicate p in
  walker#get_result


let rec s_offset_to_pretty s =
  match s with
  | ArgNoOffset -> STR ""
  | ArgFieldOffset (name,t) ->
     LBLOCK [ STR "." ; STR name ; s_offset_to_pretty t ]
  | ArgIndexOffset (index,t) ->
     LBLOCK [ STR "[" ; index#toPretty ; STR "]" ; s_offset_to_pretty t ]


let rec s_term_to_pretty s =
  let opt_t_topretty optt =
    match optt with
    | Some t -> s_term_to_pretty t
    | _ -> STR "_" in
  match s with
  | ArgValue (ParFormal i,soff) ->
     LBLOCK [ STR "arg_" ; INT i ; s_offset_to_pretty soff ]
  | ArgValue (ParGlobal s,soff) -> LBLOCK [ STR s ; s_offset_to_pretty soff ]
  | LocalVariable name -> LBLOCK [ STR "var_" ; STR name ]
  | ReturnValue -> STR "return-value"
  | NamedConstant s -> LBLOCK [ STR "constant_" ; STR s ]
  | NumConstant n -> n#toPretty
  | IndexSize t -> LBLOCK [ STR "index-size(" ; s_term_to_pretty t ; STR ")" ]
  | ByteSize t -> LBLOCK [ STR "byte-size(" ; s_term_to_pretty t ; STR ")" ]
  | ArgAddressedValue (t,soff) -> 
     LBLOCK [ STR "(*" ; s_term_to_pretty t ; STR ")" ;
              s_offset_to_pretty soff ; STR ")" ]
  | ArgNullTerminatorPos t ->
    LBLOCK [ STR "null-terminator-pos(" ; s_term_to_pretty t ; STR ")" ]
  | ArgSizeOfType t -> LBLOCK [ STR "sizeof(" ; s_term_to_pretty t; STR ")" ]
  | ArithmeticExpr (op,t1,t2) -> 
    LBLOCK [ s_term_to_pretty t1 ; STR (binop_to_print_string op) ;
	     s_term_to_pretty t2 ]
  | FormattedOutputSize t ->
     LBLOCK [ STR "formatted-output-size(" ; s_term_to_pretty t ; STR ")" ]
  | Region t -> LBLOCK [ STR "region(" ; s_term_to_pretty t ; STR ")" ]
  | RuntimeValue -> LBLOCK [ STR "runtime-value" ]
  | ChoiceValue (opt1,opt2) ->
     LBLOCK [ STR "choice(" ; opt_t_topretty opt1 ; STR "," ;
              opt_t_topretty opt2 ; STR ")" ]


let xpredicate_to_pretty p =
  let sp = s_term_to_pretty in
  let namet name t = LBLOCK [ STR name ; STR "(" ; sp t ; STR ")" ] in
  match p with
  | XAllocationBase t -> namet "allocation-base" t
  | XBlockWrite (ptr,len) ->
     LBLOCK [ STR "block-write(" ; sp ptr ; STR ", len: " ; sp len ; STR ")" ]
  | XBuffer (ptr,len) ->
     LBLOCK [ STR "buffer(" ; sp ptr ; STR ", len:" ; sp len ; STR ")" ]
  | XConfined t -> namet "confined" t
  | XConstTerm t -> namet "const" t
  | XControlledResource (r,t) ->
     LBLOCK [ STR "controlled-resource:" ; STR  r ; STR "(" ; sp t ; STR ")" ]
  | XFalse -> STR "false"
  | XFormattedInput t -> namet "formatted-input" t
  | XFreed t -> namet "freed" t
  | XFunctional -> STR "functional"
  | XGlobalAddress t -> namet "global-address" t
  | XHeapAddress t -> namet "heap-address" t
  | XInitialized t -> namet "initialized" t
  | XInitializedRange (ptr,len) ->
     LBLOCK [ STR "initialized-range(" ; sp ptr ; STR ", len:" ;
              sp len ; STR ")" ]
  | XInputFormatString t -> namet "input-format-string" t
  | XInvalidated t -> namet "invalidated" t
  | XNewMemory t -> LBLOCK [ STR "new-memory(" ; sp t ; STR ")" ]
  | XNoOverlap (t1,t2) ->
     LBLOCK [ STR  "no-overlap(" ; sp t1 ; STR "," ; sp t2 ; STR ")" ]
  | XNotNull t -> namet "not-null" t
  | XNotZero t -> namet "not-zero" t
  | XNonNegative t -> namet "non-negative" t
  | XNull t -> namet "null" t
  | XNullTerminated t -> namet "null-terminated" t
  | XOutputFormatString t -> namet "output-format-string" t
  | XPreservesAllMemory -> STR "preserves-all-memory"
  | XPreservesAllMemoryX l ->
     LBLOCK [ STR "preserves-all-memory" ;
              pretty_print_list l s_term_to_pretty "(" "," ")" ]
  | XPreservesMemory t -> namet "preserves-memory" t
  | XPreservesValue t -> namet "preserves-value" t
  | XPreservesNullTermination -> STR "preserves-null-termination"
  | XPreservesValidity t -> namet "preserves-validity" t
  | XRelationalExpr (op,t1,t2) ->
     LBLOCK [ sp t1 ; STR (binop_to_print_string op) ; sp t2 ]
  | XRepositioned t -> namet "repositioned" t
  | XRevBuffer (ptr,len) ->
     LBLOCK [ STR "rev-buffer(" ; sp ptr ; STR ", len:" ; sp len ; STR ")" ]
  | XStackAddress t -> namet "stack-address" t
  | XTainted (t,optlb,optub) ->
     LBLOCK [ namet "tainted" t ; STR "[" ;
              (match optlb with Some lb -> s_term_to_pretty lb | _ -> STR "_") ; STR " ; " ;
              (match optub with Some ub -> s_term_to_pretty ub | _ -> STR "_") ; STR "]" ]
  | XUniquePointer t -> namet "unique-pointer" t
  | XValidMem t -> namet "valid-memory" t
  | XPolicyPre (t,pname,pstates) ->
     LBLOCK [ STR "policy-pre(" ; sp t ; STR  ",policy:" ; STR pname ; STR ",states" ;
              pretty_print_list pstates (fun s -> STR s) "[" "," "]" ]
  | XPolicyValue (t,pname,None) ->
     LBLOCK [ STR "policy-value(" ; sp t ; STR ",policy:" ; STR pname ]
  | XPolicyValue (t,pname,Some tname) ->
     LBLOCK [ STR "policy-value(" ; sp t ; STR ",policy:" ; STR pname ;
              STR ", transition:" ; STR tname ]
  | XPolicyTransition(t,pname,ptrans) ->
     LBLOCK [ STR "policy-transition(" ; sp t ; STR ",policy:" ; STR pname ;
              STR ",transition:" ; STR ptrans ]


let rec get_term_parameters (t:s_term_t) =
  match t with
  | ArgValue (ParFormal i,_) -> [ i ]
  | IndexSize t
    | ByteSize t
    | ArgNullTerminatorPos t
    | ArgSizeOfType t -> get_term_parameters t
  | ArgAddressedValue (t,_) -> get_term_parameters t
  | ArithmeticExpr (_,t1,t2) -> (get_term_parameters t1) @ (get_term_parameters t2)
  | ChoiceValue (opt1,opt2) ->
     (get_optterm_parameters opt1) @ (get_optterm_parameters opt2)
  | _ -> []


and get_optterm_parameters (t:s_term_t option) =
  match t with Some t -> get_term_parameters t | _ -> []


let rec get_term_global_variables (t:s_term_t) =
  match t with
  | ArgValue (ParGlobal s,_) -> [ s ]
  | IndexSize t
    | ByteSize t
    | ArgNullTerminatorPos t
    | ArgSizeOfType t
    | ArgAddressedValue (t,_) -> get_term_global_variables t
  | ArithmeticExpr (_,t1,t2) ->
     (get_term_global_variables t1) @ (get_term_global_variables t2)
  | ChoiceValue (opt1,opt2) ->
     (get_optterm_global_variables opt1) @ (get_optterm_global_variables opt2)
  | _ ->  []

and get_optterm_global_variables  (t:s_term_t option) =
  match t with Some t -> get_term_global_variables t | _ -> []
    
let get_xpredicate_terms (pred:xpredicate_t) =
  match pred with
  | XFalse
    | XFunctional
    | XPreservesAllMemory
    | XPreservesNullTermination  -> []
  | XAllocationBase t
    | XConstTerm t
    | XControlledResource (_,t)
    | XFormattedInput t
    | XFreed t
    | XGlobalAddress t
    | XHeapAddress t
    | XInitialized t
    | XInputFormatString t
    | XInvalidated t
    | XNotNull t
    | XNotZero t
    | XNonNegative t
    | XNull t
    | XNullTerminated t
    | XOutputFormatString t
    | XPreservesMemory t
    | XPreservesValue t
    | XPreservesValidity t
    | XNewMemory t
    | XRepositioned t
    | XStackAddress  t
    | XConfined t
    | XUniquePointer t
    | XValidMem t
    | XPolicyPre (t,_,_)
    | XPolicyValue (t,_,_)
    | XPolicyTransition (t,_,_) -> [ t ]
  | XBuffer (t1,t2)
    | XBlockWrite (t1,t2)
    | XInitializedRange(t1,t2)
    | XNoOverlap (t1,t2)
    | XRelationalExpr (_,t1,t2)
    | XRevBuffer (t1,t2) ->  [ t1 ; t2 ]
  | XPreservesAllMemoryX l ->  l
  | XTainted (t,optlb,optub) ->
     match (optlb,optub) with
     | (Some t1, Some t2) -> [ t ; t1 ; t2 ]
     | (Some t1, _) -> [ t ; t1 ]
     | (_, Some t2) -> [ t ; t2 ]
     | _ -> [ t ]

let get_xpredicate_parameters p =
  let terms = get_xpredicate_terms p in
  List.concat (List.map get_term_parameters terms)

let get_xpredicate_global_variables p =
  let terms = get_xpredicate_terms p in
  List.concat (List.map get_term_global_variables terms)


let binop_from_mathml_string s =
  match s with
  | "plus" -> PlusA
  | "minus" -> MinusA
  | "times" -> Mult
  | "divide" -> Div
  | "eq" -> Eq
  | "neq" -> Ne
  | "gt" -> Gt
  | "lt" -> Lt
  | "geq" -> Ge
  | "leq" -> Le
  | s -> raise (Invalid_argument ("Mathml binop not recognized: " ^ s))
    
let binop_to_mathml_string op =
  match op with
  | PlusA -> "plus"
  | MinusA -> "minus"
  | Mult -> "times"
  | Div -> "divide"
  | Eq -> "eq"
  | Ne -> "neq"
  | Gt -> "gt"
  | Lt -> "lt"
  | Ge -> "geq"
  | Le -> "leq"
  | _ -> raise (Invalid_argument 
		  ("No math ml symbol available for " ^ (binop_to_print_string op)))

let rec s_offset_to_dfs_string (s:s_offset_t) =
  let tag = s_offset_mcts#ts s in
  let tofs = s_offset_to_dfs_string in
  match s with
  | ArgNoOffset -> tag
  | ArgFieldOffset (name,t) -> tag ^ "," ^ name ^ "," ^ (tofs t)
  | ArgIndexOffset (index,t) -> tag ^  "," ^ index#toString ^ "," ^ (tofs t)

let rec s_term_to_dfs_string (t:s_term_t) =
  let tag = s_term_mcts#ts t in
  let optag = binop_mfts#ts in
  let par p = match p with ParFormal i -> "pf," ^ (string_of_int i) | ParGlobal s -> "pg," ^ s in
  let tdfs = s_term_to_dfs_string in
  let tofs = s_offset_to_dfs_string in
  let optdfs t = match t with Some t -> tdfs t | _ -> "none" in  
  match t with
  | ArgValue (p,soff) -> String.concat "," [ tag ; par p ; tofs soff ]
  | LocalVariable  s -> tag ^ "," ^ s
  | ReturnValue -> tag
  | NamedConstant s -> tag ^ "," ^ s
  | NumConstant n -> tag ^ "," ^ n#toString
  | IndexSize t
    | ByteSize t -> tag ^ "," ^ (tdfs t)
  | ArgAddressedValue (t,soff) -> String.concat "," [ tag ; tdfs t ; tofs soff ]
  | ArgNullTerminatorPos t -> tag ^ "," ^ (tdfs t)
  | ArgSizeOfType t -> tag ^ "," ^ (tdfs t)
  | ArithmeticExpr (op,t1,t2) -> String.concat "," [ tag ; optag op ; tdfs t1 ; tdfs t2 ]
  | FormattedOutputSize t -> tag ^ "," ^ (tdfs t)
  | Region t -> tag ^ "," ^ (tdfs t)
  | RuntimeValue -> tag
  | ChoiceValue (opt1,opt2) -> tag ^ "," ^ (optdfs opt1) ^ "," ^ (optdfs opt2)

let xpredicate_to_dfs_string (p:xpredicate_t) =
  let tag = xpredicate_mcts#ts p in
  let optag = binop_mfts#ts in
  let tdfs = s_term_to_dfs_string in
  let optdfs t = match t with Some t -> tdfs t | _ -> "none" in
  match p with
  | XFalse
    | XFunctional
    | XPreservesAllMemory
    | XPreservesNullTermination -> tag
  | XAllocationBase t
    | XConfined t
    | XConstTerm t
    | XControlledResource (_,t) 
    | XFormattedInput t
    | XFreed t
    | XGlobalAddress t
    | XHeapAddress t
    | XInitialized t
    | XInputFormatString t
    | XInvalidated t
    | XNotNull t
    | XNotZero t
    | XNonNegative t
    | XNull t
    | XNullTerminated t
    | XOutputFormatString t
    | XNewMemory t
    | XPreservesMemory t
    | XPreservesValue t
    | XPreservesValidity t
    | XRepositioned t
    | XStackAddress t
    | XUniquePointer t
    | XValidMem t -> tag ^ "," ^ (tdfs t)
  | XPolicyPre (t,pname,pstates) -> tag ^ "," ^ (tdfs t) ^ "," ^ pname
  | XPolicyValue (t,pname,None) -> tag ^ "," ^ (tdfs t) ^ "," ^ pname
  | XPolicyValue (t,pname,Some tname) ->
     tag ^ "," ^ (tdfs t) ^ "," ^ pname ^ "," ^ tname
  | XPolicyTransition (t,pname,ptrans) ->
     tag ^ "," ^ (tdfs t) ^ pname ^ "," ^ ptrans
  | XInitializedRange (t1,t2)
    | XBlockWrite (t1,t2)
    | XNoOverlap (t1,t2) 
    | XBuffer (t1,t2)
    | XRevBuffer (t1,t2) -> tag ^ "," ^ (tdfs t1) ^ "," ^ (tdfs t2)
  | XPreservesAllMemoryX l -> String.concat "," (tag::(List.map tdfs l))
  | XRelationalExpr (op,t1,t2) ->
     String.concat "," [ tag ; (optag op) ; (tdfs t1) ; (tdfs t2) ]
  | XTainted (t,optlb,optub) ->
     String.concat "," [ tag ; (tdfs t)  ; (optdfs optlb) ; (optdfs optub) ]

let rec simplify_sterm (t:s_term_t) =
  match t with
  | ArithmeticExpr (op, t1, t2) ->
     begin
       match (simplify_sterm t1, simplify_sterm t2) with
       | (NumConstant n1, NumConstant n2) ->
          begin
            match op with
            | PlusA ->  NumConstant (n1#add n2)
            | MinusA -> NumConstant (n1#sub n2)
            | Mult -> NumConstant (n1#mult n2)
            | Div -> NumConstant (n1#div n2)
            | _ -> t
          end
       | _ -> t
     end
  | _ -> t

let simplify_xpredicate (p:xpredicate_t) =
  match p with
  | XRelationalExpr (op,t1,t2) ->
     XRelationalExpr (op,simplify_sterm t1, simplify_sterm t2)
  | _ -> p

let rec read_xml_s_offset (node:xml_element_int):s_offset_t =
  let get = node#getAttribute in
  let hasc () = node#hasOneChild in
  let getc () = node#getChild in
  match node#getTag with
  | "no-offset" -> ArgNoOffset
  | "field" ->
     if hasc () then
       ArgFieldOffset (get "name", read_xml_s_offset (getc ()))
     else
       ArgFieldOffset (get "name", ArgNoOffset)
  | "index" ->
     if hasc () then
       ArgIndexOffset (mkNumericalFromString (get "i"), read_xml_s_offset (getc ()))
     else
       ArgIndexOffset (mkNumericalFromString (get "i"), ArgNoOffset)
  |  s ->  raise_error node 
                       (LBLOCK [ STR "read_xml_offset: " ; STR s ;
	                         STR " not recognized as offset tag" ])
    
      

let rec read_xml_term (node:xml_element_int) ?(lvars=[]) ?(gvars=[]) params : s_term_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let has_param name = List.exists (fun (n,_) -> n = name) params in
  let has_gvar name = List.mem name gvars in
  let has_lvar name = List.mem name lvars in
  let get_param name = 
    let (_,i) = (List.find (fun (n,_) -> n = name) params) in i in
  let get_constant txt =
    if is_macro_value txt then
      get_macro_value txt
    else
      try
        NumConstant (mkNumericalFromString txt)
      with
      | Failure _ ->
         raise_error
           node (LBLOCK [ STR "read_xml_term NumConstant with " ; STR txt ]) in
  match node#getTag with
  | "runtime-value" -> RuntimeValue
  | "ci" -> 
    let name = node#getText in
    if has_param name then 
      ArgValue (ParFormal (get_param name),ArgNoOffset)
    else if has_gvar name then
      ArgValue (ParGlobal name,ArgNoOffset)
    else if has_lvar name then
      LocalVariable name
    else
      get_macro_value name
  | "cn" -> get_constant node#getText
  | "choice" ->
     let lb = if has "lb" then Some (get_constant (get "lb")) else None in
     let ub = if has "ub" then Some (get_constant (get "ub")) else None in
     ChoiceValue (lb,ub)
  | "return" | "return-value" -> ReturnValue
  | "apply" -> 
    let (opnode,op,terms) = read_xml_apply ~gvars node#getChildren params in 
    begin
      match terms with
      | [ t ] ->
	begin
	  match op with
          | "addressed-value" ->
             if opnode#hasOneChild then
               ArgAddressedValue (t, read_xml_s_offset opnode#getChild)
             else
               ArgAddressedValue (t, ArgNoOffset)
	  | "index-size" -> IndexSize t
	  | "byte-size" -> ByteSize t
          | "formatted-output-size" -> FormattedOutputSize t
          | "region" -> Region t
	  | "nullterminator-pos" -> ArgNullTerminatorPos t
	  | "size-of-type" -> ArgSizeOfType t
	  | s -> raise_error node 
	    (LBLOCK [ STR "read_xml_term: " ; STR s ;
		      STR " not recognized as term function " ])
	end
      | [ t1 ; t2 ] ->
         begin
           try
             simplify_sterm (ArithmeticExpr (binop_from_mathml_string op,t1,t2))
           with
           | Invalid_argument s ->
              raise_error node
                          (LBLOCK [ STR "read_xml_term: " ; STR s ])
         end
      | _ -> raise_error node 
	(LBLOCK [ STR "read_xml_term with " ; INT (List.length terms) ;
		  STR " arguments" ])
    end
  | s -> raise_error node 
    (LBLOCK [ STR "read_xml_term: " ; STR s ;
	      STR " not recognized as term function" ])
    
and read_xml_apply (nodes:xml_element_int list)
?(lvars=[])
?(gvars=[]) params : (xml_element_int * string * s_term_t list) =
  (List.hd nodes, (List.hd nodes)#getTag,
   List.map (fun x -> read_xml_term x ~gvars params) (List.tl nodes))

let read_xml_instr
      (node:xml_element_int) ?(lvars=[]) params: contract_instr_t =
  let line = node#getIntAttribute "line" in
  let getc = node#getTaggedChild in
  let xapp = (getc "apply")#getChildren in
  let (n,op,terms) = read_xml_apply xapp ~lvars params in
  match terms with
  | [ t1 ; t2 ] ->
     begin
       match op with
       | "set" -> SetVar (line,t1,t2)
       | s ->
          raise_error
            (getc "apply")
            (LBLOCK [ STR "read_xml_instr: " ; STR s ;
                                STR  " not recognized as nullary predicate" ])
     end
  | _ ->
     raise_error
       (getc "apply")
       (LBLOCK [ STR "read_xml_pre_predicate: incorrect number of arguments " ; 
		 INT (List.length terms) ; STR " (2 expected)" ])

    
let read_xml_xpredicate (node:xml_element_int) ?(gvars=[]) params : xpredicate_t list =
  let getc = node#getTaggedChild in
  let xapp = (getc "apply")#getChildren in
  let (n,op,terms) = read_xml_apply xapp ~gvars params in
  let get = n#getAttribute in
  let has = n#hasNamedAttribute in
  let get_constant txt =
    if is_macro_value txt then
      get_macro_value txt
    else
      try
        NumConstant (mkNumericalFromString txt)
      with
      | Invalid_argument s ->
         raise_error
           node
           (LBLOCK [ STR "read_xml_term NumConstant with " ; STR txt ;
                     STR ": " ; STR s ])
      | Failure _ ->
         raise_error
           node
           (LBLOCK [ STR "read_xml_term NumConstant with " ; STR txt ]) in
  try
    begin
      match terms with
      | [] ->
         begin
           match op with
           | "false" -> [ XFalse ]
           | "functional" -> [ XFunctional ]
           | "preserves-all-memory" -> [ XPreservesAllMemory ]
           | "preserves-null-termination" -> [ XPreservesNullTermination ]
           | s -> raise_error (getc "apply")
                              (LBLOCK [ STR "read_xml_xpredicate: " ; STR s ;
                                        STR " not recognized as nullary predicate" ])
         end
      | [ t ] ->
         begin
	   match op with
	   | "allocation-base" -> [ XAllocationBase t ]
           | "const" -> [ XConstTerm t ]
           | "controlled-resource" ->
              if has "resource" then
                [ XControlledResource (get "resource", t) ]
              else
                [ XControlledResource ("memory", t) ]
           | "formatted-input" -> [ XFormattedInput t ]
           | "frees" -> [ XFreed t ]
           | "global-address" -> [ XGlobalAddress t ]
           | "heap-address" -> [ XHeapAddress t ]
           | "initializes" ->
              if has "field" then
                [ XInitialized (ArgAddressedValue
                                  (t,ArgFieldOffset (get "field",ArgNoOffset))) ]
              else if has "index" then
                [ XInitialized (
                      ArgAddressedValue
                        (t, ArgIndexOffset
                              (mkNumericalFromString (get "index"),
                               ArgNoOffset))) ]
              else
                [ XInitialized t  ]
           | "initialized" -> [ XInitialized t ]
           | "invalidates" -> [ XInvalidated t ]
           | "not-null" -> [ XNotNull t ]
           | "not-zero" -> [ XNotZero t ]
           | "non-negative" -> [ XNonNegative t ]
	   | "null" -> [ XNull t ]
           | "null-terminated" -> [ XNullTerminated t ]
	   | "format-string" ->
              if has "input" && (get "input") = "yes" then
                [ XInputFormatString t ]
              else 
                [ XOutputFormatString t ]
           | "preserves-validity" -> [ XPreservesValidity t ]
           | "preserves-memory" -> [ XPreservesMemory t ]
           | "preserves-all-memory-x" -> [ XPreservesAllMemoryX [ t ] ]
           | "preserves-value" -> [ XPreservesValue t ]
           | "repositions" -> [ XRepositioned t ]
           | "confined" | "confines" -> [ XConfined t ]
           | "tainted" ->
              let optlb =
                if has "lb" then Some (get_constant (get "lb")) else None in
              let optub =
                if has "ub" then Some (get_constant (get "ub")) else None in
              [ XTainted (t,optlb,optub) ]
           | "unique-pointer" -> [ XUniquePointer t ]
           | "new-memory" -> [ XNewMemory t ]
           | "stack-address" -> [ XStackAddress t ]
           | "valid-mem" -> [ XValidMem t ]
           | "policy-pre" ->
              let pname = get "policy" in
              let pstates = nsplit ',' (get "states") in
              [ XPolicyPre (t,pname,pstates) ]
           | "policy-value" ->
              let pname = get "policy" in
              let optname = if has "transition" then Some (get "transition") else None in
              [ XPolicyValue (t,pname,optname) ]
           | "policy-transition" ->
              [ XPolicyTransition (t,get "policy",get "transition") ]
	   | s -> raise_error (getc "apply") 
	                      (LBLOCK [ STR "read_xml_xpredicate: " ; STR s ; 
		                        STR " not recognized as a unary predicate" ])
         end
      | [ t1 ; t2 ] ->	
         begin
	   match op with
           | "initialized-range" | "initializes-range" -> [ XInitializedRange(t1,t2) ]
	   | "no-overlap" -> [ XNoOverlap (t1,t2) ]
           | "block-write" -> [ XBlockWrite (t1,t2) ]
           | "buffer" -> [ XBuffer(t1,t2) ]
           | "rev-buffer" -> [ XRevBuffer (t1,t2) ]
	   | "deref-read" -> [ XInitializedRange(t1,t2) ; XNotNull t1 ]
	   | "deref-read-null" -> [ XInitializedRange (t1,t2) ]
	   | "deref-write" -> [ XBuffer(t1,t2) ; XNotNull t1 ]
	   | "deref-write-null" -> [ XBuffer (t1,t2) ]
           | "preserves-all-memory-x" -> [ XPreservesAllMemoryX [ t1 ; t2 ] ]
	   | _ -> [ XRelationalExpr (binop_from_mathml_string op,t1,t2) ]
         end
      | _ ->
         match op with
         | "preserves-all-memory-x" -> [ XPreservesAllMemoryX terms ]
         | _ ->
            raise_error (getc "apply")
                        (LBLOCK [ STR "read_xml_xpredicate: incorrect number of arguments " ; 
		                  INT (List.length terms) ; STR " (1,2, or 3 expected)" ])
    end
  with
  | Invalid_argument s ->
     raise_error node (LBLOCK [ STR "read_xml_xpredicate invalid argument: " ; STR s ])

let relational_op_to_xml_string op =
  match op with
  | Eq -> "eq"
  | Le -> "leq"
  | Lt -> "lt"
  | Ge -> "geq"
  | Gt -> "gt"
  | Ne -> "neq"
  | _ ->
     raise (CCHFailure (LBLOCK [ STR "Not a relational operator: " ;
                                 STR (binop_to_print_string op ) ]))

let arithmetic_op_to_xml_string op =
  match op with
  | PlusA | PlusPI | IndexPI -> "plus"
  | MinusA | MinusPI | MinusPP -> "minus"
  | Mult -> "times"
  | Div -> "div"
  | _ ->
     raise (CCHFailure  (LBLOCK [ STR "Not an arithmetic operator: " ;
                                  STR  (binop_to_print_string op) ]))

let s_offset_to_xmlx tag o =
  let rec aux node offset =
    match offset with
    | ArgNoOffset -> ()
    | ArgFieldOffset (name,fo) ->
       let fnode = xmlElement "field" in
       begin
         aux fnode fo ;
         fnode#setAttribute "name" name ;
         node#appendChildren [ fnode ]
       end
    | ArgIndexOffset (n,io) ->
       let inode = xmlElement "index" in
       begin
         aux inode io ;
         inode#setAttribute "i"  n#toString ;
         node#appendChildren [ inode ]
       end in
  let node = xmlElement tag in
  begin
    aux node o ;
    node
  end

let api_parameter_to_xmlx params p o =
  let names = H.create 3 in
  let _ = List.iter (fun (name,index) -> H.add names index name) params in
  let get_name index =
    if H.mem names index then
      H.find names index
    else
      "arg_" ^ (string_of_int index) in
  match p with
  | ParFormal i -> xml_string "ci" (get_name i)
  | ParGlobal name -> xml_string "ci" name
  
let s_term_to_xmlx (params:(string * int) list) (t:s_term_t) =
  let rec apply_term tag terms =
    let aNode = xmlElement "apply" in
    begin aNode#appendChildren ((xmlElement tag) :: (List.map aux terms)) ; aNode end
  and aux (t:s_term_t) =
    match t with
    | ArgValue (p,o) -> api_parameter_to_xmlx params p o
    | LocalVariable s -> xml_string "ci" s
    | ReturnValue -> xmlElement "return"
    | NamedConstant s -> xml_string "ci" s
    | NumConstant n -> xml_string "cn" n#toString
    | IndexSize t -> apply_term "index-size" [ t ]
    | ByteSize t ->  apply_term "byte-size" [ t ]
    | ArgAddressedValue (t,o) ->
       let anode = xmlElement "apply" in
       let tagnode = s_offset_to_xmlx "addressed-value" o in
       begin
         anode#appendChildren [ tagnode ; aux t ] ;
         anode
       end
    |  ArgNullTerminatorPos t -> apply_term "nullterminator-pos" [ t ]
    | ArgSizeOfType t -> apply_term "size-of-type" [ t ]
    | ArithmeticExpr (op,t1,t2) ->
       apply_term (arithmetic_op_to_xml_string op) [ t1 ; t2 ]
    | FormattedOutputSize t -> apply_term "formatted-output-size" [ t ]
    | Region t -> apply_term "region" [ t ]
    | RuntimeValue -> xmlElement "runtime-value"
    | ChoiceValue  (opt1,opt2)  ->
       let tnode = xmlElement "choice" in
       begin
         (match opt1 with Some (NumConstant n) -> tnode#setAttribute "lb" n#toString | _ -> ()) ;
         (match opt2 with Some (NumConstant n) -> tnode#setAttribute "ub" n#toString | _ -> ()) ;
         tnode
       end in
  aux t

let get_xmlx_relational_expr
      (params:(string * int) list) (op:binop) (t1:s_term_t)  (t2:s_term_t) =
  let txml t = (s_term_to_xmlx params) t  in
  let apply_term tag terms =
    let aNode = xmlElement "apply" in
    begin aNode#appendChildren ((xmlElement tag) :: (List.map txml terms)) ; aNode end in
  apply_term (relational_op_to_xml_string op) [ t1 ; t2 ]
  
let write_xmlx_xpredicate (node:xml_element_int) (params:(string * int) list) (x:xpredicate_t) =
  let mNode = xmlElement "math" in
  let txml t = s_term_to_xmlx params t  in
  let apply_term tag terms =
    let aNode = xmlElement "apply" in
    begin aNode#appendChildren ((xmlElement tag) :: (List.map txml terms)) ; aNode end in
  let pnode =
    match x with
    | XAllocationBase t -> apply_term "allocation-base" [ t ]
    | XControlledResource (s,t) ->
       let anode = apply_term "controlled-resource" [ t ] in
       begin anode#setAttribute "resource" s ; anode end
    | XBlockWrite (t1,t2) -> apply_term "block-write" [ t1 ; t2 ]
    | XBuffer (t1,t2) -> apply_term "buffer" [ t1 ; t2 ]
    | XConfined t -> apply_term "confined" [ t ]
    | XConstTerm t -> apply_term "const" [ t ]
    | XFormattedInput t  -> apply_term "formatted-input" [ t ]
    | XFalse -> apply_term "false" []
    | XFreed t -> apply_term "frees" []
    | XFunctional -> apply_term "functional" []
    | XInitialized t -> apply_term "initialized" [ t ]
    | XInitializedRange  (t1,t2) -> apply_term "initialized-range" [ t1 ; t2 ]
    | XInputFormatString t ->
       let anode = apply_term "format-string"  [ t ] in
       begin anode#setAttribute "input" "yes" ;  anode end
    | XInvalidated t -> apply_term "invalidated" [ t ]
    | XNewMemory t -> apply_term "new-memory" [ t ]
    | XStackAddress t -> apply_term "stack-address" [ t ]
    | XHeapAddress t -> apply_term "heap-address"  [ t ]
    | XGlobalAddress t -> apply_term  "global-address" [ t ]
    | XNoOverlap (t1,t2) -> apply_term "no-overlap" [ t1 ; t2 ]
    | XNotNull t -> apply_term "not-null" [ t ]
    | XNull t -> apply_term "null" [ t ]
    | XNotZero t -> apply_term "not-zero" [ t ]
    | XNonNegative t -> apply_term "non-negative" [ t ]
    | XNullTerminated t -> apply_term "null-terminated" [ t ]
    | XOutputFormatString t -> apply_term "format-string" [ t ]
    | XPreservesAllMemory -> apply_term "preserves-all-memory" []
    | XPreservesAllMemoryX l -> apply_term "preserves-all-memory-x" l
    | XPreservesValue t -> apply_term "preserves-value" [ t ]
    | XPreservesValidity t -> apply_term "preserves-validity" [ t ]
    | XRepositioned t -> apply_term "repositioned" [ t ]
    | XRelationalExpr (op,t1,t2) -> get_xmlx_relational_expr params op t1 t2       
    | XPreservesNullTermination -> apply_term "preserves-null-termination" []
    | XRevBuffer (t1,t2) -> apply_term "rev-buffer" [ t1 ; t2 ]
    | XTainted (t1,lbopt,ubopt) ->
       let anode = apply_term "tainted" [ t1 ] in
       let set = anode#setAttribute in
       begin
         (match lbopt with Some (NumConstant n) -> set "lb" n#toString | _ -> ()) ;
         (match ubopt with Some (NumConstant n) -> set "ub" n#toString | _ -> ()) ;
         anode
       end
    | XUniquePointer t -> apply_term "unique-pointer" [ t ]
    | XValidMem t ->  apply_term "valid-mem" [ t ]
    | _ -> apply_term "nop"  [] in
  begin
    mNode#appendChildren [ pnode ] ;
    node#appendChildren [ mNode ]
  end
