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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
   
(* jchpre *)
open JCHApplication
open JCHPreAPI
open JCHPreSumTypeSerializer

module H = Hashtbl

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end

let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c -> if (Char.code c) < 32 || (Char.code c) > 126 then 
      found  := true) s in
  !found


let sanitize (s:string):string =
  if has_control_characters s then "__xx__" ^ (hex_string s) else s

(* Replace xml-objectional characters with standard replacement strings *)
let rec sanitize_pretty (p:pretty_t):pretty_t = 
  match p with
  | STR s -> STR (sanitize s)
  | LBLOCK l -> LBLOCK (List.map (fun p -> sanitize_pretty p) l)
  | INDENT (n,p) -> INDENT (n, sanitize_pretty p)
  | _ -> p


let dynamiccount = ref 0
let get_dynamiccount () = !dynamiccount

let loops = ref 0
let get_loop_count () = !loops

let methodsizecounts = H.create 3
let methodsize_no_pattern = H.create 3

let noteworthy =  H.create 3

let callpackages = H.create 3
let thispackages = H.create 3

let add_package t s =
  let entry = if H.mem t s then H.find t s else 0 in
  H.replace t s (entry + 1)

let get_call_packages () =  H.fold (fun k v a -> (k,v)::a) callpackages []
let get_this_packages () =  H.fold (fun k v a -> (k,v)::a) thispackages []
  
let get_noteworthy () =
  H.fold (fun k v a -> (k,v)::a) noteworthy []

let interesting = H.create 3

let get_interesting () =
  H.fold (fun k v a -> (k,v)::a) interesting []

let get_methodsize_count n =
  if H.mem methodsizecounts n then H.find methodsizecounts n else 0

let add_methodsize n =
  H.replace methodsizecounts n (1 + (get_methodsize_count n))

let get_methodsize_no_pattern_count n =
  if H.mem methodsize_no_pattern n then H.find methodsize_no_pattern n else 0
  
let add_methodsize_no_pattern n =
  H.replace methodsize_no_pattern n (1 + (get_methodsize_no_pattern_count n))

let rec bc_basic_value_to_pretty v =
  match v with
  | BcvIntConst n | BcvLongConst n | BcvByteConst n | BcvShortConst n -> n#toPretty ;
  | BcvFloatConst f | BcvDoubleConst f -> STR (Printf.sprintf "%f" f)
  | BcvArg n -> LBLOCK [ STR "arg-" ; INT n ]
  | BcvArrayElement (t,obj,index) ->
     LBLOCK [ STR "elem: " ; bc_object_value_to_pretty obj ; STR "[" ;
              bc_basic_value_to_pretty index ; STR "]" ]
  | BcvThisField (cn,fs) -> LBLOCK [ STR "field: " ; cn#toPretty ; STR "." ; fs#toPretty ]
  | BcvThatField (cn,fs,obj) ->
     LBLOCK [ STR "field:" ; bc_object_value_to_pretty obj ; STR "." ; fs#toPretty ]
  | BcvStaticField (cn,fs) ->
     LBLOCK [ STR "staticfield: " ; cn#toPretty ; STR "." ; fs#toPretty ]
  | BcvArrayLength obj -> LBLOCK [ STR "length: " ; bc_object_value_to_pretty obj ]
  | BcvInstanceOf (t,obj) ->
     LBLOCK [ STR "instanceof(" ; object_type_to_pretty t ; STR "): " ;
              bc_object_value_to_pretty obj]
  | BcvBinOpResult (opc,v1,v2) ->
     LBLOCK [ opcode_to_pretty opc ; STR ": " ; bc_basic_value_to_pretty v1 ; STR ", " ;
              bc_basic_value_to_pretty v2 ]
  | BcvUnOpResult (opc,v) ->
     LBLOCK [ opcode_to_pretty opc ; STR ": " ; bc_basic_value_to_pretty v ]
  | BcvQResult (opcs, vl, v1, v2) ->
     LBLOCK [ STR "Q" ; pretty_print_list opcs opcode_to_pretty "(" "," "): " ;
              pretty_print_list vl bc_value_to_pretty "[" "," "]: " ;
              bc_basic_value_to_pretty v1 ; STR "," ; bc_basic_value_to_pretty v2 ]
  | BcvConvert (opc,v) ->
     LBLOCK [ STR "convert(" ; opcode_to_pretty opc ; STR "): " ; bc_basic_value_to_pretty v ]
  | BcvCallRv c -> bc_call_to_pretty c
       
and bc_object_value_to_pretty v =
  let pvl l = pretty_print_list l bc_value_to_pretty "(" "," ")" in
  let pbvl l = pretty_print_list l bc_basic_value_to_pretty "(" "," ")" in
  match v with
  | BcoNull -> STR "null"
  | BcoArg n -> LBLOCK [ STR "arg-" ; INT n ]
  | BcoClassConst t -> LBLOCK [ STR "class: " ; object_type_to_pretty t ]
  | BcoNewObject (cn,vl) -> LBLOCK [ STR "new(" ; cn#toPretty ; STR ")" ; pvl vl ]
  | BcoNewArray (vt,v) ->
     LBLOCK [ STR "newarray(" ; value_type_to_pretty vt ; STR ") length:" ;
              bc_basic_value_to_pretty v ]
  | BcoMultiNewArray (ot,l) ->
     LBLOCK [ STR "newmultiarray(" ; object_type_to_pretty ot ; STR ")" ; pbvl l ]
  | BcoArrayElement (t,obj,index) ->
     LBLOCK [ STR "elem: " ; bc_object_value_to_pretty obj ; STR "[" ;
              bc_basic_value_to_pretty index ; STR "]" ]
  | BcoThisField (cn,fs) -> LBLOCK [ STR "field: " ; cn#toPretty ; STR "." ; fs#toPretty ]
  | BcoThatField (cn,fs,obj) ->
     LBLOCK [ STR "field:" ; bc_object_value_to_pretty obj ; STR "." ; fs#toPretty ]
  | BcoStaticField (cn,fs) ->
     LBLOCK [ STR "staticfield: " ; cn#toPretty ; STR "." ; fs#toPretty ]
  | BcoCheckCast (ot,v) -> LBLOCK [ STR "checkcast(" ; object_type_to_pretty ot ; STR "): " ;
                                    bc_object_value_to_pretty v ]
  | BcoStringConst s -> LBLOCK [ STR "str:'" ; STR s ; STR "'" ]
  | BcoQResult (opcs, vl, v1, v2) ->
     LBLOCK [ STR "Q" ; pretty_print_list opcs opcode_to_pretty "(" "," "): " ;
              pretty_print_list vl bc_value_to_pretty "[" "," "]: " ;
              bc_object_value_to_pretty v1 ; STR "," ; bc_object_value_to_pretty v2 ]
  | BcoCallRv c -> bc_call_to_pretty c
        
and bc_value_to_pretty v =
  match v with
  | BcBasic v -> bc_basic_value_to_pretty v
  | BcObject v -> bc_object_value_to_pretty v

and bc_call_to_pretty c =
  LBLOCK [ STR c.bcp_type ;
           (match c.bcp_base_object with
            | Some o -> LBLOCK [ STR " on(" ; bc_object_value_to_pretty o ; STR ")" ]
            | _ -> STR "") ;
           STR ":" ; STR c.bcp_ms#name ;
           pretty_print_list c.bcp_args bc_value_to_pretty "(" "," ")" ]

and bc_action_to_pretty a =
  match a with
  | BcNop -> STR "nop"
  | BcNopX -> STR "nopX"
  | BcInitObject -> STR "Object.<init>"
  | BcInitSuper -> STR "super.<init>"
  | BcNewObject (cn,args) ->
     LBLOCK [ STR "new " ; cn#toPretty ;
              pretty_print_list args bc_value_to_pretty "(" "," ")" ]
  | BcDropValues args ->
     LBLOCK [ STR "drop" ; pretty_print_list args bc_value_to_pretty "(" "," ")" ]
  | BcPutThisField (cn,fs,v) ->
     LBLOCK [ STR "put(" ; cn#toPretty ; STR ", " ; STR fs#name ; STR "): " ;
              bc_value_to_pretty v ]
  | BcPutThatField (cn,fs,obj,v) ->
     LBLOCK [ STR "put " ; bc_value_to_pretty v ; STR " (" ; cn#toPretty ;
              STR ", " ; STR fs#name ; STR "): " ; bc_value_to_pretty v ]
  | BcPutStaticField (cn,fs,v) ->
     LBLOCK [ STR "putstatic(" ; cn#toPretty ; STR ", " ; STR fs#name ; STR "): " ;
              bc_value_to_pretty v ]
  | BcArrayStore (t,obj,index,v) ->
     LBLOCK [ STR "arraystore(" ; bc_object_value_to_pretty obj ; STR "[" ;
              bc_basic_value_to_pretty index ; STR "]: " ; bc_value_to_pretty v ]
  | BcConditionalAction (opcs, vl, al1, al2) ->
     LBLOCK [ STR "Cond" ; pretty_print_list opcs opcode_to_pretty "[" "," "]" ;
              pretty_print_list vl bc_value_to_pretty "(" "," ")" ;
              pretty_print_list al1 bc_action_to_pretty " {" ", " "}" ;
              pretty_print_list al2 bc_action_to_pretty " {" ", " "}" ]
  | BcWrapCall c -> LBLOCK [ STR "wrap " ; bc_call_to_pretty c ]
  | BcThrow obj -> LBLOCK [ STR "throw " ; bc_object_value_to_pretty obj ]
                          
and bc_action_value_to_pretty a =
  match a with
  | BcaValue v -> bc_value_to_pretty v
  | BcaAction a -> bc_action_to_pretty a
  | BcaTest (_,v) -> pretty_print_list v bc_value_to_pretty "[" "," "]"
  | BcaRetGoto p -> opcode_to_pretty p
  | BcaActions aa -> pretty_print_list aa bc_action_to_pretty "[" "," "]"
  | BcaOpcodes oo -> pretty_print_list oo opcode_to_pretty "[" ","  "]"
  | BcaRvActions (aa,rv) ->
     LBLOCK [ pretty_print_list aa bc_action_to_pretty "[" "," "]" ;
              bc_value_to_pretty rv ]

and bc_pattern_to_pretty p =
  let paa l = LBLOCK (List.map (fun a -> LBLOCK [ bc_action_to_pretty a ; NL ]) l) in
  match p with
  | BcpNop -> STR "nop"
  | BcpNopX -> STR "nopX"
  | BcpAction l -> LBLOCK [ STR "Action:" ; NL ; INDENT (3, paa l) ]
  | BcpResult (l,v) ->
     LBLOCK [ STR "Result:" ; NL ; INDENT (3, paa l) ; NL ; INDENT (3,bc_value_to_pretty v) ]
  | BcpThrow (l,v) ->
     LBLOCK [ STR "Throw:" ; NL ; INDENT (3, paa l) ; NL ; INDENT (3, bc_object_value_to_pretty v) ]
  | BcpResultExcept (cn,l,v1,v2) ->
     LBLOCK [ STR "Result-except: " ; cn#toPretty ; NL ; INDENT (3, paa l) ; NL ;
              INDENT (3, bc_value_to_pretty v1) ; NL ; INDENT (3, bc_value_to_pretty v2) ]
  | BcpResultExceptThrow (cn,l,v1,v2) ->
     LBLOCK [ STR "Result-except-throw: " ; cn#toPretty ; NL ; INDENT (3, paa l) ; NL ;
              INDENT (3, bc_value_to_pretty v1) ; NL ; INDENT (3, bc_object_value_to_pretty v2) ]
  | BcpActionExcept (cn,l) ->
     LBLOCK [ STR "Action-except: " ; cn#toPretty ; NL ; INDENT (3, paa l) ]
  | BcpActionExceptThrow (cn,l,v) ->
     LBLOCK [ STR "Action-except-throw: " ; cn#toPretty ; NL ; INDENT (3, paa l) ;
              INDENT (3, bc_object_value_to_pretty v) ]
  | BcpInfiniteLoop l -> LBLOCK [ STR "InfiniteLoop: " ; paa l ]
  | BcpIllegalSeq (s,_) -> LBLOCK [ STR "Illegal: " ; STR s ]
     

let is_object_test (opc:opcode_t) =
  match opc with
  | OpIfNull _ | OpIfNonNull _ | OpIfCmpAEq _ | OpIfCmpANe _ -> true
  | _ -> false

let is_scalar_test (opc:opcode_t) =
  is_test_opcode opc && (not (is_object_test opc))

let rec basic_value_size v =
  (match v with
   | BcvArrayElement (_,base,index) -> (object_value_size base) + (basic_value_size index)
   | BcvThatField (_,_,v) -> (object_value_size v)
   | BcvArrayLength v ->  (object_value_size v)
   | BcvInstanceOf (_,v) -> (object_value_size v)
   | BcvBinOpResult (_,v1,v2) -> (basic_value_size v1) + (basic_value_size v2)
   | BcvUnOpResult (_,v) -> (basic_value_size v)
   | BcvQResult (_,tvl,v1,v2) -> (sum_values_size tvl)  + (basic_value_size v1)
                                + (basic_value_size v2)
   | BcvConvert (_,v) -> basic_value_size v
   | BcvCallRv c -> call_size c
   | _ -> 0) + 1

and object_value_size v =
  (match v with
   | BcoNewObject (_,vl) -> sum_values_size vl
   | BcoNewArray (_,v) -> basic_value_size v
   | BcoMultiNewArray (_,vl) -> sum_basic_values_size vl
   | BcoArrayElement (_,base,index) -> (object_value_size base) + (basic_value_size index)
   | BcoThatField (_,_,base) -> object_value_size base
   | BcoCheckCast (_,v) -> object_value_size v
   | BcoQResult (_,tvl,v1,v2) -> (sum_values_size tvl) + (object_value_size v1) + (object_value_size v2)
   | BcoCallRv c -> call_size c
   | _ -> 0) + 1

and value_size v =
  match v with
  | BcBasic b -> basic_value_size b
  | BcObject o -> object_value_size o

and call_size c =
  1 + (match c.bcp_base_object with Some v -> (object_value_size v) | _ -> 0)
  + (sum_values_size c.bcp_args)

and action_size a =
  match a with
  | BcNewObject (_,vl) -> sum_values_size vl
  | BcDropValues  vl ->  sum_values_size vl
  | BcPutThisField (_,_,v) -> value_size v
  | BcPutThatField (_,_,base,v) -> (object_value_size base) + (value_size v)
  | BcPutStaticField (_,_,v) -> value_size v
  | BcArrayStore (_,base,index,v) -> (object_value_size base) + (basic_value_size index) + (value_size v)
  | BcConditionalAction (_,tvl,al1,al2) ->
     (sum_values_size tvl) + (sum_actions_size al1) + (sum_actions_size al2)
  | BcWrapCall c -> call_size c
  | BcThrow v -> object_value_size v
  | _ -> 0

and pattern_size p =
  match p with
  | BcpAction al -> sum_actions_size al
  | BcpActionExcept (_,al) -> sum_actions_size al
  | BcpActionExceptThrow (_,al,v) -> (sum_actions_size al) + (object_value_size v)
  | BcpResult (al,v) -> (sum_actions_size al) + (value_size v)
  | BcpThrow (al,v) -> (sum_actions_size al) + (object_value_size v)
  | BcpResultExceptThrow (_,al,v1,v2) ->
     (sum_actions_size al) + (value_size v1) + (object_value_size v2)
  | BcpResultExcept (_,al,v1,v2) -> (sum_actions_size al) + (value_size v1) + (value_size v2)
  | BcpInfiniteLoop al -> sum_actions_size al
  | _ -> 0

and sum_values_size (l:bc_value_t list) =
  List.fold_left (fun acc v -> acc + (value_size v)) 0 l

and sum_actions_size (l:bc_action_t list) =
  List.fold_left (fun acc a -> acc + (action_size a)) 0 l

and sum_basic_values_size (l:bc_basicvalue_t list) =
  List.fold_left (fun acc v -> acc + (basic_value_size v)) 0 l

let is_backward_move (opc:opcode_t) =
  match opc with
  | OpGoto n -> n < 0
  | _ -> is_backward_test_opcode opc

let get_pattern
      ?(maxlog=5)
      ?(maxmatch=20)
      (jar:string)
      (mInfo:method_info_int)
      (cInfo:class_info_int):bc_pattern_t option =
  let cms = mInfo#get_class_method_signature in
  let thiscn = cInfo#get_class_name in
  let thispackage = thiscn#package_name in
  let _ = add_package thispackages thispackage in
  let opcodes = mInfo#get_bytecode#get_code in
  let _ = add_methodsize opcodes#instr_count in
  let get_instrs () =
    let lst = ref [] in
    let _ = opcodes#iteri (fun _ opc -> lst := opc :: !lst) in
    let dyncount = List.fold_left (fun acc opc ->
                       match opc with OpInvokeDynamic _ -> acc+1 | _ -> acc) 0 !lst in
    let _ = if dyncount > 0 then dynamiccount := !dynamiccount + dyncount in
    let _ = if List.exists is_backward_move !lst then loops := !loops + 1 in
    List.rev !lst in
  let instrs = get_instrs () in
  let _ =
    List.iter (fun opc ->
        match opc with
        | OpInvokeVirtual (TClass cn,_)
          | OpInvokeSpecial (cn,_)
          | OpInvokeStatic (cn,_)
          | OpInvokeInterface (cn,_) ->
           if cn#equal thiscn then
             add_package callpackages "thisclass"
           else
             add_package callpackages cn#package_name
        | _ -> ()) instrs in
  let intarg i = BcvIntConst (mkNumericalFromInt32 i) in
  let bytearg i = BcvByteConst (mkNumerical i) in
  let longarg i = BcvLongConst (mkNumericalFromInt64 i) in
  let shortarg i = BcvShortConst (mkNumerical i) in
  let doublearg f = BcvDoubleConst f in
  let floatarg f = BcvFloatConst f in

  let errormsg s l = LBLOCK [ STR "Error in " ; STR s ; STR " (" ; STR jar ; STR "): " ;
                              pretty_print_list l opcode_to_pretty "[" "," "]" ] in

  let add_noteworthy (msg:string) =
    let entry = if H.mem noteworthy msg then H.find noteworthy msg else [] in
    H.replace noteworthy msg ((jar,mInfo)::entry) in

  let add_interesting (msg:string) (p:pretty_t) =
    let entry = if H.mem interesting msg then H.find interesting msg else [] in
    H.replace interesting msg ((jar,p)::entry) in

  let errormsgp s l v =
    LBLOCK [ STR "Error in " ; STR s ; STR ": " ;
             pretty_print_list l opcode_to_pretty "[" "," "]" ;
             STR " (" ; pretty_print_list v bc_action_value_to_pretty "[" "," "]" ; STR ")" ] in

  let rec mklist n p =
    let rec aux k result =
      if k > 0 then p :: (aux (k-1) result) else result in
    aux n [] in

  let splitargs l =
    let rec aux l result =
      match l with
      | [] -> raise (JCH_failure (STR "splitargs"))
      | [ e ] -> (List.rev result, e)
      | h::tl -> aux tl (h::result) in
    aux l [] in

  let is_basic_java_type (t:java_basic_type_t) =
    match t with Object -> false | _ -> true in

  let is_basic_fs (fs:field_signature_int) =
    match fs#descriptor with TBasic _ -> true | _ -> false in
  let is_object_fs (fs:field_signature_int) =
    match fs#descriptor with TObject _ -> true | _ -> false in

  let has_one_exception_caught = match mInfo#get_exceptions_caught with
    | [ cn ] -> true | _ -> false in

  let get_exception_handled () =
    match mInfo#get_exceptions_caught with
    | [ cn ] -> cn
    | _ -> raise (JCH_failure (STR "exceptions caught")) in

  (*
   * <pattern>   ::= <action>* 'return'                                    # action
   *              |  <action>* <value> 'return'                            # result
   *              |  <action>* <objectref> 'throw'                         # throw
   *              |  <value> [ <value> ] <test-op> <action*> 'return'      # conditional-action
   *              |  <action>* <value> 'return' ('store' | 'pop') <value> 'return'   # try-except
   * <value>     ::= <objectref> | <scalar>
   * <scalar>    ::= <scalar-constant> 
   *              | 'getstatic'
   *              |  <objectref> 'getfield'
   *              |  <objectref> 'arraylength'
   *              |  <objectref> <scalar> 'arrayload'
   *              |  <value> 'instanceof'
   *              |  <value>* 'invokestatic'
   *              |  <objectref> <value>* <objectinvoke>
   *              |  <scalar> <converter>
   *              |  <scalar> <scalar> <binaryop>
   *              |  <scalar> <unaryop>
   *              |  <value> [ <value> ] <test-op> <scalar> 'goto' <scalar>
   * <objectref> ::= 'string-constant'
   *              |  'class-constant'
   *              |  'null'
   *              |  'getstatic'
   *              |  'new' 'dup' <value>* 'invokespecial-init'
   *              |  <objectref> 'getfield'
   *              |  <scalar> 'newarray'
   *              |  <objectref> 'checkcast'
   *              |  <objectref> <scalar> 'arrayload'
   *              |  <value>* 'invokestatic'
   *              |  <objectref> <value*> <objectinvoke>
   *              |  <value> [ <value> ] <test-op> <objectref> 'goto' <objectref>
   * <action>    ::= <value> ( 'pop' | 'pop2' )
   *              |  <value> 'putstatic'
   *              |  <objectref> <value> 'putfield'
   *              |  <objectref> <scalar> <value> 'arraystore'
   *              |  <value>* 'invokestatic'
   *              |  <objectref> <value>* <objectinvoke>
   *
   * <objectinvoke> ::= 'invokespecial | invokevirtual | invokeinterface
   * <binaryop>     ::= 'add' | 'sub' | 'mult' | 'div' | 'rem' 
   *                 | 'shl' | 'shr' | 'and' | 'or' | 'xor'
   * <unaryop>      ::= 'neg'
   * <converter>    ::= 'i2f' | 'i2d' | 'l2i' | 'l2f' | 'l2d' | 'f2i' | 'f2l'
   *                 |  'f2d' | 'd2i' | 'd2l' | 'd2f' | 'i2b' | 'i2c' | 'i2s'
   *)
  
  let rec is_basic_value_opc xregs opc =    (* xregs: registers not to be used *)
    match opc with
    | OpLoad (t,n) ->
       (match t with Object -> false | _ -> not (List.mem n xregs))
    | OpIntConst _
      | OpLongConst _
      | OpByteConst _
      | OpShortConst _
      | OpFloatConst _
      | OpDoubleConst _ -> true
    | OpGetStatic (_,fs) -> is_basic_fs fs
    | OpInvokeStatic (_,ms) -> ms#has_basic_return_value && ms#argcount = 0
    | _ -> false 

  and get_basic_value_opc xregs (opc:opcode_t) =
    match opc with
    | OpLoad (t,n) when (match t with Object -> false | _ -> true) -> BcvArg n
    | OpIntConst i -> intarg i
    | OpLongConst i -> longarg i
    | OpByteConst i -> bytearg i
    | OpShortConst i -> shortarg i
    | OpDoubleConst d -> doublearg d
    | OpFloatConst f -> floatarg f
    | OpGetStatic (cn,fs) when is_basic_fs fs -> BcvStaticField (cn,fs)
    | OpInvokeStatic (cn,ms) when ms#has_basic_return_value && ms#argcount = 0 ->
       BcvCallRv (mkstaticcall cn ms [])
    | _ -> raise (JCH_failure (errormsg "get_basic_value_opc" [ opc ]))

  and is_object_value_opc xregs opc =      (* xregs: registers not to be used *)
    match opc with
    | OpAConstNull -> true
    | OpLoad (Object,n) -> not (List.mem n xregs)
    | OpClassConst _
      | OpStringConst _ -> true
    | OpGetStatic (_,fs) -> is_object_fs fs
    | OpInvokeStatic (_,ms) -> ms#has_object_return_value && ms#argcount = 0
    | _ -> false

  and get_object_value_opc xregs (opc:opcode_t) =
    match opc with
    | OpAConstNull -> BcoNull
    | OpLoad (Object,n) -> BcoArg n
    | OpClassConst t -> BcoClassConst t
    | OpStringConst s -> BcoStringConst s
    | OpGetStatic (cn,fs) when is_object_fs fs -> BcoStaticField (cn,fs)
    | OpInvokeStatic (cn,ms) when ms#has_object_return_value && ms#argcount = 0
      -> BcoCallRv (mkstaticcall cn ms [])
    | _ -> raise (JCH_failure (errormsg "get_object_value_opc" [ opc ]))

  and is_value_opc xregs opc =
    is_basic_value_opc xregs opc || is_object_value_opc xregs opc

  and get_value_opc xregs (opc:opcode_t) =
    if is_basic_value_opc xregs opc then
      BcBasic (get_basic_value_opc xregs opc)
    else if is_object_value_opc xregs opc then
      BcObject (get_object_value_opc xregs opc)
    else
      raise (JCH_failure (errormsg "get_value_opc" [ opc ]))

  and is_action_opc opc =
    match opc with
    | OpInvokeStatic (_,ms) -> (not ms#has_return_value) && ms#argcount = 0
    | _ -> false

  and get_action_opc (opc:opcode_t) =
    match opc with
    | OpInvokeStatic (cn,ms) when (not ms#has_return_value) && ms#argcount = 0 ->
       BcWrapCall (mkstaticcall cn ms [])
    | _ -> raise (JCH_failure (errormsg "get_action_opc" [ opc ]))

  and is_basic_value xregs (l:opcode_t list) =
    match l with
    | [] -> false
    | [ opc ] -> is_basic_value_opc xregs opc
    | _ ->
       let (args,opc) = splitargs l in
       match opc with
       | OpGetField (_,fs) -> is_basic_fs fs && is_object_value xregs args
       | OpArrayLength -> is_object_value xregs args
       | OpInstanceOf _ -> is_value xregs args
       | OpNeg _ -> is_basic_value xregs args
       | OpArrayLoad t when is_basic_java_type t -> has_object_basic_partition xregs args
       | OpInvokeStatic (_,ms) -> ms#has_basic_return_value && has_values_partition xregs args ms#argcount
       | OpInvokeSpecial (_,ms) | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms) ->
          ms#has_basic_return_value && has_object_values_partition xregs args ms#argcount
       | _ when is_converter_opcode opc -> is_basic_value xregs args
       | _ when is_binop_opcode opc -> has_basic_basic_partition xregs args
       | _ -> false

  and get_basic_value xregs (l:opcode_t list) =
    match l with
    | [] -> raise (JCH_failure (STR "get_basic_value:empty"))
    | [ opc ] -> get_basic_value_opc xregs opc
    | [ OpLoad (Object,0) ; OpGetField (cn,fs) ] when is_basic_fs fs -> BcvThisField (cn,fs)
    | _ ->
       let (args,opc) = splitargs l in
       match opc with
       | OpGetField (cn,fs) when is_basic_fs fs && is_object_value xregs args ->
          BcvThatField (cn,fs,get_object_value xregs args)
       | OpArrayLength when is_object_value xregs args ->
          BcvArrayLength (get_object_value xregs args)
       | OpInstanceOf t when is_object_value xregs args ->
          BcvInstanceOf (t,get_object_value xregs args)
       | OpNeg _ when is_basic_value xregs args ->
          BcvUnOpResult (opc, get_basic_value xregs args)
       | OpArrayLoad t when is_basic_java_type t && has_object_basic_partition xregs args ->
          let (base,index) = get_object_basic_partition xregs args in
          BcvArrayElement (t,base,index)
       | OpInvokeStatic (cn,ms)
            when ms#has_basic_return_value && has_values_partition xregs args ms#argcount ->
          BcvCallRv (mkstaticcall cn ms (get_values_partition xregs args ms#argcount))
       | OpInvokeSpecial (_,ms) | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms)
            when ms#has_basic_return_value && has_object_values_partition xregs args ms#argcount ->
          let (base,methodargs) = get_object_values_partition xregs args ms#argcount in
          BcvCallRv (mkobjectcall base opc methodargs)
       | _ when is_converter_opcode opc && is_basic_value xregs args ->
          BcvConvert (opc,get_basic_value xregs args)
       | _ when is_binop_opcode opc && has_basic_basic_partition xregs args ->
          let (arg1,arg2) = get_basic_basic_partition xregs args in
          BcvBinOpResult (opc,arg1,arg2)
       | _ ->
          raise (JCH_failure (errormsg "get_basic_value" l))

  and is_initializer (cn:class_name_int) xregs (l:opcode_t list) =
    match List.rev l with
    | OpInvokeSpecial (icn,ms) :: revargs ->
       ms#name = "<init>" && icn#equal cn
       && has_values_partition xregs (List.rev revargs) ms#argcount
    | _ -> false

  and is_newobject xregs (l:opcode_t list) =
    ((List.length l ) >= 3)
    && (match l with
        | (OpNew cn) :: OpDup :: inits -> is_initializer cn xregs inits
        | _ -> false)

  and is_object_value xregs (l:opcode_t list) =
    (is_newobject xregs l)
    || (match l with [ opc ] -> is_object_value_opc xregs opc | _ -> false)
    || (((List.length l) >= 2)
        && (let (args,opc) = splitargs l in
            match opc with
            | OpGetField (_,fs) -> is_object_fs fs && is_object_value xregs args
            | OpNewArray _ -> is_basic_value xregs args
            | OpAMultiNewArray (_,dims) -> has_basic_partition_n xregs args dims
            | OpCheckCast _ -> is_object_value xregs args
            | OpArrayLoad Object -> has_object_basic_partition xregs args
            | OpInvokeStatic (_,ms) ->
               ms#has_object_return_value && has_values_partition xregs args ms#argcount
            | OpInvokeSpecial (_,ms) | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms) ->
               ms#has_object_return_value && has_object_values_partition xregs args ms#argcount
            | _ -> false))

  and get_initializer (cn:class_name_int) xregs (l:opcode_t list) =
    match List.rev l with
    | OpInvokeSpecial (icn,ms) :: revargs
         when ms#name = "<init>" && cn#equal icn
              && has_values_partition xregs (List.rev revargs) ms#argcount ->
       BcoNewObject (cn, get_values_partition xregs (List.rev revargs) ms#argcount)
    | _ ->
       raise (JCH_failure (errormsg "get_initializer" l))

  and get_newobject xregs (l:opcode_t list) =
    if (List.length l ) >= 3 then
      match l with
      | (OpNew cn) :: OpDup :: inits -> get_initializer cn xregs inits
      | _ -> raise (JCH_failure (errormsg "get_newobject" l))
    else
      raise (JCH_failure (errormsg "get_newobject" l))

  and get_object_value xregs (l:opcode_t list) =
    if is_newobject xregs l then
      get_newobject xregs l
    else
      match l with
      | [] -> raise (JCH_failure (STR "get_object_value:empty"))
      | [ opc ] when is_object_value_opc xregs opc -> get_object_value_opc xregs opc
      | [ OpLoad (Object,0) ; OpGetField (cn,fs) ] when is_object_fs fs ->
         BcoThisField (cn,fs)
      | _ ->
         let (args,opc) = splitargs l in
         match opc with
         | OpGetField (cn,fs) when is_object_fs fs && is_object_value xregs args ->
            BcoThatField (cn,fs,get_object_value xregs args)
         | OpNewArray t when is_basic_value xregs args ->
            BcoNewArray (t,get_basic_value xregs args)
         | OpAMultiNewArray  (t,dims) when has_basic_partition_n xregs args dims ->
            BcoMultiNewArray (t,get_basic_partition_n xregs args dims)
         | OpCheckCast t when is_object_value xregs args ->
            BcoCheckCast (t,get_object_value xregs args)
         | OpArrayLoad Object when has_object_basic_partition xregs args ->
            let (base,index) = get_object_basic_partition xregs args in
            BcoArrayElement (Object, base, index)
         | OpInvokeStatic (cn,ms)
              when ms#has_object_return_value
                   && has_values_partition xregs args ms#argcount ->
            BcoCallRv (mkstaticcall cn ms (get_values_partition xregs args ms#argcount))
         | OpInvokeSpecial (_,ms) | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms)
              when ms#has_object_return_value
                   && has_object_values_partition xregs  args ms#argcount ->
            let (base,methodargs) = get_object_values_partition xregs args ms#argcount in
            BcoCallRv (mkobjectcall base opc methodargs)
         | _ ->
            raise (JCH_failure (errormsg "get_object_value" l))

  and is_value xregs (l:opcode_t list) =
    is_basic_value xregs l || is_object_value xregs l

  and get_value xregs (l:opcode_t list) =
    if is_basic_value xregs l then
      BcBasic (get_basic_value xregs l)
    else if is_object_value  xregs l then
      BcObject (get_object_value xregs l)
    else
      raise (JCH_failure (errormsg "get_value" l))

  and is_action xregs (l:opcode_t list) =
    match l with
    | [] -> false
    | [ opc ] -> is_action_opc opc
    | _ ->
       let (args,opc) = splitargs l in
       match opc with
       | OpPop | OpPop2 -> is_value xregs args
       | OpPutStatic _ -> is_value xregs args
       | OpPutField _ -> has_object_value_partition xregs args
       | OpArrayStore _ -> has_object_basic_value_partition xregs args
       | OpInvokeStatic (_,ms) -> (not ms#has_return_value) && has_values_partition xregs args ms#argcount
       | OpInvokeSpecial (_,ms) | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms) ->
          (not ms#has_return_value) && has_object_values_partition xregs args ms#argcount
       | _ -> false

  and get_action xregs (l:opcode_t list) =
    match l with
    | [] -> raise (JCH_failure (STR "get_action:empty"))
    | [ opc ] -> get_action_opc opc
    | [ OpLoad (_,0) ; OpInvokeSpecial (cn,ms) ]
         when cn#name = "java.lang.Object" && ms#name = "<init>"
              && ms#argcount = 0->
       BcInitObject
    | [ OpLoad (_,0) ; OpInvokeSpecial (cn,ms) ]
         when cInfo#has_super_class && cn#equal cInfo#get_super_class
              && ms#name = "<init>" && ms#argcount = 0 ->
       BcInitSuper
    | _ ->
       let (args,opc) = splitargs l in
       match opc with
       | OpPutField (cn,fs) when has_object_value_partition xregs args ->
          let (base,value) = get_object_value_partition xregs args in
          (match args with
           | (OpLoad (Object,0))::_ -> BcPutThisField (cn,fs,value)
           | _ -> BcPutThatField (cn,fs,base,value))
       | OpPop | OpPop2 when is_value xregs args -> BcDropValues [ get_value xregs args]
       | OpPutStatic (cn,fs) when is_value xregs args -> BcPutStaticField (cn,fs,get_value xregs args)
       | OpArrayStore t when has_object_basic_value_partition xregs args ->
          let (base,index,value) = get_object_basic_value_partition xregs args in
          BcArrayStore (t, base, index, value)
       | OpInvokeStatic (cn,ms)
            when (not ms#has_return_value) && has_values_partition xregs args ms#argcount ->
          BcWrapCall (mkstaticcall cn ms (get_values_partition xregs args ms#argcount))
       | OpInvokeSpecial (_,ms) | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms)
            when (not ms#has_return_value) && has_object_values_partition xregs args ms#argcount ->
          let (base,methodargs) = get_object_values_partition xregs args ms#argcount in
          BcWrapCall (mkobjectcall base opc methodargs)
       | _ ->
          raise (JCH_failure (errormsg "get_action" l))

  and has_partition_n xregs (l:opcode_t list) (pl:(int list -> opcode_t list -> bool) list) =
    let rec aux l2 revl revps =
      match (revl,revps) with
      | (h::tl,p::ptl) ->
         (p xregs l2 && has_partition_n xregs (List.rev revl) (List.rev ptl))
         || aux (h::l2) tl revps
      | _ -> false in
    match pl with
    | [ p ] -> p xregs l
    | _ ->
       match (List.rev l, List.rev pl) with
       | ([],[]) -> true
       | ([],_) -> false
       | (_,[]) -> false
       | (h::tl,revps) -> aux [ h ] tl revps

  and get_partition_n
(xregs:int list)
(l:opcode_t list)
(pgl:((int list -> opcode_t list -> bool) * ((int list -> opcode_t list -> 'a))) list) =
    let rec aux l2 revl revps =
      match (revl,revps) with
      | (h::tl,(p,g)::pgtl)
           when (p xregs l2)
                && (has_partition_n xregs (List.rev revl) (List.rev (List.map fst pgtl))) ->
         (get_partition_n xregs (List.rev revl) (List.rev pgtl)) @ [ g xregs l2 ]
      | (h::tl,_) -> aux (h::l2) tl revps
      | _ -> raise (JCH_failure (errormsg "get_partition_n" l)) in
    match pgl with
    | [ (p,g) ] when p xregs l -> [ g xregs l ]
    | _ ->
       match (List.rev l, List.rev pgl) with
       | ([],[]) -> []
       | ([],_) -> raise (JCH_failure (errormsg "get_partition:empty-opcode-list" l))
       | (_,[]) -> raise (JCH_failure (errormsg "get_partition:empty-predicate-list" l))
       | (h::tl,revps) -> aux [ h ] tl revps                        

  and has_partition
    (xregs:int list)
    (l:opcode_t list)
    (p:(int list -> opcode_t list -> bool)) =
    let rec aux l2 revl =
      match revl with
      | h::tl ->
         (p xregs l2 && has_partition xregs (List.rev revl) p)
         || aux (h::l2) tl
      | _ -> false in
    (p xregs l) ||
      match List.rev l with
      | [] -> true
      | h::tl -> aux [ h ] tl

  and get_partition
    (xregs:int list)
    (l:opcode_t list)
    (p:(int list -> opcode_t list -> bool))
    (g:(int list -> opcode_t list -> 'a)) =
    let rec aux l2 revl =
      match revl with
      | h::tl when (p xregs l2) && (has_partition xregs (List.rev revl) p) ->
         (get_partition xregs (List.rev revl) p g) @ [ g xregs l2 ]
      | h::tl -> aux (h::l2) tl
      | _ -> raise (JCH_failure (errormsg "get_partition" l)) in
    if p xregs l then
      [ g xregs l ]
    else
      match List.rev l with
      | [] -> []
      | h::tl -> aux [ h ] tl

  and is_qop_test xregs (l:opcode_t list) =
    match List.rev l  with
    | h::revtl ->
       if is_test_opcode h then
         let tl = List.rev revtl in
         if is_scalar_test h then
           (is_forward_unary_test_opcode h && is_basic_value xregs tl)
           || (is_forward_binary_test_opcode h  && has_basic_basic_partition xregs tl)
           || (is_forward_unary_test_opcode h &&
                 (match revtl with
                  | hh::revvtl ->
                     let ttl = List.rev revvtl in
                     is_comparison_opcode hh && has_basic_basic_partition xregs ttl
                  | _ -> false))
         else if is_object_test h then
           (is_forward_unary_test_opcode h && is_object_value xregs tl)
           || (is_forward_binary_test_opcode h && has_object_object_partition xregs tl)
         else
           false
       else
         false
    |  _ -> false

  and get_qop_test xregs (l:opcode_t list) =
    match List.rev l with
    | h::revtl ->
       if is_test_opcode h then
         let tl = List.rev revtl in
         if is_forward_unary_test_opcode h then
           if is_scalar_test h then
             if is_basic_value xregs tl then
               BcaTest ([h],[ get_value xregs tl ])
             else
               (match revtl with
                | hh::revvtl when is_comparison_opcode hh ->
                   let ttl = List.rev revvtl in
                   if has_basic_basic_partition xregs ttl then
                     let (v1,v2) = get_value_value_partition xregs ttl in
                     BcaTest ([hh; h], [ v1 ; v2 ])
                   else
                     raise (JCH_failure (errormsg "get_qop_test:basic-comparison" l))
                | _ ->
                   raise (JCH_failure (errormsg "get_qop_test:basic" l)))
           else if is_object_test h then
             if is_object_value xregs tl then
               BcaTest ([h], [get_value xregs tl])
             else
               raise (JCH_failure (errormsg "get_qop_test:object" l))
           else
             raise (JCH_failure (errormsg "get_qop_test" l))
         else if is_forward_binary_test_opcode h then
           if is_scalar_test h then
             if has_basic_basic_partition xregs tl then
               let (v1,v2) = get_value_value_partition xregs tl in
               BcaTest ([h], [ v1 ; v2 ])
             else
               raise (JCH_failure (errormsg "get_qop_test:basic" l))
           else if is_object_test h then
             if has_object_object_partition xregs tl then
               let (v1,v2) = get_value_value_partition xregs tl in
               BcaTest ([h], [ v1 ; v2 ])
             else
               raise (JCH_failure (errormsg "get_qop_test:object" l))
           else
             raise (JCH_failure (errormsg "get_qop_test" l))
         else
           raise (JCH_failure (errormsg "get_qop_test" l))
       else
         raise (JCH_failure (errormsg "get_qop_test" l))
    | _ -> raise (JCH_failure (errormsg "get_qop_test" l))

  and isget_qop_test = (is_qop_test, get_qop_test)
               
  and isget_object_value =
    (is_object_value, fun xregs l -> BcaValue (BcObject (get_object_value xregs l)))
  and isget_basic_value =
    (is_basic_value, fun xregs l -> BcaValue (BcBasic (get_basic_value xregs l)))
  and isget_value  =
    (is_value, fun xregs l -> BcaValue (get_value xregs l))

  and isget_actions_partition =
    let local_get_actions_partition xregs l = BcaActions (get_actions_partition xregs l) in
    (has_actions_partition, local_get_actions_partition)

  and isget_actions_rv_partition =
    let local_get_actions_rv_partition xregs l =
      let (actions,rv) = get_actions_rv_partition xregs l in BcaRvActions (actions,rv) in
    (has_actions_rv_partition, local_get_actions_rv_partition)

  and get_value_value_partition xregs (l:opcode_t list) =
    match get_partition_n xregs l [ isget_value ; isget_value ] with
    | [ BcaValue v1 ; BcaValue v2 ] -> (v1,v2)
    | _ -> raise (JCH_failure (errormsg "get_value_value_partition" l))

  and has_object_basic_partition xregs (l:opcode_t list) =
    has_partition_n xregs l [ is_object_value ; is_basic_value ]

  and has_object_object_partition xregs (l:opcode_t list) =
    has_partition_n xregs l [ is_object_value ; is_object_value ]

  and get_object_basic_partition xregs (l:opcode_t list):(bc_objectvalue_t * bc_basicvalue_t) =
    match get_partition_n xregs l [ isget_object_value ; isget_basic_value ] with
    | [ BcaValue (BcObject obj) ; BcaValue (BcBasic basic) ] -> (obj,basic)
    | _ -> raise (JCH_failure (errormsg "get_object_basic_partition" l))

  and has_object_basic_value_partition xregs (l:opcode_t list) =
    has_partition_n xregs l [ is_object_value ; is_basic_value ; is_value ]

  and get_object_basic_value_partition xregs (l:opcode_t list) =
    match get_partition_n xregs l [ isget_object_value ; isget_basic_value ; isget_value ] with
    | [ BcaValue (BcObject obj) ; BcaValue (BcBasic basic) ; BcaValue value ] -> (obj,basic,value)
    | _ -> raise (JCH_failure (errormsg "get_object_basic_value_partition" l))

  and has_object_value_partition xregs (l:opcode_t list) =
    has_partition_n xregs l [ is_object_value ; is_value ]

  and get_object_value_partition xregs (l:opcode_t list) =
    match get_partition_n xregs l [ isget_object_value ; isget_value ] with
    | [ BcaValue (BcObject obj) ; BcaValue value ] -> (obj,value)
    | _ -> raise (JCH_failure (errormsg "get_object_value_partition" l))

  and has_basic_basic_partition xregs (l:opcode_t list) =
    has_partition_n xregs l [ is_basic_value ; is_basic_value ]

  and get_basic_basic_partition xregs (l:opcode_t list) =
    match get_partition_n xregs l [ isget_basic_value ; isget_basic_value ] with
    | [ BcaValue (BcBasic basic1) ; BcaValue (BcBasic basic2) ] -> (basic1,basic2)
    | _ -> raise (JCH_failure (errormsg "get_basic_basic_partition" l))

  and has_basic_partition_n xregs (l:opcode_t list) (n:int) =
    has_partition_n xregs l (mklist n is_basic_value)

  and get_basic_partition_n xregs (l:opcode_t list) (n:int) =
    List.map (fun v ->
        match v with
        | BcaValue (BcBasic b) -> b
        | _ -> raise (JCH_failure (errormsg "get_basic_partition_n" l)))
             (get_partition_n xregs l (mklist n isget_basic_value))
      

  and has_values_partition xregs (l:opcode_t list) (n:int) =
    has_partition_n xregs l (mklist n is_value)

  and get_values_partition xregs (l:opcode_t list) (n:int) =
    List.map (fun a ->
        match a with BcaValue v -> v | _ -> raise (JCH_failure (STR "action")))
             (get_partition_n xregs l (mklist n isget_value))

  and has_actions_partition xregs (l:opcode_t list) = has_partition xregs l is_action

  and get_actions_partition xregs (l:opcode_t list):bc_action_t list =
    match get_partition xregs l is_action (fun xregs l -> BcaAction (get_action xregs l)) with
    | [] -> raise (JCH_failure (STR "get_actions_partition:empty"))
    | l -> (List.map (fun a ->
                match a with
                | BcaAction a -> a
                | _ -> raise (JCH_failure (STR "action"))) l)

  and has_object_values_partition xregs (l:opcode_t list) (n:int) =
    has_partition_n xregs l (is_object_value :: (mklist n is_value))

  and get_object_values_partition xregs (l:opcode_t list) (n:int) =
    match get_partition_n xregs l (isget_object_value :: (mklist n isget_value)) with
    | (BcaValue (BcObject obj)) :: tl ->
       (obj,List.map (fun a -> match a with
                               | BcaValue a -> a
                               | _ -> raise (JCH_failure (STR "action"))) tl)
    | lp -> raise (JCH_failure (errormsgp "get_object_values_partition" l lp ))

  and has_actions_rv_partition xregs (l:opcode_t list) =
    let rec aux l2 revl =
      match revl with
      | [] -> is_value xregs l2
      | h::tl ->
         ((is_value xregs l2) && has_partition xregs (List.rev revl) is_action)
         || aux (h::l2) tl in
    match List.rev l with
    | [] -> false 
    | h::tl -> aux [ h ] tl

  and get_actions_rv_partition xregs (l:opcode_t list) =
    let rec aux l2 revl =
      match revl with
      | [] -> [ BcaValue (get_value xregs l2) ]
      | h::tl when (is_value xregs l2) && has_partition xregs (List.rev revl) is_action ->
         (get_partition xregs (List.rev revl) is_action (fun xregs l -> BcaAction (get_action xregs l)))
         @ [ BcaValue (get_value xregs l2) ]
      | h::tl -> aux (h::l2) tl in
    let result = match List.rev l with
      | [] -> raise (JCH_failure (STR "get_actions_rv_partition:empty"))
      | h::tl -> aux [ h ] tl in
    match List.rev result with
    | (BcaValue value) :: tl ->
       (List.map (fun a ->
            match a with BcaAction a -> a | _ -> raise (JCH_failure (STR "action")))
                 (List.rev tl),value)
    | _ -> raise (JCH_failure (errormsg "get_actions_rv_partition" l))

  and get_actions_throw_partition xregs (l:opcode_t list) =
    let (actions,rv) = get_actions_rv_partition xregs l in
    match rv with
    | BcObject obj -> (actions,obj)
    | _ -> raise (JCH_failure (errormsg "get_actions_throw_partition" l))

  and is_qop xregs (l:opcode_t list) =
    let is_goto_return xregs l =
      match l with
      | [ OpGoto n ] -> n > 0
      | [ OpReturn t ] -> (match t with Void -> false | _ -> true)
      | _ -> false in
    (has_partition_n xregs l [ is_qop_test ; is_object_value ; is_goto_return ; is_object_value ])
    || (has_partition_n  xregs l [ is_qop_test ; is_basic_value ;  is_goto_return ; is_basic_value ])

  and get_qop xregs (l:opcode_t list) =
    let is_goto_return xregs l =
      match l with
      | [ OpGoto n ] -> n > 0
      | [ OpReturn t ] -> (match t with Void -> false | _ -> true)
      | _ -> false in
    let get_goto_return xregs l =
      match l with
      | [ OpGoto n ] -> BcaRetGoto (OpGoto n)
      | [ OpReturn t ] -> BcaRetGoto (OpReturn t)
      | _ -> raise (JCH_failure (errormsg "get_goto_return" l)) in
    let isget_goto_return = (is_goto_return, get_goto_return) in
    if has_partition_n xregs l [ is_qop_test ; is_object_value ;
                           is_goto_return ; is_object_value ] then
      get_partition_n xregs l [ isget_qop_test ; isget_value ; isget_goto_return ; isget_value ]
    else if has_partition_n xregs l [ is_qop_test ; is_basic_value ;
                                is_goto_return ; is_basic_value ] then
      get_partition_n xregs l [ isget_qop_test ; isget_value ; isget_goto_return ; isget_value ]
    else
      raise (JCH_failure (errormsg "get_qop" l))

  and is_conditional_action xregs (l:opcode_t list) =
    has_partition_n xregs l [ is_qop_test ; has_actions_partition ]

  and get_conditional_action xregs (l:opcode_t list) =
    let result = get_partition_n xregs l [ isget_qop_test ; isget_actions_partition ] in
    match result with
    | [ BcaTest (testopc,vl) ; BcaActions al ] -> (testopc,vl,al)
    | _ ->
       raise (JCH_failure (errormsg "get_conditional_action" l))

  and is_action_except xregs (l:opcode_t list) =
    let is_goto_store xregs ll = match ll with [ OpGoto 4 ; (OpStore _ | OpPop) ] -> true | _ -> false in
    has_partition_n xregs l [ has_actions_partition ; is_goto_store ]

  and get_action_except xregs (l:opcode_t list) =
    let is_goto_store xregs ll = match ll with [ OpGoto 4 ; (OpStore _ | OpPop) ] -> true | _ -> false in
    let isget_goto_store =
      (is_goto_store, fun xregs ll -> match ll with
                        | [ OpGoto 4 ; (OpStore _ | OpPop) ] -> BcaOpcodes ll
                        | _ -> raise (JCH_failure (errormsg "isget_goto_store" ll))) in
    let actions = get_partition_n xregs l [ isget_actions_partition ; isget_goto_store ] in
    match actions with
    | [ BcaActions actions ; BcaOpcodes _ ] -> actions
    | _ -> raise (JCH_failure (errormsg "get_action_except" l))

  and is_result_except xregs (l:opcode_t list) =
    let is_return_store xregs ll =
      match ll with [ OpReturn _ ; (OpStore _ | OpPop) ] -> true | _ -> false in
    has_partition_n xregs l [ has_actions_rv_partition ; is_return_store ; is_value ]

  and get_result_except xregs (l:opcode_t list) =
    let is_return_store xregs ll =
      match ll with [ OpReturn _ ; (OpStore _ | OpPop) ] -> true | _ -> false in
    let isget_return_store =
      (is_return_store, fun  xregs ll -> match ll with
                        | [ OpReturn _ ; (OpStore _ | OpPop) ] -> BcaOpcodes ll
                        | _ -> raise (JCH_failure (errormsg "isget_return_store" ll))) in
    let result =
      get_partition_n xregs l [ isget_actions_rv_partition ; isget_return_store ; isget_value ] in
    match result with
    | [ BcaRvActions (actions,rv) ; BcaOpcodes _ ; BcaValue v ] -> (actions,rv,v)
    | _ -> raise (JCH_failure (errormsg "get_result_except" l))
    
  and getinvoke opc =
    match opc with
    | OpInvokeVirtual (ty,ms) -> ("virtual",ty,ms)
    | OpInvokeInterface (cn,ms) -> ("interface",(TClass cn),ms)
    | OpInvokeSpecial (cn,ms) -> ("private",(TClass cn),ms)
    | _ -> raise (JCH_failure (errormsg "getinvoke" [ opc ]))

  and mkcall
        (calltype:string)
        (base:bc_objectvalue_t option)
        (basetype:object_type_t)
        (ms:method_signature_int)
        (args:bc_value_t list) =
    { bcp_type = calltype ; bcp_base_type = basetype ; bcp_base_object = base ;
      bcp_ms = ms ; bcp_args = args }

  and mkstaticcall cn ms args = mkcall "static" None (TClass cn) ms args 
  
  and mkobjectcall base opci args =
    let (ty,basetype,ms) = getinvoke opci in
    { bcp_type = ty ; bcp_base_type = basetype ; bcp_base_object = Some base ;
      bcp_ms = ms ; bcp_args = args } in

  let addtolog instrs =
    let _ = add_methodsize_no_pattern (List.length instrs) in
    let len = List.length instrs in
    if len <= maxlog then
      chlog#add
        ("bc patterns " ^ (string_of_int len))
        (sanitize_pretty
           (LBLOCK [ cms#toPretty ; STR " (" ; STR jar ; STR ")" ; NL ;
                     (LBLOCK (List.map (fun p ->
                                  LBLOCK [ STR "        " ;
                                           opcode_to_pretty p ; NL ]) instrs)) ; NL ;
                     (if mInfo#has_handlers then
                        mInfo#get_exception_handlers#toPretty
                      else STR "") ])) in
  
  if opcodes#instr_count = 1 then
    match opcodes#at 0 with
    | OpReturn _ -> Some BcpNop
    | opc ->
       begin
         chlog#add "bc patterns 1"
                   (LBLOCK [ cms#toPretty ; STR ": " ; opcode_to_pretty opc ]) ;
         None
       end

  else
    let pattern =
      if opcodes#instr_count <= maxmatch then
        let (args,opc) = splitargs instrs  in
        match opc with
        | OpReturn Void when has_actions_partition [] args ->
           Some (BcpAction (get_actions_partition [] args))
        | OpReturn _ when has_actions_rv_partition [] args ->
           let (actions,rv) = get_actions_rv_partition [] args in
           Some (BcpResult (actions,rv))
        | OpThrow when has_actions_rv_partition [] args ->
           let (actions,rv) = get_actions_throw_partition [] args in
           Some (BcpThrow (actions,rv))
        | OpReturn Void when is_conditional_action [] args ->
           let (testopc,testval,actions) = get_conditional_action [] args in
           Some (BcpAction [ BcConditionalAction (testopc,testval,actions,[]) ])
        | OpReturn Void when has_one_exception_caught && is_action_except [] args ->
           let actions = get_action_except [] args in
           let exn = get_exception_handled () in
           Some (BcpActionExcept (exn,actions))
        | OpReturn _ when has_one_exception_caught && is_result_except [] args ->
           let (actions,rv,ev) = get_result_except [] args in
           let exn = get_exception_handled () in
           Some (BcpResultExcept (exn,actions,rv,ev))
        | OpReturn Void when
               (match args with
                | opc1 :: opc2 :: opc3 :: (OpIfCmpANe 4) :: (OpReturn Void) :: actionargs ->
                   is_value [] [ opc1 ; opc2 ] && is_value_opc [] opc3 &&
                     has_actions_partition [] actionargs
                | _ -> false) ->
           (match args with
            | opc1 :: opc2 :: opc3 :: (OpIfCmpANe 4 as testopc) :: (OpReturn Void) :: actionargs ->
               Some (BcpAction ( [ BcConditionalAction
                                     ( [ testopc ],
                                       [ get_value [] [ opc1 ; opc2 ] ; get_value_opc [] opc3 ],
                                       [], get_actions_partition [] actionargs) ]))
            | _ -> None)
        | OpReturn Void when is_qop_test [] args ->
           (match get_qop_test [] args with
            | BcaTest (_,vl) -> Some (BcpAction [ BcDropValues vl ])
            | _ ->
               raise (JCH_failure (errormsg "pattern:bcatest" instrs)))
        | OpReturn _ when is_qop [] args ->
           let v = 
             match get_qop [] args with
             | [ BcaTest (opc,vl) ; BcaValue (BcBasic fv) ; BcaRetGoto _ ;
                 BcaValue (BcBasic tv) ] ->
                BcBasic (BcvQResult (opc, vl, fv, tv))
             | [ BcaTest (opc,vl) ; BcaValue (BcObject fv) ; BcaRetGoto _ ;
                 BcaValue (BcObject tv) ] ->
                BcObject (BcoQResult (opc, vl, fv, tv))
             | _ ->
                raise (JCH_failure (errormsg "pattern" instrs)) in
           Some (BcpResult ([],v))
        | OpNop ->
           if opcodes#instr_count > 2 then
             let (args2,opc2) = splitargs args in
             (match opc2 with
              | OpReturn Void when has_actions_partition [] args2 ->
                 Some (BcpAction (get_actions_partition [] args2))
              | OpReturn _ when has_actions_rv_partition [] args2 ->
                 let (actions,rv) = get_actions_rv_partition [] args2 in
                 Some (BcpResult (actions,rv))
              | _ -> None)
           else
             None
                
        | _ ->
           None
      else
        None in

    match pattern with
    | Some p -> Some p

    | _ ->                                                      

       if opcodes#instr_count = 2 then
         match instrs  with
         | [ opc ; OpReturn Void ] when is_action_opc opc ->
            Some (BcpAction [ get_action_opc opc])

         | [ opc ; OpReturn _ ] when is_value_opc [] opc ->
            Some (BcpResult ([],get_value_opc [] opc))

         | [ opc ; OpThrow ] when is_object_value_opc [] opc ->
            Some (BcpThrow ([],get_object_value_opc [] opc))
           
         | [ opc ; OpGoto (-3) ] when is_action_opc opc ->
            let _ = add_noteworthy "infinite loop" in
            Some (BcpInfiniteLoop [get_action_opc opc])
           
         | [ OpGoto 3 ; OpGoto 0 ] ->
            let _ = add_noteworthy "infinite loop" in
            Some (BcpInfiniteLoop ([]))
                                    
         | [ OpGoto 3 ; OpReturn Void ] -> Some BcpNop
                                         
         | instrs -> begin addtolog instrs ; None end
              
       else if opcodes#instr_count = 3 then
         match instrs with
           
         | [ OpNew cn ; OpInvokeSpecial (icn,ms) ; OpReturn Void ]
              when cn#equal icn && ms#name = "<init>" ->
            Some (BcpAction [ BcNewObject (cn,[])]) 
           
         | [ OpLoad (_,0) ; OpInvokeSpecial (cn,ms) ; OpReturn Void ]
              when cn#name = "java.lang.Object" && ms#name = "<init>" ->
            Some (BcpAction [ BcInitObject ])
                                                                       
         | [ OpLoad (_,0) ; OpInvokeSpecial (cn,ms) ; OpReturn Void ]
              when cInfo#has_super_class && cn#equal cInfo#get_super_class && ms#name = "<init>" ->
            Some (BcpAction [ BcInitSuper ])

         | [ OpLoad (_,n) ; OpIInc _ ; OpReturn _ ] ->
            let _ = add_noteworthy "probably unintentional" in
            Some (BcpResult ([],BcBasic (BcvArg n)))
                      
         | [ opc ; OpNop ; OpReturn _ ] when is_value_opc [] opc ->
            Some (BcpResult ([],get_value_opc [] opc))
           
         | [ opc ; (OpIfEq 3 | OpIfNe 3 | OpIfNonNull 3 | OpIfNull 3) ; OpReturn _ ]
              when is_value_opc [] opc ->
            Some (BcpAction [BcDropValues [ get_value_opc [] opc]])
           
         | [ opc ; OpStore _ ; OpReturn Void ] when is_value_opc [] opc ->
            Some (BcpAction [BcDropValues [ get_value_opc [] opc]])
           
         | [ opc ; OpLookupSwitch (11,[]) ; OpReturn Void ] when is_value_opc [] opc ->
            Some (BcpAction [BcDropValues [get_value_opc [] opc]])
           
         | [ opc1 ; opc2 ; OpThrow ] when is_object_value [] [ opc1 ; opc2 ] ->
            Some (BcpThrow ([],get_object_value [] [ opc1 ; opc2 ]))
           
         | [ OpGoto 3 ; opc ; OpReturn Void ] when is_action_opc opc ->
            Some (BcpAction [ get_action_opc opc ])
                                                                      
         | [ OpGoto 3 ; opc ; OpReturn _ ] when is_value [] [ opc ] ->
            Some (BcpResult ([],get_value_opc [] opc))
           
         | [ opc ; OpReturn _ ; OpNop ] when  is_value [] [ opc ] ->
            Some (BcpResult ([],get_value_opc [] opc))
                                                                
         | instrs -> begin addtolog instrs ; None end


       else if opcodes#instr_count = 4 then
         match instrs with

        | [ opc1 ; OpReturn Void ; OpNop ; OpThrow ] when has_actions_partition [] [ opc1 ] ->
           Some (BcpAction (get_actions_partition [] [opc1]))
          
        | [ opc1 ; OpReturn _ ; OpNop ; OpThrow ] when has_actions_rv_partition [] [ opc1 ] ->
           let (actions,rv) = get_actions_rv_partition [] [ opc1 ] in
           Some (BcpResult (actions,rv))

        | [ opc1 ; OpReturn Void ; OpReturn Void ; OpNop ]
              when is_action_opc opc1 ->
            Some (BcpAction ( [ get_action_opc opc1 ]))
                                                       
         | [ opc1 ; (OpDup | OpDup2) ; OpPutStatic (cn,fs) ; OpReturn _ ]
              when is_value_opc [] opc1 ->
            let v = get_value_opc [] opc1 in
            Some (BcpResult ([ BcPutStaticField (cn,fs,v) ],v))
                       
         | [ opc1 ; opc2 ; OpStore _ ; OpReturn Void ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ] ->
            let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ] in
            Some (BcpAction [ BcDropValues [rv] ])

         | [ opc ; OpStore (_,n1) ; OpLoad (_,n2) ; OpReturn _ ]
              when is_value_opc [] opc && n1 = n2 ->
            Some (BcpResult ([],get_value_opc [] opc))

         | [ opc1 ; OpStore _ ; opc2 ; OpReturn _ ]
              when is_value_opc [] opc1 && is_value_opc [] opc2 ->
            Some (BcpResult ([ BcDropValues [ get_value_opc [] opc1 ] ],
                             get_value_opc [] opc2))

         | [ opc1 ; opc2 ; opc3 ; OpGoto n ]
              when is_action [] [ opc1 ; opc2 ; opc3 ] && n < 0 ->
            let _ = add_noteworthy "infinite loop" in
            Some (BcpInfiniteLoop  [ get_action [] [ opc1 ; opc2 ; opc3 ] ])

         | [ opc1 ; OpLookupSwitch (11,[]) ; opc2 ; OpReturn _ ]
              when is_basic_value_opc [] opc1 && is_value_opc [] opc2 ->
            Some (BcpResult ([ BcDropValues [get_value_opc [] opc1] ],get_value_opc [] opc2))
           
         | [ opc1 ; opc2 ; OpLookupSwitch (12,[]) ; OpReturn Void ]
              when is_basic_value [] [ opc1 ; opc2 ] ->
            Some (BcpAction [ BcDropValues [get_value [] [ opc1 ; opc2 ]] ])
                      
         | [ OpLongConst _ ; OpLongConst _ ; OpPutStatic _ ; OpReturn Void ] ->
            Some (BcpIllegalSeq ("nLnL-putstatic", instrs))
           
         | instrs -> begin addtolog instrs ; None end

       (* -------------------------------------------------------------- 5 instrs -- *)
      
       else if opcodes#instr_count = 5 then
         match instrs with
                      
         | [ opc1 ; opc2 ; OpReturn Void ; OpNop ; OpThrow ]
              when has_actions_partition [] [ opc1 ; opc2 ] ->
           Some (BcpAction (get_actions_partition [] [opc1 ; opc2]))
          
         | [ opc1 ; opc2 ; OpReturn _ ; OpNop ; OpThrow ]
              when has_actions_rv_partition [] [ opc1 ; opc2  ] ->
           let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ] in
           Some (BcpResult (actions,rv))

        | [ OpNew ncn ; OpDup ; opc ; OpInvokeSpecial (cn,ms) ; OpThrow ]
              when ncn#equal cn && ms#name = "<init>" && is_value_opc [] opc ->
            Some (BcpThrow ([],BcoNewObject (cn,[ get_value_opc [] opc ])))

         | [ OpNew ncn ; opc1 ; opc2 ; OpInvokeSpecial (cn,ms) ; OpReturn Void ]
              when ncn#equal cn && ms#name = "<init>" && is_value [] [ opc1 ; opc2 ] ->
            Some (BcpAction [ BcDropValues [ BcObject (BcoNewObject (cn, [ get_value [] [ opc1 ; opc2 ] ])) ] ])
           
         | [ OpGoto 6 ; OpStore (_,n1) ; OpLoad (_,n2) ; OpThrow ; OpReturn Void ]
              when n1 < 4 && n2 < 4 -> Some BcpNop

         | [ OpLoad _ ; OpStore (_,n) ; opc1 ; opc2 ; OpReturn _ ]
              when is_value [ n ] [ opc1 ; opc2 ] ->
            Some (BcpResult ([], get_value [ n ] [ opc1 ; opc2 ]))

         | [ opc1 ; opc2 ; testopc ; OpReturn Void ; OpReturn Void ]
              when is_value [] [ opc1 ; opc2 ] && is_forward_unary_test_opcode testopc ->
            Some (BcpAction [ BcDropValues [ get_value [] [ opc1 ; opc2 ] ] ])

         | [ opc1 ; OpStore (_,n1) ; OpLoad (_,n2) ; opc2 ; OpReturn Void ]
              when is_action [] [ opc1 ; opc2 ] && n1 = n2 ->
            Some (BcpAction [ get_action [] [ opc1 ; opc2 ] ])

         | [ opc1 ; OpStore (_,n) ; opc2 ; OpReturn _ ; OpNop ]
              when is_value_opc [] opc1 && is_value_opc [ n ] opc2 ->
            Some (BcpResult ([ BcDropValues [ get_value_opc [] opc1 ] ], get_value_opc [ n ] opc2))
                                                
         | [ opc1 ; opc2 ; opc3 ; OpReturn Void ; OpNop ]
              when has_actions_partition [] [ opc1 ; opc2 ; opc3 ] ->
            Some (BcpAction (get_actions_partition [] [ opc1 ; opc2 ; opc3 ]))

         | [ opc1 ; opc2 ; OpStore (_,n) ; opc3 ; OpReturn _ ]
              when is_value [] [ opc1 ; opc2 ] && is_value_opc [n] opc3 ->
            Some (BcpResult ( [ BcDropValues [ get_value [] [ opc1 ; opc2 ] ] ], get_value_opc [n] opc3))
                      
         | [ opc1 ; opc2 ; opc3 ; OpStore _ ; OpReturn Void ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ] ->
            let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ] in
            Some (BcpAction [ BcDropValues [rv] ])
           
         | [ opc1 ; OpStore (_,n1) ; OpLoad (_,n2) ; opc2 ; OpReturn _ ]
              when is_value [] [opc1 ; opc2 ] && n1 = n2 ->
            Some (BcpResult ([],get_value [] [ opc1 ; opc2 ]))
           
         | [ opc1 ; opc2 ; OpStore (_,n1) ; OpLoad (_,n2) ; OpReturn _ ]
              when is_value [] [ opc1 ; opc2 ] && n1 = n2 ->
            Some (BcpResult ([],get_value [] [ opc1 ; opc2 ]))

         | [ opc1 ; OpDup ; opc2 ; opc3 ; OpReturn _ ]
              when is_value [] [ opc1 ] && is_action [] [ opc1 ; opc2 ; opc3 ] ->
            Some (BcpResult ([ get_action [] [ opc1 ; opc2 ; opc3 ] ], get_value [] [ opc1 ]))
           
         | [ opc1 ; opc2 ; OpDup ; OpPutStatic (cn,fs) ; OpReturn _ ]
              when is_value [] [ opc1 ; opc2 ] ->
            let v = get_value [] [ opc1 ; opc2 ] in
            Some (BcpResult ( [ BcPutStaticField (cn,fs,v) ],v))
            
         | [ opc1 ; OpStore _ ; OpAConstNull ; OpPutStatic (cn,fs) ; OpReturn Void ]
              when is_value [] [ opc1 ] ->
            Some (BcpAction [ BcDropValues [get_value [] [ opc1 ]] ;
                              BcPutStaticField (cn,fs,BcObject BcoNull) ])
           
         | [ opc1 ; OpStore _ ; OpReturn Void ; OpReturn Void ; OpNop ]
              when is_value_opc [] opc1 ->
            Some (BcpAction [ BcDropValues [get_value_opc [] opc1] ])
                                      
         | [ OpLoad (Object,0) ; opc ; ( OpDupX1 | OpDup2X1 ) ; OpPutField (cn,fs) ; OpReturn _ ]
              when is_value_opc [] opc ->
            let v = get_value_opc [] opc in
            Some (BcpResult ( [ BcPutThisField (cn,fs,v) ], v))
            
         | [ OpLoad (Object,0) ; OpDup ; OpStore _ ; OpGetField (cn,fs) ; OpReturn _ ] ->
            Some (BcpResult ([], get_value [] [ OpLoad (Object,0) ; OpGetField (cn,fs) ]))
           
         | [ opc1 ; opc2 ; (OpIfNonNull 4 | OpIfEq 4 | OpIfNull 4) ; OpReturn Void ; OpReturn Void ]
              when is_value [] [ opc1 ; opc2 ] ->
            Some (BcpAction [ BcDropValues [get_value [] [ opc1 ; opc2 ]]])

         | [ OpLoad (_,n1) ; testopc ; OpLoad (_,n2) ; OpStore _ ; OpReturn Void ]
              when n1 = n2 && is_forward_unary_test_opcode testopc -> Some BcpNop

         | [ opc1 ; opc2 ; opc3 ; OpThrow ; OpReturn Void ]
              when is_object_value [] [ opc1 ; opc2 ; opc3 ] ->
            Some (BcpThrow ([], get_object_value [] [ opc1 ; opc2 ; opc3 ]))
                      
         | instrs -> begin addtolog instrs ; None end
                   
                       (* -------------------------------------------------------------- 6 instrs -- *)
     
       else if opcodes#instr_count = 6 then
         match instrs with

         | [ opc1 ; opc2 ; opc3 ; OpReturn Void ; OpNop ; OpThrow ]
              when has_actions_partition [] [ opc1 ; opc2 ; opc3 ] ->
           Some (BcpAction (get_actions_partition [] [opc1 ; opc2 ; opc3 ]))
          
         | [ opc1 ; opc2 ; opc3 ; OpReturn _ ; OpNop ; OpThrow ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ] ->
           let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ] in
           Some (BcpResult (actions,rv))

         | [ opc1 ; OpStore (_,n1) ; OpLoad (_,n2) ; opc2 ; opc3 ; OpReturn _ ]
              when is_value [] [ opc1 ; opc2 ; opc3 ] && n1 = n2 ->
            Some (BcpResult([],get_value [] [ opc1 ; opc2 ; opc3 ]))

         | [ opc1 ; OpStore (_,n) ; opc2 ; opc3 ; opc4 ; OpReturn Void ]
              when is_value_opc [] opc1 && is_action [n] [ opc2 ; opc3 ; opc4 ] ->
            Some (BcpAction ( [ BcDropValues [ get_value_opc [] opc1 ] ;
                                get_action [n] [ opc2 ; opc3 ; opc4 ]]))

         | [ opc1 ; opc2 ; OpStore (_,n1) ; OpLoad (_,n2) ; opc3 ; OpReturn _ ]
           | [ opc1 ; opc2 ; opc3 ; OpStore (_,n1) ; OpLoad (_,n2) ; OpReturn _ ]
              when is_value [] [ opc1 ; opc2 ; opc3 ] && n1 = n2 ->
            Some (BcpResult ([],get_value [] [ opc1 ; opc2 ; opc3 ]))

         | [ opc1 ; opc2 ; opc3 ; OpStore _ ; OpReturn Void ; OpNop ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ] ->
            let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ] in
            Some (BcpAction ( actions @ [ BcDropValues [ rv ] ] ))
           
         | [ opc1 ; opc2 ; opc3 ; opc4 ; OpStore _ ; OpReturn Void ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] ->
            let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] in
            Some (BcpAction [ BcDropValues [rv] ])

         | [ opc1 ; (OpDup | OpDup2) ; opc2 ; opc3 ; OpPutStatic (cn,fs) ; OpReturn _ ]
              when is_value_opc [] opc1 && is_value [] [ opc1 ; opc2 ; opc3 ] ->
            let action = BcPutStaticField (cn,fs, get_value [] [ opc1 ; opc2 ; opc3 ]) in
            Some (BcpResult ( [ action ], get_value_opc [] opc1))

         | [ opc1 ; OpStore _ ; opc2 ; OpReturn _ ;  opc3 ; OpReturn _ ]
              when is_value_opc [] opc1 && is_value_opc [] opc2 && is_value_opc [] opc3 ->
            Some (BcpResult ([ BcDropValues [ get_value_opc [] opc1 ]], get_value_opc [] opc2))

         | [ opc1 ; OpDup ; testopc ; opc2 ; opc3 ; OpReturn _ ]
              when is_value_opc [] opc1 && is_test_opcode testopc
                   && is_action [] [ opc2 ; opc3 ] ->
            let v = get_value_opc [] opc1 in
            Some (BcpResult ([ BcConditionalAction ( [ testopc ] , [ v ],
                                                      [ get_action [] [ opc2 ; opc3 ]], []) ],v))
            

         | [ opc1 ; ((OpLookupSwitch _ | OpTableSwitch _) as testopc) ; opc2 ;
             OpReturn _ ; opc3 ; OpReturn _ ]
              when is_value_opc [] opc1 && is_basic_value_opc [] opc2 && is_basic_value_opc [] opc3 ->
            Some (BcpResult ( [ ], BcBasic (BcvQResult([testopc], [ get_value_opc [] opc1 ],
                                              get_basic_value_opc [] opc2,
                                              get_basic_value_opc [] opc3))))

         | [ opc1 ; ((OpLookupSwitch _ | OpTableSwitch _) as testopc) ; opc2 ;
             OpReturn _ ; opc3 ; OpReturn _ ]
              when is_value_opc [] opc1 && is_object_value_opc [] opc2 && is_object_value_opc [] opc3 ->
            Some (BcpResult ( [ ], BcObject (BcoQResult([testopc], [ get_value_opc [] opc1 ],
                                              get_object_value_opc [] opc2,
                                              get_object_value_opc [] opc3))))

         | l -> begin addtolog l ; None end

         (* -------------------------------------------------------------- 7 instrs -- *)      
        
       else if opcodes#instr_count = 7 then
         match instrs with

         | [ opc1 ; opc2 ; opc3 ; opc4 ; OpReturn Void ; OpNop ; OpThrow ]
              when has_actions_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] ->
           Some (BcpAction (get_actions_partition [] [opc1 ; opc2 ; opc3 ; opc4 ]))
          
         | [ opc1 ; opc2 ; opc3 ; opc4 ; OpReturn _ ; OpNop ; OpThrow ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] ->
           let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4] in
           Some (BcpResult (actions,rv))

         | [ opc1 ; opc2 ; OpDup ; opc3 ; opc4 ; OpArrayStore t ; OpReturn _ ]
              when is_object_value [] [ opc1 ; opc2 ] && is_basic_value_opc [] opc3
                   && is_object_value_opc [] opc4 ->
            let base = get_object_value [] [ opc1 ; opc2 ] in
            let index = get_basic_value_opc [] opc3 in
            let aval = get_value_opc [] opc4 in
            Some (BcpResult ( [ BcArrayStore (t, base, index, aval) ], BcObject base) )
            
         | [ OpLoad (Object,0) ; OpDup ; OpGetField (cn1,fs1) ; opc ; binopc ;
             OpPutField (cn2,fs2) ; OpReturn Void ]
              when is_binop_opcode binopc && is_basic_value_opc[]  opc ->
            let binop = BcvBinOpResult (binopc, BcvThisField (cn1,fs1), get_basic_value_opc [] opc) in
            Some (BcpAction [ BcPutThisField (cn2,fs2,BcBasic binop) ])

         | [ opc1 ; OpStore (_,n) ; opc2 ; opc3 ; opc4 ; OpReturn _ ; OpNop ]
              when is_value_opc [] opc1 && is_value [ n ] [ opc2 ; opc3 ; opc4 ] ->
            Some (BcpResult ([ BcDropValues [ get_value_opc [] opc1 ]],
                             get_value [ n ] [ opc2 ; opc3 ; opc4 ]))
           
         | [ opc1 ; OpStore (_,n) ; opc2 ; opc3 ; opc4 ; opc5 ; OpReturn Void  ]
              when is_value_opc [] opc1 && is_action [ n ] [ opc2 ; opc3 ; opc4 ; opc5 ] ->
            Some (BcpAction ([ BcDropValues [ get_value_opc [] opc1 ] ; 
                               get_action [ n ] [ opc2 ; opc3 ; opc4 ; opc5 ]]))

         | [ opc1 ; opc2 ; opc3 ; OpStore (_,n1) ; OpLoad (_,n2) ; opc4 ; OpReturn _ ]
           | [ opc1 ; opc2 ; opc3 ; opc4 ; OpStore (_,n1) ; OpLoad (_,n2) ; OpReturn _ ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] && n1 = n2 ->
            let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] in
            Some (BcpResult (actions,rv))

         | [ opc1 ; opc2 ; opc3 ; OpStore (_,n1) ; OpLoad (_,n2) ; opc4 ; OpReturn Void ]
           | [ opc1 ; opc2 ; opc3 ; opc4 ; OpStore (_,n1) ; OpLoad (_,n2) ; OpReturn _ ]
              when has_actions_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] && n1 = n2 ->
            let actions = get_actions_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ] in
            Some (BcpAction actions)

         | [ opc1 ; opc2 ; OpDup ; testopc ; opc3 ; opc4 ; OpReturn _ ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && is_action [] [ opc3 ; opc4 ] ->
            let v = get_value [] [ opc1 ; opc2 ] in
            Some (BcpResult ([ BcConditionalAction ( [ testopc ] , [ v ],
                                                     [ get_action [] [ opc3 ; opc4 ]], []) ],v))
            
         | [ opc1 ; OpNewArray t1 ; OpDup ; opc2 ; opc3 ; OpArrayStore t2 ; OpReturn _ ]
              when is_basic_value_opc [] opc1 && is_basic_value_opc [] opc2
                   && is_value_opc [] opc3 ->
            let a = BcoNewArray (t1, get_basic_value_opc [] opc1) in
            let index = get_basic_value_opc [] opc2 in
            Some (BcpResult ([ BcArrayStore (t2, a, index, get_value_opc [] opc3) ],BcObject a))

         | [ OpLoad (_,0) ; OpLoad(_,0) ; opc1 ; OpDupX1 ; OpPutField (cn1,fs1) ;
             OpPutField (cn2,fs2) ; OpReturn Void ] when is_value_opc [] opc1 ->
            let v = get_value_opc [] opc1 in
            Some (BcpAction [ BcPutThisField (cn1,fs1, v) ; BcPutThisField (cn2,fs2,v) ])

         | [ opc1 ; testopc ; opc2 ; opc3 ; opc4 ; opc5 ; OpReturn _ ]
              when is_value_opc [] opc1 && is_forward_unary_test_opcode testopc
                   && is_action [] [ opc2 ; opc3 ; opc4 ] && is_value_opc [] opc5 ->
            let action = get_action [] [ opc2 ; opc3 ; opc4 ] in
            let testv = get_value_opc [] opc1 in
            let rv = get_value_opc [] opc5 in
            Some (BcpResult ([ BcConditionalAction ([testopc],[testv],[ action ],[])], rv))

         | l -> begin addtolog l ; None end

         (* -------------------------------------------------------------- 8 instrs -- *)      

       else if opcodes#instr_count = 8 then
         match instrs with
         | [ opc1 ; opc2 ; opc3 ; opc4 ; opc5 ; OpStore (_,n1) ; OpLoad (_,n2) ; OpReturn _ ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ; opc5 ] && n1 = n2 ->
            let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ; opc5 ] in
            Some (BcpResult (actions,rv))

         | [ opc1 ; opc2 ; opc3 ; opc4 ; OpStore (_,n1) ; OpLoad (_,n2) ; opc5 ; OpReturn _ ]
              when has_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ; opc5 ] && n1 = n2 ->
            let (actions,rv) = get_actions_rv_partition [] [ opc1 ; opc2 ; opc3 ; opc4 ; opc5 ] in
            Some (BcpResult (actions,rv))

         | [ opc1 ; OpNewArray t1 ; OpDup ; opc2 ; opc3 ; OpArrayStore t2 ; OpPutStatic (cn,fs) ;
             OpReturn Void ]
              when is_basic_value_opc [] opc1 && is_basic_value_opc [] opc2
                   && is_value_opc [] opc3 ->
            let v = BcoNewArray (t1, get_basic_value_opc [] opc1) in
            let a1 = BcArrayStore (t2, v, get_basic_value_opc [] opc2, get_value_opc [] opc3) in
            let a2 = BcPutStaticField (cn,fs,  BcObject v) in
            Some (BcpAction [ a1 ; a2 ])

         | [ opc1 ; OpStore (_,n) ; opc2 ; opc3 ; opc4 ; opc5 ; OpReturn Void ; OpNop ]
              when is_value_opc [] opc1 && is_action [ n ] [ opc2 ; opc3 ; opc4 ; opc5 ] ->
            Some (BcpAction [ BcDropValues [ get_value_opc [] opc1 ] ;
                              get_action [n] [ opc2 ; opc3 ; opc4 ; opc5 ] ])

         | l -> begin addtolog l ; None end

         (* -------------------------------------------------------------- 9 instrs -- *)

       else if opcodes#instr_count = 9 then
         match instrs with
           
         | [ OpLoad (Object,0) ; OpDup ; OpGetField (cn1,fs1) ; opc1 ; opc2 ; binopc ;
             OpPutField (cn2,fs2) ; opc ; OpReturn _ ]
              when is_basic_value [] [ opc1 ; opc2 ] && is_binop_opcode binopc
                   && is_value_opc [] opc ->
            let v = BcBasic (BcvBinOpResult (binopc, BcvThisField (cn1,fs1), 
                                            get_basic_value [] [ opc1 ; opc2 ])) in
            Some (BcpResult ( [ BcPutThisField (cn2,fs2, v) ], get_value_opc [] opc) )

         | l -> begin addtolog l ; None end

         (* -------------------------------------------------------------- 10 instrs -- *)

       else if opcodes#instr_count = 10 then
         match instrs with

         | l -> begin addtolog l ; None end

           
         (* -------------------------------------------------------------- 16 instrs -- *)

       else if opcodes#instr_count = 16 then
         match instrs with

         | [ OpLoad (Object,0) ; OpInvokeSpecial (cn,ms) ; opc1 ; opc2 ; testopc ;
             opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ; opc10 ; opc11 ;
             OpReturn Void ; OpReturn Void ]
              when ms#name = "<init>"
                   && (cn#name = "java.lang.Object"
                      || cInfo#has_super_class && cn#equal cInfo#get_super_class)
                   && is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && is_action [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ; opc10 ; opc11 ] ->
            let  testv = get_value [] [ opc1 ; opc2 ] in
            let action = get_action [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ; opc10 ; opc11 ] in
            let ainit = if cn#name = "java.lang.Object" then BcInitObject else BcInitSuper in
            Some (BcpAction [ ainit ; BcConditionalAction ( [testopc],[testv],[ action ],[]) ])
            
         | l -> begin addtolog l ; None end

         (* -------------------------------------------------------------- 18 instrs -- *)

       else if opcodes#instr_count = 18 then
         match instrs with

         | [ opc1 ; opc2 ; testopc ;
             opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ; opc10 ; opc11 ;
             OpReturn Void ;
             opc12 ; opc13 ; opc14 ; opc15 ; OpThrow ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc 
                   && is_action [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ; opc10 ; opc11 ]
                   && is_object_value [] [ opc12 ; opc13 ; opc14 ; opc15 ] ->
            let testv = get_value [] [ opc1 ; opc2 ] in
            let action = get_action [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ; opc10 ; opc11 ] in
            let exv = get_object_value [] [ opc12 ; opc13 ; opc14 ; opc15 ] in
            let taction = BcThrow exv in
            Some (BcpAction [ BcConditionalAction ( [testopc], [ testv ], [ action ], [ taction ]) ])

         | l -> begin addtolog l ; None end           


           (* -------------------------------------------------------------- 20 instrs -- *)
              
       else if maxmatch >= 20 && opcodes#instr_count = 20 then
         match instrs with

         | [ opc1 ; opc2 ; testopc ; opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ;
             opc10 ; opc11 ; opc12 ; OpReturn _ ; OpStore _ ;
             (OpLoad (_,n1) as opc13) ; opc14 ; OpPop ; OpLoad (_,n2) ; OpThrow ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && has_one_exception_caught
                   && has_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ]
                   && is_value [] [ opc10 ; opc11 ; opc12 ] && is_object_value [] [ opc13 ; opc14 ]
                   && n1 = n2 ->
            let exn = get_exception_handled () in
            let testv = get_value [] [ opc1 ; opc2 ] in
            let actions = get_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ] in
            let condaction = BcConditionalAction ([testopc], [testv], actions,[]) in
            let returnv = get_value [] [ opc10 ; opc11 ; opc12 ] in
            let throwv = get_object_value [] [ opc13 ; opc14 ] in
            Some (BcpResultExceptThrow (exn, [ condaction ], returnv, throwv))

         | [ opc1 ; opc2 ; OpDup ; opc3 ; opc4 ; OpArrayStore t1 ; OpStore (_,n1) ;
             opc5 ; opc6 ; OpDup ; opc7 ; OpLoad (_,n2) ; OpArrayStore t2 ; OpStore (_,n3) ;
             OpLoad (_,0) ;  opc8 ; opc9 ; OpLoad (_,n4) ; opci ; OpReturn Void ]
              when is_object_value [] [ opc1 ; opc2 ] && is_basic_value_opc [] opc3
                   && is_value_opc [] opc4 && n1 = n2 && n3 = n4 
                   && is_object_value [] [ opc5 ; opc6 ] && is_basic_value_opc [] opc7
                   && is_value_opc [] opc8 && is_value_opc [] opc9
                   && (match opci with OpInvokeVirtual _ | OpInvokeInterface _ -> true | _ -> false) ->
            let base1 = get_object_value [] [ opc1 ; opc2 ] in
            let index1 = get_basic_value_opc [] opc3 in
            let aval1 = get_value_opc [] opc4 in
            let action1 = BcArrayStore (t1, base1, index1, aval1) in
            let base2 = get_object_value [] [ opc5 ; opc6 ] in
            let index2 = get_basic_value_opc [] opc7 in
            let aval2 = BcObject base1 in
            let action2 = BcArrayStore (t2, base2, index2, aval2) in
            let arg1 = get_value_opc [] opc8 in
            let arg2 = get_value_opc [] opc9 in
            let arg3 = BcObject base2 in 
            let call = mkobjectcall (BcoArg 0) opci [ arg1 ; arg2 ; arg3 ] in
            let msname = match opci with | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms) -> ms#name | _ -> "?" in
            let cn = match opci with
              | OpInvokeVirtual (TClass cn,_) | OpInvokeInterface (cn,_) -> cn#simple_name
              | _ -> "?" in
            let p = LBLOCK [ STR cn ; STR "." ; STR msname ; STR "(" ; bc_value_to_pretty arg1 ; STR "," ;
                             bc_value_to_pretty arg2 ; STR ", _)" ] in
            let _ = add_interesting "vtbl" p in
            Some (BcpAction [ action1 ; action2 ; BcWrapCall call ])

         | l -> begin addtolog l ; None end

          (* -------------------------------------------------------------- 21 instrs -- *)
              
       else if maxmatch >= 21 && opcodes#instr_count = 21 then
         match instrs with

         | [ opc1 ; opc2 ; testopc ; opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ;
             opc10 ; opc11 ; opc12 ; opc13 ; OpReturn _ ; OpStore _ ;
             (OpLoad (_,n1) as opc14) ; opc15 ; OpPop ; OpLoad (_,n2) ; OpThrow ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && has_one_exception_caught
                   && has_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ]
                   && is_value [] [ opc10 ; opc11 ; opc12 ; opc13 ] && is_object_value [] [ opc14 ; opc15 ]
                   && n1 = n2 ->
            let exn = get_exception_handled () in
            let testv = get_value [] [ opc1 ; opc2 ] in
            let actions = get_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ] in
            let condaction = BcConditionalAction ([testopc], [testv], actions,[]) in
            let returnv = get_value [] [ opc10 ; opc11 ; opc12 ; opc13 ] in
            let throwv = get_object_value [] [ opc14 ; opc15 ] in
            Some (BcpResultExceptThrow (exn, [ condaction ], returnv, throwv))

         | [ opc1 ; opc2 ; testopc ; opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ;
             opc10 ; opc11 ; opc12 ; OpGoto 11 ; OpStore _ ;
             (OpLoad (_,n1) as opc13) ; opc14 ; OpPop ; OpLoad (_,n2) ; OpThrow ; OpReturn Void ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && has_one_exception_caught
                   && has_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ]
                   && has_actions_partition [] [ opc10 ; opc11 ; opc12 ]
                   && is_object_value [] [ opc13 ; opc14 ]
                   && n1 = n2 ->
            let exn = get_exception_handled () in
            let testv = get_value [] [ opc1 ; opc2 ] in
            let actions = get_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ] in
            let condaction = BcConditionalAction ([testopc], [testv], actions,[]) in
            let actionv = get_actions_partition [] [ opc10 ; opc11 ; opc12 ] in
            let throwv = get_object_value [] [ opc13 ; opc14 ] in
            Some (BcpActionExceptThrow (exn, [ condaction ] @ actionv , throwv))

         | l -> begin addtolog l ; None end


          (* -------------------------------------------------------------- 22 instrs -- *)
              
       else if maxmatch >= 22 && opcodes#instr_count = 22 then
         match instrs with

         | [ opc1 ; opc2 ; testopc ; opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ;
             opc10 ; opc11 ; opc12 ; opc13 ; opc14 ; OpReturn _ ; OpStore _ ;
             (OpLoad (_,n1) as opc15) ; opc16 ; OpPop ; OpLoad (_,n2) ; OpThrow ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && has_one_exception_caught
                   && has_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ]
                   && is_value [] [ opc10 ; opc11 ; opc12 ; opc13 ; opc14 ]
                   && is_object_value [] [ opc15 ; opc16 ]
                   && n1 = n2 ->
            let exn = get_exception_handled () in
            let testv = get_value [] [ opc1 ; opc2 ] in
            let actions = get_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ] in
            let condaction = BcConditionalAction ([testopc], [testv], actions,[]) in
            let returnv = get_value [] [ opc10 ; opc11 ; opc12 ; opc13 ; opc14 ] in
            let throwv = get_object_value [] [ opc15 ; opc16 ] in
            Some (BcpResultExceptThrow (exn, [ condaction ], returnv, throwv))

         | [ opc1 ; opc2 ; testopc ; opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ;
             opc10 ; opc11 ; opc12 ; opc13 ; OpGoto 11 ; OpStore _ ;
             (OpLoad (_,n1) as opc14) ; opc15 ; OpPop ; OpLoad (_,n2) ; OpThrow ; OpReturn Void ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && has_one_exception_caught
                   && has_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ]
                   && has_actions_partition [] [ opc10 ; opc11 ; opc12 ; opc13 ]
                   && is_object_value [] [ opc14 ; opc15 ]
                   && n1 = n2 ->
            let exn = get_exception_handled () in
            let testv = get_value [] [ opc1 ; opc2 ] in
            let actions = get_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ] in
            let condaction = BcConditionalAction ([testopc], [testv], actions,[]) in
            let actionv = get_actions_partition [] [ opc10 ; opc11 ; opc12 ; opc13 ] in
            let throwv = get_object_value [] [ opc14 ; opc15 ] in
            Some (BcpActionExceptThrow (exn, [ condaction ] @ actionv , throwv))

         | l -> begin addtolog l ; None end

          (* -------------------------------------------------------------- 23 instrs -- *)
              
       else if maxmatch >= 23 && opcodes#instr_count = 23 then
         match instrs with

         | [ opc1 ; opc2 ; testopc ; opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ;
             opc10 ; opc11 ; opc12 ; opc13 ; opc14 ; (OpGoto 11 | OpGoto 14) ; OpStore _ ;
             (OpLoad (_,n1) as opc15) ; opc16 ; OpPop ; OpLoad (_,n2) ; OpThrow ; OpReturn Void ]
              when is_value [] [ opc1 ; opc2 ] && is_test_opcode testopc
                   && has_one_exception_caught
                   && has_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ]
                   && has_actions_partition [] [ opc10 ; opc11 ; opc12 ; opc13 ; opc14 ]
                   && is_object_value [] [ opc15 ; opc16 ]
                   && n1 = n2 ->
            let exn = get_exception_handled () in
            let testv = get_value [] [ opc1 ; opc2 ] in
            let actions = get_actions_partition [] [ opc3 ; opc4 ; opc5 ; opc6 ; opc7 ; opc8 ; opc9 ] in
            let condaction = BcConditionalAction ([testopc], [testv], actions,[]) in
            let actionv = get_actions_partition [] [ opc10 ; opc11 ; opc12 ; opc13 ; opc14 ] in
            let throwv = get_object_value [] [ opc15 ; opc16 ] in
            Some (BcpActionExceptThrow (exn, [ condaction ] @ actionv , throwv))

         | [ opc1 ; opc2 ; OpDup ; opc3 ; opc4 ; OpArrayStore t1 ; OpStore (_,n1) ;
             opc5 ; opc6 ; OpDup ; opc7 ; OpLoad (_,n2) ; OpArrayStore t2 ; OpStore (_,n3) ;
             OpLoad (_,0) ; opc8 ; opc9 ; OpLoad (_,n4) ; opci ;
             OpLoad (_,n5) ; opc10 ; OpArrayLoad t3 ; OpReturn _ ]
              when is_object_value [] [ opc1 ; opc2 ] && is_basic_value_opc [] opc3
                   && is_value_opc [] opc4 && n1 = n2 && n3 = n4 && n1 = n5
                   && is_object_value [] [ opc5 ; opc6 ] && is_basic_value_opc [] opc7
                   && is_value_opc [] opc8 && is_value_opc [] opc9
                   && is_basic_value_opc [] opc10
                   && (match opci with OpInvokeVirtual _ | OpInvokeInterface _ -> true | _ -> false) ->
            let base1 = get_object_value [] [ opc1 ; opc2 ] in
            let index1 = get_basic_value_opc [] opc3 in
            let aval1 = get_value_opc [] opc4 in
            let action1 = BcArrayStore (t1, base1, index1, aval1) in
            let base2 = get_object_value [] [ opc5 ; opc6 ] in
            let index2 = get_basic_value_opc [] opc7 in
            let aval2 = BcObject base1 in
            let action2 = BcArrayStore (t2, base2, index2, aval2) in
            let arg1 = get_value_opc [] opc8 in
            let arg2 = get_value_opc [] opc9 in
            let arg3 = BcObject base2 in 
            let call = mkobjectcall (BcoArg 0) opci [ arg1 ; arg2 ; arg3 ] in
            let index3 = get_basic_value_opc [] opc10 in
            let returnv = BcObject (BcoArrayElement (t3,base1,index3)) in
            let msname = match opci with | OpInvokeVirtual (_,ms) | OpInvokeInterface (_,ms) -> ms#name | _ -> "?" in
            let cn = match opci with
              | OpInvokeVirtual (TClass cn,_) | OpInvokeInterface (cn,_) -> cn#simple_name
              | _ -> "?" in
            let p = LBLOCK [ STR cn ; STR "." ; STR msname ; STR "(" ; bc_value_to_pretty arg1 ; STR "," ;
                             bc_value_to_pretty arg2 ; STR ", _)" ] in
            let _ = add_interesting "vtbl" p in
            Some (BcpResult ([ action1 ; action2 ; BcWrapCall call ],returnv))

         | l -> begin addtolog l ; None end

       else if opcodes#instr_count <= maxmatch then
         begin addtolog instrs ; None end

       else
         None
