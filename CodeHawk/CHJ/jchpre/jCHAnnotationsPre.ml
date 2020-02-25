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

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI

let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p

let get_varname mInfo varindex pc =
  if mInfo#has_local_variable_name varindex pc then
    mInfo#get_local_variable_name varindex pc 
  else
    "var" ^ (string_of_int varindex)


let get_stack_top_slot mInfo pc =
  (mInfo#get_method_stack_layout#get_stack_layout pc)#get_top_slot

let get_stack_top_slots mInfo pc n =
  (mInfo#get_method_stack_layout#get_stack_layout pc)#get_top_slots n

let is_boolean_type slot =
  match slot#get_type with [ TBasic Bool ] -> true | _ -> false

let rec get_static_call_value mInfo pc cn ms =
  match (cn#name, ms#name) with
  | ("java.lang.Character", "isDigit") ->
    "isDigit(" ^ (get_slot_value mInfo pc (get_stack_top_slot mInfo pc)) ^ ")"
  | ("java.lang.Character", "isLetter") ->
    "isLetter(" ^ (get_slot_value mInfo pc (get_stack_top_slot mInfo pc)) ^ ")"
  | ("java.lang.Character", "valueOf") ->
    "valueOf("^ (get_slot_value mInfo pc (get_stack_top_slot mInfo pc)) ^ ")"
  | _ -> 
    let nArgs = List.length ms#descriptor#arguments in
    let slots = get_stack_top_slots mInfo pc nArgs in
    let argslots = List.rev slots in
    let argsv =
      let rec aux slots =
	match slots with
	| [] -> ""
	| [ s ] -> get_slot_value mInfo pc s
	| s::tl -> (get_slot_value mInfo pc s) ^ "," ^ (aux tl) in
      aux argslots in
    cn#abbreviated_name ^ "." ^ ms#name ^ "(" ^ argsv ^ ")"	

and get_dynamic_call_value mInfo pc bmindex ms =
  let nArgs = List.length ms#descriptor#arguments in
  let slots = get_stack_top_slots mInfo pc nArgs in
    let argslots = List.rev slots in
    let argsv =
      let rec aux slots =
	match slots with
	| [] -> ""
	| [ s ] -> get_slot_value mInfo pc s
	| s::tl -> (get_slot_value mInfo pc s) ^ "," ^ (aux tl) in
      aux argslots in
    "bootstrapmethod_" ^ (string_of_int bmindex) ^  "." ^ ms#name ^ "(" ^ argsv ^ ")"

and get_dynamic_call_lambda_value mInfo pc ms lfot lfms =
  let nArgs = List.length ms#descriptor#arguments in
  let slots = get_stack_top_slots mInfo pc nArgs in
    let argslots = List.rev slots in
    let argsv =
      let rec aux slots =
	match slots with
	| [] -> ""
	| [ s ] -> get_slot_value mInfo pc s
	| s::tl -> (get_slot_value mInfo pc s) ^ "," ^ (aux tl) in
      aux argslots in
    "lambdafn:" ^ ms#name ^ "(" ^ argsv ^ "):" ^ (pp_str (object_type_to_pretty lfot))
    ^ "." ^ lfms#to_string
    

and get_special_call_value mInfo pc cn ms =
  if ms#name = "<init>" then
    let nArgs = List.length ms#descriptor#arguments in
    let slots = get_stack_top_slots mInfo pc (nArgs + 1) in
    let args = 
      let rec aux slots =
	match slots with
	| [] -> ""
	| [ s ] -> ""
	| [ s1 ; s2 ] -> get_slot_value mInfo pc s1
	| s::tl -> (get_slot_value mInfo pc s) ^ "," ^ (aux tl) in
      aux slots in
    "new " ^ cn#abbreviated_name ^ "(" ^ args ^ ")"
  else
    let nArgs = List.length ms#descriptor#arguments in
    let slots = get_stack_top_slots mInfo pc (nArgs + 1) in
    let args = 
      let rec aux slots =
	match slots with
	| [] -> ""
	| [ s ] -> ""
	| [ s1 ; s2 ] -> get_slot_value mInfo pc s1
	| s::tl -> (get_slot_value mInfo pc s) ^ "," ^ (aux tl) in
      aux slots in
    ms#name ^ "(" ^ args ^ ")"


and get_virtual_call_value mInfo pc ob ms =
  match ob with
  | TClass cn ->
    begin
      match (cn#name, ms#name) with
      | ("java.lang.StringBuilder", "append") ->
	let topslots = get_stack_top_slots mInfo pc 2 in 
	"append(" ^
	  (get_slot_value mInfo pc (List.nth topslots 0)) ^ "," ^
	     (get_slot_value mInfo pc (List.nth topslots 1)) ^ ")"
      | (_,"toString") ->
	(get_slot_value mInfo pc (get_stack_top_slot mInfo pc)) ^ ".toString()"
      | _ -> 
	let nArgs = List.length ms#descriptor#arguments in
	let slots = get_stack_top_slots mInfo pc (nArgs + 1) in
	let tgtslot = List.hd (List.rev slots) in
	let argslots = List.tl (List.rev slots) in
	let tgtv = get_slot_value mInfo pc tgtslot in
	let argsv =
	  let rec aux slots =
	    match slots with
	    | [] -> ""
	    | [ s ] -> get_slot_value mInfo pc s
	    | s::tl -> (get_slot_value mInfo pc s) ^ "," ^ (aux tl) in
	  aux argslots in
	tgtv ^ "." ^ ms#name ^ "(" ^ argsv ^ ")"	
    end
  | _ -> "??"
		     
and get_interface_call_value mInfo pc cn ms =
  let nArgs = List.length ms#descriptor#arguments in
  let slots = get_stack_top_slots mInfo pc (nArgs + 1) in
  let tgtslot = List.hd (List.rev slots) in
  let argslots = List.tl (List.rev slots) in
  let tgtv = get_slot_value mInfo pc tgtslot in
  let argsv =
    let rec aux slots =
      match slots with
      | [] -> ""
      | [ s ] -> get_slot_value mInfo pc s 
      | s :: tl -> (get_slot_value mInfo pc s) ^ "," ^ (aux tl) in
    aux argslots in
  tgtv ^ "." ^ ms#name ^ "(" ^ argsv ^ ")"

and get_slot_src_value mInfo pc slot =
  let cInfo = app#get_class mInfo#get_class_name in
  match slot#get_sources with
  | [ opSrc ] when opSrc = -1 -> "exn object"
  | [ opSrc ] ->
    begin
      let tsv () = get_slot_value mInfo opSrc (get_stack_top_slot mInfo opSrc) in
      let ts2v () =
	let topslots = get_stack_top_slots mInfo opSrc 2 in
	let topslot = List.nth topslots 0 in
	let sndslot = List.nth topslots 1 in
	let sv1 = get_slot_value mInfo opSrc sndslot in
	let sv2 = get_slot_value mInfo opSrc topslot in
	(sv1,sv2) in
      match mInfo#get_opcode opSrc with
      | OpAConstNull -> "null"
      | OpIntConst i32 -> Int32.to_string i32
      | OpLongConst i64 -> Int64.to_string i64
      | OpDoubleConst f -> string_of_float f
      | OpFloatConst f -> string_of_float f
      | OpByteConst i -> string_of_int i
      | OpShortConst i -> string_of_int i
      | OpStringConst s -> "\"" ^ s ^ "\""
      | OpClassConst (TClass cn) -> cn#name
      | OpInstanceOf t ->
	"(" ^ (tsv ()) ^ " instanceof " ^ (object_type_to_string t) ^")"
      | OpLoad (_,i) -> get_varname mInfo i pc 
      | OpI2C -> "i2c(" ^ (tsv ()) ^ ")"
      | OpI2L -> "i2l(" ^ (tsv ()) ^ ")"
      | OpI2F -> "i2f(" ^ (tsv ()) ^ ")"
      | OpI2D -> "i2d(" ^ (tsv ()) ^ ")"
      | OpL2D -> "l2d(" ^ (tsv ()) ^ ")"
      | OpL2I -> "l2i(" ^ (tsv ()) ^ ")"
      | OpL2F -> "l2f(" ^ (tsv ()) ^ ")"
      | OpF2I -> "f2i(" ^ (tsv ()) ^ ")"
      | OpF2L -> "f2l(" ^ (tsv ()) ^ ")"
      | OpF2D -> "f2d(" ^ (tsv ()) ^ ")"
      | OpD2I -> "d2i(" ^ (tsv ()) ^ ")"
      | OpD2L -> "d2l(" ^ (tsv ()) ^ ")"
      | OpD2F -> "d2f(" ^ (tsv ()) ^ ")"
      | OpI2B -> "i2b(" ^ (tsv ()) ^ ")"
      | OpI2S -> "i2s(" ^ (tsv ()) ^ ")"
      | OpAdd _ -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " + " ^ sv2 ^ ")"
      | OpSub _ -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " - " ^ sv2 ^ ")"
      | OpMult _ -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " * " ^ sv2 ^ ")"
      | OpDiv _ -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " / " ^ sv2 ^ ")"
      | OpRem _ -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " % " ^ sv2 ^ ")"
      | OpNeg _ -> " -(" ^ tsv () ^ ")"
      | OpIAnd | OpLAnd -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " && " ^ sv2 ^ ")"
      | OpIOr | OpLOr -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " || " ^ sv2 ^ ")"
      | OpIXor | OpLXor -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " ^ " ^ sv2 ^ ")"
      | OpIShl -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " << " ^ sv2 ^ ")"
      | OpLShr -> let (sv1,sv2) = ts2v () in "(" ^ sv1 ^ " >> " ^ sv2 ^ ")"
      | OpDup -> tsv ()
      | OpDupX1 -> tsv ()
      | OpNew cn -> "new " ^ cn#abbreviated_name
      | OpNewArray (TBasic ty) -> 
	"new " ^ (java_basic_type_to_string ty) ^ "[" ^	(tsv ()) ^ "]"
      | OpNewArray (TObject (TClass cn)) -> "new " ^ cn#abbreviated_name  ^ "[" ^ (tsv ()) ^ "]"
      | OpArrayLength -> "arraylength(" ^ (tsv ()) ^ ")" 
      | OpArrayLoad _ -> let (sv1,sv2) = ts2v () in sv1 ^ "[" ^ sv2 ^ "]"
      | OpCmpL -> let (sv1,sv2) = ts2v() in "cmpl(" ^ sv1 ^ ", " ^ sv2 ^ ")"
      | OpCmpFL -> let (sv1,sv2) = ts2v() in "cmpfl(" ^ sv1 ^ ", " ^ sv2 ^ ")"
      | OpCmpFG -> let (sv1,sv2) = ts2v() in "cmpfg(" ^ sv1 ^ ", " ^ sv2 ^ ")"
      | OpCmpDL -> let (sv1,sv2) = ts2v() in "cmpdl(" ^ sv1 ^ ", " ^ sv2 ^ ")"
      | OpCmpDG -> let (sv1,sv2) = ts2v() in "cmpdg(" ^ sv1 ^ ", " ^ sv2 ^ ")"
      | OpGetStatic (cn,fs) -> "field(" ^ cn#abbreviated_name ^ "." ^ fs#name ^ ")"
      | OpGetField (cn,fs) -> (tsv ()) ^ "." ^ fs#name
      | OpInvokeStatic (cn,ms) -> get_static_call_value mInfo opSrc cn ms
      | OpInvokeVirtual (ob,ms) -> get_virtual_call_value mInfo opSrc ob ms
      | OpInvokeSpecial (cn,ms) -> get_special_call_value mInfo opSrc cn ms
      | OpInvokeInterface (cn,ms) -> get_interface_call_value mInfo opSrc cn ms
      | OpInvokeDynamic (bmindex,ms) when cInfo#returns_lambda_function bmindex ->
         let (lfot,lfms) = cInfo#get_lambda_function bmindex in
         "lambdafn:" ^ lfms#name
      | OpInvokeDynamic (bmindex,ms) ->
         "bootstrapmethod_" ^ (string_of_int bmindex) ^ "_invoke_return"
      | _ -> "??" ^ (string_of_int opSrc) ^ "??"
    end
  | [ opSrc1 ; opSrc2 ] -> "2 sources: " ^ (string_of_int opSrc1) ^ " and " ^
    (string_of_int opSrc2)
  | _ ->  "??" ^ "no-src" ^ "??"

and get_slot_value mInfo pc slot =
(*   if slot#has_value then 
    match slot#get_value with
    | IntValueRange (Some low,Some high) when low = high -> string_of_int low
    | ObjectValue s -> (try (make_cn s)#abbreviated_name with _ -> s)
    | _ -> get_slot_src_value mInfo pc slot
  else *) get_slot_src_value mInfo pc slot


let opcode_annotation (mInfo:method_info_int) (pc:int) (opc:opcode_t) =
  let cInfo = app#get_class mInfo#get_class_name in
  let tsv () = get_slot_value mInfo pc (get_stack_top_slot mInfo pc) in
  let ts2v () =
    let topslots = get_stack_top_slots mInfo pc 2 in
    let topslot = List.nth topslots 0 in
    let sndslot = List.nth topslots 1 in
    let sv1 = get_slot_value mInfo pc sndslot in
    let sv2 = get_slot_value mInfo pc topslot in
    (sv1,sv2) in
  let cmps pred offset = 
    let topslots = get_stack_top_slots mInfo pc 2 in
    let topslot = List.nth topslots 0 in
    let sndslot = List.nth topslots 1 in
    LBLOCK [ STR "if " ; STR (get_slot_value mInfo pc sndslot) ; STR pred ;
	     STR (get_slot_value mInfo pc topslot) ; STR " then goto " ; 
	     INT (pc + offset) ] in
  let cmpz pred offset =
    let topslot = get_stack_top_slot mInfo pc in
    LBLOCK [ STR "if " ; STR (get_slot_value mInfo pc topslot) ; STR pred ; INT 0 ;
	     STR " then goto " ; INT (pc + offset) ] in
  try
    match opc with
    | OpIInc (v,1) -> LBLOCK [ STR (get_varname mInfo v pc) ; STR "++" ]
    | OpIInc (v,inc) -> LBLOCK [ STR (get_varname mInfo v pc) ; STR " += " ; INT inc ]
    | OpIfCmpNe offset | OpIfCmpANe offset -> cmps " != " offset
    | OpIfCmpEq offset | OpIfCmpAEq offset -> cmps " == " offset
    | OpIfCmpLt offset -> cmps " < " offset
    | OpIfCmpLe offset -> cmps " <= " offset
    | OpIfCmpGt offset -> cmps " > " offset
    | OpIfCmpGe offset -> cmps " >= " offset
    | OpIfEq offset -> cmpz " == " offset
    | OpIfNe offset -> cmpz " != " offset
    | OpIfLt offset -> cmpz " < " offset
    | OpIfLe offset -> cmpz " <= " offset
    | OpIfGt offset -> cmpz " > " offset
    | OpIfGe offset -> cmpz " >= " offset
    | OpIfNonNull offset ->
      LBLOCK [ STR "if nonnull(" ; STR (tsv ()) ; STR ") then goto " ; INT (pc + offset) ]
    | OpIfNull offset ->
      LBLOCK [ STR "if null(" ; STR (tsv ()) ; STR ") then goto " ; INT (pc + offset) ]
    | OpPutStatic (cn,fs) -> STR (cn#abbreviated_name ^ "." ^ fs#name ^ " := " ^ (tsv ()))
    | OpPutField (cn,fs) -> 
      let (sv1,sv2) = ts2v () in STR (sv1 ^ "." ^ fs#name ^ " := " ^ sv2)
    | OpInvokeVirtual (ob,ms) -> LBLOCK [ STR (get_virtual_call_value mInfo pc ob ms) ]
    | OpInvokeSpecial (cn,ms) -> LBLOCK [ STR (get_special_call_value mInfo pc cn ms) ]
    | OpInvokeStatic (cn,ms) -> LBLOCK [ STR (get_static_call_value mInfo pc cn ms) ]
    | OpInvokeDynamic (bmindex,ms) when cInfo#returns_lambda_function bmindex ->
       let (lfot,lfms) = cInfo#get_lambda_function bmindex in
       LBLOCK [ STR (get_dynamic_call_lambda_value mInfo pc ms lfot lfms) ]
    | OpInvokeDynamic (bmindex,ms) ->
       LBLOCK [ STR (get_dynamic_call_value mInfo pc bmindex ms) ]
    | OpStore (_,v) -> 
      LBLOCK [ STR (get_varname mInfo v (mInfo#get_next_bytecode_offset pc)) ; 
	       STR  " := " ;
	       STR (get_slot_value mInfo pc (get_stack_top_slot mInfo pc)) ]
(*    | OpPutStatic (cn,fs) ->
      LBLOCK [ STR "field(" ; STR cn#abbreviated_name ; STR "." ; STR fs#name ; STR ") := " ;
	       STR (get_slot_value mInfo pc (get_stack_top_slot mInfo pc)) ]  *)
    | OpTableSwitch (default,_,_,table) ->
      let tgts = Array.to_list (Array.mapi (fun i v -> (string_of_int (i+1),pc+v)) table) in
      let tgts = ("default",pc+default) :: tgts in
      pretty_print_list tgts (fun (v,tgt) -> LBLOCK [ STR "(" ; STR v ; STR ":" ; INT tgt ;
						      STR ")" ]) "[" ", " "]"
    | OpLookupSwitch (default,table) ->
      let tgts = List.map (fun (l,tgt) -> (Int32.to_string l, pc+tgt)) table in
      let tgts = ("default",default+pc) :: tgts in
      pretty_print_list tgts (fun (v,tgt) -> LBLOCK [ STR "(" ; STR v ; STR ":" ; INT tgt ;
						      STR ")" ]) "[" ", " "]"
    | _ -> STR ""
  with
  | JCH_failure p -> LBLOCK [ STR "Error: " ; p ]
 
let is_conditional_jump (mInfo:method_info_int) pc =
  match mInfo#get_opcode pc with
  | OpIfCmpNe _ | OpIfCmpEq _ | OpIfCmpLt _ | OpIfCmpLe _ 
  | OpIfCmpAEq _ | OpIfCmpANe _ 
  | OpIfCmpGt _ | OpIfCmpGe _ | OpIfEq _ | OpIfNe _
  | OpIfLt _ | OpIfLe _ | OpIfGt _ | OpIfGe _ 
  | OpIfNull _ | OpIfNonNull _ -> true
  | _ -> false

let is_switch_table (mInfo:method_info_int) pc =
  match mInfo#get_opcode pc with
  | OpTableSwitch _ | OpLookupSwitch _ -> true
  | _ -> false

let get_cfg_tf_annotations (mInfo:method_info_int) pc = 
  let cmps t f =
    let topslots = get_stack_top_slots mInfo pc 2 in
    let topslot = List.nth topslots 0 in
    let sndslot = List.nth topslots 1 in
    let sv1 = get_slot_value mInfo pc sndslot in
    let sv2 = get_slot_value mInfo pc topslot in
    (sv1 ^ t ^ sv2, sv1 ^ f ^ sv2) in
  let cmpz t f =
    let slot = get_stack_top_slot mInfo pc in
    let sv = get_slot_value mInfo pc slot in
    let default () =
      if is_boolean_type slot then
	match t with
	| "==" -> ("!" ^ sv, sv)
	| "!=" -> (sv, "!" ^ sv)
	| _ -> (sv ^ t ^ "0", sv ^ f ^ "0")
      else
	(sv ^ t ^ "0", sv ^ f ^ "0") in
    match slot#get_sources with
    | [ opSrc ] ->
      let ts2v () =
	let topslots = get_stack_top_slots mInfo opSrc 2 in
	let topslot = List.nth topslots 0 in
	let sndslot = List.nth topslots 1 in
	let sv1 = get_slot_value mInfo opSrc sndslot in
	let sv2 = get_slot_value mInfo opSrc topslot in
	(sv1,sv2) in
      (match mInfo#get_opcode opSrc with
      | OpCmpL | OpCmpFL | OpCmpFG | OpCmpDL | OpCmpDG ->
	let (sv1,sv2) = ts2v () in
	(match t with
	| ">=" -> (sv1 ^ " >= " ^ sv2, sv1 ^ " < " ^ sv2)
	| _ -> default ())
      | _ -> default()) 
    | _ -> default () in	
  let isnull t =
    let slot = get_stack_top_slot mInfo pc in
    let sv = get_slot_value mInfo pc slot in
    if t then 
      ("!" ^ sv, sv)
    else
      (sv, "!" ^ sv) in
  match mInfo#get_opcode pc with
  | OpIfCmpNe _ | OpIfCmpANe _ -> cmps "!=" "=="
  | OpIfCmpEq _ | OpIfCmpAEq _ -> cmps "==" "!="
  | OpIfCmpLt _ -> cmps "<" ">="
  | OpIfCmpLe _ -> cmps "<=" ">"
  | OpIfCmpGt _ -> cmps ">" "<="
  | OpIfCmpGe _ -> cmps ">=" "<"
  | OpIfEq _ -> cmpz "==" "!="
  | OpIfNe _ -> cmpz "!=" "=="
  | OpIfLt _ -> cmpz "<" ">="
  | OpIfLe _ -> cmpz "<=" ">"
  | OpIfGt _ -> cmpz ">" "<="
  | OpIfGe _ -> cmpz ">=" "<"
  | OpIfNull _ -> isnull true
  | OpIfNonNull _ -> isnull false
  | _ -> ("true","false")

let get_offset (mInfo:method_info_int) pc =
  match mInfo#get_opcode pc with
  | OpIfCmpNe offset 
  | OpIfCmpEq offset
  | OpIfCmpLt offset
  | OpIfCmpLe offset
  | OpIfCmpGt offset
  | OpIfCmpGe offset
  | OpIfEq offset
  | OpIfNe offset
  | OpIfLt offset 
  | OpIfLe offset
  | OpIfGt offset
  | OpIfGe offset 
  | OpIfCmpAEq offset
  | OpIfCmpANe offset
  | OpIfNull offset
  | OpIfNonNull offset -> offset
  | _ -> 0
  
let get_assignments mInfo varindex startpc endpc =
  let pc_leadsto pc = 
    let vartable = mInfo#get_local_variable_table in
    let ivartable = List.filter (fun (_,_,_,_,i) -> i = varindex) vartable in
    (List.for_all (fun (s,l,_,_,_) -> pc < s || pc > s+l) ivartable) in
  let pc_inrange pc = (pc >= startpc && pc <= endpc) || pc_leadsto pc in
  let result = ref [] in
  begin 
    (mInfo#bytecode_iteri (fun pc opc ->
      match opc with 
      | OpStore (_,i) when varindex = i && pc_inrange pc ->
	result := (pc,opcode_annotation mInfo pc opc) :: !result
      | OpIInc (i,_) when varindex = i && pc_inrange pc ->
	result := (pc,opcode_annotation mInfo pc opc) :: !result
      | _ -> ())) ;
    List.rev !result
  end
