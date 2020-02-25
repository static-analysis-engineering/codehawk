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

(* jchlib *)
open JCHBasicTypesAPI
open JCHJTDictionary
open JCHJTerm

(* jchpre *)
open JCHMethodInfo
open JCHPreAPI

class expression_stack_t (mInfo:method_info_int) (stacklayout:method_stack_layout_int) =
object (self)

  method get_pc_stacklayout (pc:int) =
    stacklayout#get_stack_layout pc 

  method get_pc_stackslot (pc:int) (n:int) =
    if n = 1 then
      (self#get_pc_stacklayout pc)#get_top_slot
    else
      let slots = (self#get_pc_stacklayout pc)#get_top_slots n in
      List.nth slots (n-1)

  method get_slot_value (pc:int) (n:int):jterm_t option =
    let slot = self#get_pc_stackslot pc n in
    if slot#has_value then
      slot#get_value#to_jterm
    else
      match slot#get_sources with
      | [ opSrc ] when opSrc = -1 -> None
      | [ opSrc ] ->
	(match mInfo#get_opcode opSrc with
	| OpIntConst i32 -> Some (JConstant (mkNumerical (Int32.to_int i32)))
	| OpLongConst i64 -> Some (JConstant (mkNumerical (Int64.to_int i64)))
	| _ -> None)
      | _ -> None

  method get_slot_value_string_length (pc:int) (n:int):jterm_t option =
    let slot = self#get_pc_stackslot pc n in
    let mk_jterm s = Some (JConstant (mkNumerical (String.length s))) in
    let get_string_length () =
      match slot#get_sources with
      | [ opSrc ] when opSrc = -1 -> None
      | [ opSrc ] ->
         (match mInfo#get_opcode opSrc with
          | OpStringConst s -> mk_jterm s
          | _ -> None)
      | _ -> None in
    if slot#has_value then
      match slot#get_value#to_jterm with
      | Some (JStringConstant s) -> mk_jterm s
      | _ -> get_string_length ()
    else
      get_string_length ()
    
end
  
let rec instantiate_stack_values
          (mInfo:method_info_int) (pc:int) (c:jterm_range_int) (defaults:(int * int) list) =
  let cms = mInfo#get_class_method_signature in
  let xstack = new expression_stack_t mInfo mInfo#get_method_stack_layout in
  let substitute jt newjt =
    match newjt with
    | Some t -> t
    | _ ->
       let jtix = jtdictionary#index_jterm jt in
       if List.exists (fun (k,_) -> jtix = k) defaults then
         let (_,defaultvalue) = List.find (fun (k,_) -> jtix = k) defaults in
         let _ = chlog#add "use library method default value"
                           (LBLOCK [ cms#toPretty ; STR "; pc = " ; INT pc ;
                                     STR "; default value: " ; INT defaultvalue ]) in
         JConstant (mkNumerical defaultvalue)
       else
        jt in
  let rec evaluate jt =
    match jt with
    | JLocalVar i -> substitute jt (xstack#get_slot_value pc (i+1))
    | JArithmeticExpr (op,jt1,jt2) -> JArithmeticExpr (op, evaluate jt1, evaluate jt2)
    | _ -> jt in
  let lbounds = List.map evaluate c#get_lowerbounds in
  let ubounds = List.map evaluate c#get_upperbounds in
  mk_jterm_range lbounds ubounds

