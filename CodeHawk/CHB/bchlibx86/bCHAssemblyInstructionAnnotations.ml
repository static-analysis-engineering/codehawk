(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHBounds
open CHPretty
open CHNumerical
open CHLanguage

(* chutil *)
open CHLogger
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify

(* bchlib *)
open BCHFtsParameter
open BCHAssemblyInstructions
open BCHBasicTypes
open BCHCallTarget
open BCHConstantDefinitions
open BCHCPURegisters
open BCHDemangler
open BCHDoubleword
open BCHFloc
open BCHFunctionInterface
open BCHFunctionInfo
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHMemoryReference
open BCHStrings
open BCHSystemInfo
open BCHVariable
open BCHVariableNames
open BCHVariableType
   
(* bchlibx86 *)
open BCHConditionalJumpExpr
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHOperand
open BCHPredefinedCallSemantics
open BCHX86OpcodeRecords
   
module B = Big_int_Z
module FFU = BCHFileFormatUtil
module TR = CHTraceResult


let sym_printer = (fun s -> STR s#getBaseName)


class assembly_instruction_annotation_t 
  (annotation_type:assembly_instruction_annotation_type_t) (annotation:pretty_t) =
object
  method get_annotation_type = annotation_type
  method toPretty = annotation
end

let check_range ?low ?high (msg:pretty_t) value =
  let returnValue = ref value in
  begin
    (match low with
     | Some low ->
        if value < low then
	  begin
            ch_error_log#add "range error" msg;
            returnValue := low
          end
        else ()
     | _ -> ());
    (match high with
     | Some high ->
        if value > high then
	  begin
            ch_error_log#add "range error" msg;
            returnValue := high
          end
        else ()
     | _ -> ());
    !returnValue
  end


let no_annotation =
  new assembly_instruction_annotation_t NoAnnotation (STR "")


let make_annotation (annotationType:assembly_instruction_annotation_type_t)
    (annotation:pretty_t) =
  new assembly_instruction_annotation_t annotationType annotation


let get_lhs (op:operand_int) floc = op#to_variable floc 


let get_rhs (op:operand_int) floc = op#to_expr floc


let create_annotation_aux (floc:floc_int) =
  (* let invio = floc#f#finv in *)
  let env:function_environment_int = floc#f#env in 
  let instr = !assembly_instructions#at_address floc#ia in
  let variable_to_pretty = env#variable_name_to_pretty in
  let xpr_formatter = make_xpr_formatter sym_printer variable_to_pretty in
  let pr_expr ?(typespec=None) ?(partype=t_unknown) x = 
    let x = simplify_xpr x in
    match get_xpr_symbolic_name ~typespec x with
    | Some name -> STR name
    | _ -> 
      if is_unsigned partype then
	match get_const x with
	| Some num -> (TR.tget_ok (numerical_to_doubleword num))#toPretty
	| _ ->  xpr_formatter#pr_expr x 
      else
	xpr_formatter#pr_expr x in
  let pr_argument_expr ?(typespec=None) (p: fts_parameter_t) (xpr: xpr_t) =
    let is_code_address n = 
      try system_info#is_code_address
            (TR.tget_ok (numerical_to_doubleword n)) with
	Invalid_argument _ -> false in
    match get_string_reference floc xpr with 
    | Some s ->  STR ("\"" ^ s ^ "\"") 
    | _ ->
      match xpr with
      | XVar v when env#is_bridge_value v -> STR "?" 
      | XVar v -> variable_to_pretty v
      | XConst (IntConst n) when is_code_address n ->
	LBLOCK [STR "fp:"; (TR.tget_ok (numerical_to_doubleword n))#toPretty]
      | XConst (IntConst n) when FFU.is_image_address n ->
	LBLOCK [STR "ds:"; (TR.tget_ok (numerical_to_doubleword n))#toPretty]
      | _ -> 
	if floc#is_address xpr then
	  let (memref,memoffset) = floc#decompose_address xpr in
	  if is_constant_offset memoffset then
            let offset = get_total_constant_offset memoffset in
	    LBLOCK [
                STR "&";
                variable_to_pretty (env#mk_memory_variable memref offset)]
	  else if memref#is_unknown_reference then
	    pr_expr xpr
	  else
	    memref#toPretty
	  else
	    pr_expr ~typespec ~partype:p.apar_type xpr in
  let pr_sum_argument_expr
        (ct: call_target_info_int) (p: fts_parameter_t) (xpr: xpr_t) =
    let typespec = ct#get_enum_type p in
    match get_xpr_symbolic_name ~typespec xpr with
    | Some name -> STR name
    | _ -> pr_argument_expr ~typespec p  xpr in
  let lhs_to_pretty (lhs_op:operand_int) (var:variable_t) = 
    if env#is_unknown_memory_variable var || var#isTmp then
      STR "?"
    else
      variable_to_pretty var in
  
  let rhs_to_pretty ?(partype=t_unknown) (xpr:xpr_t) =
    if is_random xpr then STR " ? " else
      match xpr with 
      | XVar v when env#is_unknown_memory_variable v || v#isTmp -> 
	LBLOCK [ STR " ?  (" ; pr_expr xpr ; STR ")" ] 
      | _ -> pr_expr ~partype xpr in

  let rewrite_expr_pretty (expr:xpr_t) =
    let newExpr = floc#inv#rewrite_expr expr env#get_variable_comparator in
    if syntactically_equal expr newExpr then STR "" else 
      LBLOCK [ STR  " = " ; pr_expr newExpr ]  in
  
  let rewrite_expr (expr:xpr_t) = 
    floc#inv#rewrite_expr expr (env#get_variable_comparator) in

  let packed_operation_annotation (floc:floc_int) (name:string) (dst:operand_int) =
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [ STR "packed op:" ; STR name ; STR " (abstract " ; 
		      lhs_to_pretty dst lhs ; STR ")" ] in
    make_annotation NotModeled pp in
  
  match instr#get_opcode with
  | Jcc (_, op) when system_info#is_fixed_true_branch floc#l#i ->
    if op#is_absolute_address then
      let pp = LBLOCK [ STR "goto " ; STR op#get_absolute_address#to_hex_string ;
			STR " (guaranteed true)" ] in
      make_annotation (Jump op#get_absolute_address) pp
    else
      no_annotation
  | Jecxz op 
  | Jcc (_, op) ->
    if op#is_absolute_address then
      if floc#has_test_expr then
	let testExpr = floc#get_test_expr in
	let pp =
          LBLOCK [
              STR "if ";
              xpr_formatter#pr_expr testExpr;
              STR " then goto ";
	      STR op#get_absolute_address#to_hex_string] in
	make_annotation (Jump op#get_absolute_address) pp
      else
	let pp =
          LBLOCK [
              STR "if ? then goto ";
	      STR op#get_absolute_address#to_hex_string] in
	make_annotation (Jump op#get_absolute_address) pp
    else
      no_annotation
	
  | Lea (dst, src) ->
    let rhs = src#to_address floc in
    let lhs = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty rhs in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; 
		      rhs_to_pretty rhs ; rewritten ] in
    make_annotation Assignment pp
      
  | Mov (_, dst, src) when dst#equal src -> make_annotation Assignment (STR "nop")
    
  | Mov ( _, _,src) when src#is_function_argument ->
    let (callSite, argIndex) = src#get_function_argument in
    let callSiteFloc = get_floc (ctxt_string_to_location floc#fa callSite) in
    if callSiteFloc#has_call_target
       && callSiteFloc#get_call_target#is_signature_valid then
      let fintf = callSiteFloc#get_call_target#get_function_interface in
      let functionName = fintf.fintf_name in
      let param = 
	try
	  get_stack_parameter fintf argIndex
	with
	  BCH_failure p ->
	    begin
	      ch_error_log#add
                "number of arguments"
		(LBLOCK [
                     floc#l#toPretty;
                     STR ": ";
                     STR functionName;
                     STR ": ";
                     p]) ;
	      mk_stack_parameter argIndex ;
	    end in
      let rhs = get_rhs src floc in
      let rhs_pp = match get_string_reference floc rhs with 
	| Some s -> STR s
	| _ -> 
	  match get_xpr_symbolic_name rhs with
	  | Some name -> STR name 
	  | _ -> rhs_to_pretty ~partype:param.apar_type rhs in
      make_annotation FunctionArgument 
	(LBLOCK [
             STR "[";
             STR functionName;
             STR " : ";
	     STR param.apar_name;
             STR " = ";
             rhs_pp;
             STR " ]"])
    else
      no_annotation

  | Mov (_, dst, src) when src#is_immediate_value ->
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; 
		      STR src#get_immediate_value#to_string ] in
    make_annotation Assignment pp
	
  | Mov (_, dst, src) -> 
    let rhs = get_rhs src floc in
    let lhs = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty rhs in
    let pp =
      LBLOCK [
          lhs_to_pretty dst lhs; STR " := "; rhs_to_pretty rhs; rewritten] in
    make_annotation Assignment pp
      
  | Movzx (_, dst, src) ->
    let rhs = get_rhs src floc in
    let lhs = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty rhs in
    let pp =
      LBLOCK [
          lhs_to_pretty dst lhs; STR " := "; rhs_to_pretty rhs; rewritten] in
    make_annotation Assignment pp
      
  | Movsx (_, dst, src) ->
    let rhs = get_rhs src floc in
    let lhs = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty rhs in
    let pp =
      LBLOCK [
          lhs_to_pretty dst lhs; STR " := "; rhs_to_pretty rhs; rewritten] in
    make_annotation Assignment pp
      
  | Movs (width, dst, src,srcptr,dstptr) ->
    let rhs = rewrite_expr (get_rhs src floc) in
    let lhs = get_lhs dst floc in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp =
      LBLOCK [
          STR "(Esi): ";
          rhs_to_pretty rhs;
          STR "; (Edi): ";
	  lhs_to_pretty dst lhs;
	  STR "; Ecx: ";
          rhs_to_pretty ecx;
          STR "; width: ";
          INT width] in
    make_annotation Assignment pp

  | FXmmMove (_,scalar,single,dst,src) ->
    let rhs = rewrite_expr (get_rhs src floc) in
    let lhs = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty rhs in
    let sScalar = if scalar then "scalar" else "packed" in
    let sSingle = if single then "single prec" else "double prec" in
    let pp =
      LBLOCK [
          lhs_to_pretty dst lhs;
          STR " := ";
          rhs_to_pretty rhs;
          rewritten;
	  STR " (";
          STR sScalar;
          STR ", ";
          STR sSingle;
          STR ")"] in
    make_annotation Assignment pp
      
  | Stos (width, dst, src, opedi,opdf) ->
    let rhs = rewrite_expr (get_rhs src floc) in
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [lhs_to_pretty dst lhs; STR " := "; rhs_to_pretty rhs] in
    make_annotation Assignment pp
      
  | RepECmps (width,src1,src2) ->
    let rhs1 = rewrite_expr (get_rhs src1 floc) in
    let rhs2 = rewrite_expr (get_rhs src2 floc) in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Edi):" ; rhs_to_pretty rhs1 ; 
		      STR "; (Edi): " ; rhs_to_pretty rhs2 ;
		      STR "Ecx: " ; rhs_to_pretty ecx ; 
		      STR " (width: " ; INT width ; STR ")" ] in
    make_annotation RepInstruction pp
      
  | RepEScas (width,src) ->
    let rhs = rewrite_expr (get_rhs src floc) in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp =
      LBLOCK [
          STR "(Edi): ";
          rhs_to_pretty rhs;
	  STR "Ecx: ";
          rhs_to_pretty ecx;
          STR " (width: ";
          INT width;
          STR ")"] in
    make_annotation RepInstruction pp
      
  | RepIns (width,dst) ->
    let lhs = get_lhs dst floc in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp =
      LBLOCK [
          STR "(Edi): ";
          lhs_to_pretty dst lhs;
	  STR "Ecx: ";
          rhs_to_pretty ecx;
          STR " (width: ";
          INT width; STR ")"] in
    make_annotation RepInstruction pp
      
  | RepLods (width,src) ->
    let rhs = rewrite_expr (get_rhs src floc) in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Esi): " ; rhs_to_pretty rhs ;
		      STR "Ecx: " ; rhs_to_pretty ecx ; STR " (width: " ; INT width ; STR ")" ] in
    make_annotation RepInstruction pp
      
  | RepMovs (width,dst,src) ->
    let rhs = rewrite_expr (get_rhs src floc) in
    let lhs = get_lhs dst floc in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Esi): " ; rhs_to_pretty rhs; STR "; (Edi): " ; lhs_to_pretty dst lhs ;
		      STR "; Ecx: " ; rhs_to_pretty ecx ; STR " (width: " ; INT width ; STR ")" ] in
    make_annotation RepInstruction pp
      
  | RepNeCmps (width,src1,src2) ->
    let rhs1 = rewrite_expr (get_rhs src1 floc) in
    let rhs2 = rewrite_expr (get_rhs src2 floc) in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Esi): " ; rhs_to_pretty rhs1 ; STR "; (Edi): " ; 
		      rhs_to_pretty rhs2 ;
		      STR "; Ecx: " ; rhs_to_pretty ecx ; STR " (width: " ; 
		      INT width ; STR ")" ] in
    make_annotation RepInstruction pp
      
  | RepNeScas (width, dst) ->
    let rhs = rewrite_expr (get_rhs dst floc) in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Edi): " ; rhs_to_pretty rhs ; 
		      STR "; Ecx: " ; rhs_to_pretty ecx ; STR " (width: " ; 
		      INT width ; STR ")" ] in
    make_annotation RepInstruction pp
      
  | RepOuts (width,src) ->
    let rhs = rewrite_expr (get_rhs src floc) in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Esi): " ; rhs_to_pretty rhs ;
		      STR "Ecx: " ; rhs_to_pretty ecx ; STR " (width: " ;
		      INT width ; STR ")" ] in
    make_annotation RepInstruction pp
      
  | RepStos (width,dst) ->
    let lhs = get_lhs dst floc in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Edi): " ; lhs_to_pretty dst lhs ;
		      STR "; Ecx: " ; rhs_to_pretty ecx ; STR " (width: " ; 
		      INT width ; STR ")" ] in
    make_annotation RepInstruction pp
      
  | XCrypt _ ->
    let rhs = rewrite_expr (get_rhs (ds_esi RD) floc) in
    let lhs = get_lhs (es_edi WR) floc in
    let ecx = rewrite_expr (get_rhs (ecx_r RD) floc) in
    let pp = LBLOCK [ STR "(Esi): " ; rhs_to_pretty rhs ; STR "; (Edi): " ; 
		      lhs_to_pretty (es_edi WR) lhs ; STR "; Ecx: " ; 
		      rhs_to_pretty ecx   ] in
    make_annotation RepInstruction pp
      
  | Xchg (op1, op2) when op1#equal op2 -> make_annotation Assignment (STR "nop")
    
  | Xchg (op1, op2) ->
    let rhs1 = get_rhs op1 floc in
    let lhs2 = get_lhs op2 floc in
    let rhs2 = get_rhs op2 floc in
    let lhs1 = get_lhs op1 floc in
    let pp = LBLOCK [ STR "tmp := " ; rhs_to_pretty rhs2 ; STR "; " ; 
		      lhs_to_pretty op2 lhs2 ; STR " := " ; rhs_to_pretty rhs1 ; STR "; " ;
		      lhs_to_pretty op1 lhs1; STR " := tmp" ] in
    make_annotation Assignment pp

  | Enter (op1,op2) ->
     let size = get_rhs op1 floc in
     let nesting = get_rhs op2 floc in
     let ppnesting =
       match nesting with
       | XConst (IntConst n) ->
          let nesting = n#toInt in
          if nesting =  0 then
            STR ""
          else
            LBLOCK [ STR " (nesting: " ; INT nesting ; STR ")" ]
       | _ -> STR " (nesting: ?)" in
     let pp = LBLOCK [ STR "push ebp ; ebp := esp ; esp := esp - " ;
                       rhs_to_pretty size ; ppnesting ] in
     make_annotation Assignment pp
      
  | Leave ->
    let restoredValue = get_rhs (ebp_deref RD) floc in
    let pp = LBLOCK [ STR "esp := ebp ; ebp := " ; rhs_to_pretty restoredValue ; STR " ; " ;
		      STR "esp := esp + 4 " ] in
    make_annotation Assignment pp
      
  | Increment op ->
    let rhs = get_rhs op floc in
    let lhs = get_lhs op floc in
    let rewritten = rewrite_expr_pretty (XOp (XPlus, [ rhs ; int_constant_expr 1 ])) in
    let pp = LBLOCK [ lhs_to_pretty op lhs ; STR " := " ; 
		      rhs_to_pretty rhs ; STR " + 1" ; rewritten ] in
    make_annotation Assignment pp
      
  | Decrement op ->
    let rhs = get_rhs op floc in
    let lhs = get_lhs op floc in
    let rewritten = rewrite_expr_pretty (XOp (XMinus, [ rhs ; int_constant_expr 1 ])) in
    let pp = LBLOCK [ lhs_to_pretty op lhs ; STR " := " ; rhs_to_pretty rhs ; 
		      STR " - 1" ; rewritten ] in
    make_annotation Assignment pp
      
  | Add (dst, src) ->
    let rhs1 = get_rhs src floc in
    let rhs2 = get_rhs dst floc in
    let lhs  = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty (XOp (XPlus, [ rhs2 ; rhs1 ])) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs2 ; STR " + " ; 
		      rhs_to_pretty rhs1 ;	rewritten ] in
    make_annotation Assignment pp
      
  | AddCarry (dst, src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs2 ; STR " + " ; 
		      rhs_to_pretty rhs1 ;	STR " + (0 or 1)" ] in
    make_annotation Assignment pp

  | XAdd (dst,src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs1 = get_lhs dst floc in
    let lhs2 = get_lhs src floc in
    let rewritten = rewrite_expr_pretty (XOp (XPlus, [ rhs1 ; rhs2 ])) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs1 ; STR " := " ; rhs_to_pretty rhs1 ; STR " + " ;
		      rhs_to_pretty rhs2 ; rewritten ; STR " ; " ; 
		      lhs_to_pretty src lhs2 ; STR " := " ; rhs_to_pretty rhs1 ] in
    make_annotation Assignment pp

  | Sub (dst, src) ->
    let rhs1 = get_rhs src floc in
    let rhs2 = get_rhs dst floc in
    let lhs  = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty (XOp (XMinus, [ rhs2 ; rhs1 ])) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs2 ; STR " - " ; 
		      rhs_to_pretty rhs1 ; rewritten ] in
    make_annotation Assignment pp
      
  | TwosComplementNegate op ->
    let rhs = get_rhs op floc in
    let lhs = get_lhs op floc in
    let rewritten = rewrite_expr_pretty (XOp (XMinus, [ int_constant_expr 0 ; rhs ])) in
    let pp = LBLOCK [ lhs_to_pretty op lhs ; STR " := 0 - " ; rhs_to_pretty rhs ; 
		      rewritten ] in
    make_annotation Assignment pp
      
  | SubBorrow (dst, src) when dst#equal src ->
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := 0 or -1" ] in
    make_annotation Assignment pp
      
  | SubBorrow (dst, src) ->
    let rhs1 = get_rhs src floc in
    let rhs2 = get_rhs dst floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs2 ; STR " - (" ; 
		      rhs_to_pretty rhs1 ; STR " - (0 or 1))" ] in
    make_annotation Assignment pp
      
  | IMul (_,dst,src1,src2) ->
    let rhs1 = get_rhs src1 floc in
    let rhs2 = get_rhs src2 floc in
    let lhs  = get_lhs dst floc in
    let rewritten = rewrite_expr_pretty (XOp (XMult, [ rhs1 ; rhs2 ])) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " * " ; 
		      rhs_to_pretty rhs2 ; rewritten ] in
    make_annotation Assignment pp

  | Mul (width,dst,src1,src2) ->
    let lhs = get_lhs dst floc in
    let rhs1 = get_rhs src1 floc in
    let rhs2 = get_rhs src2 floc in
    let rewritten = rewrite_expr_pretty (XOp (XMult, [ rhs1 ; rhs2 ])) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " * " ;
		      rhs_to_pretty rhs2 ; rewritten ; STR " (unsigned)" ] in
    make_annotation Assignment pp
      
  | IDiv (width,divisor,dividend,quot,rem) ->
(*    let (dividend,quot,rem) =
      let edxv = rewrite_expr (get_rhs (edx_r RD) floc) in
      match (width,is_zero edxv) with 
      | (1,_) -> (ax_r RD      , al_r WR , ah_r WR)
      | (2,false) -> (dx_ax_r RD   , ax_r WR , dx_r WR)
      | (2,true) -> (ax_r RD   , ax_r WR , dx_r WR)
      | (_,false) -> (edx_eax_r RD , eax_r WR, edx_r WR)
      | (_,true) -> (eax_r RD , eax_r WR, edx_r WR) in *)
    let lhs1 = get_lhs quot floc in
    let lhs2 = get_lhs rem floc in
    let rhs1 = get_rhs dividend floc in
    let rhs2 = get_rhs divisor floc in
    let rewritten = rewrite_expr_pretty (XOp (XDiv, [ rhs1 ; rhs2 ])) in
    let pp = LBLOCK [ STR "(" ; lhs_to_pretty quot lhs1 ; STR "," ; 
		      lhs_to_pretty rem lhs2 ; STR ") = " ; 
		      rhs_to_pretty rhs1 ; STR " / " ; rhs_to_pretty rhs2 ; rewritten ] in
    make_annotation Assignment pp

  | Div (width,divisor,dividend,quot,rem) ->
 (*   let (dividend,quot,rem) = 
      let edxv = rewrite_expr (get_rhs (edx_r RD) floc) in
      match (width,is_zero edxv) with 
      | (1,_) -> (ax_r RD      , al_r WR , ah_r WR)
      | (2,false) -> (dx_ax_r RD   , ax_r WR , dx_r WR)
      | (2,true) -> (ax_r RD   , ax_r WR , dx_r WR)
      | (_,false) -> (edx_eax_r RD , eax_r WR, edx_r WR)
      | (_,true) -> (eax_r RD , eax_r WR, edx_r WR) in *)
    let lhs1 = get_lhs quot floc in 
    let lhs2 = get_lhs rem floc in
    let rhs1 = get_rhs dividend floc in 
    let rhs2 = get_rhs divisor floc in
    (* note: this should be unsigned divide *)
    let rewritten = rewrite_expr_pretty (XOp (XDiv, [ rhs1 ; rhs2 ])) in
    let pp = LBLOCK [ STR "(" ; lhs_to_pretty quot lhs1 ; STR "," ;
		      lhs_to_pretty rem lhs2 ; STR ") = " ;
		      rhs_to_pretty rhs1 ; STR " / " ; rhs_to_pretty rhs2 ; rewritten ;
		      STR " (unsigned)"] in
    make_annotation Assignment pp

  | FXmmOp (opname,scalar,single,dst,src) when
      (match opname with "mul" | "add" | "sub" -> true | _ -> false) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs = get_lhs dst floc in
    let sScalar = if scalar then "scalar" else "packed" in
    let sSingle = if single then "single prec" else "double prec" in
    let sOp = match opname with 
      | "mul" -> " * "
      | "add" -> " + "
      | "sub" -> " -"
      | _ -> " ? " in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR  " := " ; rhs_to_pretty rhs1 ;
		      STR sOp ; rhs_to_pretty rhs2 ;
		      STR " (" ; STR sScalar ; STR ", " ; STR sSingle ; STR ")" ] in
    make_annotation Assignment pp
      
  | LogicalAnd (dst, src) when src#is_zero ->
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := 0" ] in
    make_annotation Assignment pp
      
  | LogicalAnd (dst, src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " & " ; 
		      rhs_to_pretty rhs2 ] in
    make_annotation Assignment pp
      
  | LogicalOr (dst, src) when src#is_immediate_value && 
      (src#get_immediate_value#to_numerical#equal (mkNumerical (-1))) ->
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ;  STR " := -1 " ] in
    make_annotation Assignment pp
      
  | LogicalOr (dst, src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " | " ; 
		      rhs_to_pretty rhs2 ] in
    make_annotation Assignment pp
      
  | Xor (dst, src) when dst#equal src ->
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := 0 " ] in
    make_annotation Assignment pp
      
  | Xor (dst, src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " xor " ; 
		      rhs_to_pretty rhs2 ] in
    make_annotation Assignment pp

  | Rcr (dst, src) when src#is_immediate_value ->
    let rhs1 = get_rhs dst floc in
    let lhs = get_lhs dst floc in
    let rot = match src#get_immediate_value#to_int with
      | Some i -> check_range ~high:31 ~low:0 instr#toPretty i
      | _ ->
	begin
	  ch_error_log#add "translation"
	    (LBLOCK [ STR "Instruction operand of " ; instr#toPretty ; 
		      STR " is out of range " ;
		      STR "(does not fit in 32 bit integer); assign 0" ]) ;
	  0
	end in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := rotate_right(CF," ; 
		      rhs_to_pretty (rewrite_expr rhs1) ; STR ") by " ; INT rot ] in
    make_annotation Assignment pp
      
  | Shl (dst, src) when src#is_immediate_value ->
    let rhs1 = get_rhs dst floc in
    let lhs = get_lhs dst floc in
    let exponent = match src#get_immediate_value#to_int with
      |	Some i -> check_range ~high:31 ~low:0 instr#toPretty i
      | _ ->
	begin 
	  ch_error_log#add "translation"
	    (LBLOCK [ STR "Instruction operand of " ; instr#toPretty ; 
		      STR " is out of range " ;
		      STR "(does not fit in 32 bit integer); assign 0" ]) ;
	  0
	end in
    let multiplier = mkNumerical_big (B.power_int_positive_int 2 exponent) in
    let rewritten = rewrite_expr_pretty (XOp (XMult, [ rhs1  ; num_constant_expr multiplier ])) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " * " ; 
		      multiplier#toPretty ;	rewritten ] in
    make_annotation Assignment pp
      
  | Shl (dst, src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " << " ; 
		      rhs_to_pretty rhs2 ] in
    make_annotation Assignment pp
      
  | Sar (dst, src) when src#is_immediate_value ->
    let rhs = get_rhs dst floc in
    let lhs = get_lhs dst floc in
    let exponent = match src#get_immediate_value#to_int with
	Some i -> check_range ~high:31 ~low:0 instr#toPretty i
      | _ ->
	begin 
	  ch_error_log#add "translation"
	    (LBLOCK [ STR "Instruction operand of " ; instr#toPretty ; 
		      STR " is out of range " ;
		      STR "(does not fit in 32 bit integer); assign 0" ]) ;
	  0
	end in
    let multiplier = mkNumerical_big (B.power_int_positive_int 2 exponent) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs ; STR " / " ; 
		      multiplier#toPretty ] in
    make_annotation Assignment pp
      
  | Sar (dst, src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " >> " ; 
		      rhs_to_pretty rhs2 ] in
    make_annotation Assignment pp
      
  | Shr (dst, src) when src#is_immediate_value ->
    let rhs = get_rhs dst floc in
    let lhs = get_lhs dst floc in
    let exponent = match src#get_immediate_value#to_int with
	Some i -> check_range ~high:31 ~low:0 instr#toPretty i
      | _ ->
	begin 
	  ch_error_log#add "translation"
	    (LBLOCK [ STR "Instruction operand of " ; instr#toPretty ; 
		      STR " is out of range " ;
		      STR "(does not fit in 32 bit integer); assign 0" ]) ;
	  0
	end in
    let multiplier = mkNumerical_big (B.power_int_positive_int 2 exponent) in
    let rewritten = rewrite_expr_pretty (XOp (XDiv, [ rhs ; num_constant_expr multiplier ])) in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs ; STR " / " ; 
		      multiplier#toPretty ; rewritten ] in
    make_annotation Assignment pp
      
  | Shr (dst, src) ->
    let rhs1 = get_rhs dst floc in
    let rhs2 = get_rhs src floc in
    let lhs  = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := " ; rhs_to_pretty rhs1 ; STR " >> " ; 
		      rhs_to_pretty rhs2 ] in
    make_annotation Assignment pp

  | DirectCall op when op#is_absolute_address && 
      has_callsemantics op#get_absolute_address ->
    let semantics = get_callsemantics op#get_absolute_address in
    make_annotation (ApplicationCall op#get_absolute_address) 
      (semantics#get_annotation floc)
      
  | DirectCall _ | IndirectCall _
       when floc#has_call_target && floc#get_call_target#is_signature_valid ->
     let fintf = floc#get_call_target#get_function_interface in
     let fts = fintf.fintf_type_signature in
    let fn = fintf.fintf_name in
    let pStackAdjustment = 
      if floc#get_call_target#is_nonreturning then
        STR " (nonreturning)" 
      else if system_info#has_esp_adjustment floc#fa floc#ia then 
	LBLOCK [
            STR " (adj ";
            INT (system_info#get_esp_adjustment floc#fa floc#ia); 
	    STR ")"]
      else
        match fts.fts_stack_adjustment with
        | Some adj ->
           if adj = 0 then STR "" else LBLOCK [STR " (adj "; INT adj; STR ")"]
      | _ -> STR " (?adj?)" in
    let pr_arg = if floc#get_call_target#is_semantics_valid then
	pr_sum_argument_expr floc#get_call_target
      else
	pr_argument_expr ~typespec:None in
    let pp =
      LBLOCK [
          STR (demangle fn);
	  pretty_print_list floc#get_call_args
	    (fun (p,expr) ->
	      LBLOCK [
                  STR p.apar_name;
                  STR ":";
		  pr_arg p expr]) "(" ", " ")" ;
	  pStackAdjustment] in
    let _ =
      if fn = "strncmp" then
	let rvar = floc#f#env#mk_return_value floc#cia in
	floc#f#env#set_variable_name rvar (pretty_to_string pp) in
    make_annotation (LibraryCall fn) pp 

  | DirectCall _ | IndirectCall _ when floc#has_call_target -> 
     let calltgt = floc#get_call_target in
     let pp = call_target_to_pretty calltgt#get_target in
    make_annotation Call pp

  | IndirectCall op ->
    let opx = op#to_expr floc in
    let pp = 
      match opx with
      | XConst (IntConst num) -> 
	 let addr =
           TR.tvalue (numerical_to_hex_string num) ~default:num#toString in
	LBLOCK [STR "fp:"; STR addr; STR "( ?? )"]
      | XVar v when (not v#isTmp) ->
	let pr_arg = pr_argument_expr ~typespec:None in
	let ppargs =
	  LBLOCK [ pretty_print_list floc#get_call_args
		     (fun (p,expr) -> 
		       LBLOCK [ STR p.apar_name ; STR ":" ; 
				pr_arg p expr ]) "(" ", " ")" ] in
	let ppStackAdj = if system_info#has_esp_adjustment floc#l#f floc#l#i then
	    LBLOCK [ STR " (adj " ; 
		     INT (system_info#get_esp_adjustment floc#l#f floc#l#i) ;
		     STR ") " ]
	  else STR "" in
	let x = floc#rewrite_variable_to_external v in
	begin
	  match x with
	  | XVar vv ->
	    LBLOCK [ STR "*( " ; floc#f#env#variable_name_to_pretty vv ; STR " )" ;
		   ppargs ; ppStackAdj ]
	  | _ -> LBLOCK [ STR "*( " ; pr_expr x ; STR ") " ; ppargs ; ppStackAdj ]
	end
      | _ -> LBLOCK [ STR "unknown( ? )" ] in
    make_annotation Call pp

  | Push (_,op) when op#is_function_argument -> 
    let rhs = get_rhs op floc in
    let (callSite, argIndex) = op#get_function_argument in
    let callSiteFloc = get_floc (ctxt_string_to_location floc#fa callSite) in
    if callSiteFloc#has_call_target && floc#get_call_target#is_signature_valid then
      let fintf = callSiteFloc#get_call_target#get_function_interface in
	let fName = fintf.fintf_name in
	let param = 
	  try
	    get_stack_parameter fintf argIndex
	  with
	    BCH_failure p ->
	      begin
		ch_error_log#add
                  "number of arguments"
		  (LBLOCK [ STR fName ; STR ": " ; p ]) ;
		mk_stack_parameter argIndex
	      end in
	let rhs_pp = match get_string_reference floc rhs with 
	  | Some s -> STR s
	  | _ ->
	    match get_xpr_symbolic_name rhs with
	    | Some name -> STR name 
	    | _ -> rhs_to_pretty ~partype:param.apar_type rhs in
	let pp =
          LBLOCK [
              STR "[";
              STR fName;
              STR " : ";
	      STR param.apar_name;
              STR " = ";
              rhs_pp;
              STR " ]"] in
	make_annotation FunctionArgument pp
      else 
	no_annotation
	  
  | Push (_,op) when op#is_register ->
    let var = env#mk_cpu_register_variable op#get_cpureg in
    if floc#has_initial_value var then
      let pp = LBLOCK [ STR "save " ; (variable_to_pretty var) ] in
      make_annotation Assignment pp
    else
      let rhs = get_rhs op floc in
      let lhs_op = esp_deref ~with_offset:(-4) WR in
      let lhs = get_lhs lhs_op floc in
      let pp =
        LBLOCK [
            STR "esp := esp - 4 ; ";
            lhs_to_pretty lhs_op lhs;
            STR " := ";
	    rhs_to_pretty rhs] in
      make_annotation Assignment pp
	
  | Push (_,op) ->
    let rhs = get_rhs op floc in
    let lhs_op = esp_deref ~with_offset:(-4) WR in
    let lhs = get_lhs lhs_op floc in
    let pp =
      LBLOCK [
          STR "esp := esp - 4 ; ";
          lhs_to_pretty lhs_op lhs;
          STR " := ";
	  rhs_to_pretty rhs] in
    make_annotation Assignment pp
      
  | PushFlags ->
    let lhs_op = esp_deref ~with_offset:(-4) WR in
    let lhs = get_lhs lhs_op floc in
    let pp =
      LBLOCK [
          STR "esp := esp - 4 ; ";
          lhs_to_pretty lhs_op lhs;
          STR " := cpu-flags"] in
    make_annotation Assignment pp
      
  | Pop (_,op) when op#is_register ->
    let rhs = get_rhs (esp_deref RD) floc in
    let rhs = floc#inv#rewrite_expr rhs env#get_variable_comparator in
    let initVal = env#mk_initial_register_value (CPURegister op#get_cpureg) in
    if syntactically_equal rhs (XVar initVal) then
      let pp = LBLOCK [STR "restore "; STR (cpureg_to_string op#get_cpureg)] in
      make_annotation Assignment pp
    else
      let lhs = get_lhs op floc in
      let esp = env#mk_cpu_register_variable Esp in
      let rewritten =
        rewrite_expr_pretty (XOp (XPlus, [XVar esp; int_constant_expr 4])) in
      let pp =
        LBLOCK [
            lhs_to_pretty op lhs;
            STR " := ";
            rhs_to_pretty rhs;
	    STR " ; esp := esp + 4";
            rewritten ] in
      make_annotation Assignment pp
	
  | Pop (_,op) ->
    let rhs = get_rhs (esp_deref RD) floc in
    let lhs = get_lhs op floc in
    let esp = env#mk_cpu_register_variable Esp in
    let rewritten =
      rewrite_expr_pretty (XOp (XPlus, [XVar esp; int_constant_expr 4])) in
    let pp =
      LBLOCK [
          lhs_to_pretty op lhs;
          STR " := ";
          rhs_to_pretty rhs; 
	  STR " ; esp := esp + 4";
          rewritten] in
    make_annotation Assignment pp
      
  | PopFlags ->
    let rhs = get_rhs (esp_deref RD) floc in
    let pp =
      LBLOCK [
          STR "cpu-flags := ";
          rhs_to_pretty rhs;
          STR " ; esp := esp + 4"] in
    make_annotation Assignment pp

  | Setcc (_,op) when floc#f#has_associated_cc_setter floc#cia ->
     let testIAddr = floc#f#get_associated_cc_setter floc#cia in
     let testloc = ctxt_string_to_location floc#fa testIAddr in
     let testAddr = testloc#i in
     let testopc = ((!assembly_instructions)#at_address testAddr)#get_opcode in
     let setopc = instr#get_opcode in
     let setloc = floc#l in
     let setexpr = conditional_set_expr ~setopc ~testopc ~setloc ~testloc in
     let lhs = get_lhs op floc in
     let pp = LBLOCK [ lhs_to_pretty op lhs ; STR " := " ;
		       rhs_to_pretty setexpr ] in
     make_annotation Assignment pp

  | Setcc (_, op) ->
    let lhs = get_lhs op floc in
    let pp = LBLOCK [ lhs_to_pretty op lhs ; STR " := (0 or 1)" ] in
    make_annotation Assignment pp
      
  | Cpuid ->
    let eax = env#mk_cpu_register_variable Eax in
    let eaxExpr = floc#rewrite_variable_to_external eax in
    let pp = LBLOCK [ STR "(eax,ebx,ecx,edx) := cpuid [ eax = " ; 
		      rhs_to_pretty eaxExpr ; STR " ]" ] in
    make_annotation Assignment pp

  | FStore (_,_,width,op) ->
    let lhs = get_lhs op floc in
    let pp = LBLOCK [ lhs_to_pretty op lhs ; STR " := ST(0) (" ; INT width ; 
		      STR " bytes)" ] in
    make_annotation Assignment pp

  | FStoreState ("cw",false,2,op) ->
    let lhs = get_lhs op floc in
    let pp = LBLOCK [ lhs_to_pretty op lhs ; STR " := " ; STR "FPU control word" ] in
    make_annotation Assignment pp

  | FLoadState ("cw",2,op) ->
    let rhs = get_rhs op floc in
    let pp = LBLOCK [ STR "FPU control word := " ; rhs_to_pretty rhs ] in
    make_annotation Assignment pp

  | Ret (Some numPopped) | BndRet (Some numPopped) ->
    let pp = LBLOCK [ STR "return (increment stackpointer by " ; INT numPopped ; STR ")" ] in
    make_annotation Return pp

  | Ret None | BndRet None when system_info#is_goto_return floc#l#i ->
    let dst = system_info#get_goto_return floc#l#i in
    let pp = LBLOCK [ STR "esp := esp + 4 ; goto " ; dst#toPretty ] in
    make_annotation (Jump dst) pp
      
  | RepzRet | Ret None -> make_annotation Return (STR "return")

  | SysEnter ->
    let eax = env#mk_cpu_register_variable Eax in
    let eaxExpr = floc#rewrite_variable_to_external eax in
    let pp = LBLOCK [ STR "sysenter [ eax = " ; 
		      rhs_to_pretty eaxExpr ; STR " ]" ] in
    make_annotation Call pp

  | SysCall ->
    let eax = env#mk_cpu_register_variable Eax in
    let eaxExpr = floc#rewrite_variable_to_external eax in
    let pp = LBLOCK [ STR "syscall [ eax = " ; 
		      rhs_to_pretty eaxExpr ; STR " ]" ] in
    make_annotation Call pp

  | SysExit -> make_annotation Return (STR "sysexit")

  | SysReturn -> make_annotation Return (STR "sysret")

  | DirectJmp op when op#is_absolute_address ->
    let pp = LBLOCK [STR "goto "; STR op#get_absolute_address#to_hex_string] in
    make_annotation (Jump op#get_absolute_address) pp

  | IndirectJmp op when floc#f#is_dll_jumptarget floc#cia ->
    if floc#has_call_target && floc#get_call_target#is_signature_valid then
      let fintf = floc#get_call_target#get_function_interface in
      let fts = fintf.fintf_type_signature in
      let fn = fintf.fintf_name in
      let pStackAdjustment = 
	match fts.fts_stack_adjustment with
	| Some adj -> if adj = 0 then 
	    STR "" 
	  else 
	    LBLOCK [STR " (adjust "; INT adj ; STR ")"]
	| _ -> STR " (?adj?)" in
      let pr_arg =
        if floc#has_call_target && floc#get_call_target#is_semantics_valid then
	  pr_sum_argument_expr floc#get_call_target
	else
	  pr_argument_expr ~typespec:None in
      let pp =
        LBLOCK [
            STR (demangle fn);
	    pretty_print_list floc#get_call_args
	      (fun (p,expr) ->
		LBLOCK [
                    STR p.apar_name;
                    STR ":";
		    pr_arg p expr ]) "(" ", " ")";
	    pStackAdjustment ] in
      let _ = if fn = "strncmp" then
	  let rvar = floc#f#env#mk_return_value floc#cia in
	  floc#f#env#set_variable_name rvar (pretty_to_string pp) in
      make_annotation (LibraryCall fn) pp 
    else
      let calltgt = floc#get_call_target in
      let pp = call_target_to_pretty calltgt#get_target in
      make_annotation Call pp

  | IndirectJmp op when floc#has_jump_target ->
    let ppdefault = LBLOCK [ STR "goto ?" ] in
    let pr_targets tgts =
      pretty_print_list tgts (fun tgt -> tgt#toPretty) "[" "; " "]" in
    let tgt = floc#get_jump_target in
    let pp = match tgt with
      | JumptableTarget (base,jt,reg) ->
	let indexVar = floc#f#env#mk_register_variable reg in
	if floc#is_interval indexVar then
	  let range = floc#get_interval indexVar in
	  let pprange = match (range#getMin#getBound, range#getMax#getBound) with
	    | (NUMBER lb, NUMBER ub) -> 
	      LBLOCK [ STR " [" ; lb#toPretty ; STR " - " ; ub#toPretty ; STR "] " ]
	    | (_, NUMBER ub) -> LBLOCK [ STR " ( <- ; " ; ub#toPretty ; STR "] " ]
	    | _ -> STR "" in
	  let tgts = match (range#getMin#getBound, range#getMax#getBound) with
	    | (NUMBER lb, NUMBER ub) -> jt#get_targets base lb#toInt ub#toInt
	    | (_, NUMBER ub) -> jt#get_targets base 0 ub#toInt
	    | _ -> jt#get_all_targets in
	  LBLOCK [ STR "jump on " ; STR (register_to_string reg) ; pprange ; STR ": " ; 
		   pr_targets tgts ]
	else
	  LBLOCK [ STR "jump on " ; STR (register_to_string reg) ; STR ": " ; 
		   pr_targets jt#get_all_targets ] 
      | OffsettableTarget (base,jt,db) ->
	if db#is_offset_table then
	  match db#get_offset_range with
	  | Some (min,max) -> 
	    LBLOCK [ STR "jump on offsets [" ; INT min ; STR "," ; INT max ; STR "]: " ;
		     pr_targets (jt#get_targets base min max) ]
	  | _ -> ppdefault
	else 
	  ppdefault
      | _ -> ppdefault in
    make_annotation (Jump wordzero) pp
	  
  | IndirectJmp op ->
      let pp = LBLOCK [ STR "goto ?" ] in
      make_annotation (Jump wordzero) pp
	
  | Movdq (_, dst,_)  ->
    let lhs = get_lhs dst floc in
    let pp = LBLOCK [ lhs_to_pretty dst lhs ; STR " := ?" ] in
    make_annotation Assignment pp
      
  | ConvertLongToDouble _ -> make_annotation NotModeled (STR "convert long to double")
    
  | ClearCF -> make_annotation Assignment (STR "carry-flag := 0")
  | ClearDF -> make_annotation Assignment (STR "direction-flag := 0") 
  | ClearInterruptFlag -> make_annotation NotModeled (STR "interrupt-flag := 0")
  | ClearTaskSwitchedFlag -> make_annotation NotModeled (STR "task-switch-flag := 0")
    
  | SetCF -> make_annotation Assignment (STR "carry-flag := 1") 
  | SetDF -> make_annotation Assignment (STR "direction-flag := 1")
  | SetInterruptFlag -> make_annotation NotModeled (STR "interrupt-flag := 0") 
    
    
  | Fmul _ | Fadd _ | Fsub _ | Fdiv _ | Finit _ | Fxch _ 
  | Fucom _ | Fcom _  ->  no_annotation
    
    (* to be added *)
  | CMovcc _ -> no_annotation

  | PackedOp (name,_,dst,_) -> packed_operation_annotation floc name dst
  | PackedAlignRight (dst,_,_) -> packed_operation_annotation floc "align-right" dst
  | PackedExtract (_,dst,_,_) -> packed_operation_annotation floc "extract" dst
  | PackedInsert (_,dst,_,_) -> packed_operation_annotation floc "insert" dst
  | PackedShift (_,_,dst,_) -> packed_operation_annotation floc "shift" dst
  | PackedCompare (_,_,dst,_) -> packed_operation_annotation floc "compare" dst 
  | PackedAdd (_,_,_,dst,_) -> packed_operation_annotation floc "add" dst
  | PackedSubtract (_,_,_,dst,_) -> packed_operation_annotation floc "subtract" dst
  | PackedMultiply (_,dst,_) -> packed_operation_annotation floc "multiply" dst

  | PackedCompareString (explicit,index,op1,op2,controlbyte) ->
    let rhs1 = get_rhs op1 floc in
    let rhs2 = get_rhs op2 floc in
    let lengths = if explicit then " lengths in eax and edx" else " implicit lengths" in
    let pp = LBLOCK [ STR "compare strings in " ; rhs_to_pretty rhs1 ; STR " and " ; 
		      rhs_to_pretty rhs2 ; STR " with " ; STR lengths ; 
		      STR " and controlvalue " ; controlbyte#toPretty ;
		      (if index then STR " (abstract ecx)" else STR "") ] in
    make_annotation NotModeled pp
    
  | _ ->  no_annotation
    
 
let create_annotation (floc:floc_int) =
  try
    create_annotation_aux floc 
  with
    BCH_failure p ->
      let instr = !assembly_instructions#at_address floc#ia in
      raise (BCH_failure (LBLOCK [ STR "Error in create annotation with " ;
				   STR (opcode_to_string instr#get_opcode) ;
				   STR ": " ; p  ]))
