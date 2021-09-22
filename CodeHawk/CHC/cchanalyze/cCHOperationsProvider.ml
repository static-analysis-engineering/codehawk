(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHLibTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes
open CCHProofObligation

(* cchanalyze *)
open CCHAnalysisTypes
open CCHCommand
open CCHEnvironment
open CCHExpTranslator

module H = Hashtbl

let x2p = xpr_formatter#pr_expr

let fenv = CCHFileEnvironment.file_environment


module ProgramContextCollections = CHCollections.Make
  (struct
    type t = program_context_int
    let compare c1 c2 = c1#compare c2
    let toPretty c = c#toPretty
   end)


module ExpCollections = CHCollections.Make
  (struct
    type t = exp
    let compare  = exp_compare
    let toPretty = exp_to_pretty
   end)


class checkset_t (isppo:bool) (x:int) (y:int) =
object (self)

  val mutable triples = [ (isppo,x,y) ]
    
  method add (isppo:bool) (x:int) (y:int) =
    if List.exists (fun (i,a,b) -> i=isppo && a=x && b=y) triples then
      ()
    else
      triples <- List.sort Stdlib.compare ((isppo,x,y) :: triples)
	
  method get = triples
    
  method toPretty = 
    pretty_print_list
      triples
      (fun (isppo, x, y) ->
        LBLOCK [
            STR "(";
            STR (if isppo then "ppo:" else "spo:");
            INT x;
            STR ",";
            INT y;
            STR ")"])
    "[" ";" "]"
    
end
  
  	
let add_proof_obligation_to_set 
      (exps:checkset_t ExpCollections.table_t) (p:proof_obligation_int) =
  if p#is_opaque then () else
    let expsList = collect_indexed_predicate_expressions p#get_predicate in
    List.iter (fun (seqnr,e) -> 
        match exps#get e with
        | Some checkset -> checkset#add p#is_ppo p#index seqnr
        | _ ->
           let checkset =
             new checkset_t
               p#is_ppo p#index seqnr in exps#set e checkset) expsList


let add_proof_obligation 
    (t:(checkset_t ExpCollections.table_t) ProgramContextCollections.table_t)
    (p:proof_obligation_int) =
  let cfgcontext = p#get_context#project_on_cfg in
  let expSet = match t#get cfgcontext with
    | Some expSet -> expSet
    | _ -> 
      let expSet = new ExpCollections.table_t in 
      begin t#set cfgcontext expSet ; expSet end in
  add_proof_obligation_to_set expSet p


class operations_provider_t 
  (env:c_environment_int)
  (exp_translator:exp_translator_int)
  (proof_obligations:proof_obligation_int list)
  (vtype:variable_type_t):operations_provider_int =
object (self)
  
  val op_contexts = 
    let t = new ProgramContextCollections.table_t in
    let _ = List.iter (fun p -> add_proof_obligation t p) proof_obligations in t
  val fdecls = env#get_fdecls
  val mutable count = 0         (* counting invariant locations *)
    
  method get_cmd_operations (context:program_context_int) =
    if op_contexts#has context then 
      let _ = env#start_transaction in
      let cmds = self#make_context_operation context in
      let (tmps,assigns) = env#end_transaction in
      let assigns = List.map make_c_cmd assigns in
      let tlabel = new symbol_t "proof-obligation-expressions" in
      [ make_transaction tlabel tmps (assigns @ cmds) ]
    else
      []

  method get_return_operation (context:program_context_int) (e:exp) =
    let _ = env#start_transaction in
    let cmds = self#make_return_operation context e in
    let (tmps,assigns) = env#end_transaction in
    let assigns = List.map make_c_cmd assigns in
    let tlabel = new symbol_t "return-values" in
    [ make_transaction tlabel tmps (assigns @ cmds ) ]
	
  method get_c_cmd_operations (context:program_context_int) =
    if op_contexts#has context then
      self#make_context_operation context
    else
      []
      
  method private make_context_operation context =
    let assign_check_value v e =
      match vtype with
      | NUM_VAR_TYPE -> 
	let tmpProvider = (fun () -> env#mk_num_temp) in
	let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
	let numExp = exp_translator#translate_exp context e in
	let (rhsCode,numExp) = xpr2numexpr tmpProvider cstProvider numExp in
	[ rhsCode ; make_c_cmd (ASSIGN_NUM (v,numExp)) ]
      | SYM_VAR_TYPE ->
         begin
           match e with
           | Lval lval
             | CastE (_,Lval lval)  ->
              let symvar = exp_translator#translate_lhs context lval in
              if not v#isTmp then
                [ make_c_cmd (ASSIGN_SYM (v, SYM_VAR symvar)) ]
              else
                [ make_c_cmd SKIP ]
           | _ ->
              match exp_translator#translate_exp context e with
              | XVar symvar -> [ make_c_cmd (ASSIGN_SYM (v, SYM_VAR symvar)) ]
              | XConst _ -> [ make_c_cmd SKIP ]
              | xpr ->
                 begin
                   chlog#add "no symbolic check value assigned"
                             (LBLOCK [ STR env#get_functionname ; STR ": " ;
                                       exp_to_pretty e ; STR " --> " ;
                                       x2p xpr ]) ;
                   [ make_c_cmd SKIP ]
                 end
         end
      | _ -> [ make_c_cmd SKIP ] in
    let name = self#mk_invariant_label context in
    let vars = ref [] in
    let code = ref [] in
    let exps = match op_contexts#get context with
      | Some t -> t
      | _ ->
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Internal error in make_context_operation"])) in
    let _ =
      exps#iter
        (fun e checkset ->
          let checkVar =
            env#mk_check_variable checkset#get (type_of_exp fdecls e) vtype in
          try
            let assign = make_c_cmd_block (assign_check_value checkVar e) in
            begin
              vars := checkVar :: !vars;
              code := assign :: !code
            end
          with
          | CCHFailure p ->
             ch_error_log#add
               "proof obligation expression translation"
               (LBLOCK [
                    STR "Variable: ";
                    checkVar#toPretty;
                    STR "; Expr: ";
                    exp_to_pretty e;
                    STR ": ";
                    p]))  in
    let args = List.map (fun v -> (v#getName#getBaseName,v,READ)) !vars in
    let op =
      make_c_cmd (OPERATION {op_name = new symbol_t name; op_args = args}) in
    let abstract = make_c_cmd (ABSTRACT_VARS !vars) in
    !code @ [op; abstract]

  method private make_return_operation context e =
    let assign_return_value v e =
      let tmpProvider = (fun () -> env#mk_num_temp) in
      let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
      let numExp = exp_translator#translate_exp context e in
      let (rhsCode,numExp) = xpr2numexpr tmpProvider cstProvider numExp in
      [ rhsCode ; make_c_cmd (ASSIGN_NUM (v,numExp)) ] in
    let name = self#mk_invariant_label context in
    let rVar = env#get_return_var in
    let assign = make_c_cmd_block (assign_return_value rVar e) in
    let args = [ (rVar#getName#getBaseName,rVar,READ) ] in
    let op =
      make_c_cmd (OPERATION {op_name = new symbol_t name; op_args = args}) in
    [assign; op]
         
  method private mk_invariant_label context =
    let _ = count <- count + 1 in
    let ictxt = ccontexts#index_context context in
    "inv_" ^ (string_of_int ictxt) ^ "_" ^ (string_of_int count)
end


let get_operations_provider = new operations_provider_t
