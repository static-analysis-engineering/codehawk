(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt

(* cchlib *)
open CCHBasicTypes
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHInvariantFact
open CCHPreTypes
open CCHProofScaffolding

(* cchanalyze *)
open CCHAnalysisTypes

let record_postconditions
      (fname:string)
      (env:c_environment_int)
      (invio:invariant_io_int)  =

  (* If one of the return contexts returns a recursive call to itself,
     this context is removed from the list and relationships between
     parameters and returnvalue are removed from all other contexts
     (as the original parameters are likely not the same as those passed
     to the recursive call
   *)
  try
    let (recursion,postconditions) =
      List.fold_left (fun (frecursion,results) ctxt ->
          let locinv = invio#get_location_invariant ctxt in
          let rv = env#get_return_var in
          let rinvs = locinv#get_var_invariants rv in
          let (recursion,facts) =
            List.fold_left (fun (recursion,acc) (rinv:invariant_int) ->
                if recursion then
                  (recursion,acc)
                else
                  try
                    match rinv#get_fact with
                    | NonRelationalFact (_,FSymbolicExpr (XVar v))
                         when env#is_initial_parameter_value v ->
                       let e = env#get_parameter_exp v in
                       begin
                         match e with
                         | Lval (Var (vname,vid),NoOffset) ->
                            let vinfo = env#get_varinfo vid in
                            let param = ArgValue (ParFormal vinfo.vparam,ArgNoOffset) in
                            (false,(XRelationalExpr (Eq, ReturnValue, param)) :: acc)
                         | _ -> (false,acc)
                       end
                    | NonRelationalFact (_,FSymbolicExpr (XVar v))
                         when env#is_initial_global_value v ->
                       let e = env#get_global_exp v in
                       begin
                         match e with
                         | Lval (Var (vname,vid),NoOffset) ->
                            let param = ArgValue (ParGlobal vname,ArgNoOffset) in
                            (false, (XRelationalExpr (Eq,ReturnValue, param)) :: acc)
                         | _ -> (false,acc)
                       end
                    | NonRelationalFact (_,FSymbolicExpr (XVar v))
                         when env#is_function_return_value v &&
                                (let callee = env#get_callvar_callee v in
                                 callee.vname = env#get_functionname) ->
                       (true,[])
                    | NonRelationalFact (_,FIntervalValue (Some lb, Some ub)) when lb#equal ub ->
                       (false,(XRelationalExpr (Eq, ReturnValue, NumConstant lb)) :: acc)
                    | NonRelationalFact (_,FIntervalValue (Some lb, Some ub)) ->
                       (false,(XRelationalExpr (Ge, ReturnValue, NumConstant lb)) ::
                                (XRelationalExpr (Le, ReturnValue, NumConstant ub)) :: acc)
                    | NonRelationalFact (_,FIntervalValue (Some lb, _)) ->
                       (false,(XRelationalExpr (Ge, ReturnValue, NumConstant lb)) :: acc)
                    | NonRelationalFact (_,FIntervalValue (_,Some ub)) ->
                       (false,(XRelationalExpr (Le, ReturnValue, NumConstant ub)) :: acc)
                    | _ -> (false,acc)
                  with
                  | CCHFailure e ->
                    begin
                      ch_error_log#add
                        "error in postcondition"
                        (LBLOCK [ STR fname ; STR ": " ; non_relational_fact_to_pretty rinv#get_fact ;
                                  STR ": " ; e ]) ;
                      (false,acc)
                    end
                  | _ ->
                     begin
                       ch_error_log#add
                         "other error in postcondition"
                         (LBLOCK [ STR fname ; STR ": " ; non_relational_fact_to_pretty rinv#get_fact ]);
                       (false,acc)
                     end) (false,[]) rinvs in
          (frecursion || recursion,
           if recursion then results else facts :: results))
                     (false,[]) env#get_return_contexts in
    let postconditions =
      if recursion then
        List.map (fun r ->
            List.filter (fun p ->
                match p with
                | XRelationalExpr(_,ArgValue _,_)
                  | XRelationalExpr(_,_,ArgValue _) -> false
                | _ -> true) r) postconditions
      else
        postconditions in
    match postconditions with
    | [ pl ] ->
       let fApi = proof_scaffolding#get_function_api fname in
       List.iter fApi#add_postcondition_guarantee pl
    | _ ->
       ()
  with
  | CHFailure p
    | CCHFailure p ->
     ch_error_log#add "postcondition generation" (LBLOCK [ STR fname ; STR ": " ; p ])
           
  
  
