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
open CHAtlas
open CHLanguage
open CHNumerical
open CHSymbolicSets
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHFileEnvironment
open CCHLibTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHInvariantFact
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes
open CCHEnvironment
open CCHVariable


let x2p = xpr_formatter#pr_expr
  	
let rec is_zero e = match e with
  | Const (CInt (i64,_,_)) -> (Int64.compare i64 Int64.zero) = 0
  | CastE (_, e) -> is_zero e
  | _ -> false

let rec get_constant_value e = match e with
  | Const (CInt (i64,_,_)) -> Some (Int64.to_int i64)
  | CastE (_, e) -> get_constant_value e
  | _ -> None

let make_constant_value i = Const (CInt (Int64.of_int i, IInt, None))
    
class orakel_t 
  (env:c_environment_int) 
  (invio:invariant_io_int):orakel_int =
object (self)

  method private get_invariant (context:program_context_int) =
    invio#get_location_invariant context

  method private get_expressions (context:program_context_int) (var:variable_t) =
    let cmp i1 i2 =
      match (i1#const_value,i2#const_value) with
      | (Some _, Some _) -> 0
      | (Some _, _) -> -1
      | (_, Some _) -> 1
      | _ -> 0 in
    let invs = (self#get_invariant context)#get_sorted_invariants cmp in
    List.rev
      (List.fold_left (fun acc (inv:invariant_int) ->
           if inv#applies_to_var var then
             match inv#get_fact with
             | NonRelationalFact (_,nrv) -> nrv :: acc
             | _ -> acc
           else acc) [] invs)

  method get_external_value (context:program_context_int) (xpr:xpr_t):xpr_t option =
    let logmsg () =
      chlog#add "xpr not externalized"
                (LBLOCK [ location_to_pretty env#get_current_location ;
                          STR ": " ; x2p xpr ]) in

    let find_value v =
      List.fold_left (fun acc nrv ->
          match acc with
          |Some _ -> acc
          | _ ->
             match nrv with
             | FSymbolicExpr x -> Some x
             | FIntervalValue (Some lb,Some ub) when lb#equal ub ->
                Some (num_constant_expr lb)
             | _ -> None) None (self#get_expressions context v) in
    match xpr with
    | XConst (IntConst _) -> Some xpr
    | XVar v when (
      match v#getName#getAttributes with
      | ["symsize"] -> true
      | _ -> false) -> Some xpr
    | XVar v -> find_value v
    | XOp (op, l) ->
       let xl = List.map (fun x -> self#get_external_value context x) l in
       if List.for_all (fun x -> match x with Some _ -> true | _ -> false) xl then
         Some (XOp (op, List.map Option.get xl))
       else
         begin logmsg (); None end
    | _ ->
       begin logmsg (); None end

  method get_regions (context:program_context_int) (xpr:xpr_t):symbol_t list =
    let find_value v =
      List.fold_left (fun acc nrv ->
          match nrv with
          | FRegionSet l -> l :: acc
          | _ -> acc) [] (self#get_expressions context v) in
    match xpr with
    | XVar v ->
       begin
         match find_value v with
         | [] -> []
         | l ->
            List.hd (
                List.sort
                  (fun x1 x2 ->
                    Stdlib.compare (List.length x1) (List.length x2)) l)
       end
    | _ -> []
  
end


let get_function_orakel = new orakel_t 
  
  
