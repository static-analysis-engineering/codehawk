(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHPrettyUtil

(* xprlib *)
open XprTypes
open XprToPretty

(* cchlib *)
open CCHBasicTypes
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHMemoryBase
open CCHPreTypes
open CCHProofObligation

(* cchanalyze *)
open CCHAnalysisTypes

let cd = CCHDictionary.cdictionary

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)

(* The difficulty in delegating initialized-range is that it is hard to check
   that the pointed to string or array has not been changed within the function
   (due to potential aliasing *)


let is_initialized_range sym = sym#getBaseName = "initialized-range"


let get_initialized_range_len sym =
  if is_initialized_range sym then
    match sym#getAttributes with
    | [fname; irlen] ->
       (try
          Some (fname, mkNumericalFromString irlen)
        with
        | Failure _ ->
           raise
             (CCHFailure
                (LBLOCK [
                     STR "get_initialized_range: int_of_string on ";
                     STR irlen;
                     STR "(";
                     STR fname;
                     STR ")"])))
    | _ -> None
  else
    None


class initialized_range_checker_t
        (poq: po_query_int)
        (e1: exp)
        (e2: exp)
        (invs1: invariant_int list)
        (invs2: invariant_int list) =
object (self)

  method private memref_to_string (memref: memory_reference_int) =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  method private unsigned_length_conflict =
    match e2 with
    | CastE (t, _) when is_unsigned_integral_type t ->
       let _ =
         poq#set_diagnostic_arg
           4 ("value is cast to unsigned: " ^  (p2s (typ_to_pretty t))) in
       List.fold_left (fun acc inv2 ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv2#lower_bound_xpr with
              | Some (XConst (IntConst n)) when n#lt numerical_zero ->
                 let deps = DLocal ([inv2#index]) in
                 let msg =
                   Printf.sprintf
                     ("negative value: %s may be cast to a large positive "
                        ^^ "value when cast to %s")
                     n#toString
                     (p2s (typ_to_pretty t)) in
                 Some (deps, msg)
              | _ -> None)  None invs2
    | _ -> None

  method private get_initialization_length (vinfo: varinfo) =
    let vinfovalues = poq#get_vinfo_offset_values vinfo in
    List.fold_left (fun acc (inv,offset) ->
        match acc with
        | Some _ -> acc
        | _ ->
           match offset with
           | Field _ | Index _ -> None
           | NoOffset ->
              match inv#get_fact with
              | NonRelationalFact(_,FInitializedSet [sym])
                   when is_initialized_range sym ->
                 begin
                   match get_initialized_range_len sym with
                   | Some (irname, irlen) ->
                      let deps = DLocal [inv#index] in
                      Some (deps, irname,irlen)
                   | _ -> None
                 end
              | _ -> None) None vinfovalues

  method private get_element_initializations (vinfo: varinfo) =
    let vinfovalues = poq#get_vinfo_offset_values vinfo in
    List.fold_left (fun (deps, acc) (inv, offset) ->
        match offset with
        | Index (Const (CInt (i64, _, _)), NoOffset) ->
           begin
             match inv#expr with
             | Some x ->
                let n = mkNumericalFromInt64 i64 in
                let deps = join_dependencies (DLocal [inv#index]) deps in
                (deps,(n, x) :: acc)
             | _ -> (deps, acc)
           end
        | _ -> (deps, acc)) (DLocal [],[]) vinfovalues

  method private check_elementinits l (len: numerical_t) =
    if len#gt (mkNumerical 50) then
      None
    else
      if List.length l < len#toInt then
        None
      else
        let lst = List.sort (fun (n1, _x) (n2, _x) -> n1#compare n2) l in
        let result =
          List.fold_left (fun acc (n, x) ->
              match acc with
              | None -> None
              | Some (r, prev) ->
                 if (prev#add numerical_one)#equal n then
                   Some ((n,x)::r, n)
                 else
                   None) (Some ([], mkNumerical (-1))) lst in
        match result with
        | Some (l, n) when n#geq (len#sub numerical_one) ->
           Some
             (String.concat
                ","
                (List.map
                   (fun (n,x) -> "(" ^ n#toString ^ ": " ^ (x2s x) ^ ")")
                   (List.rev l)))
        | _ -> None


  (* ----------------------------- safe ------------------------------------- *)

  method private var1_implies_safe (inv1index: int) v1 =
    let deps1 = DLocal [inv1index] in
    if poq#env#is_memory_address v1 then
      let memref = poq#env#get_memory_reference v1 in
      let _ =
        poq#set_diagnostic_arg
          1 ("memory variable: " ^ (self#memref_to_string memref)) in
      match memref#get_base with
      | CStringLiteral _ ->
         begin
           match e2 with
           | CnApp ("ntp", [Some x], _)
             | CastE (_, CnApp ("ntp", [Some x], _))
                when (cd#index_exp e1) = (cd#index_exp x) ->
              let deps = DLocal [inv1index] in
              let msg  = "string literal is initialized up to null terminator" in
              Some (deps, msg)
           | _ ->
              begin
                poq#set_diagnostic ("unusual bounds expression for string literal");
                None
              end
         end
      | CStackAddress stackvar when poq#env#is_local_variable stackvar ->
         let (vinfo,offset) = poq#env#get_local_variable stackvar in
         begin
           match (vinfo.vtype, offset) with
           | (TArray (_,Some (Const (CInt (len64,_,_))),_),NoOffset) ->
              let arraylen = mkNumericalFromInt64 len64 in
              begin
                match self#get_initialization_length vinfo with
                | Some (deps, irname, irlen) when irlen#geq arraylen ->
                   let deps = join_dependencies deps1 deps in
                   let msg =
                     Printf.sprintf
                       "initialized by %s with %s bytes" irname irlen#toString in
                   Some (deps, msg)
                | Some (deps, irname, irlen)
                     when irlen#geq (arraylen#sub numerical_one) ->
                   let (edeps, elementinits) =
                     self#get_element_initializations vinfo in
                   if List.exists (fun (n, _x) ->
                          n#equal (arraylen#sub numerical_one)) elementinits then
                     let (n, x) =
                       List.find (fun (n, _x) ->
                           n#equal (arraylen#sub numerical_one)) elementinits in
                     let deps = join_dependencies deps edeps in
                     let msg =
                       Printf.sprintf
                         ("initialized by %s with %s bytes; element %s "
                          ^^ "was separately initialized with %s")
                         irname
                         irlen#toString
                         n#toString
                         (x2s x) in
                     Some (deps, msg)
                   else
                     let argmsg =
                       Printf.sprintf
                         ("stack array with length %s; initialization by %s "
                          ^^ "with length: %s; no initialization found for the "
                          ^^ "last element")
                         arraylen#toString
                         irname
                         irlen#toString in
                     begin
                       poq#set_diagnostic_arg 1 argmsg;
                       None
                     end

                | Some (_, irname, irlen) ->
                   let argmsg =
                     Printf.sprintf
                       ("stack array with length %s; initialization by %s "
                        ^^ "with length %s")
                       arraylen#toString
                       irname
                       irlen#toString in
                   begin
                     poq#set_diagnostic_arg 1 argmsg;
                     None
                   end
                | _ ->
                   let (deps,elementinits) =
                     self#get_element_initializations vinfo in
                   match self#check_elementinits elementinits arraylen with
                   | Some s ->
                      let msg =
                        Printf.sprintf
                          ("stack array with length %s has been fully initialized "
                           ^^ " with values: %s")
                          arraylen#toString
                          s in
                      Some (deps, msg)
                   | _ ->
                      let p =
                        String.concat
                          ", "
                          (List.map (fun (n,x)  ->
                               "(" ^ n#toString ^ ": " ^ (x2s x) ^ ")")
                             elementinits) in
                      let argmsg =
                        Printf.sprintf
                          "stack array with length %s and known element values: %s"
                          arraylen#toString
                          p in
                      begin
                        poq#set_diagnostic_arg 1 argmsg;
                        None
                      end
              end
           | _ ->
              begin
                poq#set_diagnostic_arg
                  1 ("address of stack variable: " ^ vinfo.vname);
                None
              end
         end
      | _ -> None
    else
      None

  method private xpr1_implies_safe (inv1index: int) (x1: xpr_t) =
    match x1 with
    | XVar v1 -> self#var1_implies_safe inv1index v1
    | _ -> None

  method private inv1_implies_safe (inv1: invariant_int) =
    match inv1#expr with
    | Some x -> self#xpr1_implies_safe inv1#index x
    | _ -> None

  method check_safe =
    let safemsg = fun index arg_count -> ("command-line argument"
                                          ^ (string_of_int index)
                                          ^ " is guaranteed initialized for argument count "
                                          ^ (string_of_int arg_count)) in
    let vmsg = fun index arg_count -> ("command-line argument "
                                       ^ (string_of_int index)
                                       ^ " is not included in argument count of "
                                       ^ (string_of_int arg_count)) in
    let dmsg = fun index -> ("no invariant found for argument count; "
                             ^ "unable to validate initialization of "
                             ^ "command-line argument "
                             ^ (string_of_int index)) in

    poq#check_command_line_argument e1 safemsg vmsg dmsg ||
    match self#unsigned_length_conflict with
    | Some _ -> false
    | _ ->
       match invs1 with
       | [] -> false
       | _ ->
          List.fold_left (fun acc inv1  ->
              acc ||
                match self#inv1_implies_safe inv1 with
                | Some (deps,msg) ->
                   begin
                     poq#record_safe_result deps msg;
                     true
                   end
                | _ -> false) false invs1

  (* ----------------------- violation -------------------------------------- *)
  method check_violation =
    match self#unsigned_length_conflict with
    | Some (deps,msg) ->
       begin
         poq#record_violation_result deps msg;
         true
       end
    | _ -> false

  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_initialized_range (poq: po_query_int) (e1: exp) (e2: exp) =
  let invs1 = poq#get_invariants 1 in
  let invs2 = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 1 in
  let _ = poq#set_diagnostic_invariants 2 in
  let _ =
    poq#set_key_diagnostic
      "DomainRef:initialized-range" "ability to track ranges of memory" in
  let checker = new initialized_range_checker_t poq e1 e2 invs1 invs2 in
  checker#check_safe || checker#check_violation || checker#check_delegation
