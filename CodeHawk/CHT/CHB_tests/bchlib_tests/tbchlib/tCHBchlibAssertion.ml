(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* chutil *)
open CHTraceResult

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHARMFunctionInterface
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHFtsParameter
open BCHLibTypes
open BCHMemoryReference

module A = TCHAssertion

module TR = CHTraceResult



let e7 = 128
let e8 = 256
let e15 = e7 * e8
let e16 = e8 * e8
let e31 = e15 * e16
let e32 = e16 * e16


let p2s = CHPrettyUtil.string_printer#print
let x2p = XprToPretty.xpr_formatter#pr_expr
let x2s x = p2s (x2p x)


let equal_doubleword =
  A.make_equal (fun dw1 dw2 -> dw1#equal dw2) (fun dw -> dw#to_hex_string)


let equal_doubleword_result
      ?(msg="") (dw: doubleword_int) (dwr: doubleword_result) =
  if Result.is_error dwr then
    A.fail
      (dw#to_hex_string)
      (String.concat "; " (TR.tget_error dwr))
      ("error:" ^ msg)
  else
    A.make_equal
      (fun dw1 dw2 -> dw1#equal dw2)
      (fun dw -> dw#to_hex_string)
      dw
      (TR.tget_ok dwr)


let equal_doubleword_alignment
      ?(msg="") (expected: (string * int)) (received: (doubleword_int * int)) =
  let (recvdw, revdr) = received in
  let rd = recvdw#to_hex_string in
  A.make_equal
    (fun (xs, xi) (rd, ri) -> (xs = rd) && (xi = ri))
    (fun (s, i) -> "(" ^ s ^ ", " ^ (string_of_int i) ^ ")")
    ~msg
    expected
    (rd, revdr)


let equal_location =
  A.make_equal (fun l1 l2 -> (l1#compare l2) = 0) (fun l -> l#ci)


let equal_int_hexstring ?(msg="") (i: int) (s: string) =
  if not ((Printf.sprintf "%x" i) = s) then
    A.fail (string_of_int i) s msg


let equal_string_imm_result_hexstring
      ?(msg="") (expected: string) (immr: immediate_result) =
  if Result.is_error immr then
    A.fail ("expected:" ^ expected) (String.concat "; " (TR.tget_error immr)) msg
  else
    A.equal_string expected (TR.tget_ok immr)#to_hex_string


let equal_string_imm_result_string
      ?(msg="") (expected: string) (immr: immediate_result) =
  if Result.is_error immr then
    A.fail ("expected:" ^ expected) (String.concat "; " (TR.tget_error immr)) msg
  else
    A.equal_string expected (TR.tget_ok immr)#to_string


let equal_array_index_offset
      ?(msg="")
      ~(expected: (xpr_t * numerical_t) option)
      ~(received: (xpr_t * numerical_t) option)
      () =
  let pri (x, n) = "(" ^ (x2s x) ^ ", " ^ n#toString ^ ")" in
  match (expected, received) with
  | (None, None) -> ()
  | (Some x, None) ->
     A.fail_msg ("Expected Some " ^ (pri x) ^ ", but received None")
  | (None, Some x) ->
     A.fail_msg ("Expected None, but received Some " ^ (pri x))
  | (Some x1, Some x2) ->
     A.make_equal
       (fun (x1, n1) (x2, n2) -> ((x2s x1) = (x2s x2)) && n1#equal n2)
       (fun (x, n) -> "(" ^ (x2s x) ^ ", " ^ n#toString ^ ")")
       ~msg
       x1
       x2


let equal_memory_offset
      ?(msg="")
      ~(expected: memory_offset_t)
      ~(received: memory_offset_t)
      () =
  match (expected, received) with
  | (UnknownOffset, UnknownOffset) -> ()
  | (m, UnknownOffset) ->
     A.fail_msg
       ("Expected a known offset " ^ (memory_offset_to_string m)
        ^ ", but received UnknownOffset")
  | (UnknownOffset, m) ->
     A.fail_msg
       ("Expected UnknownOffset but received " ^ (memory_offset_to_string m))
  | _ ->
     A.make_equal
       (fun m1 m2 -> (memory_offset_compare m1 m2) = 0)
       memory_offset_to_string
       ~msg
       expected
       received


let equal_opt_meminfo
      ?(msg="")
      ~(expected: (memory_reference_int * memory_offset_t) option)
      ~(received: (memory_reference_int * memory_offset_t) option)
      () =
  let pri (m, o) =
    "(" ^ (p2s m#toPretty) ^ ", " ^ (memory_offset_to_string o) ^ ")" in
  match (expected, received) with
  | (None, None) -> ()
  | (Some x, None) ->
     A.fail_msg ("Expected Some " ^ (pri x) ^ ", but received None")
  | (None, Some x) ->
     A.fail_msg ("Expected None, but received Some " ^ (pri x))
  | (Some x1, Some x2) ->
     A.make_equal
       (fun (m1, o1) (m2, o2) ->
         (m1#compare m2) = 0 && (memory_offset_compare o1 o2) = 0)
       pri
       ~msg
       x1
       x2


let equal_assignments
      ?(msg="")
      (finfo: function_info_int)
      ~(expected: (string * string) list)
      ~(received: (variable_t * numerical_exp_t) list) =
  let varmgr = finfo#env#varmgr in
  let srecvd =
    List.map (fun (v, e) ->
        tfold_default
          (fun asmvar ->
            let pexp =
              match e with
              | NUM_VAR nv ->
                 tfold_default
                   (fun numvar -> numvar#toPretty)
                   (numerical_exp_to_pretty e)
                   (varmgr#get_variable nv)
              | _ -> numerical_exp_to_pretty e in
            (p2s asmvar#toPretty, p2s pexp))
          (p2s (numerical_exp_to_pretty e), "error")
          (varmgr#get_variable v)) received in
  A.make_equal_list
    (fun (xv, xe) (rv, re) -> (xv = rv) && (xe = re))
    (fun (v, e) -> "(" ^ v ^ ", " ^ e ^ ")")
    ~msg
    expected srecvd


let returns_error ?(msg="") (prn: 'a -> string) (f: unit -> 'a traceresult) =
  let r = f () in
  if not (Result.is_error r) then
    let v = Result.get_ok r in
    A.fail "Error result" ("Ok result:" ^ (prn v)) msg
  else
    ()


let equal_param_locations
      ?(msg="")
      ~(expected: parameter_location_t list)
      ~(received: parameter_location_t list) () =
  A.make_equal_list
    parameter_location_equal
    parameter_location_to_string
    ~msg
    expected
    received


let equal_fts_parameter
      ?(msg="")
      ~(expected: fts_parameter_t)
      ~(received: fts_parameter_t) () =
  A.make_equal
    fts_parameter_equal
    fts_parameter_to_string
    ~msg
    expected
    received


let equal_arm_argument_state
      ?(msg="")
      ~(expected: arm_argument_state_t)
      ~(received: arm_argument_state_t) () =
  A.make_equal
    arm_argument_state_equal
    arm_argument_state_to_string
    ~msg
    expected
    received


type x_fts_loc_t = {
    xftsl_kind: string;
    xftsl_type: btype_t;
    xftsl_offset: string;
    xftsl_reg: string
  }

type x_fts_param_t = {
    xfts_index: int;
    xfts_name: string;
    xfts_type: btype_t;
    xfts_size: int;
    xfts_locations: x_fts_loc_t list
  }


let equal_function_parameters
      ?(msg="")
      ~(expected: (x_fts_param_t list))
      ~(received: (fts_parameter_t list))
      () =
  let convert_paramloc (l: parameter_location_t): x_fts_loc_t =
    match l with
    | StackParameter (i, pld) ->
       { xftsl_kind = "s";
         xftsl_type = pld.pld_type;
         xftsl_offset = string_of_int i;
         xftsl_reg = "none"
       }
    | RegisterParameter (r, pld) when Option.is_some pld.pld_extract ->
       { xftsl_kind = "rp";
         xftsl_type = pld.pld_type;
         xftsl_offset =
           string_of_int (fst (Option.get pld.pld_extract));
         xftsl_reg = register_to_string r
       }
    | RegisterParameter (r, pld) ->
        { xftsl_kind = "r";
          xftsl_type = pld.pld_type;
          xftsl_offset = "-1";
          xftsl_reg = register_to_string r
        }
    | GlobalParameter (dw, pld) ->
       { xftsl_kind = "g";
         xftsl_type = pld.pld_type;
         xftsl_offset = dw#to_hex_string;
         xftsl_reg = "none"
       }
    | UnknownParameterLocation pld ->
       { xftsl_kind = "u";
         xftsl_type = pld.pld_type;
         xftsl_offset = "-1";
         xftsl_reg = "none"
       } in

  let convert_param (p: fts_parameter_t): x_fts_param_t =
    { xfts_index = (match p.apar_index with Some i -> i | _ -> (-1));
      xfts_name = p.apar_name;
      xfts_type = p.apar_type;
      xfts_size = p.apar_size;
      xfts_locations = List.map convert_paramloc p.apar_location
    } in

  let recvd = List.map convert_param received in
  let btstr (ty: btype_t): string =
    match ty with
    | TComp _ ->
       let cinfo = get_struct_type_compinfo ty in
       "struct " ^ cinfo.bcname
    | _ -> btype_to_string ty in
  A.make_equal_list
    (fun xfts rfts ->
      (List.length xfts.xfts_locations) = (List.length rfts.xfts_locations)
      && xfts.xfts_index = rfts.xfts_index
      && xfts.xfts_name = rfts.xfts_name
      && (btstr xfts.xfts_type) = (btstr rfts.xfts_type)
      && xfts.xfts_size = rfts.xfts_size
      && List.for_all2
           (fun xl rl ->
             xl.xftsl_kind = rl.xftsl_kind
             && btype_equal xl.xftsl_type rl.xftsl_type
             && xl.xftsl_offset = rl.xftsl_offset
             && xl.xftsl_reg = rl.xftsl_reg) xfts.xfts_locations rfts.xfts_locations)
    (fun p ->
      "("
      ^ (string_of_int p.xfts_index)
      ^ ", "
      ^ p.xfts_name
      ^ ", "
      ^ (btstr p.xfts_type)
      ^ ", "
      ^ (string_of_int p.xfts_size)
      ^ ", "
      ^ "["
      ^ (String.concat
           "; "
           (List.map
              (fun pl ->
                "("
                ^ pl.xftsl_kind
                ^ ", "
                ^ (btstr pl.xftsl_type)
                ^ ", "
                ^ pl.xftsl_offset
                ^ ", "
                ^ pl.xftsl_reg
                ^ ")") p.xfts_locations))
      ^ "])")
    ~msg
    expected
    recvd
