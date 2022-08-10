(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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
open CHPretty
open CHLanguage
open CHNumericalConstraints

(* bchlib *)
open BCHLibTypes
open BCHUtilities

module H = Hashtbl


let version_date = BCHUtilities.get_date_and_time ()
let get_version () = version_date

exception BCH_failure of pretty_t 

exception Internal_error of string
exception Invocation_error of string
exception Invalid_input of string

(* raised when control flow is found to be altered *)
exception Request_function_retracing

let eflags_to_string_table = H.create 6

let eflags_from_string_table = H.create 6

let arm_cc_flags_to_string_table = H.create 6

let arm_cc_flags_from_string_table = H.create 6

let _ =
  List.iter (fun (e,s) ->
      add_to_sumtype_tables eflags_to_string_table eflags_from_string_table e s)
    [(OFlag, "OF");
     (CFlag, "CF");
     (ZFlag, "ZF");
     (SFlag, "SF");
     (PFlag, "PF");
     (DFlag, "DF");
     (IFlag, "IF")]

let _ =
  List.iter (fun (f, s) ->
      add_to_sumtype_tables
        arm_cc_flags_to_string_table arm_cc_flags_from_string_table f s)
    [(APSR_Z, "Z"); (APSR_N, "N"); (APSR_C, "C"); (APSR_V, "V")]


let eflag_to_string (e: eflag_t) =
  get_string_from_table "eflags_to_string_table" eflags_to_string_table e


let eflag_from_string (name: string) =
  get_sumtype_from_table "eflags_from_string_table" eflags_from_string_table name


let eflag_compare (f1:eflag_t) (f2:eflag_t) = 
  Stdlib.compare (eflag_to_string f1) (eflag_to_string f2)


let arm_cc_flag_to_string (f: arm_cc_flag_t): string =
  get_string_from_table
    "arm_cc_flags_to_string_table" arm_cc_flags_to_string_table f


let arm_cc_flag_from_string (name: string): arm_cc_flag_t =
  get_sumtype_from_table
    "arm_cc_flags_from_string_table" arm_cc_flags_from_string_table name


let arm_cc_flag_compare (f1: arm_cc_flag_t) (f2: arm_cc_flag_t): int =
  Stdlib.compare (arm_cc_flag_to_string f1) (arm_cc_flag_to_string f2)


let flag_to_string (f: flag_t): string =
  match f with
  | X86Flag e -> eflag_to_string e
  | ARMCCFlag c -> arm_cc_flag_to_string c


let flag_from_string (name: string): flag_t =
  if H.mem arm_cc_flags_from_string_table name then
    ARMCCFlag (arm_cc_flag_from_string name)
  else if H.mem eflags_from_string_table name then
    X86Flag (eflag_from_string name)
  else
    raise
      (BCH_failure
         (LBLOCK [STR "Name of flag "; STR name; STR " not recognized"]))


let flag_compare (f1: flag_t) (f2: flag_t): int =
  match (f1, f2) with
  | (X86Flag e1, X86Flag e2) -> eflag_compare e1 e2
  | (X86Flag _, _) -> 1
  | (_, X86Flag _) -> -1
  | (ARMCCFlag c1, ARMCCFlag c2) -> arm_cc_flag_compare c1 c2

type risk_type_t =
  | OutOfBoundsRead
  | OutOfBoundsWrite
  | NullDereference
  | TypeConditionViolation
  | FunctionFailure
  
let risk_types_to_string_table = H.create 5
let risk_types_from_string_table = H.create 5

let _ = List.iter (fun (r,s) -> 
  add_to_sumtype_tables risk_types_to_string_table risk_types_from_string_table r s)
  [ (OutOfBoundsRead, "OBR") ;
    (OutOfBoundsWrite, "OBW" ) ;
    (NullDereference, "NDR" ) ;
    (TypeConditionViolation, "TCV") ;
    (FunctionFailure, "FAIL") ]
  
let risk_type_to_string (r:risk_type_t) = 
  get_string_from_table "risk_types_to_string_table" risk_types_to_string_table r
    
let risk_type_from_string (s:string) =
  get_sumtype_from_table "risk_types_from_string_table" risk_types_from_string_table s
    
let variable_to_pretty v = STR v#getName#getBaseName

let symbol_to_pretty s   = STR s#getBaseName

let factor_to_pretty f   = variable_to_pretty f#getVariable
  
let variable_to_string v = v#getName#getBaseName

let symbol_to_string s   = s#getBaseName

let factor_to_string f   = variable_to_string f#getVariable
  
  
