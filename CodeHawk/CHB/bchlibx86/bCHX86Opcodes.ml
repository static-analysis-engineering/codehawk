(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019  Kestrel Technology LLC
   Copyright (c) 2020-2022  Henny Sipma
   Copyright (c) 2023       Aarno Labs LLC

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

(* =============================================================================
   The implementation in this file is based on the documents:

   Intel 64 and IA-32 Architectures Software Developer's Manual, September 2010
   Volume 2A: Instruction Set Reference, A-M
   Volume 2B: Instruction Set Reference, N-Z
   ============================================================================= *)

(* chlib *)
open CHPretty
open CHNumerical

(* chutil *)
open CHLogger

(* bchlib *)
open BCHLibTypes
open BCHFunctionData
open BCHSystemInfo

(* bchlibx86 *)
open BCHLibx86Types


let is_function_entry_point = functions_data#is_function_entry_point


let get_opt_function_name fa =
  if functions_data#is_function_entry_point fa
     && functions_data#has_function_name fa then
    Some (functions_data#get_function fa)#get_function_name
  else
    None


let not_code_to_string nc =
  match nc with 
  | JumpTable jt -> jt#toString ~is_function_entry_point ~get_opt_function_name
  | DataBlock db -> db#toString


let not_code_to_pretty nc = 
  match nc with 
  | JumpTable jt -> jt#toPretty ~is_function_entry_point ~get_opt_function_name
  | DataBlock db -> db#toPretty


let not_code_length nc =
  match nc with JumpTable jt -> jt#get_length | DataBlock db -> db#get_length


let not_code_set_string nc s = 
  match nc with DataBlock db -> db#set_data_string s | _ -> ()


let index_to_condition_code (i:int) =
  match i with
  |  0 -> CcOverflow
  |  1 -> CcNotOverflow
  |  2 -> CcCarry
  |  3 -> CcNotCarry
  |  4 -> CcZero
  |  5 -> CcNotZero
  |  6 -> CcBelowEqual
  |  7 -> CcAbove
  |  8 -> CcSign
  |  9 -> CcNotSign
  | 10 -> CcParityEven
  | 11 -> CcParityOdd
  | 12 -> CcLess
  | 13 -> CcGreaterEqual
  | 14 -> CcLessEqual
  | 15 -> CcGreater
  | _ ->
    begin
      ch_error_log#add "disassemly" (LBLOCK [ STR "Invalid condition code: " ; INT i ]) ;
      raise (Invalid_argument ("invalid condition code: " ^ (string_of_int i)))
    end


let condition_code_to_suffix_string (cc:condition_code_t) =
  match cc with
  | CcOverflow -> "o"
  | CcNotOverflow -> "no"
  | CcCarry -> "c"
  | CcNotCarry -> "nc"
  | CcZero -> "z"
  | CcNotZero -> "nz"
  | CcBelowEqual -> "be"
  | CcAbove -> "a"
  | CcSign -> "s"
  | CcNotSign -> "ns"
  | CcParityEven -> "pe"
  | CcParityOdd -> "po"
  | CcLess -> "l"
  | CcGreaterEqual -> "ge"
  | CcLessEqual -> "le"
  | CcGreater -> "g"


let condition_code_to_name (cc:condition_code_t) =
  match cc with
  | CcOverflow -> "Overflow"
  | CcNotOverflow -> "NotOverflow"
  | CcCarry -> "Carry"
  | CcNotCarry -> "NotCarry"
  | CcZero -> "Zero"
  | CcNotZero -> "NotZero"
  | CcBelowEqual -> "BelowEqual"
  | CcAbove -> "Above"
  | CcSign -> "Sign"
  | CcNotSign -> "NotSign"
  | CcParityEven -> "ParityEven"
  | CcParityOdd -> "ParityOdd"
  | CcLess -> "Less"
  | CcGreaterEqual -> "GreaterEqual"
  | CcLessEqual -> "LessEqual"
  | CcGreater -> "Greater"


let flags_used_by_condition (cc:condition_code_t) =
  match cc with
  | CcOverflow    | CcNotOverflow  -> [ OFlag ]
  | CcCarry       | CcNotCarry     -> [ CFlag ]
  | CcZero        | CcNotZero      -> [ ZFlag ]
  | CcBelowEqual  | CcAbove        -> [ CFlag ; ZFlag ]
  | CcSign        | CcNotSign      -> [ SFlag ]
  | CcParityEven  | CcParityOdd    -> [ PFlag ]
  | CcLess        | CcGreaterEqual -> [ SFlag ; OFlag ]
  | CcLessEqual   | CcGreater      -> [ ZFlag ; SFlag ; OFlag ]


let width_suffix_string (w:int) =
  match w with
  | 0 -> "z"
  | 1 -> "b"
  | 2 -> "w"
  | 4 -> "d"
  | 8 -> "q"
  | 16 -> "dq"
  | _ -> "u"
 

let is_nop_instruction (opcode:opcode_t) =
  match opcode with
  | BreakPoint -> true
  | Xchg (op1,op2) when op1#equal op2 -> true
  | Mov (_, op1,op2) when op1#equal op2 -> true
  | Lea (dst,src) ->
    begin 
      match src#get_kind with
      | IndReg (opr,offset)
        | ScaledIndReg (Some opr,None,1,offset) ->
	 dst#is_register && (opr = dst#get_cpureg) && offset#equal numerical_zero
      | _ -> false
    end
  | _ -> false
 
