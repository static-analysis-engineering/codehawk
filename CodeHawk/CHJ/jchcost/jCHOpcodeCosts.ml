(* =============================================================================
   CodeHawk Java Analyzer
   Author: Andrew McGraw and Henny Sipma
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

(* jchlib *)
open JCHBasicTypesAPI


let get_opcode_cost (opc:opcode_t):int =
  match opc with
  | OpLoad _  -> 2
  | OpStore _ -> 2
  | OpIInc _  -> 2

  | OpPop    -> 2
  | OpPop2   -> 2  (* TBD *)
  | OpDup    -> 2
  | OpDupX1  -> 4  (* TBD *)
  | OpDupX2  -> 4  (* TBD *)
  | OpDup2   -> 4  (* TBD *)
  | OpDup2X1 -> 4  (* TBD *)
  | OpDup2X2 -> 4  (* TBD *)
  | OpSwap   -> 4  (* TBD *)

  | OpAConstNull    -> 15
  | OpIntConst _    -> 2
  | OpLongConst _   -> 2
  | OpFloatConst _  -> 2
  | OpDoubleConst _ -> 2
  | OpByteConst _   -> 2
  | OpShortConst _  -> 2
  | OpStringConst _ -> 4
  | OpClassConst _  -> 3

  | OpAdd Float   -> 3
  | OpAdd Double  -> 3
  | OpAdd Long    -> 3
  | OpAdd _       -> 2
  | OpSub Float   -> 3
  | OpSub Double  -> 3
  | OpSub Long    -> 3
  | OpSub _       -> 2
  | OpMult Float  -> 3
  | OpMult Double -> 3
  | OpMult Long   -> 3
  | OpMult _      -> 1
  | OpDiv Float   -> 3
  | OpDiv Double  -> 3
  | OpDiv Long    -> 21
  | OpDiv _       -> 3
  | OpRem Long    -> 22
  | OpRem _       -> 4
  | OpNeg _       -> 2

  | OpIShl  -> 3
  | OpLShl  -> 1
  | OpIShr  -> 1
  | OpLShr  -> 1
  | OpIUShr -> 1
  | OpLUShr -> 1
  | OpIAnd  -> 2
  | OpLAnd  -> 1
  | OpIOr   -> 2
  | OpLOr   -> 1
  | OpIXor  -> 2
  | OpLXor  -> 1

  (* Conversion *)
  | OpI2L   -> 1
  | OpI2F   -> 2
  | OpI2D   -> 2
  | OpL2I   -> 1
  | OpL2F   -> 2
  | OpL2D   -> 2
  | OpF2I   -> 3
  | OpF2L   -> 3
  | OpF2D   -> 2
  | OpD2I   -> 3
  | OpD2L   -> 3
  | OpD2F   -> 2
  | OpI2B   -> 1
  | OpI2C   -> 1
  | OpI2S   -> 1

  | OpCmpL  -> 15
  | OpCmpFL -> 16
  | OpCmpFG -> 16
  | OpCmpDL -> 16
  | OpCmpDG -> 16

  | OpIfEq _      -> 3
  | OpIfNe _      -> 5
  | OpIfLt _      -> 5
  | OpIfGe _      -> 5
  | OpIfGt _      -> 5
  | OpIfLe _      -> 3
  | OpIfNull _    -> 8
  | OpIfNonNull _ -> 4
  | OpIfCmpEq _   -> 4
  | OpIfCmpNe _   -> 4
  | OpIfCmpLt _   -> 4
  | OpIfCmpGe _   -> 6
  | OpIfCmpGt _   -> 4
  | OpIfCmpLe _   -> 4
  | OpIfCmpAEq _  -> 3
  | OpIfCmpANe _  -> 3

  | OpGoto _      -> 0
  | OpJsr _       -> 10   (* Deprecated *)
  | OpRet _       -> 10   (* Deprecated *)
  | OpTableSwitch _ -> 15
  | OpLookupSwitch _ -> 10 (* TBD *)

  | OpNew _        -> 10 (* TBD *)
  | OpNewArray _   -> 180
  | OpAMultiNewArray _  -> 400
  | OpCheckCast _     -> 10 (* TBD *)
  | OpInstanceOf _    -> 6
  | OpGetStatic _     -> 6
  | OpPutStatic _     -> 7
  | OpGetField _      -> 2
  | OpPutField _      -> 4
  | OpArrayLength     -> 1
  | OpArrayLoad _     -> 3
  | OpArrayStore _    -> 7

  | OpInvokeVirtual _   -> 12
  | OpInvokeSpecial _   -> 12
  | OpInvokeStatic _    -> 158
  | OpInvokeInterface _ -> 12   (* TBD *)
  | OpInvokeDynamic _   -> 200  (* TBD *)
  | OpReturn _          -> 6

  | OpThrow -> 354
  | OpMonitorEnter -> 100 (* TBD *)
  | OpMonitorExit  -> 100 (* TBD *)

  | OpNop -> 0
  | OpBreakpoint -> 0
  | OpInvalid -> 0
