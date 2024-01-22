(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
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

(* cchlib *)
open CCHBasicTypes


class exp_transformer_t:
object
  method transform_exp: exp -> exp
  method transform_type: typ -> typ
  method transform_lval: lval -> lval
  method transform_lhost: lhost -> lhost
  method transform_offset: offset -> offset
end


class exp_walker_t:
object
  method walk_exp: exp -> unit
  method walk_type: typ -> unit
  method walk_lval: lval -> unit
  method walk_lhost: lhost -> unit
  method walk_offset: offset -> unit
end


class block_walker_t:
object
  method walk_block: block -> unit
  method walk_stmt: stmt -> unit
  method walk_stmtkind: stmtkind -> unit
  method walk_label: label -> unit
  method walk_instr: instr -> unit
  method walk_rhs: exp -> unit          (* evaluated only *)
  method walk_lhs: lval -> unit         (* lhs in assignment *)
  method walk_arg: exp -> unit          (* argument passed to function *)
  method walk_calltarget: exp -> unit
end


val get_exp_variables: exp -> int list         (* vid's *)

val get_block_variables: block -> int list     (* vid's *)
