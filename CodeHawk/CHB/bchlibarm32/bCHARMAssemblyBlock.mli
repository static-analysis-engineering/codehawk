(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023 Aarno Labs, LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


(** [make_arm_assembly_block ~ctxt faddr baddr laddr succ] returns a new basic
    block with context [ctxt], function address [faddr], first address [baddr],
    last address [laddr], and successors [succ].*)
val make_arm_assembly_block:
  ?ctxt:context_t list    (* inline context, other function first *)
  -> doubleword_int       (* function address *)
  -> doubleword_int       (* first address of the basic block *)
  -> doubleword_int       (* last address of the basic block *)
  -> ctxt_iaddress_t list (* addresses of successor blocks *)
  -> arm_assembly_block_int


(** [make_ctxt_arm_assembly_block ctxt blk succ] returns a new arm basic block
    that is a copy of [blk] with added context [ctxt] and added successors
    [succ]. This can be used to create an inlined block.*)
val make_ctxt_arm_assembly_block:
  context_t               (* new context to be prepended *)
  -> arm_assembly_block_int
  -> ctxt_iaddress_t list (* new successor blocks *)
  -> arm_assembly_block_int


(** [update_arm_assembly_block_successors block s_old s_new] returns a new
    assembly basic block that is identical to [block] except that successor
    [s_old] is replaced by (possibly multiple) successors [s_new].*)
val update_arm_assembly_block_successors:
  arm_assembly_block_int
  -> ctxt_iaddress_t
  -> ctxt_iaddress_t list
  -> arm_assembly_block_int
