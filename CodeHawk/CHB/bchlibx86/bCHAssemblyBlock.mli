(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
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
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types


(** [make_assembly_block ctxt faddr baddr eaddr succs] returns a basic block
    for the function at address [faddr] with start address [baddr] and end
    address [eaddr] and successors [succs], represented as full-context
    addresses.

    The optional [ctxt] argument allows creating a basic block that is part
    of an inlined function or augmented path context. The context should be
    specified from the outside in (outer function address first).
*)
val make_assembly_block:
  ?ctxt:context_t list
  -> doubleword_int
  -> doubleword_int
  -> doubleword_int
  -> ctxt_iaddress_t list
  -> assembly_block_int

val make_ctxt_assembly_block:
  context_t                (* new context to be prepended *)
  -> assembly_block_int
  -> ctxt_iaddress_t list  (* new successor blocks *)
  -> assembly_block_int
