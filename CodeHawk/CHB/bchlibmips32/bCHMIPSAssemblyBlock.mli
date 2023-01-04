(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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

(* bchlibmips32 *)
open BCHMIPSTypes

val make_mips_assembly_block:
  ?ctxt:context_t list   (* context, outer function first *)
  -> doubleword_int      (* function address *)
  -> doubleword_int          (* address of first instruction *)
  -> doubleword_int          (* address of last instruction *)
  -> ctxt_iaddress_t list    (* successors *)
  -> mips_assembly_block_int

val make_ctxt_mips_assembly_block:
  context_t                (* new context to be prepended *)
  -> mips_assembly_block_int
  -> ctxt_iaddress_t list  (* new successor blocks *)
  -> mips_assembly_block_int

val make_block_ctxt_mips_assembly_block:
  context_t
  -> mips_assembly_block_int
  -> mips_assembly_block_int

val update_mips_assembly_block_successors:
  mips_assembly_block_int   (* original block *)
  -> ctxt_iaddress_t        (* original successor *)
  -> ctxt_iaddress_t        (* replacement successor *)
  -> mips_assembly_block_int
