(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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
open CHPretty
open CHUtils

class dominance_info_t :
  cfg_int ->
    object
      method is_dominated_or_is_unreachable : symbol_t -> symbol_t -> bool
      method find_common_dominator :  symbol_t list -> symbol_t list
      method find_dominator_tree : int array * int array array
      method get_dominance_frontier : unit
      method get_index : symbol_t -> int
      method get_dom_frontier : int -> SymbolCollections.set_t
      method get_immediate_dominated_children :
          symbol_t -> SymbolCollections.set_t
      method get_nr_states : int
      method get_state : int -> symbol_t
      method is_reachable : symbol_t -> bool
      method toPretty : pretty_t
    end

val find_dominance_frontier :
  symbol_t -> cfg_int -> dominance_info_t
