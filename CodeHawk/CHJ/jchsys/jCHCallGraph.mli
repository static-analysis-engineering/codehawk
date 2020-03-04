(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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

(* chlib *)
open CHLanguage
open CHPretty
open CHUtils

class call_graph_manager_t :
  symbol_t list 
  -> IntCollections.set_t
  -> (symbol_t * symbol_t) list
  -> object ('a)
       method does_not_access_static_fields : symbol_t -> bool
       method get_bottom_up_list : symbol_t list * SymbolCollections.set_t
       method get_ancestors : symbol_t -> symbol_t list  
       method get_descendants : symbol_t list -> symbol_t list 
       method get_unsynchronized_descendants : symbol_t list -> symbol_t list 
       method get_top_down_list : symbol_t list * SymbolCollections.set_t
       method graph_to_pretty : pretty_t
       method is_recursive : symbol_t -> bool
       method pr__debug : unit 
       method toPretty : pretty_t
     end

val set_no_temp_files : unit -> unit
