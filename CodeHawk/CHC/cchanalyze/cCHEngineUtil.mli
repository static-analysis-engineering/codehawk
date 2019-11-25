(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHOnlineCodeSet

type cmd_t = (code_t, cfg_t) command_t
           
val symbol : ?atts:string list -> string -> symbol_t
  
val numbersymbol : ?atts:string list -> int -> string -> symbol_t
  
val symbol2string : < getSymbol : 'a list; .. > -> 'a
    
val getSymbolNumber : < getSeqNumber : 'a; .. > -> 'a
    
val add_to_symbol :
  < getSeqNumber : int; getSymbol : string list; .. > -> string -> symbol_t
    
val variable2string : variable_t -> string
  
val getOperationName : operation_t -> string
  
val getOperationSeqNumber : operation_t -> int
  
val mkCode : (code_int, CHLanguage.cfg_int) command_t list -> code_t
  
val mkScope : ?tmp_base:string -> unit -> scope_t
  
val mkState : symbol_t -> (code_int, cfg_int) command_t list -> state_t
  
val mkCFG : state_int -> state_int -> cfg_t
  
val mkProcedure :
  symbol_t 
  -> signature:signature_t 
  -> bindings:bindings_t 
  -> scope:scope_t 
  -> body:code_t
  -> procedure_t
  
val mkSystem : symbol_t -> system_t
