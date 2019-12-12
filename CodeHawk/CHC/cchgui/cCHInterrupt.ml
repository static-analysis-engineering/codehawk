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
open CHPretty

exception RequestInterrupt
exception RequestSkip

class type interrupt_handler_int =
object
  method request_interrupt: unit
  method request_skip     : unit

  method clear_interrupt: unit
  method clear_skip     : unit

  method reset: unit

  method is_interrupt_requested: bool
  method is_skip_requested     : bool
end

class interrupt_handler_t =
object

  val mutable interrupt_requested = false
  val mutable skip_requested = false

  method request_interrupt = interrupt_requested <- true
 
  method request_skip = skip_requested <- true

  method clear_interrupt = interrupt_requested <- false
      
  method clear_skip = skip_requested <- false

  method reset = begin interrupt_requested <- false ; skip_requested <- false end

  method is_interrupt_requested = interrupt_requested

  method is_skip_requested = skip_requested

end

let interrupt_handler = new interrupt_handler_t
