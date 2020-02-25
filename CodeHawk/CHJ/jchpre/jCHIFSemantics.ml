(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
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
open CHPretty
open CHLanguage
open CHAtlas
open CHIterator


class type j_semantics_int =
object
  method stable       : system_int -> iterator_t -> int -> int -> op_arg_t list -> atlas_t -> unit
  method propagate_fwd: system_int -> iterator_t -> int -> int -> op_arg_t list -> atlas_t -> atlas_t 
  method propagate_bwd: system_int -> iterator_t -> int -> int -> op_arg_t list -> atlas_t -> atlas_t 
end

class type j_opsemantics_int =
object
  method i_semantics       : j_semantics_int
  method ii_semantics      : j_semantics_int
  method e_semantics       : j_semantics_int
  method init_semantics    : j_semantics_int
  method exit_semantics    : j_semantics_int
  method exn_exit_semantics: j_semantics_int
end

class j_nop_semantics_t:j_semantics_int = 
object
  method stable        
    (sys:system_int) (it:iterator_t) (proc_id:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = ()
  method propagate_fwd 
    (sys:system_int) (it:iterator_t) (proc_id:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = inv
  method propagate_bwd 
    (sys:system_int) (it:iterator_t) (proc_id:int) (pc:int) (args:op_arg_t list) (inv:atlas_t) = inv
end

let j_nop_semantics = new j_nop_semantics_t

class j_nop_opsemantics_t:j_opsemantics_int =
object
  method i_semantics = j_nop_semantics
  method ii_semantics = j_nop_semantics
  method e_semantics = j_nop_semantics
  method init_semantics = j_nop_semantics
  method exit_semantics = j_nop_semantics
  method exn_exit_semantics = j_nop_semantics
end

let j_nop_opsemantics = new j_nop_opsemantics_t

let opsemantics ?(remove_dead_vars=true) (system:system_int) (procname:symbol_t) (sem:j_opsemantics_int) =
  fun ~invariant ~stable ~fwd_direction ~context ~operation ->
  let strategy = { widening = (fun _ -> (true,"")) ; narrowing = (fun _ -> true) } in
  let iterator = new iterator_t ~do_loop_counters:false ~strategy system in
  let opType  = operation.op_name#getBaseName in
  let pc = operation.op_name#getSeqNumber in
  let procId = procname#getSeqNumber in
  let args = operation.op_args in
  let _ =
    if stable then
      match opType with
      | "i" -> sem#i_semantics#stable system iterator procId pc args invariant
      | "ii" -> sem#ii_semantics#stable system iterator procId pc args invariant
      | "e" -> sem#e_semantics#stable system iterator procId pc args invariant
      | "method-init" -> sem#init_semantics#stable system iterator procId pc args invariant
      | "normal-exit" -> sem#exit_semantics#stable system iterator procId pc args invariant
      | "exn-exit" -> sem#exn_exit_semantics#stable system iterator procId pc args invariant
      | _ -> () in
  if fwd_direction then
    match opType with
    | "i" -> sem#i_semantics#propagate_fwd system iterator procId pc args invariant
    | "ii" -> sem#ii_semantics#propagate_fwd system iterator procId pc args invariant
    | "e" -> sem#e_semantics#propagate_fwd system iterator procId pc args invariant
    | "method-init" -> sem#init_semantics#propagate_fwd system iterator procId pc args invariant
    | "normal-exit" -> sem#exit_semantics#propagate_fwd system iterator procId pc args invariant
    | "exn-exit" -> sem#exn_exit_semantics#propagate_fwd system iterator procId pc args invariant
    | "dead_vars" when remove_dead_vars-> 
       invariant#analyzeFwd (ABSTRACT_VARS (List.map (fun (_,v,_) -> v) args))
    | _ ->
       invariant#analyzeFwd
	 (ABSTRACT_VARS
	    (List.map (fun (_,v,_) -> v)
		      (List.filter (fun (_,_,m) -> match m with WRITE -> true | _ -> false) args)))
  else
    match opType with
    | "i" -> sem#i_semantics#propagate_bwd system iterator procId pc args invariant
    | "ii" -> sem#ii_semantics#propagate_bwd system iterator procId pc args invariant
    | "e" -> sem#e_semantics#propagate_bwd system iterator procId pc args invariant
    | "method-init" -> sem#init_semantics#propagate_bwd system iterator procId pc args invariant
    | "normal-exit" -> sem#exit_semantics#propagate_bwd system iterator procId pc args invariant
    | "exn-exit" -> sem#exn_exit_semantics#propagate_bwd system iterator procId pc args invariant
    | "dead_vars" when remove_dead_vars-> 
       invariant#analyzeBwd (ABSTRACT_VARS (List.map (fun (_,v,_) -> v) args))
    | _ ->
       invariant#analyzeBwd
	 (ABSTRACT_VARS
	    (List.map (fun (_,v,_) -> v)
		      (List.filter (fun (_,_,m) -> match m with WRITE -> true | _ -> false) args)))
      
      
      
