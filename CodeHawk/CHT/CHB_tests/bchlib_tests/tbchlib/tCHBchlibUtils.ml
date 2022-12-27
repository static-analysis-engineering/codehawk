(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022      Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes


let extract_chif_cfg_assignments
      ?(start=0) ?(len=0) (proc: procedure_int): (variable_t * numerical_exp_t) list =
  match proc#getBody#getCmdAt 0 with
  | CFG (_, cfg) ->
     let states = cfg#getStates in
     let state = List.hd (List.tl states) in
     let state = cfg#getState state in
     let cmd = state#getCode#getCmdAt 0 in
     (match cmd with
      | TRANSACTION (_, trcode, _) ->
         let trlen = trcode#length in
         if start < 0 || start > trlen then
           []
         else
           let len =
             if len <= 0 then
               (trlen - start) + len
             else
               len in
           if start + len > trlen then
             []
           else
             let assigns = ref [] in
             let len = if len = 0 then trlen else len in
             begin
               for i = start to (start + len) - 1 do
                 let trcmd = trcode#getCmdAt i in
                 (match trcmd with
                  | ASSIGN_NUM (v, e) -> assigns := (v, e) :: !assigns
                  | _ -> ())
               done;
               List.rev !assigns
             end
      | _ -> [])
  | _ -> []
