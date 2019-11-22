(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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
  ------------------------------------------------------------------------------ *)

(* chlib *)
open CHCommon
open CHLanguage   
open CHPretty

   
module UF =
  CHUnionFind.Make
    (struct 
      type t = variable_t
      let toPretty v = v#toPretty
      let compare v = v#compare
    end)
  
class virtual ['a] symbolic_type_refinement_t =
object (self: _)
  
  inherit ['a] UF.union_find_with_attributes_t
  inherit code_walker_t as super
        
  method virtual analyzeOperation: operation_t -> unit
               
  method virtual abstract: variable_t -> unit
               
  method virtual refineSymbolicType: 'a -> variable_type_t
               
  method walkCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | ASSIGN_SYM (x, e) ->
       begin
	 match e with
	 | SYM s -> self#abstract x
	 | SYM_VAR y -> 
	    begin
	      self#union x y;
	      match (x#getPath, y#getPath) with
	      | ([], []) -> if x#isTmp || y#isTmp then self#abstract x else ()
	      | _ -> self#abstract x
	    end
       end
    | ASSIGN_SYM_ELT (_, _, v) 
      | READ_SYM_ELT (v, _, _) -> self#abstract v
    | SELECT args -> List.iter (fun (_, v) ->	if v#isSymbolic then self#abstract v else ()) args.selected
    | INSERT args -> List.iter (fun (_, v) ->	if v#isSymbolic then self#abstract v else ()) args.values
    | OPERATION o -> self#analyzeOperation o
    | CALL (_, args) -> List.iter (fun (_, v) -> if v#isSymbolic then self#abstract v else ()) args
    | _ -> super#walkCmd cmd
         
  method analyzeProcedure (proc: procedure_int) =
    self#reset;
    self#walkCode proc#getBody
    
  method transformProcedure (proc: procedure_int) =
    let refine v =
      if v#isSymbolic && not(v#isTmp || v#isArray) then
	match self#get v with
	| None -> v
	| Some a -> v#transformType (self#refineSymbolicType a)
      else
	v
    in
    proc#getScope#transformVariables refine
    
end
        
        
