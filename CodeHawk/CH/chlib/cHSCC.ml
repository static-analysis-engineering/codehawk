(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
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
  ============================================================================== *)

(* chlib *)
open CHBounds
open CHCollections   
open CHCommon
open CHLanguage
open CHNumerical   
open CHPretty
open CHStack   
open CHUtils

let zero = new bound_t (NUMBER numerical_zero)  
let one = new bound_t (NUMBER numerical_one)      
        
class loop_stack_t =
object (_: 'a)
     
  val stack = []
            
  method getStack = stack
                  
  method push (e: symbol_t) = {< stack = stack @ [e] >}
                            
  method isPrefix (s: 'a) =
    let rec parse l1 l2 =
      match (l1, l2) with
      | (e1 :: t1, e2 :: t2) -> (e1#equal e2) && (parse t1 t2)
      | ([], _) -> true
      | (_, _) -> false
    in
    parse stack s#getStack
    
  method delta (s: 'a) =
    let rec parse l1 l2 =
      match (l1, l2) with
      | (e1 :: t1, e2 :: t2) ->
         if e1#equal e2 then parse t1 t2 else (e1 :: t1, e2 :: t2)
      | _ -> (l1, l2)
    in
    let (suffix1, suffix2) = parse stack s#getStack in
    ({< stack = suffix1 >}, {< stack = suffix2 >})
    
  method toPretty = pretty_print_list stack (fun s -> s#toPretty) "[" ";" "]"
                  
end
  
type wto_component_t =
  | SCC of wto_t
  | VERTEX of symbol_t
            
and wto_t = wto_component_t list
          
let pretty_print_wto wto =
  let rec pp_comp c =
    match c with
    | SCC wto ->   pretty_print_list wto pp_comp "(" " " ")"
    | VERTEX s -> s#toPretty
  in
  pretty_print_list wto pp_comp "" " " ""
  
class wto_engine_t (g: graph_t) =
object (self: _)
     
  val graph = g
            
  val dfn = new SymbolCollections.table_t
          
  val mutable num = zero
                  
  val stack: symbol_t stack_t = new stack_t
                              
  val nodeToStack = new SymbolCollections.table_t
                  
  method getLoopStackTable = nodeToStack
                           
  method private shift vertex element =
    if element#equal vertex then
      ()
    else
      begin
	dfn#set element zero;
	self#shift vertex stack#pop
      end
    
  method private getDFN x =
    match dfn#get x with
    | Some n -> n
    | None -> zero
	    
  method private component loop_stack vertex =
    let partition = ref [] in
    let succs = graph#getNextNodes vertex in
    let _ = 
      List.iter (fun succ ->
	  if (self#getDFN succ)#equal zero then
	    let _ = self#visit loop_stack succ partition in ()
	  else
	    ()) succs
    in
    let _ = nodeToStack#set vertex loop_stack in
    SCC ((VERTEX vertex) :: (!partition))
    
  method private visit loop_stack vertex partition =
    begin
      stack#push vertex;
      num <- num#add one;
      dfn#set vertex num;
      let head = ref num in
      let loop = ref false in
      let succs = graph#getNextNodes vertex in
      begin
	List.iter (fun succ ->
	    let n = self#getDFN succ in
	    let min = 
	      if n#equal zero then
		self#visit loop_stack succ partition
	      else
		n
	    in
	    begin
	      if min#leq !head then
		begin
		  head := min;
		  loop := true
		end
	      else
		()
	    end) succs;
	let h = self#getDFN vertex in
	begin
	  if (!head)#equal h then
	    begin
	      dfn#set vertex (new bound_t PLUS_INF);	
	      let element = stack#pop in
	      if !loop then
		begin
		  self#shift vertex element;
		  partition := (self#component (loop_stack#push vertex) vertex) :: (!partition)
		end
	      else
		let _ = nodeToStack#set vertex loop_stack in
		partition := (VERTEX vertex) :: (!partition)
	    end
	  else
	    ()
	end;
	!head
      end
    end
    
  method computeWTO =
    let partition = ref [] in
    let _ = self#visit (new loop_stack_t) graph#getRootNode partition in
    !partition
    
end
  
