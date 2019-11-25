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
   ============================================================================= *)

type pretty_t =
  | STR of string
  | INT of int
  | NL
  | LBLOCK of pretty_t list
  | ABLOCK of pretty_t array
  | INDENT of int * pretty_t

let pretty_print_list l p lpar comma rpar =
  let rec loop l p =
    match l with
      | [x] -> [p x; STR rpar]
      | x :: l -> (p x) :: (STR comma) :: (loop l p)
      | [] -> [STR rpar]
  in
    LBLOCK ((STR lpar) :: (loop l p))

let pretty_print_array a p lpar comma rpar =
  pretty_print_list (Array.to_list a) p lpar comma rpar
      
class pretty_printer_t out_stream =
object
  
  val mutable do_tab = false
  val out = out_stream
    
  method print p =    
    let prTabs t =
      for i = 0 to t - 1 do
	output_string out " "	
      done
    in

    let rec prl (t, l) =
      match l with
	| [] -> 
	    ()
	| p :: l ->
	    begin
	      printTabs (t, p);
	      prl (t, l)
	    end
	      
    and printTabs (t, p) =
      match p with
	| STR s ->      
	    begin
	      if do_tab then prTabs t else ();
	      do_tab <- false;
	      output_string out s
	    end
	| INT i ->
	    begin
	      if (do_tab) then prTabs t else ();
	      do_tab <- false;
	      output_string out (string_of_int i)
	    end
	| NL ->
	    begin
	      do_tab <- true;
	      output_string out "\n"
	    end
	| LBLOCK l ->
	    prl (t, l)
	| ABLOCK a ->
	    for i = 0 to (Array.length a) - 1 do
	      printTabs (t, a.(i))
	    done
	| INDENT (tab, p) ->
	    printTabs (t + tab, p)
    in
      begin
	do_tab <- true;
	printTabs (0, p);
	flush out
      end      	      

end
    
let pr_debug l =
  let pp = new pretty_printer_t stdout in
  pp#print (LBLOCK l)

let trace_level = ref 0
let set_trace_level n = trace_level := n

let pr_trace n l =
  if n < !trace_level then
    pr_debug l
  else
    ()
