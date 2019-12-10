(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma, Anca Browne
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

open Big_int_Z

(* chlib *)
open CHPretty

class type string_printer_int =
  object
    method print: pretty_t -> string
  end

(* Utility to convert pretty_t to string *)
class string_printer_t:string_printer_int =
object (self)
     
  val mutable do_tab = false
  val mutable str:string = ""
  val mutable lines = []
                    
  method private prl (t, l) =
    match l with
    | [] -> ()
    | p :: l -> 
       begin
	 self#printTabs (t, p);
	 self#prl (t, l)
       end
      
  method private prTabs t =
    if t = 0 then
      ()
    else
      begin
	str <- str ^ " ";
	self#prTabs (t - 1)
      end
    
  method private printTabs (t, p) =
    match p with
    | STR s ->
       begin
	 if do_tab then self#prTabs t else ();
	 do_tab <- false;
	 str <- str ^ s
       end
    | INT i ->
       begin
	 if do_tab then self#prTabs t else ();
	 do_tab <- false;
	 str <- str ^ (string_of_int i)
       end
    | NL ->
       begin
	 do_tab <- true;
	 lines <- str :: lines ;
	 str <- "" ;
       end
    | LBLOCK l ->
       self#prl (t, l)
    | ABLOCK a ->
       for i = 0 to (Array.length a) - 1 do
	 self#printTabs (t, a.(i))
       done
    | INDENT (tab, p) ->
       self#printTabs (t + tab, p)
      
  method print (p:pretty_t) =
    begin
      str <- "";
      do_tab <- true;
      lines <- [] ;
      self#printTabs (0, p);
      (*      str <- str ^ "\n" ;*)
      lines <- str :: lines ;
      String.concat "\n" (List.rev lines) 
    end
    
end
  
let string_printer = new string_printer_t
                   
let pretty_to_string = (new string_printer_t)#print
                     
(* Utility to pretty print lists *)
let list_to_pretty 
      (print_element:'a->pretty_t) 
      (separator:pretty_t) 
      (lst:'a list):pretty_t =
  List.fold_right 
    (fun s a ->
      LBLOCK [ print_element s ;
               if (a = LBLOCK []) then LBLOCK [] else separator ; a ])
    lst (LBLOCK [])
  
type string_alignment_t =
  | StrCenter
  | StrLeft
  | StrRight
  
(* Utility to create a fixed length string of length len
   from a shorter string 
 *)
let fixed_length_string ?(alignment=StrLeft) (s:string) (len:int) =
  let slen = String.length s in
  if slen < len then
    let padding = len - slen in
    let str = Bytes.make len ' ' in
    let left_margin = match alignment with
      | StrLeft -> 0
      | StrRight -> padding
      | StrCenter -> padding / 2 in
    begin
      Bytes.blit (Bytes.of_string s) 0 str left_margin slen ;
      Bytes.to_string str
    end
  else
    s
  
let fixed_length_pretty ?(alignment=StrLeft) (p:pretty_t) (len:int):pretty_t =
  let s = string_printer#print p in
  STR (fixed_length_string ~alignment:alignment s len)
  
(* Utility to create a repeating pattern string *)
let string_repeat (s:string) (n:int) = 
  let t = ref "" in 
  begin
    for i=0 to n-1 do t := !t ^ s done;
    !t
  end
  
(* Return the string of length n that ends with s (padded with leading
   zeroes) *)
let fixed_length_int_string (s:string) (len:int):string =
    let slen = String.length s in
    if slen < len then
      let str = Bytes.make len '0' in
      begin
        Bytes.blit (Bytes.of_string s) 0 str (len - slen) slen ;
        Bytes.to_string str
      end
    else
      s

(* Return the suffix of s that starts at the n'th character of s *)
let string_suffix (s:string) (n:int):string = 
  try
    String.sub s n ((String.length s) - n)
  with
    Invalid_argument _ ->
      let len = String.length s in
      let msg = "String.sub s " ^ (string_of_int n) ^ " on string of length " ^ (string_of_int len) in
      raise (Invalid_argument msg)

 
(* utility function to split a character separated string into
   a list of strings *)
let nsplit (separator:char) (s:string):string list =
  let result = ref [] in
  let len = String.length s in
  let start = ref 0 in
  begin
    while !start < len do
      let s_index = try String.index_from s !start separator with Not_found -> len in
      let substring = String.sub s !start (s_index - !start) in
      begin
	result := substring :: !result ;
	start := s_index + 1
      end 
    done;
    List.rev !result
  end
  
  
(* A simple pretty print for numbers of things *)
let pp_quantity (q:int) ?(numwidth=0) (singular:string) (plural:string) =
  let num =
    if numwidth = 0 then
      if q = 0 then STR "no " else INT q
    else
      if q = 0 then fixed_length_pretty ~alignment:StrRight (STR "no") numwidth
      else fixed_length_pretty ~alignment:StrRight (INT q) numwidth in
  if q = 1 then LBLOCK [ num ; STR " " ; STR singular ]
  else LBLOCK [ num ; STR " " ; STR plural ]
  
(* A simple pretty print for lists of elements that have toPretty *)
let pp_list xs = pretty_print_list xs (fun v -> v#toPretty) "{" " , " "}" 
               
(* A simple pretty print for lists of strings *)
let pp_list_str ss = pretty_print_list ss (fun s -> STR s) "{" " , " "}" 
                   
(* A simple pretty print for lists of integers *)
let pp_list_int is = pretty_print_list is (fun i -> INT i) "{" " , " "}" 
                   
(* Pretty print for arrays of elements with toPretty *)
let pp_array a = pp_list (Array.to_list a)
               
(* Pretty print for arrays of integers *)
let pp_array_int a = 
  pretty_print_list (Array.to_list a) (fun n -> INT n) "[| " "; " " |]";;

(* Pretty print for arrays of big_int *)
let pp_array_big_int a = 
  pretty_print_list (Array.to_list a) (fun n -> STR (string_of_big_int n)) "[| " "; " " |]";;

(* Pretty print for matrices of integers *)
let pp_matrix_int m = 
  let res = ref ([]: pretty_t list) in
  for i = (Array.length m) - 1 downto 0 do
    res := (pp_array_int m.(i)) :: (STR "; ") :: NL :: !res 
  done ;
  LBLOCK ((STR "[| ") :: (INDENT (3, LBLOCK !res)) :: [NL; STR "|]"]) ;;

(* Pretty print for matrices of big_int *)
let pp_matrix_big_int m = 
  let res = ref ([]: pretty_t list) in
  for i = (Array.length m) - 1 downto 0 do
    res := (pp_array_big_int m.(i)) :: (STR "; ") :: NL :: !res 
  done ;
  LBLOCK ((STR "[| ") :: (INDENT (3, LBLOCK !res)) :: [NL; STR "|]"]) ;;

(* Pretty print for stacks of elements with toPretty *)
let pp_stack stack = 
  let elements = ref [] in
  let addElem e = 
    elements := e :: !elements in
  let _ = Stack.iter addElem stack in
  pretty_print_list (List.rev !elements) (fun e -> e#toPretty) "{" "| " "}"
  
(* Pretty print for association lists of (int, int) *)
let pp_assoc_int_int assoc = 
  let pp_pair (i, j) = LBLOCK [STR "("; INT i; STR ", "; INT j; STR ")"] in
  pretty_print_list assoc pp_pair "{" ", " "}"
  
(* Pretty print for association lists of (int, big_int) *)
let pp_assoc_int_big_int assoc = 
  let pp_pair (i, j) = LBLOCK [STR "("; INT i; STR ", "; STR (string_of_big_int j); STR ")"] in
  pretty_print_list assoc pp_pair "{" ", " "}"
  
