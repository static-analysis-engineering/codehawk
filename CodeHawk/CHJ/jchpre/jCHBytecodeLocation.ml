(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHPreAPI

module H = Hashtbl


let check_symbol (sym:symbol_t) (names:string list) =
  if List.mem sym#getBaseName names then
    ()
  else
    raise_jch_failure
      (LBLOCK [
           STR "Mismatch in symbol use: ";
           sym#toPretty;
	   STR " (expected one of: ";
	   pretty_print_list names (fun s -> STR s) "[" "," "]";
	   STR ")"])


class bytecode_location_t 
  ~(method_index:int) 
  ~(pc:int) 
  ~(is_modified:bool):bytecode_location_int =
object (self:'a)

  method m = method_index
  method i = pc

  method compare (other:'a) =
    let c1 = Stdlib.compare pc other#get_pc in
    if c1 = 0 then 
      let c2 = Stdlib.compare method_index other#get_method_index in
      if c2 = 0 then
	Stdlib.compare is_modified other#is_modified
      else c2
    else c1
  method get_class_method_signature = retrieve_cms method_index
  method get_method_index = method_index
  method get_pc = pc
  method is_modified = is_modified

  method toString = 
    let cms = self#get_class_method_signature in
    cms#class_name#simple_name
    ^ ":"
    ^ cms#method_signature#name
    ^ "@"
    ^ (string_of_int pc)

  method toPretty = 
    let cms =
      self#get_class_method_signature in
    LBLOCK [cms#toPretty; STR "; pc="; INT pc]
end


let get_bytecode_location (method_index:int) (pc:int) =
  new bytecode_location_t ~method_index ~pc ~is_modified:false


let get_bytecode_location_in_proc (procname:symbol_t) (opname:symbol_t) =
  let _ = check_symbol procname [ "procname" ] in
  let _ = check_symbol opname [ "i" ; "ii" ; "v" ] in
  let pc  = opname#getSeqNumber in
  let is_modified = opname#getBaseName = "ii" in
  new bytecode_location_t
    ~method_index:procname#getSeqNumber ~pc:pc ~is_modified:is_modified
  

class type operation_locations_int =
object
  method add_operation:bytecode_location_int -> operation_t -> unit
  method get_operation:bytecode_location_int -> operation_t
  method has_operation:bytecode_location_int -> bool
end


class operation_locations_t:operation_locations_int =
object

  val store = H.create 53
  
  method add_operation (loc:bytecode_location_int) (op:operation_t) =
    if H.mem store (loc#m,loc#i) then () else H.add store (loc#m,loc#i) op

  method get_operation (loc:bytecode_location_int) =
    try
      H.find store (loc#m,loc#i) 
    with Not_found ->
      begin
	ch_error_log#add
          "invocation error"
          (LBLOCK [STR "operation_locations#get_operation"]);
	raise (JCH_failure (STR "operation_locations#get_operation"))
      end

  method has_operation (loc:bytecode_location_int) = H.mem store (loc#m,loc#i)

end


let operation_locations = new operation_locations_t
