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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

let make_class_name = common_dictionary#make_class_name 

class type signature_bindings_int =
object
  (* accessors *)
  method get_this_variable: variable_t
  method get_indexed_ref_arguments: (int * variable_t) list
  method get_indexed_string_arguments: (int * variable_t) list
  method get_ref_argument_types   : (variable_t * value_type_t) list

  (* predicates *)
  method has_this_variable: bool
  method is_static        : bool
end

let is_arg s = s#getBaseName = "arg" 

let get_arg_index s = 
  if is_arg s then
    match s#getAttributes with
      h::_ ->
	begin
	  try
	    int_of_string h
	  with
	    _ ->
            raise (JCH_failure
                     (LBLOCK [ STR "Invalid argument symbol: " ; s#toPretty ]))
	end
    | _ ->
      raise (JCH_failure (LBLOCK [ STR "Invalid argument symbol: " ; s#toPretty ]))
  else
    raise (JCH_failure (LBLOCK [ STR "Symbol is not an argument: " ; s#toPretty ]))


class signature_bindings_t 
        (signature:method_signature_int)
        (bindings:bindings_t)
        (is_static:bool):signature_bindings_int =
object (self:_)

  method get_this_variable = 
    if is_static then
      raise (JCH_failure (LBLOCK [ STR "Static method does not have this-variable" ]))
    else
      try
	let (_,v) = List.find (fun (s,_) -> is_arg s && (get_arg_index s) = 0) bindings in v
      with
	Not_found ->
	raise (JCH_failure (LBLOCK [ STR "Bindings do not have argument 0: " ; 
				     bindings_to_pretty bindings ]))

  method private get_arg_type s = 
    let index = get_arg_index s in
    let signatureIndex = if is_static then index else index - 1 in
    try
      List.nth signature#descriptor#arguments signatureIndex
    with
      _ -> raise (JCH_failure (LBLOCK [ STR "Index argument out of range: " ; s#toPretty ]))
	 
  method private is_proper_argument s =
    is_arg s && (is_static || (get_arg_index s) > 0)

  method get_indexed_ref_arguments =
    List.fold_left (fun a (s,v) ->
        if self#is_proper_argument s then
	  let adjustment = if is_static then 1 else 0 in
	  let index = (get_arg_index s) + adjustment in
	  match self#get_arg_type s with
          | TObject _ -> (index, v) :: a 
	  | _ -> a
        else
	  a) [] bindings

  method get_indexed_string_arguments =
    let stringObj = make_class_name "java.lang.String" in
    List.fold_left (fun a (s,v) ->
	if self#is_proper_argument s then
	  let adjustment = if is_static then 1 else 0 in
	  let index = (get_arg_index s) + adjustment in
	  match self#get_arg_type s with
          | TObject (TClass cn) when cn#equal stringObj ->
	     (index, v) :: a
	  | _ -> a
	else
	  a) [] bindings
    
  method get_ref_argument_types =
    List.fold_left (fun a (s,v) ->
        if self#is_proper_argument s then
	  match self#get_arg_type s with
	  | TObject _  as ty -> (v,ty) :: a
	  | _ -> a
        else
	  a) [] bindings

  method is_static = is_static

  method has_this_variable =
    (not is_static) 
    && List.exists (fun (s,_) -> is_arg s && (get_arg_index s) = 0) bindings

end

let get_signature_bindings signature bindings is_static = 
  new signature_bindings_t signature bindings is_static
