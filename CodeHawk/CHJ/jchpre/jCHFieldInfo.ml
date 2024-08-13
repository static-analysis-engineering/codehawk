(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI


module ClassMethodSignatureCollections = CHCollections.Make (
  struct
    type t = class_method_signature_int
    let compare cms1 cms2 = cms1#compare cms2
    let toPretty cms = cms#toPretty
  end)


class field_stub_t
  ~(is_static:bool)
  ~(is_final:bool)
  ~(is_not_null:bool)
  ~(is_interface_field:bool)
  ~(is_constant:bool)
  ~(inherited_from:class_field_signature_int option)
  ~(visibility:access_t)
  ~(field_value:constant_value_t option)
  ~(cfs:class_field_signature_int):field_stub_int =
object

  val cfs = cfs
  val is_static = is_static
  val is_final = is_final
  val is_not_null = is_not_null
  val is_constant = is_constant
  val is_interface_field = is_interface_field
  val inherited_from = inherited_from
  val visibiliy = visibility
  val field_value = field_value

  method get_class_name = cfs#class_name

  method get_signature = cfs#field_signature

  method get_class_signature = cfs

  method get_value =
    match field_value with
    | Some v -> v
    | _ ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Field "; cfs#toPretty; STR " does not have a value"]))

  method get_visibility = visibility

  method get_defining_class =
    match inherited_from with Some icfs -> icfs#class_name | _ -> cfs#class_name

  method get_defining_class_field_signature =
    match inherited_from with Some icfs -> icfs | _ -> cfs

  method is_static = is_static

  method is_final  = is_final

  method is_not_null = is_not_null

  method is_interface_field = is_interface_field

  method is_constant = is_constant || ( is_static && is_final)

  method is_inherited = match inherited_from with Some _ -> true | _ -> false

  method has_value = match field_value with Some _ -> true | _ -> false

  method set_inherited (new_cfs:class_field_signature_int) =
    {< cfs = new_cfs; inherited_from = Some cfs >}

  method toPretty = cfs#toPretty
end


class field_info_t
  ~(in_stubbed_class:bool)
  ~(field_info_type:field_info_type_t):field_info_int =
object (self:'a)

  val writing_methods = new ClassMethodSignatureCollections.set_t
  val reading_methods = new ClassMethodSignatureCollections.set_t
  val in_stubbed_class = in_stubbed_class
  val mutable initialized = false
  val mutable not_null = false
  val mutable array_length = None

  method compare (other:'a) = Stdlib.compare self#get_index other#get_index

  method add_writing_method cms = writing_methods#add cms

  method add_reading_method cms = reading_methods#add cms

  method set_not_null = begin initialized <- true; not_null <- true end

  method set_array_length (n:int) = array_length <- Some n

  method get_field = field_info_type

  method get_index = self#get_class_signature#index

  method get_class_name = self#get_class_signature#class_name

  method get_class_signature = match field_info_type with
  | ConcreteField f -> f#get_class_signature
  | StubbedField x  -> x#get_class_signature
  | MissingField cfs -> cfs

  method get_value =
    match field_info_type with
    | ConcreteField f ->
       begin match f#get_value with
       | Some ff -> ff
       | _ ->
	  raise
            (JCH_failure
	       (LBLOCK [
                    STR "Field ";
                    self#toPretty;
                    STR " does not have a constant value"]))
       end
    | MissingField cfs ->
       raise
         (JCH_failure
	    (LBLOCK [
                 STR "Field ";
                 cfs#toPretty;
                 STR " does not have a value ";
		 STR "(field was not located)"]))
    | StubbedField x -> x#get_value

  method get_array_length =
    match array_length with
    | Some n -> n
    | _ ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Field ";
		 self#toPretty;
                 STR " does not have an array length"]))

  method get_visibility = match field_info_type with
      ConcreteField f -> f#get_visibility
    | StubbedField x -> x#get_visibility
    | MissingField _ -> Public

  method has_value =
    match field_info_type with
    | ConcreteField f ->
       begin match f#get_value with Some _ -> true | _ -> false end
    | MissingField _ -> false
    | StubbedField x -> x#has_value

  method has_array_length =
    match array_length with Some _ -> true | _ -> false

  method get_reading_methods = reading_methods#toList

  method get_writing_methods = writing_methods#toList

  method is_missing =
    match field_info_type with MissingField _ -> true | _ -> false

  method is_stubbed =
    match field_info_type with StubbedField _ -> true | _ -> false

  method is_static = match field_info_type with
  | ConcreteField f -> f#is_static
  | StubbedField x  -> x#is_static
  | _ -> false

  method is_final = match field_info_type with
  | ConcreteField f -> f#is_final
  | StubbedField x  -> x#is_final
  | _ -> false

  method is_constant = match field_info_type with
  | ConcreteField f -> f#is_static && f#is_final
  | StubbedField x  -> x#is_constant
  | _ -> false

  method is_initialized = initialized

  method is_not_null = not_null
  || (match field_info_type with
      | ConcreteField f ->
         f#is_final
         && f#is_static
         && (match self#get_class_signature#field_signature#descriptor with
             | TObject _ -> true
             | _ -> false)
      | StubbedField x -> x#is_not_null
      | _ -> false)

  method is_private   =
    match self#get_visibility with Private -> true | _ -> false

  method is_protected =
    match self#get_visibility with Protected -> true | _ -> false

  method is_public =
    match self#get_visibility with Public -> true | _ -> false

  method is_default_access =
    match self#get_visibility with Default -> true | _ -> false

  method is_accessible_to_stubbed_methods =
    (in_stubbed_class || self#is_stubbed) && not self#is_constant

  method toPretty =
    let nr_readers = reading_methods#size in
    let nr_writers = writing_methods#size in
    let readers_writers_p =
      LBLOCK [
          STR " (writers: ";
          INT nr_writers;
          STR "; readers: ";
	  INT nr_readers;
          STR ")"] in
    let is_final_p  = if self#is_final then STR "final " else STR "" in
    let is_static_p = if self#is_static then STR "static " else STR "" in
    let is_constant_p =
      if self#is_constant then STR "constant " else STR "" in
    let is_private_p  =
      if self#is_private then STR "private " else STR "" in
    let is_default_p  =
      if self#is_default_access then STR "default " else STR "" in
    let pValue =
      if self#has_value then
	LBLOCK [
            STR "(value: ";
            constant_value_to_pretty self#get_value;
            STR ") "]
      else
	STR "" in
    LBLOCK [
        self#get_class_signature#toPretty;
        STR " ";
        pValue;
	is_final_p;
        is_static_p;
        is_constant_p;
        is_private_p;
        is_default_p;
	readers_writers_p]

  method get_alternate_text =
    let cfs = self#get_class_signature#class_field_signature_data in
    let field_str = cfs#class_name#name ^ ":" ^ cfs#field_signature#name in
    let is_final_p  = if self#is_final then "final " else "" in
    let is_static_p = if self#is_static then "static " else "" in
    let is_constant_p = if self#is_constant then "constant " else "" in
    let is_private_p  = if self#is_private then "private " else "" in
    let is_default_p  = if self#is_default_access then "default " else "" in
    let writing_ms = List.map (fun cms -> cms#name) writing_methods#toList in
    let reading_ms = List.map (fun cms -> cms#name) reading_methods#toList in
    field_str
    ^ " "
    ^ is_final_p
    ^ is_static_p
    ^ is_constant_p
    ^ is_private_p
    ^ is_default_p
    ^ "\nwriting methods: "
    ^ (String.concat ", " writing_ms)
    ^ "\nreading methods: "
    ^ (String.concat ", " reading_ms)

end


let make_field_info (in_stubbed_class:bool) (field:field_int) =
  new field_info_t
    ~in_stubbed_class:in_stubbed_class ~field_info_type:(ConcreteField field)


let make_missing_field_info (cfs:class_field_signature_int) =
  new field_info_t ~in_stubbed_class:false ~field_info_type:(MissingField cfs)


let make_field_stub
    ?(is_static=false)
    ?(is_final=false)
    ?(is_not_null=false)
    ?(is_interface_field=false)
    ?(is_constant=false)
    ?(inherited_from=None)
    ?(visibility=Public)
    ?(field_value=None)
    (cfs:class_field_signature_int) =
  new field_stub_t
    ~is_static
    ~is_final
    ~is_not_null
    ~is_interface_field
    ~is_constant
    ~inherited_from
    ~visibility
    ~field_value
    ~cfs


let make_field_stub_info (field_stub:field_stub_int) =
  new field_info_t
    ~in_stubbed_class:true ~field_info_type:(StubbedField field_stub)
