(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
open CHUtils


type t_set_t =
  | STRING_SET of StringCollections.set_t
  | USTRING_SET of StringCollections.set_t
     (* set containing unknown strings besides the ones that are mentioned *)
  | TOP
  | BOTTOM

let st_string_set : t_set_t option ref = ref None

let set_st_string_set set = st_string_set := Some set

let get_st_string_set () = Option.get !st_string_set

(* The domain represents sets of strings. The empty set = BOTTOM *)
class string_set_t bottom top has_unknown (string_list: string list) =
  object (self: 'a)

    val strings : t_set_t =
      if bottom then
        BOTTOM
      else if top then
        TOP
      else if has_unknown then
        USTRING_SET (StringCollections.set_of_list string_list)
      else
        STRING_SET (StringCollections.set_of_list string_list)

    method private get_strings = strings
    method private get_st_strings =
      get_st_string_set ()

   (* I am not sure what this is for so I will use it to make available internal
      data *)
    method kind =
      set_st_string_set strings ;
      "?"

    method isBottom =
      match strings with
      | BOTTOM -> true
      | _ -> false

    method isTop =
      match strings with
      | TOP -> true
      | _ -> false

    method equal (s: 'a) =
      let _ = s#kind in
      match (strings, self#get_st_strings) with
      | (BOTTOM, BOTTOM) -> true
      | (TOP, TOP) -> true
      | (STRING_SET s1, STRING_SET s2) -> s1#equal s2
      |	(USTRING_SET s1, USTRING_SET s2) -> s1#equal s2
      | _ -> false

    method leq (s: 'a) =
      let _ = s#kind in
      match (strings, self#get_strings) with
      | (BOTTOM, _) -> true
      | (_, TOP) -> true
      | (STRING_SET s1, STRING_SET s2) -> s1#subset s2
      | (USTRING_SET s1, USTRING_SET s2) -> s1#subset s2
      | _ -> false

    method join (s: 'a) =
      let _ = s#kind in (* store the strings *)
      match (strings, self#get_st_strings) with
      | (BOTTOM, _) -> s
      | (_, BOTTOM) -> {< >}
      | (TOP, _) -> {< >}
      | (_, TOP) -> s
      | (STRING_SET s1, STRING_SET s2) -> {< strings = STRING_SET (s1#union s2) >}
      |	(USTRING_SET s1, STRING_SET s2)
      |	(STRING_SET s1, USTRING_SET s2)
      |	(USTRING_SET s1, USTRING_SET s2) -> {< strings = USTRING_SET (s1#union s2) >}

    method meet (s: 'a) =
      let _ = s#kind in
      match (strings, self#get_st_strings) with
      | (BOTTOM, _) -> {< >}
      | (_, BOTTOM) -> s
      | (TOP, _) -> s
      | (_, TOP) -> {< >}
      | (STRING_SET s1, STRING_SET s2)
      | (USTRING_SET s1, STRING_SET s2)
      | (STRING_SET s1, USTRING_SET s2) -> {< strings = STRING_SET (s1#inter s2) >}
      |	(USTRING_SET s1, USTRING_SET s2) -> {< strings = USTRING_SET (s1#inter s2) >}

    method widening = self#join

    method narrowing = self#meet

    method marshal =
      match strings with
      | BOTTOM -> CHExternalValues.EVX_STRING "_|_"
      | TOP -> CHExternalValues.EVX_STRING "{...}"
      | STRING_SET s
      |	USTRING_SET s ->
	  let strs = (List.map (fun e -> CHExternalValues.EVX_STRING e) s#toList) in
	  CHExternalValues.EVX_LIST strs

    method toPretty =
      match strings with
      | BOTTOM -> STR "_|_"
      | TOP -> STR "{...}"
      | STRING_SET s -> LBLOCK [STR "STRING_SET "; s#toPretty]
      | USTRING_SET s -> LBLOCK [STR "USTRING_SET "; s#toPretty]

  end

let top_string_set = new string_set_t false true false []

let bottom_string_set =  new string_set_t true false false []

let unknown_string_set = new string_set_t false false true []

let mk_string_set ss = new string_set_t false false false ss

let mk_ustring_set ss = new string_set_t false false true ss


let get_string_list (set: string_set_t) =
  let _ = set#kind in
  match get_st_string_set () with
  | STRING_SET s -> s#toList
  | _ -> []


let add_unknown set =
  let _ = set#kind in
  match get_st_string_set () with
  | STRING_SET s -> mk_ustring_set s#toList
  | BOTTOM -> mk_ustring_set []
  | _ -> set


let has_string set =
  let _ = set#kind in
  match get_st_string_set () with
  | STRING_SET s
  | USTRING_SET s -> not s#isEmpty
  | _ -> false


let has_unknown set =
  let _ = set#kind in
  match get_st_string_set () with
  | USTRING_SET _ -> true
  | _ -> false
