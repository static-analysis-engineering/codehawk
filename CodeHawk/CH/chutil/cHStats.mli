(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(** Utilities to keep track of tagged statistics *)

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument


class type category_statistics_int =
object ('a)
  (* setters *)
  method add_item : string -> unit
  method add_stat : 'a -> unit

  (* accessors *)
  method get_categories    : string list
  method get_category_total: string -> int
  method get_item_total    : int

  (* iterators *)
  method iter : (string -> int -> unit) -> unit

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: ?ptotal:string list -> (string * int) list -> pretty_t
end


class type cat2_statistics_int =
object ('a)
  (* setters *)
  method add_item : string -> string -> unit
  method add_stat : 'a -> unit

  (* accessors *)
  method get_categories     : string list
  method get_cat_1_total    : string -> int
  method get_cat_2_total    : string -> int
  method get_cat_1_2_total  : string -> string -> int
  method get_item_total     : int

  (* iterators *)
  method iter : (string -> string -> int -> unit) -> unit
  method iters: (string -> category_statistics_int -> unit) -> unit

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty : ?colsep:int -> ?ptotal:string list -> unit -> pretty_t
end


class type property_statistics_int =
object ('a)
  (* setters *)
  method add_item        : string list -> unit
  method add_stat        : 'a -> unit
  method add_max_property: string -> int -> unit

  (* accessors *)
  method get_properties     : string list
  method get_max_properties : string list
  method get_item_total     : int
  method get_property_value : string -> int

  (* iterators *)
  method iter : (string -> int -> unit) -> unit

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: (string * int) list  -> pretty_t

end


val make_category_statistics: unit -> category_statistics_int

val make_property_statistics: unit -> property_statistics_int

val make_cat2_statistics    : unit -> cat2_statistics_int
