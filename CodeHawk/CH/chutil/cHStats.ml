(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHUtils

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

module H = Hashtbl


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


class category_statistics_t:category_statistics_int =
object (self:'a)

  val table = H.create 3

  method add_item (category:string) =
    self#add_item_value category 1

  method private add_item_value (category:string) (v:int) =
    let count = self#get_category_total category in
    H.replace table category (count + v)

  method add_stat (s:'a) =
    s#iter self#add_item_value

  method get_categories =
    let l = ref [] in let _ =
                        H.iter (fun k _ -> l := k :: !l) table in !l

  method get_category_total (category:string) =
    if H.mem table category then H.find table category else 0

  method get_item_total =
    H.fold (fun _ v a -> v + a) table 0

  method iter (f:string -> int -> unit) =
    H.iter f table

  method write_xml (node:xml_element_int) =
    let seti = node#setIntAttribute in
    begin H.iter seti table; seti "total" self#get_item_total end

  method private categories_to_pretty =
    let maxLen =
      H.fold
        (fun k _ a ->
          let l = String.length k in if l > a then l else a) table 12 in
    let pr p = fixed_length_pretty p maxLen in
    let prr p = fixed_length_pretty ~alignment:StrRight p 8 in
    let perc v =
      let total = self#get_item_total in
	if total = 0 then
	  "n/a"
	else
	  Printf.sprintf "%5.2f" ((float_of_int v) /. (float_of_int total)) in
    let lines =
      List.map (fun c ->
	let v = self#get_category_total c in
	LBLOCK [pr (STR c); prr (INT v); prr (STR (perc v)); NL])
	self#get_categories in
    let footer = LBLOCK [pr (STR "total"); prr (INT self#get_item_total); NL] in
    LBLOCK [LBLOCK lines; footer]

  method toPretty ?(ptotal=[]) (categories: (string * int) list) =
    match categories with
    | [] -> self#categories_to_pretty
    | _ ->
       let perc c =
         STR (Printf.sprintf "%5.2f"
                (100.0 *. (float_of_int c) /.
		   (float_of_int self#get_item_total))) in
       let pr p w =
         if w = 0 then
           p
         else
           fixed_length_pretty ~alignment:StrRight p w in
       LBLOCK [
	   LBLOCK
             (List.map (fun (s,w) ->
	          let catTotal = self#get_category_total s in
	          LBLOCK [
                      pr (INT catTotal) w;
		      if List.mem s ptotal then
                        pr (perc catTotal) (w+2)
                      else
                        STR ""] ) categories);
	   pr (INT self#get_item_total) 8]

end


class cat2_statistics_t:cat2_statistics_int =
object (self:'a)

  val table = H.create 3

  method add_item (cat1:string) (cat2:string) =
    (self#get_inner_stat cat1)#add_item cat2

  method private get_inner_stat (cat1:string) =
    if H.mem table cat1 then
      H.find table cat1
    else
      let s = new category_statistics_t in
      begin
        H.add table cat1 s;
        s
      end

  method private add_inner_stat (cat1:string) (s:category_statistics_t) =
    (self#get_inner_stat cat1)#add_stat s

  method add_stat (s:'a) = s#iters self#add_inner_stat

  method get_categories =
    let l = ref [] in let _ = H.iter (fun k _ -> l := k :: !l) table in !l

  method private get_inner_categories =
    let c = new StringCollections.set_t in
    let _ = H.iter (fun _ s -> c#addList s#get_categories) table in
    c#toList

  method get_cat_1_total (cat1:string) =
    (self#get_inner_stat cat1)#get_item_total

  method get_cat_2_total (cat2:string) =
    H.fold (fun _ v a -> a + (v#get_category_total cat2)) table 0

  method get_cat_1_2_total (cat1:string) (cat2:string) =
    (self#get_inner_stat cat1)#get_category_total cat2

  method get_item_total =
    H.fold (fun _ v a -> a + v#get_item_total) table 0

  method iter (f:string -> string -> int -> unit) =
    H.iter (fun cat1 s -> s#iter (fun cat2 v -> f cat1 cat2 v)) table

  method iters (f:string -> category_statistics_int -> unit) =
    H.iter f table

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let seti = node#setIntAttribute in
    begin
      H.iter (fun cat1 s ->
	  let sNode = xmlElement "stat" in
	  begin
            sNode#setAttribute "tag" cat1;
            s#write_xml sNode;
            append [sNode]
          end) table;
      List.iter
        (fun c -> seti c (self#get_cat_2_total c)) self#get_inner_categories;
      seti "total" self#get_item_total
    end

  method toPretty ?(colsep=2) ?(ptotal=[]) () =
    let prr = fixed_length_pretty ~alignment:StrRight in
    let sepString = fixed_length_pretty (STR " ") colsep in
    let innerCats =
      List.map
        (fun s -> (s,(String.length s) + colsep)) self#get_inner_categories in
    let cats = List.sort Stdlib.compare self#get_categories in
    let maxCat =
      List.fold_left
        (fun a s ->
          let l = String.length s in
          if l > a
          then
            l
          else
            a) 0 cats in
    let pr s = fixed_length_pretty s (maxCat + colsep) in
    let total = self#get_item_total in
    let perc v =
      if total = 0 then "n/a" else
	let p = (float_of_int v) /. (float_of_int total) *. 100.0 in
	Printf.sprintf "%5.1f" p in
    let catHeaders =
      List.map
        (fun (s, w) ->
          LBLOCK [
              prr (STR s) w;
              if List.mem s ptotal then
                prr (LBLOCK [STR "%-"; STR s]) (w+2)
              else
                STR ""])
        innerCats in
    let header =
      LBLOCK [
          STR (string_repeat " " (maxCat + colsep));
	  LBLOCK catHeaders;
	  sepString; STR "total";
	  sepString; STR "%-of-total"; NL] in
    let lines =
      List.map (fun c ->
          let cstat = self#get_inner_stat c in
          LBLOCK [
              pr (STR c);
              cstat#toPretty ~ptotal innerCats;
	      prr (STR (perc cstat#get_item_total)) (8 + colsep);
              NL]) cats in
    let catFooters =
      List.map (fun (s, w) ->
          LBLOCK [
              prr (INT (self#get_cat_2_total s)) w;
	      if List.mem s ptotal then
                fixed_length_pretty (STR " ") (w+2)
              else
                STR ""])
               innerCats in
    let footer =
      LBLOCK [
          STR (string_repeat "-" 80); NL;
          pr (STR "total");
          LBLOCK catFooters;
          prr (INT self#get_item_total) 8; NL;
          pr (STR "");
          LBLOCK
            (List.map
               (fun (s,w) -> prr (STR (perc (self#get_cat_2_total s))) w)
	       innerCats); NL] in
    LBLOCK [header; LBLOCK lines; footer]

end


class property_statistics_t:property_statistics_int =
object (self:'a)

  val table = H.create 3
  val mutable items = 0
  val max_properties = new StringCollections.set_t

  method private add_item_value (property:string) (v:int) =
    H.replace table property ((self#get_property_value property) + v)

  method private set_max_value (property:string) (v:int) =
    let pValue = self#get_property_value property in
    if v > pValue then H.replace table property v else ()

  method add_item (properties:string list) =
    begin
      List.iter (fun p -> self#add_item_value p 1) properties;
      items <- items + 1
    end

  method add_stat (s:'a) =
    begin
      max_properties#addList s#get_max_properties;
      items <- items + s#get_item_total;
      s#iter (fun p v ->
	  if max_properties#has p then
            self#set_max_value p v
          else
            self#add_item_value p v)
    end

  method add_max_property (property:string) (v:int) =
    begin max_properties#add property; self#set_max_value property v end

  method get_properties =
    let l = ref [] in
    let _ = H.iter (fun k _ -> l := k :: !l) table in
    !l

  method get_max_properties = max_properties#toList

  method get_item_total = items

  method get_property_value (property:string) =
    if H.mem table property then H.find table property else 0

  method private is_special_property (property:string) =
    max_properties#has property

  method iter (f:string -> int -> unit) = H.iter f table

  method write_xml (node:xml_element_int) =
    H.iter node#setIntAttribute table

  method private properties_to_pretty =
    let maxLen =
      H.fold
        (fun k _ a ->
          let l = String.length k in
          if l > a then
            l
          else
            a) table 12 in
    let pr p = fixed_length_pretty p maxLen in
    let prr p = fixed_length_pretty ~alignment:StrRight p 8 in
    let perc v =
      let total = self#get_item_total in
      if total = 0 then
	"n/a"
      else
	Printf.sprintf "%5.2f" ((float_of_int v) /. (float_of_int total)) in
    let lines =
      List.map
        (fun p ->
	  let v = self#get_property_value p in
	  let perc = if self#is_special_property p then "n/a" else perc v in
	  LBLOCK [pr (STR p); prr (INT v); prr (STR perc);  NL])
	self#get_properties in
    let footer =
      LBLOCK [pr (STR "total items"); prr (INT self#get_item_total); NL] in
    LBLOCK [LBLOCK lines; footer]

  method toPretty (properties: (string * int) list) =
    match properties with
    | [] -> self#properties_to_pretty
    | _ ->
       let pr p w =
         if w = 0 then
           p
         else fixed_length_pretty ~alignment:StrRight p w in
       LBLOCK
         (List.map
            (fun (p,w) -> pr (INT (self#get_property_value p)) w) properties)

end


let make_category_statistics () = new category_statistics_t

let make_property_statistics () = new property_statistics_t

let make_cat2_statistics () = new cat2_statistics_t
