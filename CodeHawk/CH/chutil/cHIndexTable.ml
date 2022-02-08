(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHCommon
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

module H = Hashtbl


class type index_table_int =
  object
    method reset: unit
    method add: (string list * int list) -> int
    method retrieve: int -> (string list * int list)
    method values: (string list * int list) list
    method items : ((string list * int list) * int) list
    method size: int
    method get_name: string
    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit
  end


let get_list_suffix l (n:int) =
  let rec aux ll nn =
    match ll with
    | [] -> []
    | _ -> if nn <= 0 then ll else aux (List.tl ll) (nn-1) in
  aux l n

let list_pairup (lst:'a list):('a * 'a) list =
  let rec aux l r =
    match l with
    | x :: y :: tl -> aux tl ((x,y)::r)
    | [] -> List.rev r
    | _ ->
       raise (CHFailure (LBLOCK [ STR "Odd number of entries in list to pair up: " ;
                                   INT (List.length lst) ])) in
  aux lst []

let list_tripleup (lst:'a list):('a * 'a * 'a) list =
  let rec aux l r =
    match l with
    | x :: y :: z :: tl -> aux tl ((x,y,z)::r)
    | [] -> List.rev r
    | _ ->
       raise (CHFailure
                (LBLOCK [ STR "Number of entries is not a multiple of 3: " ;
                          INT (List.length lst) ])) in
  aux lst []


let t (name:string) (tags:string list) (n:int) =
  if List.length tags > n then
    List.nth tags n
  else
    raise (CHFailure
             (LBLOCK [ STR "Expected to find at least " ; INT (n+1) ;
                       STR " tags in " ; STR name ; STR ", but found only " ;
                       INT (List.length tags) ]))

let a (name:string) (args:int list) (n:int) =
  if List.length args > n then
    List.nth args n
  else
    raise (CHFailure
             (LBLOCK [ STR "Expected to find at least " ; INT (n+1) ;
                       STR " args in " ; STR name ; STR ", but found only " ;
                       INT (List.length args) ]))

let tags_args_string (tags:string list) (args:int list) =
  "t_" ^ (String.concat "," tags) ^ "_a_" ^
    (String.concat "," (List.map string_of_int args))

let keystring (k:(string list * int list)) =
  let (tags,args) = k in tags_args_string tags args


class index_table_t (name:string):index_table_int =
object (self: _)

  val mutable next = 1
  val table = H.create 3               (* (tags,args) -> index *)
  val revtable = H.create 3            (* index -> (tags,args) *)

  method reset =
    begin
      next <- 1 ;
      H.clear table ;
      H.clear revtable
    end

  method add (k:(string list * int list))  =
    if H.mem table k then
      H.find table k
    else
      let index = next in
      begin
        H.add table k index ;
        H.add revtable index k ;
        next <- next + 1 ;
        index
      end

  method retrieve (index:int) =
    try
      H.find revtable index
    with
    | Not_found ->
       raise (CHFailure
                (LBLOCK [ STR "Index not found in indexed hash table " ;
                          STR name ; STR ": " ; INT index ;
                          STR " (size: " ; INT (H.length table) ; STR ")" ]))
      
  method values = H.fold (fun k _ r -> k :: r) table []

  method items = H.fold (fun k index r -> (k,index) :: r) table []

  method size = H.length table

  method private get_indexed_keys =
    List.sort Stdlib.compare (H.fold (fun k v r -> (k,v) :: r) revtable [])

  method get_name = name

  method write_xml (node:xml_element_int) =
    let indexed_keys = self#get_indexed_keys in
    node#appendChildren
      (List.map (fun (k, (tags, args)) ->
           let knode = xmlElement "n" in
           begin
             knode#setIntAttribute "ix" k ;
             (match tags with
              | [] -> () | _ -> knode#setAttribute "t" (String.concat "," tags)) ;
             (match args with
              | [] -> ()
              | _ ->
                 knode#setAttribute
                   "a" (String.concat "," (List.map string_of_int args))) ;
             knode
           end) indexed_keys)

  method read_xml (node:xml_element_int) =
    let maxcount = ref 0 in
    begin
      List.iter (fun n ->
          let get = n#getAttribute in
          let has = n#hasNamedAttribute in
          let ix = n#getIntAttribute "ix" in
          let tags = if has "t" then nsplit ',' (get "t") else [] in
          let args =
            try
              if has "a" then
                List.map int_of_string (nsplit ',' (get "a"))
              else
                []
            with
            | Failure _ ->
               raise (CHFailure
                        (LBLOCK [
                             STR "int_of_string on ";
                             STR (get "a");
                             STR " in table ";
                             STR self#get_name])) in
          begin
            H.add table (tags,args) ix ;
            H.add revtable ix (tags,args) ;
            if ix > !maxcount then maxcount := ix
          end) (node#getTaggedChildren "n") ;
      next <- !maxcount + 1
    end

end
    
let mk_index_table = new index_table_t
