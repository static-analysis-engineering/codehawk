(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
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

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty

(* bchlib *)
open BCHCPURegisters
open BCHDoubleword
open BCHLibTypes
open BCHVariableType

module H = Hashtbl
module P = Pervasives

(* Memory accesses are kept track of per memory location *)


let memaccess_to_pretty (m:memaccess_t) =
  let prty t = match t with TUnknown _ -> STR "" | _ ->
    LBLOCK [ btype_to_pretty t ; STR ", " ] in
  let prx x = match x with XConst XRandom -> STR "?" | _ -> xpr_formatter#pr_expr x in
  match m with
  | MARead (ty,width) -> LBLOCK [ STR "read(" ; prty ty ; INT width ; STR ")" ]
  | MAWrite (ty,width) -> LBLOCK [ STR "write(" ; prty ty ; INT width ; STR ")" ]
  | MAWriteNull width -> LBLOCK [ STR "write-null(" ; INT width ; STR ")" ]
  | MAIndexedWrite (reg,index,width) ->
    LBLOCK [ STR "ix-write" ; STR "(" ; STR (register_to_string reg) ; STR "," ; 
	     INT index ; STR "," ; INT width ; STR ")" ]
  | MAIndexedRead (reg,index,width) ->
    LBLOCK [ STR "ix-read" ; STR "(" ; STR (register_to_string reg) ; STR "," ; 
	     INT index ; STR "," ; INT width ; STR ")" ]
  | MABlockWrite (ty,name,width) ->
    LBLOCK [ STR name ; STR "%write(" ; prty ty ; prx width ; STR ")" ]
  | MABlockRead (ty,name,width) ->
    LBLOCK [ STR name ; STR "%read(" ; prty ty ; prx width ; STR ")" ]
  | MARegisterSave v -> LBLOCK [ STR "save caller " ; v#toPretty ]

let memaccess_compare (m1:memaccess_t) (m2:memaccess_t) =
  let tc = btype_compare in
  match (m1,m2) with
  | (MARead (t1,w1), MARead (t2,w2)) -> 
    let l0 = tc t1 t2 in if l0 = 0 then P.compare w1 w2 else l0
  | (MARead _, _) -> -1
  | (_, MARead _) -> 1
  | (MAWrite (t1,w1), MAWrite (t2,w2)) ->
    let l0 = tc t1 t2 in if l0 = 0 then P.compare w1 w2 else l0
  | (MAWrite _, _) -> -1
  | (_, MAWrite _) -> 1
  | (MAWriteNull w1, MAWriteNull w2) -> P.compare w1 w2
  | (MAWriteNull _,_) -> -1
  | (_, MAWriteNull _) -> 1
  | (MAIndexedWrite (r1,i1,w1), MAIndexedWrite (r2,i2,w2)) ->
    let l0 = P.compare (register_to_string r1) (register_to_string r2) in
    if l0 = 0 then
      let l1 = P.compare i1 i2 in 
      if l1 = 0 then P.compare w1 w2 else l1
    else l0
  | (MAIndexedWrite _, _) -> -1
  | (_, MAIndexedWrite _) -> 1
  | (MAIndexedRead (r1,i1,w1), MAIndexedRead (r2,i2,w2)) ->
    let l0 = P.compare (register_to_string r1) (register_to_string r2) in
    if l0 = 0 then
      let l1 = P.compare i1 i2 in 
      if l1 = 0 then P.compare w1 w2 else l1
    else l0
  | (MAIndexedRead _, _) -> -1
  | (_, MAIndexedRead _) -> 1
  | (MABlockWrite (t1,n1,x1), MABlockWrite (t2,n2,x2)) ->
    let l0 = P.compare n1 n2 in
    if l0 = 0 then 
      let l1 = tc t1 t2 in
      if l1 = 0 then syntactic_comparison x1 x2 else l1
    else l0
  | (MABlockWrite _ ,_) -> -1
  | (_, MABlockWrite _) -> 1
  |  (MABlockRead (t1,n1,x1), MABlockRead (t2,n2,x2)) ->
    let l0 = P.compare n1 n2 in
    if l0 = 0 then 
      let l1 = tc t1 t2 in
      if l1 = 0 then syntactic_comparison x1 x2 else l1
    else l0
  | (MABlockRead _, _) -> -1
  | (_, MABlockRead _) -> 1
  | (MARegisterSave v1, MARegisterSave v2) -> v1#compare v2
    
(* returns a best approximation of the types indicated by the memory
   accesses *)
let get_mem_type (l:memaccess_t list):btype_t list =
  List.fold_left (fun acc m ->
    let add t = match t with
      | TUnknown _ -> acc
      | _ ->
         if List.exists (fun x ->
                (btype_compare x t) = 0) acc then acc else t :: acc in
    match m with
    | MARead (t,_) | MAWrite (t,_) -> add t
    | MABlockWrite (t,_,_) | MABlockRead (t,_,_) -> add t
    | _ -> acc) [] l

module MemoryAccessCollections = CHCollections.Make
( struct
  type t = doubleword_int * memaccess_t
  let compare (a1,m1) (a2,m2) = 
    let l0 = a1#compare a2 in if l0 = 0 then memaccess_compare m1 m2 else l0
  let toPretty (a,m) =
    LBLOCK [ a#toPretty ; STR ": " ; memaccess_to_pretty m ; NL ]
  end)

module MemoryReferenceCollections = CHCollections.Make
( struct
  type t = memory_reference_int
  let compare x y = x#compare y
  let toPretty x = x#toPretty
  end)

module DoublewordCollections = CHCollections.Make
( struct
  type t = doubleword_int
  let compare x y = x#compare y
  let toPretty x = x#toPretty
  end)


class memory_accesses_t:memory_accesses_int =
object (self)

  val table = new MemoryReferenceCollections.table_t

  method private get (m:memory_reference_int) =
    match table#get m with Some e -> e | _ ->
      let e = new MemoryAccessCollections.set_t in
      begin table#set m e ; e end

  method add_read (iaddr:doubleword_int) (m:memory_reference_int) ?(ty=t_unknown) (width:int) =
    (self#get m)#add (iaddr,MARead (ty,width))

  method add_write (iaddr:doubleword_int) (m:memory_reference_int) ?(ty=t_unknown)
    ?(is_zero=false) (width:int) =
    let acc = if is_zero then MAWriteNull width else MAWrite (ty,width) in
    (self#get m)#add (iaddr,acc)

  method add_block_write (iaddr:doubleword_int) (m:memory_reference_int) ?(ty=t_unknown)
    (name:string) (width:xpr_t) =
    (self#get m)#add (iaddr,MABlockWrite (ty,name,width))

  method add_block_read (iaddr:doubleword_int) (m:memory_reference_int) ?(ty=t_unknown)
    (name:string) (width:xpr_t) =
    (self#get m)#add (iaddr,MABlockRead (ty,name,width))

  method add_indexed_write (iaddr:doubleword_int) (m:memory_reference_int) (reg:register_t)
    (index:int) (width:int) =
    (self#get m)#add (iaddr,MAIndexedWrite (reg,index,width))

  method add_indexed_read (iaddr:doubleword_int) (m:memory_reference_int) (reg:register_t)
    (index:int) (width:int) =
    (self#get m)#add (iaddr,MAIndexedRead (reg,index,width))

  method add_register_save (iaddr:doubleword_int) (m:memory_reference_int) (v:variable_t) =
    (self#get m)#add (iaddr,MARegisterSave v)

  method get_accesses = List.map (fun (m,s) -> (m,s#toList)) table#listOfPairs

  method write_xml (node:xml_element_int) = ()

  method toPretty = table#toPretty

end

let make_memory_access_record () = new memory_accesses_t
