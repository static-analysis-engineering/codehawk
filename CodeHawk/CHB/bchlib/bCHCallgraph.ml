(* =============================================================================
   CodeHawk Binary Analyzer
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

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHFunctionData
open BCHLibTypes


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


type callgraph_node_t =
  | AppNode of doubleword_int
  | DllNode of string
  | SONode of string
  | JniNode of int    (* jni index *)
  | VirtualNode of function_interface_t
  | UnresolvedNode of int    (* likely number of arguments *)


let _callgraph_node_kind_to_string n =
  match n with
  | AppNode _ -> "app"
  | DllNode _ -> "dll"
  | SONode _ -> "so"
  | JniNode _ -> "jni"
  | VirtualNode _ -> "virtual"
  | UnresolvedNode _ -> "unr"

let _callgraph_node_data_to_string n =
  match n with
  | AppNode a -> a#to_hex_string
  | DllNode s -> s
  | SONode s -> s
  | JniNode i -> (string_of_int i)
  | VirtualNode s -> s.fintf_name ^ "(V)"
  | UnresolvedNode i -> string_of_int i

let callgraph_node_to_pretty n =
  match n with
  | AppNode a -> a#toPretty
  | DllNode s -> (STR s)
  | SONode s -> (STR s)
  | JniNode i -> LBLOCK [ STR "jni_" ; INT i ]
  | VirtualNode s -> LBLOCK [STR s.fintf_name; STR "(V)"]
  | UnresolvedNode i -> LBLOCK [STR "unresolved( "; INT i; STR " )"]

let callgraph_node_compare n1 n2 =
  match (n1, n2) with
  | (AppNode a1,AppNode a2) -> a1#compare a2
  | (AppNode _, _) -> -1
  | (_, AppNode _) -> 1
  | (DllNode n1,DllNode n2) -> Stdlib.compare n1 n2
  | (DllNode _, _) -> -1
  | (_, DllNode _) -> 1
  | (SONode a1, SONode a2) -> Stdlib.compare a1 a2
  | (SONode _,_ ) -> -1
  | (_, SONode _) -> 1
  | (JniNode i1,JniNode i2) -> Stdlib.compare i1 i2
  | (JniNode _, _) -> -1
  | (_, JniNode _) -> 1
  | (VirtualNode s1,VirtualNode s2) -> Stdlib.compare s1.fintf_name s2.fintf_name
  | (VirtualNode _, _) -> -1
  | (_, VirtualNode _) -> 1
  | (UnresolvedNode i1, UnresolvedNode i2) -> Stdlib.compare i1 i2

module CallgraphNodeCollections = CHCollections.Make (
  struct
    type t = callgraph_node_t
    let compare = callgraph_node_compare
    let toPretty = callgraph_node_to_pretty
  end)


class type callgraph_node_info_int =
object
  (* accessors *)
  method get_node         : callgraph_node_t
  method get_address      : doubleword_int
  method get_name         : string
  method get_num_arguments: int

  (* predicates *)
  method is_app_function  : bool
  method is_so_function   : bool
  method is_dll_function  : bool
  method is_jni_function  : bool
  method is_resolved      : bool

  (* saving *)
  method write_xml        : xml_element_int -> unit

  (* printing *)
  method toPretty         : pretty_t

end


class type callgraph_edge_int =
object ('a)

  method compare               : 'a -> int

  (* accessors *)
  method get_source            : doubleword_int
  method get_target            : callgraph_node_t
  method get_callsite          : ctxt_iaddress_t
  method get_constraint        : xpr_t
  method get_stack_arguments   : (int * xpr_t) list
  method get_register_arguments: (variable_t * xpr_t) list

  (* printing *)
  method toPretty : pretty_t

end

module CallgraphEdgeCollections = CHCollections.Make (
  struct
    type t = callgraph_edge_int
    let compare e1 e2 = e1#compare e2
    let toPretty e = e#toPretty
  end)


class callgraph_node_info_t (cgnode:callgraph_node_t):callgraph_node_info_int =
object

  method get_node = cgnode

  method get_address = match cgnode with AppNode addr -> addr | _ ->
    raise (Invocation_error "callgraph_node#get_address")

  method get_name = match cgnode with
    | AppNode a ->
       if functions_data#has_function_name a then
         (functions_data#get_function a)#get_function_name else a#to_hex_string
    | SONode name -> name
    | DllNode name -> name
    | JniNode i -> "jni_" ^ (string_of_int i)
    | VirtualNode s -> s.fintf_name
    | UnresolvedNode n -> "unresolved_" ^ (string_of_int n)

  method get_num_arguments = 0

  method is_so_function = match cgnode with SONode _ -> true | _ -> false

  method is_app_function = match cgnode with AppNode _ -> true | _ -> false

  method is_dll_function = match cgnode with DllNode _ -> true | _ -> false

  method is_jni_function = match cgnode with JniNode _ -> true | _ -> false

  method is_resolved = match cgnode with UnresolvedNode _ -> false | _ -> true

  method write_xml (node:xml_element_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let seta t a = set t a#to_hex_string in
    match cgnode with
    | AppNode a ->
      begin
	set "kd" "app" ;
	seta "a" a ;
	if functions_data#has_function_name a then
          set "fn" (functions_data#get_function a)#get_function_name
      end
    | SONode name -> begin set "kd" "so" ; set "fn" name end
    | DllNode name -> begin set "kd" "dll" ; set "fn" name end
    | JniNode i -> begin set "kd" "jni" ; seti "jx" i end
    | VirtualNode s -> begin set "kd" "virtual"; set "sum" s.fintf_name end
    | UnresolvedNode i -> begin set "kd" "unr" ; seti "numa" i end

  method toPretty = callgraph_node_to_pretty cgnode

end

class callgraph_edge_t
        (src:doubleword_int)
        (tgt:callgraph_node_t)
        (callsite:ctxt_iaddress_t)
        (_argExprs:(int * string * xpr_t) list)
      :callgraph_edge_int =
object (_:'a)

  method compare (other:'a) =
    let l0 = src#compare other#get_source in
    if l0 = 0 then
      let l1 = callgraph_node_compare tgt other#get_target in
      if l1 = 0 then
	Stdlib.compare  callsite other#get_callsite
      else l1
    else l0

  method get_source = src

  method get_target = tgt

  method get_callsite = callsite

  method get_constraint = true_constant_expr

  method get_stack_arguments = []

  method get_register_arguments = []

  method toPretty =
    LBLOCK [ src#toPretty ; STR " -> " ;
             callgraph_node_to_pretty tgt ; STR " @ " ;
	     STR callsite ]

end


class callgraph_t:callgraph_int =
object (self)

  val nodes = new CallgraphNodeCollections.table_t
  val out_n = new DoublewordCollections.table_t
  val in_n  = new CallgraphNodeCollections.table_t

  method private probe_tgt (node:callgraph_node_t) =
    if nodes#has node then () else
      begin
	nodes#set node (new callgraph_node_info_t node) ;
	(match node with (AppNode a) ->
	  out_n#set a (new CallgraphEdgeCollections.set_t) | _ -> ()) ;
	in_n#set node (new CallgraphEdgeCollections.set_t)
      end

  method private probe_app (a:doubleword_int) =
    if nodes#has (AppNode a) then () else
      begin
	nodes#set (AppNode a) (new callgraph_node_info_t (AppNode a)) ;
	out_n#set a (new CallgraphEdgeCollections.set_t) ;
	in_n#set (AppNode a) (new CallgraphEdgeCollections.set_t)
      end

  method private get_in_edges (node:callgraph_node_t) =
    match in_n#get node with
      Some s -> s
    | _ -> raise (Invocation_error "callgraph#get_in_edges")

  method private get_out_edges (a:doubleword_int) =
    match out_n#get a with
      Some s -> s
    | _ -> raise (Invocation_error "callgraph#get_out_edges")

  method add_app_node (a:doubleword_int) = self#probe_app a

  method private add_edge
                   (srca:doubleword_int)
                   (tgtnode:callgraph_node_t)
                   (callsite:ctxt_iaddress_t)
                   (argExprs: (int * string * xpr_t) list) =
    let edge = new callgraph_edge_t srca tgtnode callsite argExprs in
    begin
      self#probe_app srca ;
      self#probe_tgt tgtnode ;
      (self#get_out_edges srca)#add edge ;
      (self#get_in_edges tgtnode)#add edge
    end

  method add_app_edge
           (srcfa:doubleword_int)
           (tgtfa:doubleword_int)
           (callsite:ctxt_iaddress_t)
           (argExprs:(int * string * xpr_t) list) =
    self#add_edge srcfa (AppNode tgtfa) callsite argExprs

  method add_dll_edge
           (srcfa:doubleword_int)
           (tgtfname:string)
           (callsite:ctxt_iaddress_t)
           (argExprs:(int * string * xpr_t) list) =
    self#add_edge srcfa (DllNode tgtfname) callsite argExprs

  method add_so_edge
           (srcfa:doubleword_int)
           (tgtfname:string)
           (callsite:ctxt_iaddress_t)
           (argExprs:(int * string * xpr_t) list) =
    self#add_edge srcfa (SONode tgtfname) callsite argExprs

  method add_jni_edge
           (srcfa:doubleword_int)
           (jnin:int)
           (callsite:ctxt_iaddress_t)
           (argExprs:(int * string * xpr_t) list) =
    self#add_edge srcfa (JniNode jnin) callsite argExprs

  method add_unresolved_edge
           (srcfa:doubleword_int)
           (narg:int)
           (callsite:ctxt_iaddress_t)
           (argExprs:(int * string * xpr_t) list) =
    self#add_edge srcfa (UnresolvedNode narg) callsite argExprs

  method add_virtual_edge
           (srcfa:doubleword_int)
           (s:function_interface_t)
           (callsite:ctxt_iaddress_t)
           (argExprs:(int * string * xpr_t) list) =
    self#add_edge srcfa (VirtualNode s) callsite argExprs

  method write_xml (node:xml_element_int) =
    let eNode = xmlElement "edges" in
    let edges = ref [] in
    let _ = out_n#iter (fun _ s -> edges := s#toList @ !edges) in
      node#appendChildren [ eNode ]

end


let make_callgraph () =	new callgraph_t
