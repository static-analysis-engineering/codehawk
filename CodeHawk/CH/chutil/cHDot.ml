(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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

(** Utilities to output a GraphViz dot file *)

(* chlib  *)
open CHCommon
open CHLanguage   
open CHPretty
open CHUtils

(* chutil *)
open CHUtil


exception Node_not_found of int

let replace_lst = [ ('"', "") ] (* [ ('>'," gt ") ; ('<', " lt ") ] *)

let sanitize (s:string):string =
  List.fold_left (fun sa (c,r) -> string_replace c r sa) s replace_lst

class dot_node_t (name:string) =
object (self: 'a)

  val name = name 
  val mutable label:string option = None

  val mutable shaded = false
  val mutable color = None
  val mutable addquotes = true

  method clone = {< >}

  method getName = name
  method equal (n:'a) = name = n#getName 

  method setLabel s = label <- Some s
  method setColor (c:string) = color <- Some c
  method setShaded = shaded <- true

  method toPretty =
    let quote = if addquotes then STR "\"" else STR "" in
    let label_text = match label with
      | Some v -> "label=\"" ^ v ^ "\" " 
      | _ -> "" in
    let shade = if shaded then "style=filled,color=\".7 .3 1.0\"" else "" in
      LBLOCK [
	quote ; STR name ; quote ; 
	if label_text = "" then STR "" else
	  LBLOCK [ STR " [" ; STR label_text ; STR "," ; STR shade ; STR "];" ]
      ]
end

class dot_edge_t (bidirectional:bool) (src:string) (tgt:string) =
object (self:'a)
  val src = src
  val tgt = tgt
  val bidirectional = bidirectional
  val mutable label:string option = None
  val mutable addquotes = true

  method clone = {< >}

  method getSrc = src
  method getTgt = tgt

  method setLabel s = label <- Some s

  method equal (n:'a) =  (src = n#getSrc) && (tgt = n#getTgt)

  method toPretty = 
    let quote = if addquotes then STR "\"" else STR "" in
    let attributes = match (label,bidirectional) with
      | (Some v, false) -> "[ label=\"" ^ (sanitize v) ^ "\" ] ;"
      | (Some v, true) -> "[ label=\"" ^ (sanitize v) ^ "\", dir=both ] ;"
      | (_,true) -> "[ dir=both ];"
      | _ -> ";" in
    LBLOCK [ quote ; STR src ; quote ; STR " -> " ;
             quote ; STR tgt ; quote ; STR attributes ]
end

module DotEdgeCollections = CHCollections.Make
    (struct
      type t = dot_edge_t
      let compare x y = 
	let c = Pervasives.compare x#getSrc y#getSrc in
	if c = 0 then
	  Pervasives.compare x#getTgt y#getTgt
	else
	  c
      let toPretty x = x#toPretty
    end)

class type dot_graph_int =
object ('a)
  method setPreamble: pretty_t -> unit
  method setRankdir : string -> unit
  method addEdge: ?bidirectional:bool -> ?label:string -> string -> string -> unit
  method addNode: ?label:string -> ?shaded:bool -> string -> unit
  method hasNode: string -> bool
  method hasEdge: string -> string -> bool
  method subgraph: string -> string -> 'a
  method revsubgraph: string -> string -> 'a
  method toPretty: pretty_t
end

class dot_graph_t
        ?(enable_bidirectional_edges=false)
        (gname:string):dot_graph_int =
object (self)

  val graph_name = gname 
  val enable_bidirectional_edges = 
    let _ = if enable_bidirectional_edges then
	pr_debug [ STR "Enable bidirectional edges" ; NL ] else
	pr_debug [ STR "Don't enable bidirectional edges" ; NL ] in
    enable_bidirectional_edges
  val mutable preamble = LBLOCK [
    STR "digraph " ; STR ("\"" ^ gname ^ "\""); STR " { " ; NL ;
    STR "edge [fontname=\"FreeSans\",fontsize=\"24\"," ;
    STR " labelfontname=\"FreeSans\",labelfontsize=\"24\"]; " ; NL ;
    STR "node [fontname=\"FreeSans\",fontsize=\"24\",shape=record]; " ; NL 
  ]
  val mutable rankdir = "LR"

  val nodes: dot_node_t StringCollections.table_t =
    new StringCollections.table_t
  val edges =  new DotEdgeCollections.set_t

  method private probe (n:string) =
    if nodes#has n then
      ()
    else
      nodes#set n (new dot_node_t n)

  method private get (n:string) =
    match nodes#get n with
      Some node -> node
    | _ ->
	let node = new dot_node_t n in
	begin
	  nodes#set n node ;
	  node
	end

  method setPreamble p = preamble <- p
  method setRankdir  d = rankdir  <- d

  method addNode ?label ?(shaded=false) (name:string) =
    let node = self#get name in
    let _ = if shaded then node#setShaded else () in
    match label with
      Some txt -> node#setLabel txt
    | _ -> ()

  method addEdge ?(bidirectional=false) ?label (src:string) (tgt:string) =
    begin
      self#probe src ;
      self#probe tgt ;
      let edge =
	if bidirectional then
	  new dot_edge_t bidirectional src tgt
	else if (not (src = tgt))
                && enable_bidirectional_edges
                && self#hasEdge tgt src then
	  begin
	    edges#remove (self#getEdge tgt src) ;
	    new dot_edge_t true tgt src
	  end
	else
	  new dot_edge_t false src tgt in
      begin
	edges#add edge ;
	match label with
	  Some txt -> edge#setLabel txt
	| _ -> ()
      end
    end

  method hasNode (n:string) =
    match nodes#get n with Some _ -> true | _ -> false

  method private getNode (n:string) =
    match nodes#get n with 
    | Some v -> v
    | _ ->
       raise (CHFailure
                (LBLOCK [ STR "Dotgraph: no node with name " ; STR n ]))
      
  method hasEdge (src:string) (tgt:string) =
    List.exists (fun e -> e#getSrc = src && e#getTgt = tgt) edges#toList

  method private getEdge (src:string) (tgt:string) =
    try
      List.find (fun e -> e#getSrc = src && e#getTgt = tgt) edges#toList
    with
      Not_found ->
	raise (CHFailure (LBLOCK [ STR "Dotgraph: no edge with source " ;
				   STR src ; STR " and target " ; STR tgt ]))

  method private getSuccessors (n:string) =
    edges#fold (fun a e -> if e#getSrc = n then  e#getTgt :: a else a) []

  method private getPredecessors (n:string) =
    edges#fold (fun a e -> if e#getTgt = n then e#getSrc :: a else a) []

  method subgraph (root:string) (graphName:string) =
    if not (self#hasNode root) then
      {< graph_name = graphName ; 
	 nodes = new StringCollections.table_t ; 
	 edges = new DotEdgeCollections.set_t >}
    else
      let rec build ws nodes edges =
	match ws with
	| [] -> (nodes, edges)
	| h::tl ->
	   let succ = self#getSuccessors h in
	   let h_edges = List.map (fun s -> (h,s)) succ in
	   let succ = List.filter (fun n -> not (List.mem n (nodes @ tl) )) succ in
	   build (succ @ tl) (h::nodes) (h_edges @ edges) in
      let (snodes,sedges) = build [root] [] [] in
      let subnodes = 
	let c = new StringCollections.table_t in
	begin List.iter (fun n -> c#set n (self#getNode n)#clone) snodes; c end in
      let subedges =
	let c = new DotEdgeCollections.set_t in
	begin List.iter (fun (s,t) ->
                  c#add (self#getEdge s t)#clone) sedges; c end in
      {< graph_name = graph_name ^ "_" ^ root ;
         nodes = subnodes ; edges = subedges >}
      
  method revsubgraph (root:string) (graphName:string) =
    if not (self#hasNode root) then
      {< graph_name = graphName ;
	 nodes = new StringCollections.table_t ;
	 edges = new DotEdgeCollections.set_t >}
    else
      let rec build ws nodes edges =
	match ws with
	| [] -> (nodes, edges)
	| h :: tl ->
	   let pred = self#getPredecessors h in
	   let h_edges = List.map (fun p -> (p,h)) pred in
	   let pred = List.filter (fun n -> not (List.mem n (nodes @ tl) )) pred in
	   build (pred @ tl) (h::nodes) (h_edges @ edges) in
      let (snodes,sedges) = build [ root ] [] [] in
      let subnodes =
	let c = new StringCollections.table_t in
	begin List.iter (fun n -> c#set n (self#getNode n)#clone) snodes; c end in
      let subedges =
	let c = new DotEdgeCollections.set_t in
	begin List.iter (fun (s,t) -> c#add (self#getEdge s t)#clone) sedges; c end in
      {< graph_name = graph_name ^ "_rv_" ^ root ; nodes = subnodes ; edges = subedges >}
      
      
  method toPretty =
    LBLOCK [
        preamble ;
        STR "rankdir=" ; STR rankdir ; STR ";" ; NL ;
        nodes#fold (fun a _ n -> LBLOCK [ a ; NL ; n#toPretty ]) (STR "") ; NL ;
        edges#fold (fun a e -> LBLOCK [ a ; NL ; e#toPretty ]) (STR "") ; NL ;
        STR " } "
      ]
    
end
  
let cfg_to_dot (cfg:cfg_int) =
  let g = new dot_graph_t "cfg" in
  let states = cfg#getStates in
  begin
    List.iter (fun s -> g#addNode ~label:s#getBaseName s#getBaseName) states ;
    List.iter (fun s -> 
        List.iter 
	  (fun t ->
            g#addEdge s#getBaseName t#getBaseName) (cfg#getState s)#getOutgoingEdges)
              states;
    g#setRankdir "TB" ;
    g
  end
  
  
