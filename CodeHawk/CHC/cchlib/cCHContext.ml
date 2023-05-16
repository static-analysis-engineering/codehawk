(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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

(** Representation of a location within a program *)

(* chlib *)
open CHPretty

(* chutil *)
open CHIndexTable
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHIndexedCollections
open CCHLibTypes
open CCHUtilities


type context_node_t = {
  cn_name   : string;
  cn_strings: string list;
  cn_numbers: int list
  }

class type cfg_context_manager_int =
  object

    method reset: unit

    method mk_cfg_context : int list -> cfg_context_int

    method get_cfg_context: int -> cfg_context_int

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

  end


class type exp_context_manager_int =
  object

    method reset: unit

    method mk_exp_context : int list -> exp_context_int

    method get_exp_context: int -> exp_context_int

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

  end


let mk_context_node (key:string list * int list) =
  let (tags,args) = key in
  if (List.length tags) > 0 then
    { cn_name = List.hd tags; cn_strings = List.tl tags; cn_numbers = args }
  else
    raise (CCHFailure (LBLOCK [STR "Context node without a name"]))


let is_return_node (n:context_node_t) = n.cn_name = "return"


let context_node_to_pretty (cn:context_node_t) =
  LBLOCK [
      STR cn.cn_name;
      pretty_print_list cn.cn_strings (fun s -> STR s) "[" "_" "]";
	   pretty_print_list cn.cn_numbers (fun i -> INT i) "(" "," ")" ]


let context_node_to_string (cn:context_node_t) =
  (String.concat "_" (cn.cn_name :: cn.cn_strings))
  ^ (match cn.cn_numbers with
     | [] -> ""
     | _ -> ":" ^ (String.concat "_" (List.map string_of_int cn.cn_numbers)))


let lcompare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
  if (List.length l1) < (List.length l2) then
    -1
  else if (List.length l1) > (List.length l2) then
    1
  else
    List.fold_left2 (fun a e1 e2 -> if a = 0 then (f e1 e2) else a) 0 l1 l2


module IntListCollections =
  CHCollections.Make
    (struct
      type t = int list
      let compare = Stdlib.compare
      let toPretty r = pretty_print_list r (fun i -> INT i) "[" "," "]"
    end)


let context_node_table = mk_index_table "context-node-table"

    
class cfg_context_t ~(index:int) ~(nodes:int list):cfg_context_int =
object (self:'a)
  
  val nodes = nodes

  method index = index

  method compare (other:'a) = lcompare nodes other#get_context Stdlib.compare
  
  method equal (other:'a) = (self#compare other) = 0
    
  method pop = 
    if (List.length nodes) > 0 then {< nodes = List.tl nodes >} else {< >}
      
  method private add s = 
    {< nodes = (context_node_table#add ([s],[])) :: nodes >}

  method private addi s i = 
    {< nodes = (context_node_table#add ([s],[i])) :: nodes >}
    
  method add_instr (n:int) = self#addi "instr" n

  method add_stmt  (n:int) = self#addi "stmt" n

  method add_if_expr = self#add "if-expr"

  method add_if_then = self#add "if-then"

  method add_if_else = self#add "if-else"

  method add_goto = self#add "goto"
    
  method add_loop = self#add "loop"

  method add_return = self#add "return"

  method add_switch_expr = self#add "switch-expr"
    
  method get_context = nodes
    
  method get_complexity =
    let cnodes = List.map context_node_table#retrieve nodes in
    let loops = List.filter (fun (tags,_) -> (List.hd tags) = "loop") cnodes in
    let ifs =
      List.filter (fun (tags,_) ->
          let name = List.hd tags in
          name = "if-then" || name = "if-else") cnodes in
    (List.length ifs) + ( 5 * (List.length loops))

  method is_return_context =
    (List.length nodes) > 0 &&
      (is_return_node (mk_context_node (context_node_table#retrieve (List.hd nodes))))
      
  method write_xml (node:xml_element_int) =
    begin
      node#setAttribute "a" (String.concat "," (List.map string_of_int nodes));
      node#setIntAttribute "ix" self#index
    end

  method to_string =
    String.concat
      "_"
      (List.map (fun ix ->
           context_node_to_string
             (mk_context_node (context_node_table#retrieve ix))) nodes)
      
  method toPretty = 
    pretty_print_list
      nodes (fun ix -> 
        LBLOCK [
            context_node_to_pretty
              (mk_context_node (context_node_table#retrieve ix)); NL ]) "" "" ""
      
end


let read_xml_cfg_context (node:xml_element_int):cfg_context_int =
  let nodes =
    try
      List.map int_of_string (nsplit ',' (node#getAttribute "a"))
    with
    | Failure _ ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "read_xml_cfg_context: int_of_string on ";
                 STR (node#getAttribute "a") ])) in
  let index = node#getIntAttribute "ix" in
  new cfg_context_t ~index ~nodes


class cfg_context_table_t =
object (self)

  inherit [int list, cfg_context_int] indexed_table_with_retrieval_t as super

  val map = new IntListCollections.table_t

  method insert = map#set
  method lookup = map#get
  method values = map#listOfValues

  method reset = begin map#removeList map#listOfKeys; super#reset end

end


class cfg_context_manager_t:cfg_context_manager_int =
object

  val table = new cfg_context_table_t

  method reset = table#reset

  method mk_cfg_context (nodes:int list) =
    table#add nodes (fun index -> new  cfg_context_t ~index ~nodes)

  method get_cfg_context (index:int) =
    try
      table#retrieve index
    with
    | CCHFailure p ->
       raise (CCHFailure (LBLOCK [STR "cfg context not found: "; p]))

  method write_xml (node:xml_element_int) =
    table#write_xml node "n" (fun node c -> c#write_xml node)

  method read_xml (node:xml_element_int) =
    let get_value = read_xml_cfg_context in
    let get_key c = c#get_context in
    let get_index c = c#index in
    table#read_xml node get_value get_key get_index

end


let cfg_context_manager = new cfg_context_manager_t
                        
    
class exp_context_t ~(index:int) ~(nodes:int list):exp_context_int =
object (self:'a)
  
  val nodes = nodes

  method index = index
    
  method compare (other:'a) = lcompare nodes other#get_context Stdlib.compare
    
  method private add s = 
    {< nodes = (context_node_table#add([s],[])) :: nodes >}

  method private addi s i = 
    {< nodes = (context_node_table#add([s],[i])) :: nodes >}

  method private addii s l =
    {< nodes = (context_node_table#add([s],l)) :: nodes >}

  method private adds s t = 
    {< nodes = (context_node_table#add([s;t],[])) :: nodes >}
    
  method add_var  = self#add "var"

  method add_lhs  = self#add "lhs"

  method add_rhs  = self#add "rhs"

  method add_lval = self#add "lval"

  method add_mem  = self#add "mem"

  method add_deref_read = self#add "deref-read"
    
  method add_addrof  = self#add "addrof" 

  method add_startof = self#add "startof"

  method add_binop i = self#addi "2op" i

  method add_unop    = self#add "op" 

  method add_cast    = self#add "cast"
    
  method add_field_offset f = self#adds "field-offset" f

  method add_index = self#add "index" 

  method add_index_offset = self#add "index-offset"
    
  method add_ftarget = self#add "ftarget"       (* indirect call target *)

  method add_arg i = self#addi "arg" i

  method add_args l = self#addii "args" l       (* depends on multiple arguments *)

  method add_question i = self#addi "question" i
    
  method get_context = nodes
    
  method get_complexity = 
    5 * (List.length
           (List.filter
              (fun n ->
                let (tags,_) = context_node_table#retrieve n in
                List.hd tags = "mem") nodes))
    
  method write_xml (node:xml_element_int) =
    begin
      node#setAttribute "a" (String.concat "," (List.map string_of_int nodes));
      node#setIntAttribute "ix" self#index
    end

  method to_string =
    String.concat
      "_"
      (List.map (fun ix ->
           context_node_to_string
             (mk_context_node (context_node_table#retrieve ix))) nodes)
      
  method toPretty = 
    pretty_print_list
      nodes (fun n ->
        let cn =
          mk_context_node (context_node_table#retrieve n) in
        LBLOCK [context_node_to_pretty cn; NL]) "" "" ""
      
end


let read_xml_exp_context (node:xml_element_int):exp_context_int =
  let nodes =
    try
      List.map int_of_string (nsplit ',' (node#getAttribute "a"))
    with
      Failure _ ->
      raise
        (CCHFailure
           (LBLOCK [
                STR "read_xml_exp_context: int_of_string on ";
                STR (node#getAttribute "a")])) in
  let index = node#getIntAttribute "ix" in
  new exp_context_t ~index ~nodes


class exp_context_table_t =
object (self)

  inherit [int list, exp_context_int] indexed_table_with_retrieval_t as super

  val map = new IntListCollections.table_t

  method insert = map#set
  method lookup = map#get
  method values = map#listOfValues

  method reset =
    begin map#removeList map#listOfKeys; super#reset end

end


class exp_context_manager_t:exp_context_manager_int =
object

  val table = new exp_context_table_t

  method reset = table#reset

  method mk_exp_context (nodes:int list) =
    table#add nodes (fun index -> new  exp_context_t ~index ~nodes)

  method get_exp_context (index:int) =
    try
      table#retrieve index
    with
    | CCHFailure p ->
       raise (CCHFailure (LBLOCK [ STR "exp context not found: "; p ]))

  method write_xml (node:xml_element_int) =
    table#write_xml node "n" (fun node c -> c#write_xml node)

  method read_xml (node:xml_element_int) =
    let get_value = read_xml_exp_context in
    let get_key c = c#get_context in
    let get_index c = c#index in
    table#read_xml node get_value get_key get_index

end

let exp_context_manager = new exp_context_manager_t


class program_context_t:program_context_int =
object (self:'a)

  val cfg_context = cfg_context_manager#mk_cfg_context []
  val exp_context = exp_context_manager#mk_exp_context []

  method compare (other:'a) =
    let d1 = cfg_context#compare other#get_cfg_context in
    if d1 = 0 then exp_context#compare other#get_exp_context else d1

  method construct (c:cfg_context_int) (e:exp_context_int) =
    {< cfg_context = c; exp_context = e >}

  method get_cfg_context = cfg_context

  method get_exp_context = exp_context

  method project_on_cfg =
    let e = exp_context_manager#mk_exp_context [] in
    self#construct cfg_context e

  method private add_cfg cfgc =
    {< cfg_context = cfg_context_manager#mk_cfg_context cfgc#get_context >}

  method private add_exp expc =
    {< exp_context = exp_context_manager#mk_exp_context expc#get_context >}

  method add_instr (n:int) = self#add_cfg (cfg_context#add_instr n)

  method add_stmt (n:int) = self#add_cfg (cfg_context#add_stmt n)

  method add_return = self#add_cfg cfg_context#add_return

  method add_if_expr = self#add_cfg cfg_context#add_if_expr

  method add_if_then = self#add_cfg cfg_context#add_if_then

  method add_if_else = self#add_cfg cfg_context#add_if_else

  method add_switch_expr = self#add_cfg cfg_context#add_switch_expr

  method add_loop = self#add_cfg cfg_context#add_loop

  method add_goto = self#add_cfg cfg_context#add_goto

  method add_var = self#add_exp exp_context#add_var

  method add_arg (n:int) = self#add_exp (exp_context#add_arg n)

  method add_args (r:int list) = self#add_exp (exp_context#add_args r)

  method add_addrof = self#add_exp exp_context#add_addrof

  method add_binop (n:int) = self#add_exp (exp_context#add_binop n)

  method add_cast = self#add_exp exp_context#add_cast

  method add_field_offset (s:string) = self#add_exp (exp_context#add_field_offset s)

  method add_lhs = self#add_exp exp_context#add_lhs

  method add_rhs = self#add_exp exp_context#add_rhs

  method add_ftarget = self#add_exp exp_context#add_ftarget

  method add_unop = self#add_exp exp_context#add_unop

  method add_index = self#add_exp exp_context#add_index

  method add_index_offset = self#add_exp exp_context#add_index_offset

  method add_lval = self#add_exp exp_context#add_lval

  method add_mem = self#add_exp exp_context#add_mem

  method add_deref_read = self#add_exp exp_context#add_deref_read

  method add_question (n:int) = self#add_exp (exp_context#add_question n)

  method add_startof = self#add_exp exp_context#add_startof

  method pop = {< cfg_context = cfg_context#pop >}

  method is_return_context = cfg_context#is_return_context

  method to_string = cfg_context#to_string ^ ","  ^ exp_context#to_string

  method toPretty =
    LBLOCK [
        STR "Cfg context: "; NL;
        INDENT(3, cfg_context#toPretty); NL;
        STR "Exp context: "; NL;
        INDENT(3, exp_context#toPretty); NL]

end


let mk_program_context () = new program_context_t


class ccontexts_t:ccontexts_int =
object (self)

  val table = mk_index_table "context"

  method reset = table#reset

  method index_context (c:program_context_int) =
    try
      let args = [c#get_cfg_context#index; c#get_exp_context#index] in
      table#add ([],args)
    with
    | Failure s ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Failure in indexing context ";
                 c#toPretty;
                 STR ": ";
                 STR s ]))

  method get_context (index:int):program_context_int =
    let (_, args) = table#retrieve index in
    match args with
    | cfgc :: expc :: _ ->
       let cfgcontext = cfg_context_manager#get_cfg_context cfgc in
       let expcontext = exp_context_manager#get_exp_context expc in
       (new program_context_t)#construct cfgcontext expcontext
    | _ ->
      raise (CCHFailure (LBLOCK [STR "Cfg context node without name"]))

  method write_xml_context
           ?(tag="ictxt") (node:xml_element_int) (c:program_context_int) =
    node#setIntAttribute tag (self#index_context c)

  method read_xml_context ?(tag="ictxt") (node:xml_element_int):program_context_int =
    self#get_context (node#getIntAttribute tag)

  method write_xml (node:xml_element_int) =
    let nnode = xmlElement "nodes" in
    let gnode = xmlElement "cfg-contexts" in
    let enode = xmlElement "exp-contexts" in
    let cnode = xmlElement "contexts" in
    begin
      context_node_table#write_xml nnode;
      cfg_context_manager#write_xml gnode;
      exp_context_manager#write_xml enode;
      table#write_xml cnode;
      node#appendChildren [ nnode; gnode; enode; cnode ]
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      context_node_table#read_xml (getc "nodes");
      cfg_context_manager#read_xml (getc "cfg-contexts");
      exp_context_manager#read_xml (getc "exp-contexts");
      table#read_xml (getc "contexts")
    end

end


let ccontexts = new ccontexts_t
