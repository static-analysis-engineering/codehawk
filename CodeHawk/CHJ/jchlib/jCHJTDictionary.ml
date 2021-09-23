(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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
open CHNumerical
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHPrettyUtil
open CHXmlDocument
   
(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHSumTypeSerializer

module H = Hashtbl


let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l
    
let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done ;
    !h
  end

         
let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c -> 
    if !found then
      ()
    else if Char.code c = 10 then      (* NL *)
      ()
    else if (Char.code c) < 32 || (Char.code c) > 126 then 
      found  := true) s in
  !found


let mk_constantstring (s:string):constantstring =
  if has_control_characters s then
    (hex_string s, true, String.length s)
  else
    (s,false, String.length s)


class jtdictionary_t:jtdictionary_int =
object (self)

  val symbolic_jterm_constant_table =
    mk_index_table "symbolic-jterm-constant-table"
  val jterm_table = mk_index_table "jterm-table"
  val relational_expr_table = mk_index_table "relational-expr-table"
  val jterm_list_table = mk_index_table "jterm-list-table"
  val relational_expr_list_table = mk_index_table "relational-expr-list-table"
  val jterm_range_table = mk_index_table "jterm-range-table"
  val string_table = mk_index_table "string-table"
  val numerical_table = mk_index_table "numerical-table"
  val float_table = mk_index_table "float-table"

  val mutable tables = []

  initializer
    tables <- [
      symbolic_jterm_constant_table ;
      jterm_table ;
      relational_expr_table ;
      jterm_list_table ;
      relational_expr_list_table ;
      jterm_range_table ;
      string_table ;
      numerical_table ;
      float_table
    ]

  method index_symbolic_jterm_constant (t:symbolic_jterm_constant_t) =
    let (typ,lbopt,ubopt,name) = t in
    let args = [
        common_dictionary#index_value_type typ;
        (match lbopt with Some n -> self#index_numerical n | _ -> -1);
        (match ubopt with Some n -> self#index_numerical n | _ -> -1);
        self#index_string name] in
    symbolic_jterm_constant_table#add ([],args)

  method get_symbolic_jterm_constant (index:int) =
    let (_,args) = symbolic_jterm_constant_table#retrieve index in
    let a = a "symbolic-jterm-constant" args in
    let typ = common_dictionary#get_value_type (a 0) in
    let lbopt = if (a 1) = (-1) then None else Some (self#get_numerical (a 1)) in
    let ubopt = if (a 2) = (-1) then None else Some (self#get_numerical (a 2)) in
    let name = self#get_string (a 3) in
    (typ, lbopt, ubopt, name)

  method index_jterm (t:jterm_t) =
    let tags = [ jterm_serializer#to_string t ] in
    let key = match t with
      | JAuxiliaryVar s -> (tags,[ self#index_string s ])
      | JLocalVar i -> (tags,[i])
      | JLoopCounter i -> (tags,[i])
      | JSymbolicConstant c -> (tags, [self#index_symbolic_jterm_constant c])
      | JConstant n -> (tags,[ self#index_numerical n ])
      | JStaticFieldValue (cnix,fname) -> (tags,[ cnix ; self#index_string fname ])
      | JObjectFieldValue (cmsix,varix,cnix,fname) ->
         (tags, [ cmsix ; varix ; cnix ; self#index_string fname ])
      | JBoolConstant b -> (tags,[ if b then 1 else 0 ])
      | JFloatConstant fc -> (tags, [ self#index_float fc ])
      | JStringConstant s -> (tags, [ self#index_string s ])
      | JSize t -> (tags, [ self#index_jterm t ])
      | JPower (t,n) -> (tags, [ self#index_jterm t; n ])
      | JUninterpreted (name,terms) ->
         (tags @ [ name ], List.map self#index_jterm terms)
      | JArithmeticExpr (op,t1,t2) ->
         (tags @ [ arithmetic_op_serializer#to_string op ],
          [ self#index_jterm t1 ; self#index_jterm t2 ]) in
    jterm_table#add key

  method get_jterm (index:int) =
    let (tags,args) = jterm_table#retrieve index in
    let t = t "jterm" tags in
    let a = a "jterm" args in
    match (t 0) with
    | "xv" -> JAuxiliaryVar (self#get_string (a 0))
    | "lv" -> JLocalVar (a 0)
    | "symc" -> JSymbolicConstant (self#get_symbolic_jterm_constant (a 0))
    | "lc" -> JLoopCounter (a 0)
    | "c" -> JConstant (self#get_numerical (a 0))
    | "sf" -> JStaticFieldValue (a 0, self#get_string (a 1))
    | "of" -> JObjectFieldValue (a 0, a 1, a 2, self#get_string (a 3))
    | "bc" -> JBoolConstant ((a 0) = 1)
    | "fc" -> JFloatConstant (self#get_float (a 0))
    | "sc" -> JStringConstant (self#get_string (a 0))
    | "si" -> JSize (self#get_jterm (a 0))
    | "pw" -> JPower (self#get_jterm (a 0), a 1)
    | "un" -> JUninterpreted ((t 1), (List.map self#get_jterm args))
    | "ar" ->
       JArithmeticExpr
         (arithmetic_op_serializer#from_string (t 1),
          self#get_jterm (a 0), self#get_jterm (a 1))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "jterm tag "; STR s; STR " not recognizezd"]))

  method index_relational_expr (x:relational_expr_t) =
    let (op,t1,t2) = x in
    let tags = [ relational_op_serializer#to_string op ] in
    let args = [ self#index_jterm t1 ; self#index_jterm t2 ] in
    relational_expr_table#add (tags,args)

  method get_relational_expr (index:int):relational_expr_t =
    let (tags,args) = relational_expr_table#retrieve index in
    let t = t "relational-expr" tags in
    let a = a "relational-expr" args in
    (relational_op_serializer#from_string (t 0),
     self#get_jterm (a 0),self#get_jterm (a 1))    

  method index_jterm_list (l:jterm_t list):int =
    jterm_list_table#add
      ([],List.sort Stdlib.compare (List.map self#index_jterm l))

  method get_jterm_list (index:int):jterm_t list  =
    let (_,args) = jterm_list_table#retrieve index in
    List.map self#get_jterm args

  method index_relational_expr_list (l:relational_expr_t list) =
    relational_expr_list_table#add
      ([],List.sort Stdlib.compare (List.map self#index_relational_expr l))

  method get_relational_expr_list (index:int):relational_expr_t list =
    let (_,args) = relational_expr_list_table#retrieve index in
    List.map self#get_relational_expr args

  method index_jterm_range (lb:jterm_t list) (ub:jterm_t list) =
    jterm_range_table#add ([],[ self#index_jterm_list lb ;
                                self#index_jterm_list ub ])

  method get_jterm_range (index:int):(jterm_t list * jterm_t list) =
    let (_,args) = jterm_range_table#retrieve index in
    let a = a "jterm-range" args in
    (self#get_jterm_list (a 0), self#get_jterm_list (a 1))

  method index_numerical (n:numerical_t) = numerical_table#add ([n#toString],[])

  method get_numerical (index:int) =
    let (tags,_) = numerical_table#retrieve index in
    let t = t "numerical" tags in
    mkNumericalFromString (t 0)

  method index_float (f:float) = float_table#add ([ (string_of_float f) ], [])

  method get_float (index:int) =
    let (tags,_) = float_table#retrieve index in
    let t = t "float" tags in
    float_of_string (t 0)

  method index_string (s:string):int =
    let cs = mk_constantstring s in
    let (s,ishex,len) = cs in
    let x = if ishex then [ "x" ] else [] in
    let tags = if len = 0 then [] else [ s ] @ x in
    let args = [ len ] in
    string_table#add (tags,args)
    
  method get_string (index:int) =
    let (tags,args) = string_table#retrieve index in
    let (s,_,_) = if (List.length tags) > 0  && (List.length args) > 0 then
      (List.hd tags, List.length tags > 1, List.hd args)
    else if (List.length args) > 0 && (List.hd args) = 0 then  (* empty string *)
      ("", false, 0)
    else if (List.length args) > 0 then
      (" ", false, (List.hd args))                (* string of spaces of lengt n *)
    else
      raise
        (JCH_failure
           (LBLOCK [STR "Invalid string record: "; INT (List.hd args)])) in
    s

  method write_xml_jterm ?(tag="ijt") (node:xml_element_int) (t:jterm_t) =
    node#setIntAttribute tag (self#index_jterm t)

  method read_xml_jterm ?(tag="ijt") (node:xml_element_int):jterm_t =
    self#get_jterm (node#getIntAttribute tag)

  method write_xml_relational_expr
           ?(tag="ire") (node:xml_element_int) (x:relational_expr_t) =
    node#setIntAttribute tag (self#index_relational_expr x)

  method read_xml_relational_expr
           ?(tag="ire") (node:xml_element_int):relational_expr_t =
    self#get_relational_expr (node#getIntAttribute tag)

  method write_xml_jterm_list
           ?(tag="ijtl") (node:xml_element_int) (l:jterm_t list) =
    node#setIntAttribute tag (self#index_jterm_list l)

  method read_xml_jterm_list ?(tag="ijtl") (node:xml_element_int):jterm_t list =
    self#get_jterm_list (node#getIntAttribute tag)

  method write_xml_relational_expr_list
           ?(tag="irel") (node:xml_element_int) (l:relational_expr_t list) =
    node#setIntAttribute tag (self#index_relational_expr_list l)

  method read_xml_relational_expr_list
           ?(tag="irel") (node:xml_element_int):relational_expr_t list =
    self#get_relational_expr_list (node#getIntAttribute tag)

  method write_xml_jterm_range
           ?(tag="ijtr")
           (node:xml_element_int)
           (lbs:jterm_t list)
           (ubs:jterm_t list) =
    node#setIntAttribute tag (self#index_jterm_range lbs ubs)

  method read_xml_jterm_range
           ?(tag="ijtr") (node:xml_element_int):(jterm_t list * jterm_t list) =
    self#get_jterm_range (node#getIntAttribute tag)

  method write_xml_numerical ?(tag="in") (node:xml_element_int) (n:numerical_t) =
    node#setIntAttribute tag (self#index_numerical n)

  method read_xml_numerical ?(tag="in") (node:xml_element_int):numerical_t =
    self#get_numerical (node#getIntAttribute tag)

  method write_xml_float ?(tag="ifl") (node:xml_element_int) (f:float) =
    node#setIntAttribute tag (self#index_float f)

  method read_xml_float ?(tag="ifl") (node:xml_element_int):float =
    self#get_float (node#getIntAttribute tag)

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_string s)

  method read_xml_string ?(tag="istr") (node:xml_element_int):string =
    self#get_string (node#getIntAttribute tag)    

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t -> let tnode = xmlElement t#get_name in
           begin t#write_xml tnode; tnode end) tables)
    

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables ;

  method toPretty =
    LBLOCK
      (List.map (fun t ->
           LBLOCK [STR t#get_name; STR ": "; INT t#size; NL]) tables)

end


let jtdictionary = new jtdictionary_t
