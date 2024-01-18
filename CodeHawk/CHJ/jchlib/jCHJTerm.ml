(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny Sipma

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

(* -----------------------------------------------------------------------------
 * The jterm_t type is the basis for a shared expression language in the Java
 * analyzer. It is used in the method summaries to express pre- and postconditions,
 * side effects, and time/space cost. It is also used internally to express
 * and share invariants.
 *
 * The internal and external (in xml) representations of the jterm are the same
 * except for the representation of arguments. Internally both arguments and
 * local variables are represented by their internal local variable number,
 * since in bytecode method arguments (including "this") are simply the first
 * local variables. The return value is represented by JLocalVar -1.
 *
 * There are two external (xml) representations for the jterm, one for method
 * summaries and generally for user-directed input/output, and one for
 * intermediate storage of invariants, cost data, etc. The first external
 * representation (referred to as xmlx) follows the W3C mathml convention for
 * representing expressions and makes a distinction between arguments and local
 * variables. It numbers the method arguments as they are encountered in the
 * source code, starting with 1; the "this" argument for an object method is
 * represented by <this/>, and the return value is represented by <return/>.
 * Thus, in this xmlx representation the argument number for a static method is
 * equal to the local variable internal representation plus 1; for object
 * methods the argument numbering is the same for the internal local variable
 * numbering except for the name "this" for the first bytecode method argument.
 *
 * The second external (xml) representation is a more systematic attribute-based
 * representation that closely reflects the internal representation.
 *
 * Examples:
 * -----------------------------------------
 * Example 1:
 *
 * IndexOutOfBounds precondition for
 *                             java.util.ArrayList.listIterator(int index):
 *
 * public ListIterator<E> listIterator(int index)
 *
 * with published condition for ArrayIndexOutOfBoundsException:
 *     if the index is out of range (index < 0 || index > size())
 *
 * summary representation of lower-bound condition:
 * <math><apply><geq/><arg nr="1"/><cn>0</cn></apply></math>
 *
 * summary representation of upper-bound condition:
 * <math><apply><leq/><arg nr="1"/><apply><size/><this/></apply></apply></math>
 *
 * In the internal xml representation these conditions would be represented as
 * <jxpr xtag="binop" binop="geq">
 *    <jxpr1 xtag="var" nr="1"/>
 *    <jxpr2 xtag="iconst" val="0"/>
 * </jxpr>
 *
 * and
 * <jxpr xtag="binop" binop="leq">
 *    <jxpr1 xtag="var" nr="1"/>
 *    <jxpr2 xtag="size">
 *       <jxpr xtag="var" nr="0"/>
 * </jxpr>
 *
 * The internal representation for both external representations is the same
 * (omitting the numerical datatype):
 *
 * (GreaterEqual, JLocalVar 1, JConstant 0)
 *
 * and
 *
 * (LessEqual, JLocalVar 1, JSize(JLocalVar 0))
 *
 * -------------------------------------------------
 * Example 2:
 *
 * public static int[] copyOf(int[] original, int newLength)
 *
 * published condition for NegativeArraySizeException:
 *    if newLength is negative
 *
 * summary representation:
 * <math><apply><geq/><arg nr="2"/><cn>0</cn></apply></math>
 *
 * the internal xml representation would be
 * <jxpr xtag="binop" binop="geq">
 *    <jxpr1 xtag="var" nr="2"/>
 *    <jxpr2 xtag="iconst" val="0"/>
 * </jxpr>
 *
 * The internal data structure representation for both is
 *
 * (GreaterEqual, JLocalVar 2, JConstant 0)
 *
 * -----------------------------------------------------
 *
 * Note:
 * To all other parts of the code the internal data structures are the
 * only representation relevant; the external xml representation is irrelevant
 * to all other parts of the code. It is described here only to document
 * the two different input/output formats.
 *
 * Data structure description:
 *
 * JAuxiliaryVar <name>  : used to introduce a local binding for constraints
 * JLocalVar <seqnr>     : argument/local variable starting with 0
 *                         return value is represented by JLocalVar -1
 * JLoopCounter <pc>     : used to represent the loop counter for the loop with
 *                           loophead at <pc>
 * JSize <t>             : collection size of a term
 * JConstant <n>         : integer/long constant
 * JBoolConstant <b>     : boolean constant
 * JFloatConstant <f>    : float/double constant
 * JPower (<t>,n)        : t^n
 * JUninterpreted (name,terms) : uninterpreted function name over argument terms
 * JArithmeticExpr (op,t1,t2): arithmetic expression of terms
 *
 * -----------------------------------------------------------------------------
 *)

(* chlib *)
open CHBounds
open CHIntervals
open CHPretty
open CHNumerical

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTDictionary

module H = Hashtbl


let p2s = string_printer#print

let maxint = mkNumericalFromString "2147483647"
let minint = mkNumericalFromString "-2147483648"

let maxlong = mkNumericalFromString "9223372036854775807"
let minlong = mkNumericalFromString "-9223372036854775808"

let macroconstants = H.create 11

let _ =
  List.iter (fun (name,tval) ->
      H.add macroconstants name (mkNumericalFromString tval))
            [("MAXCHAR", "65535");
             ("MAXCODEPOINT", "1114111");
             ("MAXINT", "2147483647");
             ("MININT", "-2147483648");
             ("MAXLONG", "9223372036854775807");
             ("MINLONG", "-9223372036854775808")]

let is_macro_constant (name:string) = H.mem macroconstants name

let get_macro_constant (name:string):numerical_t =
  if H.mem macroconstants name then
    H.find macroconstants name
  else
    raise (JCH_failure (LBLOCK [STR "Macro constant "; STR name;
                                 STR " not found"]))

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [
        STR "("; INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end


let arithmetic_op_to_string = function
  | JPlus -> " + "
  | JMinus -> " - "
  | JDivide -> " / "
  | JTimes -> " x "


let arithmetic_op_to_xml_string = function
  | JPlus -> "plus"
  | JMinus -> "minus"
  | JDivide -> "divide"
  | JTimes -> "times"


let arithmetic_op_compare x y =
  match (x,y) with
  | (JPlus, JPlus) -> 0
  | (JPlus, _) -> -1
  | (_, JPlus) -> 1
  | (JMinus,JMinus) -> 0
  | (JMinus,_) -> -1
  | (_, JMinus) -> 1
  | (JDivide,JDivide) -> 0
  | (JDivide,_) -> -1
  | (_,JDivide) -> 1
  | (JTimes,JTimes) -> 0


let relational_op_to_string = function
  | JEquals -> " = "
  | JLessThan -> " < "
  | JLessEqual -> " <= "
  | JGreaterThan -> " > "
  | JGreaterEqual -> " >= "
  | JNotEqual -> " <> "


let relational_op_to_xml_string = function
  | JEquals -> "eq"
  | JLessThan -> "lt"
  | JLessEqual -> "leq"
  | JGreaterThan -> "gt"
  | JGreaterEqual -> "geq"
  | JNotEqual -> "neq"


let xml_string_to_relational_op (s:string) =
  match s with
  | "eq" -> JEquals
  | "lt" -> JLessThan
  | "leq" -> JLessEqual
  | "gt" -> JGreaterThan
  | "geq" -> JGreaterEqual
  | "neq" -> JNotEqual
  | s ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "Relational operator ";
               STR s;
	       STR " not recognized"]))


let _xml_string_to_arithmetic_op (s:string) =
  match s with
  | "plus" -> JPlus
  | "minus" -> JMinus
  | "times" -> JTimes
  | "divide" -> JDivide
  | s ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "Arithmetic operator ";
               STR  s;
	       STR " not recognized"]))


let is_relational_op (s:string) =
  match s with
  | "eq" | "lt" | "leq" | "gt" | "geq" | "neq" -> true | _ -> false


let _is_arithmetic_op (s:string) =
  match s with
  | "plus" | "minus" | "times" | "divide" -> true | _ -> false


let symbolic_jterm_constant_compare (_,_,_,s1) (_,_,_,s2) =
  Stdlib.compare s1 s2


let rec jterm_compare t1 t2 =
  match (t1,t2) with
  | (JAuxiliaryVar s1, JAuxiliaryVar s2) -> Stdlib.compare s1 s2
  | (JAuxiliaryVar _, _) -> -1
  | (_, JAuxiliaryVar _) -> 1
  | (JSymbolicConstant c1, JSymbolicConstant c2) ->
     symbolic_jterm_constant_compare c1 c2
  | (JSymbolicConstant _,_) -> -1
  | (_, JSymbolicConstant _) -> 1
  | (JLocalVar x, JLocalVar y) -> Stdlib.compare x y
  | (JLocalVar _,_) -> -1
  | (_, JLocalVar _) -> 1
  | (JLoopCounter x, JLoopCounter y) -> Stdlib.compare x y
  | (JLoopCounter _,_) -> -1
  | (_,JLoopCounter _) -> 1
  | (JStaticFieldValue (cnix1,name1), JStaticFieldValue (cnix2,name2)) ->
     let l1 = Stdlib.compare cnix1 cnix2 in
     if l1 = 0 then
       Stdlib.compare name1 name2
     else
       l1
  | (JStaticFieldValue _, _) -> -1
  | (_, JStaticFieldValue _) -> 1
  | (JObjectFieldValue (cmsix1,varix1,cnix1,name1),
     JObjectFieldValue (cmsix2,varix2,cnix2,name2)) ->
     let l1 = Stdlib.compare cmsix1 cmsix2 in
     if l1 = 0 then
       let l2 = Stdlib.compare varix1 varix2 in
       if l2 = 0 then
         let l3 = Stdlib.compare cnix1 cnix2 in
         if l3 = 0 then
           Stdlib.compare name1 name2
         else
           l3
       else
         l2
     else
       l1
  | (JObjectFieldValue _,_) -> -1
  | (_, JObjectFieldValue _) -> 1
  | (JConstant x, JConstant y) -> x#compare y
  | (JConstant _, _) -> -1
  | (_, JConstant _) -> 1
  | (JBoolConstant x, JBoolConstant y) -> Stdlib.compare x y
  | (JBoolConstant _, _) -> -1
  | (_, JBoolConstant _) -> 1
  | (JFloatConstant x, JFloatConstant y) -> Stdlib.compare x y
  | (JFloatConstant _, _) -> -1
  | (_, JFloatConstant _) -> 1
  | (JStringConstant x, JStringConstant y) -> Stdlib.compare x y
  | (JStringConstant _, _) -> -1
  | (_, JStringConstant _) -> 1
  | (JSize x, JSize y) -> jterm_compare x y
  | (JSize _, _) -> -1
  | (_, JSize _) -> 1
  | (JPower (t1,n1), JPower (t2,n2)) ->
     let l0 =
       jterm_compare t1 t2 in if l0 = 0 then Stdlib.compare n1 n2 else l0
  | (JPower _, _) -> -1
  | (_, JPower _) -> 1
  | (JUninterpreted (n1,t1),JUninterpreted (n2,t2)) ->
     let l0 = Stdlib.compare n1 n2 in
     if l0 = 0 then
       jterm_list_compare t1 t2
     else
       l0
  | (JUninterpreted _, _) -> -1
  | (_, JUninterpreted _) -> 1
  | (JArithmeticExpr (op1,x1,x2), JArithmeticExpr (op2,y1,y2)) ->
    let l1 = arithmetic_op_compare op1 op2 in
    if l1 = 0 then
      let l2 = jterm_compare x1 y1 in
      if l2 = 0 then
	jterm_compare x2 y2
      else
        l2
    else
      l1


and jterm_list_compare l1 l2 =
  match (l1, l2) with
  | ([], []) -> 0
  | ([], _) -> -1
  | (_, []) -> 1
  | (t1::ll1, t2::ll2) ->
     let c = jterm_compare t1 t2 in
     if c = 0 then
       jterm_list_compare ll1 ll2
     else
       c


let relational_expr_compare e1 e2 =
  match (e1, e2) with
  | ((op1,jt11,jt12),(op2,jt21,jt22)) ->
    let l1 = Stdlib.compare op1 op2 in
    if l1 = 0 then
      let l2 = jterm_compare jt11 jt21 in
      if l2 = 0 then
	jterm_compare jt12 jt22
      else l2
    else l1


let depth_of_jterm (t:jterm_t) =
  let rec aux (x:jterm_t) =
    match x with
    | JSize t -> 1 + (aux t)
    | JPower (t,_) -> 1 + (aux t)
    | JUninterpreted (_,l) ->
       1 + (List.fold_left (fun acc x -> max acc (aux x)) 0 l)
    | JArithmeticExpr  (_,t1,t2) ->  1 + (max (aux t1) (aux t2))
    | _ -> 1 in
  aux t


let symbolic_jterm_constant_to_string (c:symbolic_jterm_constant_t) =
  match c with
  | (_,Some lb, Some ub, name) ->
     "symconst:" ^ name ^ " [" ^ lb#toString ^ "; " ^ ub#toString ^ "]"
  | (_,Some lb, _, name) ->
     "symconst:" ^ name ^ " [" ^ lb#toString ^ "; ->"
  | (_,_, Some ub, name) ->
     "symconst:" ^ name ^ " <-; " ^ ub#toString ^ "]"
  | (_,_,_,name) -> "symconst:" ^ name


let rec jterm_to_string
    ?(varname=default_varname_mapping)
    (t:jterm_t) =
    match t with
    | JLocalVar (-1) -> "return"
    | JLocalVar i -> "localvar:" ^ (varname i)
    | JSymbolicConstant c -> symbolic_jterm_constant_to_string c
    | JAuxiliaryVar s -> "auxvar:" ^ s
    | JLoopCounter i -> "loop-counter@pc_" ^ (string_of_int i)
    | JStaticFieldValue (cnix,name) ->
       ((retrieve_cn cnix)#name ^ "." ^ name)
    | JObjectFieldValue (cmsix, varix, _cnix, name) ->
       let mname = (retrieve_cms cmsix)#name in
       mname ^ ":var" ^ (string_of_int varix) ^ "." ^ name
    | JConstant i -> i#toString
    | JBoolConstant b -> if b then "true" else "false"
    | JFloatConstant f -> string_of_float f
    | JStringConstant s -> "string:" ^ s
    | JSize t -> "size(" ^ (jterm_to_string ~varname t) ^ ")"
    | JPower (t,n) ->
       "pow(" ^ (jterm_to_string ~varname t) ^ "," ^ (string_of_int n) ^ ")"
    | JUninterpreted (name,terms) ->
       "un:"
       ^ name
       ^ "("
       ^ (String.concat "," (List.map jterm_to_string terms))
       ^ ")"
    | JArithmeticExpr (op,t1,t2) ->
       "("
       ^ (jterm_to_string ~varname t1)
       ^ " "
       ^ (arithmetic_op_to_string op)
       ^ " "
       ^ (jterm_to_string ~varname t2)
       ^ ")"


let rec jterm_to_pretty
    ?(varname=default_varname_mapping)
    (t:jterm_t) =
    match t with
    | JArithmeticExpr (op, t1, t2) ->
       LBLOCK [
           STR "(";
           jterm_to_pretty ~varname t1;
           STR " ";
	   STR (arithmetic_op_to_string op);
           STR " ";
	   jterm_to_pretty ~varname t2;
           STR ")"]
    | JConstant i -> i#toPretty
    | JSize t -> LBLOCK [STR "size("; jterm_to_pretty ~varname t; STR ")"]
    | jterm -> STR (jterm_to_string ~varname jterm)


let rec jterm_to_sexpr_pretty
    ?(varname=default_varname_mapping)
    (t:jterm_t) =
  match t with
  | JArithmeticExpr (op, t1, t2) ->
    LBLOCK [STR "("; STR (arithmetic_op_to_string op); STR " ";
	     jterm_to_sexpr_pretty ~varname t1; STR " ";
	     jterm_to_sexpr_pretty ~varname t2; STR ")"]
  | JConstant i -> i#toPretty;
  | JSize t -> LBLOCK [STR "(size "; jterm_to_sexpr_pretty ~varname t; STR ")"]
  | jterm -> STR (jterm_to_string ~varname jterm)


let rec get_jterm_class_dependencies (t:jterm_t) =
  match t with
  | JStaticFieldValue (cnix,_)
    | JObjectFieldValue (_,_,cnix,_) ->
     [retrieve_cn cnix]
  | JSize t | JPower (t,_) -> get_jterm_class_dependencies t
  | JUninterpreted (_,l) ->
     List.concat (List.map get_jterm_class_dependencies l)
  | JArithmeticExpr (_,t1,t2) ->
     (get_jterm_class_dependencies t1) @ (get_jterm_class_dependencies t2)
  | _ -> []


let relational_expr_to_pretty
    ?(varname=default_varname_mapping)
    (x:relational_expr_t) =
  let (op,t1,t2) = x in
  LBLOCK [jterm_to_pretty ~varname t1; STR " ";
	   STR (relational_op_to_string op); STR " ";
	   jterm_to_pretty ~varname t2]


let relational_expr_to_sexpr_pretty
    ?(varname=default_varname_mapping)
    (x:relational_expr_t) =
  let (op,t1,t2) = x in
  LBLOCK [
      STR "(";
      STR (relational_op_to_string op);
      STR " ";
      jterm_to_sexpr_pretty ~varname t1;
      STR " ";
      jterm_to_sexpr_pretty ~varname t2;
      STR ")"]


let is_relational x =
  let (_op, t1, t2) = x in
  let isCompound t = match t with JArithmeticExpr _ -> true | _ -> false in
  isCompound t1 || isCompound t2


let _findupperbound (v:string) (cc:relational_expr_t list) =
  let ub = List.fold_left (fun acc c ->
    match c with
    | (JLessEqual, JAuxiliaryVar vv, JConstant n)
    | (JGreaterEqual, JConstant n, JAuxiliaryVar vv) when vv = v ->
      (match acc with
      | Some b when n#lt b -> Some n | Some _ -> acc | None -> Some n)
    | _ -> acc) None cc in
  match ub with
  | Some n -> new bound_t (NUMBER n)
  | _ -> new bound_t PLUS_INF


let _findlowerbound (v:string) (cc:relational_expr_t list) =
  let lb = List.fold_left (fun acc c ->
    match c with
    | (JGreaterEqual, JAuxiliaryVar vv, JConstant n)
    | (JLessEqual, JConstant n, JAuxiliaryVar vv) when vv = v ->
      (match acc with
      | Some b when n#gt b -> Some n | Some _ -> acc | None -> Some n)
    | _ -> acc) None cc in
  match lb with
  | Some n -> new bound_t (NUMBER n)
  | _ -> new bound_t MINUS_INF


(* -------------------------------------------------------------------------
 * External xml representation according to W3C mathml standard
 * ------------------------------------------------------------------------- *)

let jterm_to_xmlx (jterm:jterm_t) (ms:method_signature_int):xml_element_int =
  let argcount = List.length ms#descriptor#arguments in
  let var tag i =
    let node = xmlElement tag in
    begin node#setIntAttribute "nr" i; node end in
  let localvar i =
    if ms#is_static then
      if i < argcount then var "arg" (i+1) else var "var" i
    else
      if i <= argcount then var "arg" i else var "var" i in
  let lc i =
    let node = xmlElement "loop-counter" in
    begin node#setIntAttribute "pc" i; node end in
  let auxvar s =
    let node = xml_string "ci" s in
    begin node#setAttribute "kind" "aux"; node end in
  let symconst (typ,lbopt,ubopt,name) =
    let node = xmlElement "symbolic-constant" in
    begin
      write_xmlx_value_type node typ;
      (match lbopt with Some n -> node#setAttribute "lb" n#toString | _ -> ());
      (match ubopt with Some n -> node#setAttribute "ub" n#toString | _ -> ());
      node#setAttribute "name" name;
      node
    end in
  let rec aux (t:jterm_t) = match t with
    | JLocalVar (-1) -> xmlElement "return"
    | JAuxiliaryVar s -> auxvar s
    | JSymbolicConstant c -> symconst c
    | JLocalVar 0 when (not ms#is_static) -> xmlElement "this"
    | JLocalVar i -> localvar i
    | JLoopCounter i -> lc i
    | JStaticFieldValue (cnix,fname) ->
       let node = xmlElement "static-field-value" in
       let cname = (retrieve_cn cnix)#name in
       begin
         node#setAttribute "cname" cname;
         node#setAttribute "fname" fname;
         node
       end
    | JObjectFieldValue (cmsix,varix,cnix,fname) ->
       let node =
         if varix = 0 && not ms#is_static then
           xmlElement "this"
         else
           let n = xmlElement "arg" in
           let argix = if ms#is_static then varix + 1 else varix in
           begin n#setIntAttribute "nr" argix; n end in
       let cname = (retrieve_cn cnix)#name in
       let cms = retrieve_cms cmsix in
       let cn = cms#class_name in
       begin
         node#setAttribute "field" fname;
         (if cn#index = cnix then () else node#setAttribute "cn" cname);
         node
       end
    | JConstant n -> xml_string "cn" n#toString
    | JBoolConstant b -> xmlElement (if b then "true" else "false")
    | JFloatConstant f ->
      let node = xml_string "cn" (string_of_float f) in
      let _ = node#setAttribute "type" "float" in
      node
    | JStringConstant s -> xml_string "cs" s
    | JSize t ->
      let node = xmlElement "apply" in
      begin
	node#appendChildren [xmlElement "size"; aux t];
	node
      end
    | JPower (t,n) ->
       let node = xmlElement "apply" in
       let tnode = xmlElement "pow" in
       begin
         node#appendChildren [tnode; aux t];
         tnode#setIntAttribute "exp" n;
         node
       end
    | JUninterpreted (name,terms) ->
       let node = xmlElement "apply" in
       let tnode = xmlElement "free" in
       begin
         node#appendChildren (tnode :: (List.map aux terms));
         tnode#setAttribute "name" name;
         node
       end
    | JArithmeticExpr (op,t1,t2) ->
      let node = xmlElement "apply" in
      begin
	node#appendChildren
	 [xmlElement (arithmetic_op_to_xml_string op); aux t1; aux t2];
	node
      end in
  aux jterm


let read_xmlx_simple_jterm
      (node:xml_element_int) (cms:class_method_signature_int) =
  let ms = cms#method_signature in
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  match node#getTag with
  | "symbolic-constant" ->
     let name = node#getAttribute "name" in
     let typ = read_xmlx_value_type node in
     let lbopt =
       if has "lb" then Some (mkNumericalFromString (get "lb")) else None in
     let ubopt =
       if has "ub" then Some (mkNumericalFromString (get "ub")) else None in
     JSymbolicConstant (typ,lbopt,ubopt,name)
  | "return-value" | "return" ->
    (match ms#descriptor#return_value with
    | Some _ -> JLocalVar (-1)
    | _ ->
      raise_xml_error node (STR "Method does not have a return value"))
  | "loop-counter" -> JLoopCounter (node#getIntAttribute "pc")
  | "var" -> JLocalVar (node#getIntAttribute "nr")
  | "static-field-value" ->
     let cname = node#getAttribute "cname" in
     let cnix = (make_cn cname)#index in
     JStaticFieldValue (cnix, node#getAttribute "fname")
  | "object-field-value" ->
     let cname = node#getAttribute "cname" in
     let cnix = (make_cn cname)#index in
     let varix = node#getIntAttribute "varix" in
     let mnode = node#getTaggedChild "method" in
     let mclass = make_cn (mnode#getAttribute "cname") in
     let cms = read_xmlx_class_method_signature mnode mclass in
     JObjectFieldValue(cms#index, varix,cnix, node#getAttribute "fname")
  | "this" ->
    if ms#is_static then
      raise_xml_error node (STR "Static function cannot have a this argument")
    (* else if has "field" then
      let fname = get "field" in
      let cnix =
        if has "cn" then
          (make_cn (get "cn"))#index
        else
          cms#class_name#index in
      JObjectFieldValue (cms#index, 0, cnix, fname)  *)
    else
      JLocalVar 0
  | "arg" ->
     let nr = node#getIntAttribute "nr" in
     let arg = if ms#is_static then nr - 1 else nr in
     let _ =
       if (arg < 0)
          || arg > (List.length ms#descriptor#arguments)
          || (ms#is_static && arg >= List.length ms#descriptor#arguments) then
	       raise_xml_error
                 node
	         (LBLOCK [
                      STR "Term "; INT arg; STR " is not part of signature"]) in
     if has "field" then
       let fname = get "field" in
       let cnix =
         if has "cn" then
           (make_cn (get "cn"))#index
         else
           cms#class_name#index in
       JObjectFieldValue (cms#index, arg, cnix, fname)
     else
       JLocalVar arg
  | tag ->
     raise_xml_error
       node
       (LBLOCK [STR "Name of term: "; STR tag; STR " not recognized"])


let rec read_xmlx_jterm
    (node:xml_element_int)
    ?(argumentnames:(int * string) list = [])
    (cms:class_method_signature_int):jterm_t =
  let ms = cms#method_signature in
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let getterm n = read_xmlx_jterm n ~argumentnames cms in
  let getconstantvalue s =
    try JConstant (mkNumericalFromString s) with _ ->
      raise_xml_error node
	(LBLOCK [STR "Error in constant value: "; STR s]) in
  let getfloatconstantvalue s =
    try JFloatConstant (float_of_string s) with _ ->
      raise_xml_error node
	(LBLOCK [STR "Error in constant float value: "; STR s]) in
  let getargument n =
    let argnr = if ms#is_static then n-1 else n in
    let _ =
      if argnr < 0 || argnr > (List.length ms#descriptor#arguments) then
	raise_xml_error node
	  (LBLOCK [
               STR "Term ";
               INT argnr;
	       STR " is not part of the signature"]) in
    JLocalVar argnr in
  let getnamedargument n name =
    try
      if is_macro_constant name then
        JConstant (get_macro_constant name)
      else
        let (i,_) = List.find (fun (_,n) -> n = name) argumentnames in
        getargument i
    with
    | JCH_failure p ->
       raise_xml_error n (LBLOCK [STR "Macro error: "; p])
    | Not_found ->
      if n#hasNamedAttribute "kind" && (n#getAttribute "kind") = "aux" then
	JAuxiliaryVar name
      else
	raise_xml_error n
	  (LBLOCK [STR "Name of argument not found: "; STR name]) in
  let getreturnvalue () = match ms#descriptor#return_value with
    | Some _ -> JLocalVar (-1)
    | _ ->
      raise_xml_error node
	(LBLOCK [STR "Method does not have a return value"]) in
  let getthis () =
    if ms#is_static then
      raise_xml_error
        node
	(LBLOCK [STR "Static method does not have a this value"])
    else
      JLocalVar 0 in
  let jterm =
    match node#getTag with
    | "math" -> read_xmlx_jterm node#getChild ~argumentnames cms
    | "loop-counter" -> JLoopCounter (geti "pc")
    | "var" -> JLocalVar (geti "nr")
    | "cn" when has "type" && (get "type") = "float" ->
       getfloatconstantvalue node#getText
    | "cn" -> getconstantvalue node#getText
    | "ci" -> getnamedargument node node#getText
    | "cs" -> JStringConstant node#getText
    | "return-value" | "return" -> getreturnvalue ()
    | "symbolic-constant" ->
       let typ = read_xmlx_value_type node in
       let name = node#getAttribute "name" in
       let lbopt =
         if has "lb" then Some (mkNumericalFromString (get "lb")) else None in
       let ubopt =
         if has "ub" then Some (mkNumericalFromString (get "ub")) else None in
       JSymbolicConstant (typ,lbopt,ubopt,name)
    | "static-field-value" ->
       let cname = node#getAttribute "cname" in
       let cnix = (make_cn cname)#index in
       JStaticFieldValue (cnix, node#getAttribute "fname")
    | "object-field-value" ->
       let cname = node#getAttribute "cname" in
       let cnix = (make_cn cname)#index in
       let varix = node#getIntAttribute "varix" in
       let mnode = node#getTaggedChild "method" in
       let mclass = make_cn (mnode#getAttribute "cname") in
       let cms = read_xmlx_class_method_signature mnode mclass in
       JObjectFieldValue (cms#index,varix,cnix, node#getAttribute "fname")
    | "this" -> getthis ()
    | "true" -> JBoolConstant true
    | "false" -> JBoolConstant false
    | "arg" -> getargument (geti "nr")
    | "apply" ->
       let cc = node#getChildren in
       begin
         match cc with
         | [] -> raise_xml_error node (STR "Empty apply node")
         | fNode :: args ->
	    let arglen = List.length args in
	    let getarg i =
              if i < arglen then
                List.nth args i
              else
	        raise_xml_error
                  node
	          (LBLOCK [
                       STR "Attempt to fetch argument ";
                       INT (i+1);
		       STR " (only ";
                       INT arglen;
                       STR " provided) "]) in
	    let read_arithmetic_expr tag =
	      let op = match tag with
	        | "plus" -> JPlus
	        | "minus" -> JMinus
	        | "times" -> JTimes
	        | "divide" -> JDivide
	        | _ ->
                   raise_xml_error
                     node
	             (LBLOCK [STR "Error in arithmetic expr: "; STR tag]) in
              let t1 = getterm (getarg 0) in
              let t2 = getterm (getarg 1) in
	      JArithmeticExpr (op, t1, t2) in
	    match fNode#getTag with
	    | "times" | "plus" | "minus" | "divide" ->
	       read_arithmetic_expr fNode#getTag
            | "scale" ->
               let multfactor =
                 if fNode#hasNamedAttribute "mult" then
                   fNode#getIntAttribute "mult" else 1 in
               let divfactor =
                 if fNode#hasNamedAttribute "div" then
                   fNode#getIntAttribute "div" else 1 in
               let t = getterm (getarg 0) in
               begin
                 match (multfactor, divfactor) with
                 | (1,1) -> t
                 | (k,1) ->
                    JArithmeticExpr (JTimes, JConstant (mkNumerical k), t)
                 | (1,d) ->
                    JArithmeticExpr (JDivide, t, JConstant (mkNumerical d))
                 | (k,d) ->
                    let scalefactor =
                      JArithmeticExpr (
                          JDivide, JConstant (mkNumerical k),
                          JConstant (mkNumerical d)) in
                    JArithmeticExpr (JTimes, scalefactor, t)
               end
            | "pow" -> JPower (getterm (getarg 0),fNode#getIntAttribute "exp")
            | "free" ->
               let freeargs = List.map getterm args in
               JUninterpreted (fNode#getAttribute "name",freeargs)
	    | "array-length" -> JSize (getterm (getarg 0))
	    | "string-length" -> JSize (getterm (getarg 0))
	    | "size" -> JSize (getterm (getarg 0))
	    | tag ->
	       raise_xml_error
                 node
	         (LBLOCK [
                      STR "Operator ";
		      STR tag;
                      STR " not recognized in jterm"])
       end
    | tag ->
       raise_xml_error
         node
         (LBLOCK [STR "Argument term "; STR tag; STR " not recognized"]) in
  jterm


let write_xmlx_relational_expr
      (node:xml_element_int)
      (ms:method_signature_int)
      ?(setxpr=true)
      (x:relational_expr_t) =
  let (op,t1,t2) = x in
  let txml t = jterm_to_xmlx t ms in
  let apply_terms tag t1 t2 =
    let aNode = xmlElement "apply" in
    begin
      aNode#appendChildren [xmlElement tag; txml t1; txml t2];
      aNode
    end in
  let aNode = apply_terms (relational_op_to_xml_string op) t1 t2 in
  begin
    node#appendChildren [aNode];
    (if setxpr then node#setAttribute "xpr" (p2s (relational_expr_to_pretty x)));
    (if is_relational x then node#setAttribute "relational" "yes")
  end


(* node tag is expected to be "apply", with the operator and arguments
   as children *)
let read_xmlx_relational_expr
      (node:xml_element_int)
      ?(argumentnames=[])
      (cms:class_method_signature_int) =
  let getterm n = read_xmlx_jterm n ~argumentnames cms in
  match node#getChildren with
  | [] -> raise_xml_error node (STR "Predicate without arguments")
  | opNode :: argNodes ->
    let arglen = List.length argNodes in
    let getarg n =
      if n >= 0 && n < arglen then
        List.nth argNodes n
      else
	raise_xml_error
          node
	  (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    let op =
      try
        xml_string_to_relational_op opNode#getTag
      with _ ->
	raise_xml_error
          node
	  (LBLOCK [
               STR "Relational operator ";
               STR opNode#getTag;
	       STR " not recognized (valid values are : ";
	       STR "eq, lt, leq, gt, geq, neq)"]) in
    (op, getterm (getarg 0), getterm (getarg 1))

(* -------------------------------------------------------------------------
 * Internal xml representation following the data structure
 * ------------------------------------------------------------------------- *)

let _write_constant (node:xml_element_int) (n:numerical_t) =
  let set = node#setAttribute in
  if n#equal minint then
    set "xtag" "minint"
  else if n#equal maxint then
    set "xtag" "maxint"
  else if n#equal minlong then
    set "xtag" "minlong"
  else if n#equal maxlong then
    set "xtag" "maxlong"
  else
    begin
      set "xtag" "iconst";
      set "val" n#toString
    end


let _simplify (t:jterm_t) =
  match t with
  | JArithmeticExpr (JPlus, JConstant n1, JConstant n2) ->
     JConstant (n1#add n2)
  | JArithmeticExpr (JPlus,
                     JConstant n1,
                     JArithmeticExpr
                       (JPlus,
                        (JAuxiliaryVar "aux"),
                        JConstant n2)) ->
     JArithmeticExpr (JPlus, (JAuxiliaryVar "aux"), JConstant (n1#add n2))
  | JArithmeticExpr (JPlus,
                     JArithmeticExpr
                       (JPlus,
                        (JAuxiliaryVar "aux"),
                        JConstant n1), JConstant n2) ->
     JArithmeticExpr (JPlus, (JAuxiliaryVar "aux"), JConstant (n1#add n2))
  | JArithmeticExpr (JTimes, JConstant n1, JConstant n2) ->
     JConstant (n1#mult n2)
  | _ -> t


let jterm_add t1 t2 =
  match (t1,t2) with
  | (JConstant n1, JConstant n2) -> JConstant (n1#add n2)
  | (JConstant n1, JArithmeticExpr (JPlus, JConstant n2, t2)) ->
     JArithmeticExpr (JPlus, JConstant (n1#add n2), t2)
  | (JConstant n1, JArithmeticExpr (JPlus, t2, JConstant n2)) ->
     JArithmeticExpr (JPlus, JConstant (n1#add n2), t2)
  | _ -> JArithmeticExpr (JPlus, t1, t2)


class jterm_range_t
        ~(index:int)
        ~(lowerbounds:jterm_t list)
        ~(upperbounds:jterm_t list) =
object (self:'a)

  val index = index
  val lowerbounds = lowerbounds
  val upperbounds = upperbounds

  method index = index

  method add_lowerbound (t:jterm_t) =
    if List.exists (fun x -> (jterm_compare t x) = 0) lowerbounds then
      self
    else
      match (t,self#get_fixed_lowerbound) with
      | (JConstant n, Some m) when m#leq n -> self
      | (JConstant _, Some _) ->
         let newlowerbounds =
           List.rev
             (List.fold_left (fun acc x ->
                  match x with
                  | JConstant _ -> t :: acc
                  | _ -> x :: acc) [] lowerbounds) in
         self#mk_new newlowerbounds upperbounds
      | _ -> self#mk_new (t::lowerbounds) upperbounds

  method private get_fixed_lowerbound =
    List.fold_left (fun acc t ->
        match acc with
        | Some _ -> acc
        | _ ->
           match t with
           | JConstant n -> Some n
           | _ -> acc) None lowerbounds

  method add_term (t:jterm_t) =
    let newlowerbounds = List.map (jterm_add t) lowerbounds in
    let newupperbounds = List.map (jterm_add t) upperbounds in
    self#mk_new newlowerbounds newupperbounds


  method add_upperbound (t:jterm_t) =
    if List.exists (fun x -> (jterm_compare t x) = 0) upperbounds then
      self
    else
      match (t,self#get_fixed_upperbound) with
      | (JConstant n, Some m) when n#leq m -> self
      | (JConstant _, Some _) ->
         let newupperbounds =
           List.rev
             (List.fold_left (fun acc x  ->
                  match x with
                  | JConstant _ -> t :: acc
                  | _ -> x :: acc) [] upperbounds) in
         self#mk_new lowerbounds newupperbounds
      | _ -> self#mk_new lowerbounds (t::upperbounds)

  method private get_fixed_upperbound =
    List.fold_left (fun acc t ->
        match acc with
        | Some _ -> acc
        | _ ->
           match t with
           | JConstant n -> Some n
           | _ -> acc) None upperbounds

  method equals (a:'a) = index = a#index

  method leq (a:'a) =
    match (self#to_interval, a#to_interval) with
    | (Some i1, Some i2) -> i1#leq i2
    | _ -> false

  method get_upperbounds = upperbounds

  method get_lowerbounds = lowerbounds

  method to_interval =
    match (lowerbounds,upperbounds) with
    | ([JConstant n],[]) ->
       Some (new interval_t (bound_of_num n) plus_inf_bound)
    | ([],[JConstant n]) ->
       Some (new interval_t minus_inf_bound (bound_of_num n))
    | _ -> None

  method to_constant =
    match (lowerbounds,upperbounds) with
    | ([JConstant n], [JConstant m]) when n#equal m -> Some n
    | _ -> None

  method to_jterm =
    match (lowerbounds,upperbounds) with
    | ([t1],[t2]) when jterm_compare t1 t2 = 0 -> Some t1
    | _ -> None

  method is_top =
    match (lowerbounds,upperbounds) with ([],[]) -> true | _ -> false

  method is_bottom =
    match self#to_interval with Some i -> i#isBottom | _ -> false

  method is_constant =
    match (lowerbounds,upperbounds) with
    | ([JConstant n],[JConstant m]) -> n#equal m
    | _ -> false

  method is_interval = match self#to_interval with Some _ -> true | _ -> false

  method is_jterm = match self#to_jterm with Some _ -> true | _ -> false

  method write_xml (node:xml_element_int) =
    node#setIntAttribute "ijtr" index

  method write_xmlx (node:xml_element_int) (ms:method_signature_int) =
    let set = node#setAttribute in
    match self#to_jterm with
    | Some j -> node#appendChildren [jterm_to_xmlx j ms]
    | _ ->
       match (lowerbounds,upperbounds) with
       | ([JConstant n],[]) -> set "lb" n#toString
       | ([],[JConstant n]) -> set "ub" n#toString
       | ([JConstant lb],[JConstant ub]) ->
          begin
            set "lb" lb#toString;
            set "ub" ub#toString
          end
       | _ ->
          let _ =
            match lowerbounds with
            | [] -> ()
            | _ ->
               let bbNode = xmlElement "lower-bounds" in
               let _ =
                 bbNode#appendChildren
                   (List.map (fun b -> jterm_to_xmlx b ms) lowerbounds) in
               node#appendChildren [bbNode] in
          let _ =
            match upperbounds with
            | [] -> ()
            | _ ->
               let bbNode = xmlElement "upper-bounds" in
               let _ =
                 bbNode#appendChildren
                   (List.map (fun b -> jterm_to_xmlx b ms) upperbounds) in
               node#appendChildren [bbNode] in
          ()

  method toPretty =
    if self#is_top then STR "TOP" else
      match self#to_constant with
      | Some c -> c#toPretty
      | _ ->
         match self#to_interval with
         | Some i -> i#toPretty
         | _ ->
            match self#to_jterm with
            | Some j -> jterm_to_pretty j
            | _ ->
               LBLOCK [
                   STR "lowerbounds:";
                   pretty_print_list lowerbounds jterm_to_pretty "[" "; " "]";
                   STR "; upperbounds:";
                   pretty_print_list upperbounds jterm_to_pretty "[" ";" "]"]

  method private mk_new (lb:jterm_t list) (ub:jterm_t list) =
    let newindex = jtdictionary#index_jterm_range lb ub in
    {< index = newindex; lowerbounds = lb; upperbounds = ub >}

end


let mk_jterm_range
      (lowerbounds:jterm_t list) (upperbounds:jterm_t list):jterm_range_int =
  let index = jtdictionary#index_jterm_range lowerbounds upperbounds in
  new jterm_range_t ~index ~lowerbounds ~upperbounds


let read_xml_jterm_range (node:xml_element_int):jterm_range_int =
  let index = node#getIntAttribute "ijtr" in
  let (lowerbounds,upperbounds) = jtdictionary#get_jterm_range index in
  new jterm_range_t ~index ~lowerbounds ~upperbounds


let mk_jterm_jterm_range t = mk_jterm_range [t] [t]


let mk_intconstant_jterm_range (n:numerical_t) =
  mk_jterm_range [JConstant n] [JConstant n]


let mk_floatconstant_jterm_range (f:float) =
  mk_jterm_range [JFloatConstant f] [JFloatConstant f]


let mk_boolconstant_jterm_range (b:bool) =
  mk_jterm_range [JBoolConstant b] [JBoolConstant b]


let mk_intrange (lb:numerical_t option) (ub:numerical_t option) =
  let lbs =
    match lb with
    | Some lb -> [JConstant lb]
    | _ -> [] in
  let ubs =
    match ub with
    | Some ub -> [JConstant ub]
    | _ -> [] in
  mk_jterm_range lbs ubs


let read_xmlx_jterm_range
      (node:xml_element_int)
      ?(argumentnames=[])
      (cms:class_method_signature_int):jterm_range_int =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  if has "iconst" then
    mk_intconstant_jterm_range (mkNumerical (geti "iconst"))
  else if has "fconst" then
    mk_floatconstant_jterm_range (float_of_string (get "fconst"))
  else if has "lb" || has "ub" then
    let lb = if has "lb" then Some (mkNumerical (geti "lb")) else None in
    let ub = if has "ub" then Some (mkNumerical (geti "ub")) else None in
    mk_intrange lb ub
  else if hasc "cn" then
    let jt = read_xmlx_jterm (getc "cn") cms in
    mk_jterm_jterm_range jt
  else if hasc "symbolic-constant" then
    mk_jterm_jterm_range (read_xmlx_simple_jterm (getc "symbolic-constant") cms)
  else if hasc "math" then
    let jt = read_xmlx_jterm (getc "math") ~argumentnames cms in
    mk_jterm_jterm_range jt
  else if hasc "apply" then
    let jt = read_xmlx_jterm (getc "apply") ~argumentnames cms in
    mk_jterm_jterm_range jt
  else
    let tag = node#getChild#getTag in
    raise_xml_error node
                    (LBLOCK [STR "jterm range not recognized: "; STR tag])


let top_jterm_range = mk_jterm_range [] []


let intminmax_jterm_range =
  mk_intrange (Some (mkNumerical (-2147483648))) (Some (mkNumerical (2147483647)))


let mk_floatrange (lb:float option) (ub:float option) =
  let lbs =
    match lb with
    | Some lb -> [JFloatConstant lb]
    | _ -> [] in
  let ubs =
    match ub with
    | Some ub ->[JFloatConstant ub]
    | _ -> [] in
  mk_jterm_range lbs ubs
