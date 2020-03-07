(* =============================================================================
   CodeHawk Java Analyzer
   Author: Andrew McGraw and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* chutil *)
open CHLogger
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI
open JCHJTDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI
open JCHPreFileIO
   
module H = Hashtbl

class costvalue_t (lbs:jterm_t list) (ubs:jterm_t list) =
object

  method to_string =
    match (lbs,ubs) with
    | ([ JConstant lb ], [ JConstant ub ]) when lb#equal ub -> lb#toString
    | ([ JConstant lb ], [ JConstant ub ]) ->
       "[" ^ lb#toString ^ "; " ^ ub#toString ^ "]"
    | _ ->  "X"

  method loop_bounds_to_string (cost:costvalue_t):string =
    let (other_lbs, other_ubs) = cost#get_bounds in
    let lower_bounds =
        match (lbs, other_lbs) with
        | ([ JConstant lb ], [ JConstant other_lb ]) ->
           string_of_int (lb#toInt * other_lb#toInt)
        | _ -> "X" in
    let upper_bounds =
        match (ubs, other_ubs) with
        | ([ JConstant ub ], [ JConstant other_ub ]) ->
           string_of_int (ub#toInt * other_ub#toInt)
        | _ -> "X" in
    "[" ^ lower_bounds ^ "; " ^ upper_bounds ^ "]"

  method get_bounds = (lbs, ubs)

end

class type costvalues_int =
  object
    method get_block_cost_string: int -> int -> string option
    method get_method_cost_string: int -> string option
    method get_loop_cost_string: int -> int -> string option
    method get_loop_iter_string: int -> int -> string option
    method load: unit
  end    
         
class costvalues_t:costvalues_int =
object (self)

  (* (int, cost_bounds_t) H.t *)     
  val methodcoststore = H.create 3

  (* (int, (int, costvalue_t) H.t) H.t ; only used for reporting *)                      
  val blockcoststore = H.create 3

  (* (int, loop_structure_int) H.t *)                     
  val loopstructures = H.create 3

  (* (int, (int, costvalue_t) H.t) H.t; cmsix -> looop head -> cost of loop *)                     
  val loopcoststore = H.create 3

  (* (int, (int, cost_values_t) H.t) H.t; cmsix -> loop head -> loop iterations *)                    
  val loopiterstore = H.create 3 

  method private set_block_cost (cmsix:int) (pc:int) (cost:costvalue_t) =
    let _ = if H.mem blockcoststore cmsix then () else
	H.add blockcoststore cmsix (H.create 3) in
    let t = H.find blockcoststore cmsix in
    H.replace t pc cost

  method private set_loop_cost (cmsix:int) (pc:int) (cost: costvalue_t) =
    let _ = if H.mem loopcoststore cmsix then () else
    H.add loopcoststore cmsix (H.create 3) in
    let t = H.find loopcoststore cmsix in
    H.replace t pc cost

  method private set_loop_iter (cmsix:int) (pc:int) (cost: costvalue_t) =
    let _ = if H.mem loopiterstore cmsix then () else
    H.add loopiterstore cmsix (H.create 3) in
    let t = H.find loopiterstore cmsix in
    H.replace t pc cost

  method private set_methodcost (cmsix:int) (cost:costvalue_t) =
    H.replace methodcoststore cmsix cost

  method get_block_cost_string cmsix pc =
    if H.mem blockcoststore cmsix then
      let t = H.find blockcoststore cmsix in
      if H.mem t pc then
        Some (H.find t pc)#to_string
      else
        None
    else
      None
    
  method get_loop_cost_string cmsix pc =
    if H.mem loopcoststore cmsix then
      let t = H.find loopcoststore cmsix in
      if H.mem t pc then
	Some (H.find t pc)#to_string
      else
	None
    else
      None
    
  method get_loop_iter_string cmsix pc =
    if H.mem loopiterstore cmsix then
      let t = H.find loopiterstore cmsix in
      if H.mem t pc then
	Some (H.find t pc)#to_string
      else
	None
    else
      None

  method get_method_cost_string cmsix =
    if H.mem methodcoststore cmsix then
      Some (H.find methodcoststore cmsix)#to_string
    else
      None

  method private read_xml_cost ?(tag="ibcost") (node:xml_element_int) =
    let (lbs,ubs) = jtdictionary#read_xml_jterm_range ~tag node in
    new costvalue_t lbs ubs

  method private read_xml_method_cost_results node =
    let cms = node#getIntAttribute "cmsix" in
    begin
      (if node#hasOneTaggedChild "blocks" then
         let bbNode = (node#getTaggedChild "blocks") in
         let bNodes = (bbNode#getTaggedChildren "block") in
         List.iter
           (fun bNode ->
             let pc = bNode#getIntAttribute "pc" in
             let bCost = self#read_xml_cost ~tag:"ibcost" bNode in
             self#set_block_cost cms pc bCost)  bNodes
       else
         pr_debug [ STR "No blocks node" ; NL ] ) ;
      (if node#hasNamedAttribute "imcost" then
         let mCost = self#read_xml_cost ~tag:"imcost" node in
         (self#set_methodcost cms mCost) ) ;
      (if node#hasOneTaggedChild "loops" then
          let llNode = (node#getTaggedChild "loops") in
          let lNodes = (llNode#getTaggedChildren "loop") in
            (List.iter
              (fun lNode ->
                let i1it = self#read_xml_cost ~tag:"i1it" lNode in
                let iitcount = self#read_xml_cost ~tag:"iitcount" lNode in
                let hpc = lNode#getIntAttribute "hpc" in
                let _ = self#set_loop_cost cms hpc i1it in
				self#set_loop_iter cms hpc iitcount
                ) lNodes ) )
    end


  method private read_xml_class_cost_results node (cInfo:class_info_int) =
    let mmNode = node#getTaggedChild "methods" in
    let mNodes = mmNode#getTaggedChildren "method" in
    List.iter self#read_xml_method_cost_results mNodes

  method private read_xml_class (cInfo:class_info_int) =
    if cInfo#is_stubbed || cInfo#is_missing then () else
     let cn = (cInfo#get_class_name) in
     let node_option = (load_xml_cost_analysis_results cn) in
     match node_option with
     | None ->
        pr_debug [ STR "Warning: No cost results file found for " ;
                   cn#toPretty ; NL ]
     | Some node -> self#read_xml_class_cost_results node cInfo

  method load = List.iter self#read_xml_class app#get_application_classes

end

let costvalues = new costvalues_t
    
                    

