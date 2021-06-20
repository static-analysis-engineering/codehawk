(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHLanguage

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHXmlUtil

module H = Hashtbl

let nsplit (separator:char) (s:string):string list =
  let result = ref [] in
  let len = String.length s in
  let start = ref 0 in
  begin
    while !start < len do
      let s_index = try String.index_from s !start separator with Not_found -> len in
      let substring = String.sub s !start (s_index - !start) in
      begin
	result := substring :: !result ;
	start := s_index + 1
      end 
    done;
    List.rev !result
  end


let fcontext_compare (c1:fcontext_t) (c2:fcontext_t) =
  let l0 = c1.ctxt_faddr#compare c2.ctxt_faddr in
  if l0 = 0 then
    c1.ctxt_callsite#compare c2.ctxt_callsite
  else
    l0

let context_compare (c1:context_t) (c2:context_t) =
  match (c1,c2) with
  | (BlockContext b1,BlockContext b2) -> b1#compare b2
  | (BlockContext _, _) -> 1
  |  (_,BlockContext _) -> -1
  | (FunctionContext f1,FunctionContext f2) -> fcontext_compare  f1 f2

let list_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
  let length = List.length in
  if (length l1) < (length l2) then -1
  else if (length l1) > (length l2) then 1 
  else List.fold_right2 (fun e1 e2 a -> if a = 0 then (f e1 e2) else a) l1 l2 0

let context_list_compare (lst1:context_t list) (lst2:context_t list) =
  list_compare lst1 lst2 context_compare

let ctxt_string_to_string (s:ctxt_iaddress_t):string = s

let mk_base_location (faddr:doubleword_int) (iaddr:doubleword_int) =
  { loc_faddr = faddr ; loc_iaddr = iaddr }
                                                     
let contexts = H.create 3

let add_function_ctxt_iaddress
      (faddr:doubleword_int)      (* outer function address *)
      (s:ctxt_iaddress_t)
      (basef:doubleword_int)      (* inner function address *)
      (c:context_t list) =
  let faddr = faddr#to_hex_string in
  let basef = basef#to_hex_string in
  let f_entry =
    if H.mem contexts faddr then
      H.find contexts faddr
    else
      let t = H.create 3 in
      let _ = H.add contexts faddr t in
      t in
  if H.mem f_entry s then
    ()
  else
    H.add f_entry s (basef,c)

let get_context (faddr:doubleword_int) (s:string) =
  if s = "" then
    (faddr,[])
  else
    let faddr = faddr#to_hex_string in
    if H.mem contexts faddr then
      let f_entry = H.find contexts faddr in
      if H.mem f_entry s then
        let (f,c) = H.find f_entry s in
        (string_to_doubleword f, c)
      else
        raise (BCH_failure
                 (LBLOCK [ STR "Contexts for " ; STR faddr ;
                           STR " do not include: " ; STR s ]))
    else
      raise (BCH_failure
               (LBLOCK [ STR "No contexts found for " ; STR faddr ]))

      
let decompose_ctxt_string
      (faddr:doubleword_int)    (* outer function address *)
      (s:ctxt_iaddress_t) =
  let s2dw = string_to_doubleword in
  let components = nsplit '_' s in
  let iaddr = s2dw (List.hd (List.rev components)) in
  let ctxtcomponents = List.rev (List.tl (List.rev components)) in
  match ctxtcomponents with
  | [] -> ([],faddr,iaddr)
  | _ ->
     let ctxtstr = String.concat "_" ctxtcomponents in
     let (basef,ctxt) = get_context faddr ctxtstr in
     (ctxt,basef,iaddr)

let is_iaddress (s:ctxt_iaddress_t) =
  let components = nsplit '_' s in (List.length components) = 1

let is_same_iaddress (d:doubleword_int) (s:ctxt_iaddress_t) =
  (is_iaddress s) && (d#to_hex_string = s)
    
class location_t
        ?(ctxt=[])
        (loc:base_location_t)     (* inner function address, instruction address *)
      :location_int =
object (self:'a)

  method compare (other:'a) =
    match (self#ctxt,other#ctxt) with
    | ([],[]) ->
       let l0 = self#f#compare other#f in
       if l0 = 0 then self#i#compare other#i else l0
    | ([],(FunctionContext h)::_) ->
       let l0 = self#f#compare other#f in
       if l0 = 0 then self#i#compare h.ctxt_callsite else l0
    | ((FunctionContext h)::_,[]) ->
       let l0 = self#f#compare other#f in
       if l0 = 0 then h.ctxt_callsite#compare other#i else l0
    | (ctx1,ctx2) ->
       let l0 = context_list_compare ctx1 ctx2 in
       if l0 = 0 then self#i#compare other#i else l0       

  method i = loc.loc_iaddr    (* instruction address *)

  (* ctxt_iaddress_t spec:
     ci ( [], { faddr,iaddr } ) = iaddr
     ci ( [ F{ fa,cs,rs } ], { faddr,iaddr } ) = F:cs_iaddr
     ci ( [ F{ fa1,cs1,rs1 },F{ fa2,cs2,rs2 } ], { faddr,iaddr } ) = F:cs1_F:cs2_iaddr
     ci ( [ B{ js } ], { faddr,iaddr }) = B:js_iaddr
     ci ( [ B{ js1 }, B{ js2 } ], { faddr,iaddr }) = B:js1_B:js2_iaddr
   *)
  method ci =
    match ctxt with
    | [] -> self#i#to_hex_string
    | _ ->
       let ctxtstr =
         String.concat
           "_" (List.map (fun c ->
                    match c with
                    | FunctionContext h ->
                       "F:" ^ h.ctxt_callsite#to_hex_string
                    | BlockContext js ->
                       "B:" ^ js#to_hex_string) ctxt) in
       begin
         add_function_ctxt_iaddress self#f ctxtstr self#base_f ctxt ;
         ctxtstr ^ "_" ^ self#i#to_hex_string
       end

  method f =      (* address of function analyzed *)
    let rec aux c =
      match c with
      | [] -> loc.loc_faddr
      | (FunctionContext h)::_ -> h.ctxt_faddr   (* first ctxt element is the outer context *)
      | (BlockContext _)::tc -> aux tc in
    aux ctxt

  method base_loc = loc
  method base_f = loc.loc_faddr         (* address of inner function *)

  method ctxt = ctxt

  method has_context = match ctxt with [] -> false | _ -> true

  method toPretty =
    LBLOCK [ STR "(" ; self#f#toPretty ; STR "," ; self#i#toPretty ; STR ")" ]

end

let make_location = new location_t

let make_i_location (loc:location_int) (iaddr:doubleword_int) =
  let ctxt = loc#ctxt in
  let loc = { loc_faddr = loc#base_f ; loc_iaddr = iaddr } in
  make_location ~ctxt loc

let make_c_location (loc:location_int) (ctxt:context_t) =
  let newctxt = ctxt :: loc#ctxt in
  make_location ~ctxt:newctxt loc#base_loc

let ctxt_string_to_location (faddr:doubleword_int) (s:ctxt_iaddress_t) =
  let (ctxt,basef,iaddr) = decompose_ctxt_string faddr s in
  make_location ~ctxt { loc_faddr = basef ; loc_iaddr = iaddr }

let add_ctxt_to_ctxt_string
      (faddr:doubleword_int)    (* outer function of existing context *)
      (ctxtstr:ctxt_iaddress_t)
      (newctxt:context_t) =
  let loc = ctxt_string_to_location faddr ctxtstr in
  (make_c_location loc newctxt)#ci

let symbol_to_ctxt_string (s:symbol_t) =
  match s#getAttributes with
  | c :: _ -> c
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR "Symbol cannot be converted to context string: " ;
                        s#toPretty ]))

let ctxt_string_to_symbol (name:string) ?(atts=[]) (s:ctxt_iaddress_t) =
  new symbol_t ~atts:(s::atts) name
