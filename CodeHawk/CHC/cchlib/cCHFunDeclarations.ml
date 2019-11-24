(* =============================================================================
   CodeHawk C Analyzer 
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
open CHPretty

(* chutil *)
open CHIndexTable
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHFileEnvironment
open CCHLibTypes
open CCHSumTypeSerializer
open CCHUtilities

module H = Hashtbl
module P = Pervasives
   
let cd = CCHDictionary.cdictionary
let cdecls = CCHDeclarations.cdeclarations

let ibool b = if b then 1 else 0

let t (name:string) (tags:string list) (n:int) =
  if List.length tags > n then
    List.nth tags n
  else
    raise (CCHFailure
             (LBLOCK [ STR "Expected to find at least " ; INT (n+1) ;
                       STR " tags in " ; STR name ; STR ", but found only " ;
                       INT (List.length tags) ]))

let a (name:string) (args:int list) (n:int) =
  if List.length args > n then
    List.nth args n
  else
    raise (CCHFailure
             (LBLOCK [ STR "Expected to find at least " ; INT (n+1) ;
                       STR " args in " ; STR name ; STR ", but found only " ;
                       INT (List.length args) ]))
    



class cfundeclarations_t:cfundeclarations_int =
object (self)

  val varinfo_table = mk_index_table "local-varinfo-table"
  val vidtable = H.create 3
  val mutable tables = []

  initializer
    tables <- [ varinfo_table ]

  method private getrep (vinfo:varinfo) =
    let tags = [ vinfo.vname; storage_mfts#ts vinfo.vstorage ] in
    let args = [ vinfo.vid; cd#index_typ vinfo.vtype; cd#index_attributes vinfo.vattr;
                 ibool vinfo.vglob ; ibool vinfo.vinline; cdecls#index_location vinfo.vdecl;
                 ibool vinfo.vaddrof ; vinfo.vparam ] in
    (tags,args)

  method private xrep (tags,args): varinfo =
    let t = t "varinfo" tags in
    let a = a "varinfo" args in
    { vname = t 0 ;
      vstorage = storage_mfts#fs (t 1) ;
      vid = a 0 ;
      vtype = cd#get_typ (a 1) ;
      vattr = cd#get_attributes (a 2) ;
      vglob = (a 3) = 1 ;
      vinline = (a 4) = 1 ;
      vdecl = cdecls#get_location (a 5) ;
      vaddrof = (a 6) = 1 ;
      vparam = (a 7) ;
      vinit = None
    }

  method get_formals =
    List.filter (fun vinfo -> vinfo.vparam > 0)
                (List.map self#xrep varinfo_table#values)

  method get_formal (n:int) =      (* starting index 1 *)
    try
      List.find (fun vinfo -> vinfo.vparam = n)
                (List.map self#xrep varinfo_table#values)
    with
    | Not_found ->
       raise (CCHFailure (LBLOCK [ STR "Formal " ; INT n ;
                                   STR " not found in function declarations"]))
    
  method get_locals =
    List.filter (fun vinfo -> vinfo.vparam = 0)
                (List.map self#xrep varinfo_table#values)

  method is_formal (vid:int) =
    vid > 0 && ((self#get_varinfo_by_vid vid).vparam > 0)

  method is_local (vid:int) =
    vid > 0  &&
      (let vinfo = self#get_varinfo_by_vid vid in
       vinfo.vparam  = 0  && not vinfo.vglob)

  method get_varinfo_by_name (name:string) =
    try
      List.find (fun vinfo -> vinfo.vname = name)
                (List.map self#xrep varinfo_table#values)
    with
    | Not_found ->
       if cdecls#has_varinfo_by_name name then
         cdecls#get_varinfo_by_name name
       else
         raise (CCHFailure
                  (LBLOCK [ STR "Global variable with name: " ;  STR name ;
                            STR " not found" ]))
      
  method get_varinfo_by_vid (vid:int) =
    if H.mem vidtable vid then
      self#xrep (varinfo_table#retrieve (H.find vidtable vid))
    else
      file_environment#get_globalvar vid

  method has_varinfo (vid:int) =
    H.mem vidtable vid || file_environment#has_globalvar vid

  method get_varinfo (index:int) = self#xrep (varinfo_table#retrieve index)

  method index_formal (vinfo:varinfo) =
    let index = varinfo_table#add (self#getrep vinfo) in
    begin
      H.replace vidtable vinfo.vid index ;
      index
    end              

  method index_varinfo (vinfo:varinfo) =
    varinfo_table#add (self#getrep vinfo)

  method index_local (vinfo:varinfo) =
    let index = varinfo_table#add (self#getrep vinfo) in
    begin
      H.replace vidtable vinfo.vid index ;
      index
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables ;
      List.iter (fun (index,vinfo) -> H.add vidtable vinfo.vid index)
                (List.map (fun (key,index) -> (index,self#xrep key)) varinfo_table#items)
    end
    
end

let mk_cfundeclarations () = new cfundeclarations_t
    
