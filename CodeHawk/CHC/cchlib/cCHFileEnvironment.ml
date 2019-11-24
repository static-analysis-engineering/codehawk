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
open CHLogger

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHMachineSizes
open CCHSettings
open CCHUtilities

module H = Hashtbl

let rec get_type_unrolled (typedefs: (string,typ) Hashtbl.t) (t:typ) =
  let aux = get_type_unrolled typedefs in
  let addattrs attrs ty =
    match ty with
    | TVoid a -> TVoid (attrs @ a)
    | TInt (ik,a) -> TInt (ik,attrs @ a)
    | TFloat (fk,a) -> TFloat (fk,attrs @ a)
    | TPtr (t,a) -> TPtr (t, attrs @ a)
    | TArray (t,e,a) -> TArray (t,e,attrs @ a)
    | TFun (t,l,b,a) -> TFun (t,l,b,attrs @ a)
    | TNamed (s,a) -> TNamed(s, attrs @ a)
    | TComp (i,a) -> TComp (i,attrs @ a)
    | TEnum (s,a) -> TEnum (s,attrs @ a)
    | TBuiltin_va_list a -> TBuiltin_va_list (attrs @ a) in
  match t with
  | TNamed (name,attrs) ->
    if H.mem typedefs name then addattrs attrs (aux (H.find typedefs name)) else
      raise (Invalid_argument ("get_type_unrolled " ^ name))
  | TPtr (t,attrs) -> TPtr (aux t, attrs)
  | TArray (t,optE,attrs) -> TArray (aux t,optE,attrs)
  | TFun (t,optArgs,b,attrs) ->
    let urArgs = match optArgs with
      | None -> None
      | Some l -> Some (List.map (fun (name,t,attrs) -> (name,aux t,attrs)) l) in
    TFun (aux t, urArgs,b,attrs)
  | _ -> t


class file_environment_t: file_environment_int =
object (self)

  val externalFns = H.create 3
  val applicationFns = H.create 3
  val globalvars = H.create 3
  val compinfos = H.create 3
  val enuminfos = H.create 3
  val typedefs = H.create 3

  method private reset =
    begin
      H.clear externalFns ;
      H.clear applicationFns ;
      H.clear globalvars ;
      H.clear compinfos ;
      H.clear enuminfos ;
      H.clear typedefs 
    end

  method initialize (f:file) =
    let _ = self#reset in
    let is_application_function (v:varinfo) =
      if system_settings#filterabspathfiles then
        not ((String.get v.vdecl.file 0) = '/')
      else
        true in
    begin
      List.iter (fun g ->
          match g with
          | GVar (vinfo,_,_) | GVarDecl (vinfo,_) | GFun (vinfo,_) ->
             H.replace globalvars vinfo.vid vinfo
          | GCompTag (cinfo,_) | GCompTagDecl (cinfo,_) ->
             H.replace compinfos cinfo.ckey cinfo
          | GEnumTag (einfo,_) | GEnumTagDecl (einfo,_) ->
             H.replace enuminfos einfo.ename einfo
          | GType (tinfo,_) ->
             H.replace typedefs tinfo.tname tinfo.ttype
          | _ -> ()) f.globals ;
      List.iter (fun g ->
          match g with
          | GFun (vinfo,_) when is_application_function vinfo ->
             H.replace applicationFns vinfo.vid vinfo
          | _ -> ()) f.globals ;
      List.iter (fun g ->
          match g with
          | GVarDecl (vinfo,_) when vinfo.vstorage = Extern ->
             begin
               match vinfo.vtype with
               | TFun _ -> H.add externalFns vinfo.vname vinfo
               | _ -> ()
             end
          | _ -> ()) f.globals ;
    end

  method get_application_functions = H.fold (fun _ v r -> v :: r) applicationFns []

  method is_application_function (vid:int) = H.mem applicationFns vid

  method get_globalvars = H.fold (fun _ v a -> v::a) globalvars []

  method get_globalvar (vid:int) = 
    try
      H.find globalvars vid
    with
    | Not_found ->
       let gvars = H.fold (fun k v r -> (k,v) :: r) globalvars [] in
       raise (CCHFailure
                (LBLOCK [
                     STR "Global variable with vid " ; INT vid ;
                     STR " not found: " ;
                     pretty_print_list gvars
                                       (fun (vid,v) -> LBLOCK [ INT vid ; STR ":" ; STR v.vname ])
                                       " [" ", " "]" ]))
	
  method has_globalvar (vid:int) = Hashtbl.mem globalvars vid

  method get_globalvar_by_name (name:string) =
    let gvar = H.fold (fun _ vinfo result ->
                   match result with
                   | Some _ -> result
                   | _ -> if vinfo.vname = name then Some vinfo else None) globalvars None in
    match gvar with
    | Some v -> v
    | _ ->
       raise (CCHFailure
                (LBLOCK [ STR "Global variable " ; STR name ; STR " not found" ]))
    
  method get_comp (key:int) =
    try
      H.find compinfos key
    with
      Not_found -> raise (Invalid_argument ("get_comp " ^ (string_of_int key)))
	
  method get_enum (name:string) =
    try
      H.find enuminfos name
    with
      Not_found -> raise (Invalid_argument ("get_enum" ^ name))
	
  method get_type (name:string) =
    try
      H.find typedefs  name
    with
      Not_found -> raise (Invalid_argument ("get_type " ^ name))
	
  method get_type_unrolled (t:typ) = get_type_unrolled typedefs t

  method get_field_type (ckey:int) (fname:string) =
    try
      let comp = self#get_comp ckey in
      try
        let finfo = List.find (fun f -> f.fname = fname) comp.cfields in
        finfo.ftype
      with
      | Not_found ->
         raise (CCHFailure
                  (LBLOCK [ STR "Fieldinfo not found for fname " ; STR fname ;
                            STR "; fields found: " ;
                            pretty_print_list comp.cfields (fun f -> STR f.fname) "[" "," "]"]))
    with
      Invalid_argument s ->
      let msg = LBLOCK [ STR "Compinfo not found for fieldname " ; STR fname ;
                         STR " with key " ; INT ckey ] in
      begin
        ch_error_log#add "struct not found" msg ;
        raise (CCHFailure msg)
      end
       
  method get_field_info (ckey:int) (fname:string) =
    let comp = self#get_comp ckey in
    try
      List.find (fun f -> f.fname = fname) comp.cfields
    with
    | Not_found ->
       raise (CCHFailure
                (LBLOCK [ STR "Fieldinfo not found for fname " ; STR fname ;
                          STR "; fields found: " ;
                          pretty_print_list comp.cfields (fun f -> STR f.fname) "[" "," "]"]))
      
  method get_machine_sizes =
    if system_settings#has_wordsize then
      match system_settings#get_wordsize with
      | 32 -> linux_32_machine_sizes
      | 64 -> linux_64_machine_sizes
      | _ -> symbolic_sizes
    else
      symbolic_sizes
    
  method is_external_function (name:string) = H.mem externalFns name

  method has_external_header (name:string) =
    (H.mem externalFns name)
    && (String.length ((H.find externalFns name).vdecl.file) > 0)
    
  method get_external_header (name:string) =
    try
      let vinfo = H.find externalFns name in
      (try
        Filename.chop_extension (Filename.basename vinfo.vdecl.file)
       with
         _ ->
         begin
           raise (CCHFailure (LBLOCK [ STR "unknown file: " ; STR vinfo.vdecl.file ]))
         end)
    with
    | Not_found -> raise (Invalid_argument ("get_external_header " ^ name))
    | Invalid_argument s ->
       begin
         ch_error_log#add "chop extension"
                          (LBLOCK [ STR "external header: " ; STR name ]) ;
         raise (CCHFailure (LBLOCK [ STR "get_external_header: " ; STR name ;
                                     STR ": " ; STR s ]))
       end
	
end
  

let file_environment = new file_environment_t

