(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
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

(* =============================================================================
   The implementation in this file is based on the documents:

   Matt Pietrek. A Crash Course on the Depths of Win32 Structured Exception Handling.
   http://www.microsoft.com/msj/0197/exception/exception.aspx ;

   Igorsk, Reversing Microsoft Visual C++ Part I: Exception Handling
   http://www.openrce.org/articles/full_view/21
   ============================================================================= *)

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHLibTypes
open BCHLocation
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibpe *)
open BCHPESections
open BCHLibPETypes

module H = Hashtbl

class exn_unwind_map_entry_t:exn_unwind_map_entry_int =
object (self)

  val mutable toState = (-1)
  val mutable action = wordzero

  method read (s:string) =
    let ch = make_pushback_stream s in
    begin
      toState <- ch#read_doubleword#to_signed_numerical#toInt ;
      action <- ch#read_doubleword
    end

  method get_targetstate = toState

  method get_action = action

  method write_xml (node:xml_element_int) =
    begin
      node#setIntAttribute "targetstate" self#get_targetstate ;
      node#setAttribute "action" self#get_action#to_hex_string
    end

  method toPretty =
    LBLOCK [ 
      STR "target state: " ; INT self#get_targetstate ; NL ;
      STR "action      : " ; self#get_action#toPretty ; NL
    ]

end

class exn_function_info_t:exn_function_info_int =
object (self)

  val mutable magicNumber = wordzero
  val mutable maxState = (-1)
  val mutable pUnwindMap = wordzero
  val mutable nTryBlocks = 0
  val mutable pTryBlockMap = wordzero
  val mutable nIPMapEntries = 0
  val mutable pIPtoStateMap = wordzero
  val mutable pESTypeList = wordzero
  val mutable eHFlags = 0

  method read (s:string) =
    let ch = make_pushback_stream s in
    begin
      (* compiler version ---------------------------------------------------------
	 0x19930520: up to VC6, 0x19930521: VC7.x(2002-2003), 0x19930522: VC8 (2005) 
	 -------------------------------------------------------------------------- *)
      magicNumber <- ch#read_doubleword ;

      (* maxState -----------------------------------------------------------------
	 number of entries in unwind table
	 -------------------------------------------------------------------------- *)
      maxState <- ch#read_i32 ;

      (* pUnwindMap ---------------------------------------------------------------
	 table of unwind destructors
	 -------------------------------------------------------------------------- *)
	pUnwindMap <- ch#read_doubleword ;

      (* nTryBlocks ---------------------------------------------------------------
	 number of try blocks in the function
	 -------------------------------------------------------------------------- *)
	nTryBlocks <- ch#read_i32 ;

      (* pTryBlockMap -------------------------------------------------------------
	 mapping of catch blocks to try blocks
	 -------------------------------------------------------------------------- *)
	pTryBlockMap <- ch#read_doubleword ;

      (* nIPMapEntries ------------------------------------------------------------
	 not used on x86
	 -------------------------------------------------------------------------- *)
	nIPMapEntries <- ch#read_i32 ;

      (* pIPtoStateMap ------------------------------------------------------------
	 not used on x86
	 -------------------------------------------------------------------------- *)
	pIPtoStateMap <- ch#read_doubleword ;
	
      (* pESTypeList -------------------------------------------------------------
	 VC7+ only, expected exceptions list (function "throw" specifier)
	 ------------------------------------------------------------------------- *)
	pESTypeList <- ch#read_doubleword ;

      (* eHFlags -----------------------------------------------------------------
	 VC8+ only, bit 0 set if function was compiled with /EHs
	 ------------------------------------------------------------------------- *)
	eHFlags <- ch#read_i32 

    end

  method get_magicnumber = magicNumber

  method get_maxstate = maxState

  method get_unwindmap = pUnwindMap

  method get_ntryblocks = nTryBlocks

  method get_tryblockmap = pTryBlockMap

  method get_estypelist = pESTypeList

  method get_ehflags = eHFlags

  method write_xml (node:xml_element_int) =
    let seta t v = node#setAttribute t v#to_hex_string in
    let seti = node#setIntAttribute in
    begin
      seta "magic" self#get_magicnumber ;
      seti "maxstate" self#get_maxstate ;
      seta "unwindmap" self#get_unwindmap ;
      seti "ntryblocks" self#get_ntryblocks ;
      seta "tryblockmap" self#get_tryblockmap ;
      seta "estypelist" self#get_estypelist ;
      seti "ehflags" self#get_ehflags
    end

  method toPretty = 
    LBLOCK [
      STR "magic number : " ; self#get_magicnumber#toPretty ; NL ;
      STR "max state    : " ; INT self#get_maxstate ; NL ;
      STR "unwindmap    : " ; self#get_unwindmap#toPretty ; NL ;
      STR "try blocks   : " ; INT self#get_ntryblocks ; NL ;
      STR "tryblockmap  : " ; self#get_tryblockmap#toPretty ; NL ;
      STR "es type list : " ; self#get_estypelist#toPretty ; NL ;
      STR "EH flags     : " ; INT self#get_ehflags ; NL
    ]

end

class exn_handler_t 
  (voff1:int option)
  (voff2:int option)
  (voff3:int option)
  (voff4:int option)
  (exnfinfo:exn_function_info_int) 
  (unwindmaps:exn_unwind_map_entry_int list) =
object (self)

  method get_function_info = exnfinfo

  method get_unwindmaps = unwindmaps

  method private write_xml_varoffsets (node:xml_element_int) =
    List.iter (fun (vt,vv) ->
      match vv with
      | Some i -> node#setIntAttribute vt i
      | _ -> ()) [ ("v1",voff1) ; ("v2",voff2) ; ("v3",voff3) ; ("v4",voff4) ]

  method private write_xml_unwindmaps (node:xml_element_int) =
    node#appendChildren (List.map (fun m ->
      let mnode = xmlElement "unwindmap" in
      begin m#write_xml mnode ; mnode end) unwindmaps)

  method write_xml (node:xml_element_int) = 
    let fnode = xmlElement "funcinfo" in
    let unode = xmlElement "unwindmaps" in
    let vnode = xmlElement "varoffsets" in
    begin
      self#get_function_info#write_xml fnode ;
      self#write_xml_varoffsets vnode ;
      self#write_xml_unwindmaps unode ;
      node#appendChildren [ fnode ; vnode ; unode ]
    end
end

let exnhandlers = H.create 5

let write_xml_exnhandlers (node:xml_element_int) =
  let handlers = ref [] in
  let _ = H.iter (fun k v -> handlers := (index_to_doubleword k, v) :: !handlers)
    exnhandlers in
  let handlers = List.sort (fun (a1,_) (a2,_) -> a1#compare a2) !handlers in
  node#appendChildren (List.map (fun (a,v) ->
    let hnode = xmlElement "exnhandler" in
    begin
      v#write_xml hnode ;
      hnode#setAttribute "faddr" a#to_hex_string ;
      hnode
    end) handlers)
    

let get_unwindmaps (n:int) (addr:doubleword_int) =
  let pesection = pe_sections#get_containing_section addr in
  let rec range n = if n = 0 then [] else if n > 0 then (n-1) :: range (n-1) else [] in
  match pesection with
  | Some section ->
    let s = section#get_exe_string in
    let va = section#get_section_VA in
    let voffset = (addr#subtract va)#to_int in
    let sectionlen = String.length s in
    List.map (fun i ->
        let offset = voffset + (i * 8) in
        if offset < sectionlen then
          let xstr = string_suffix s offset in
          let unwindmap = new exn_unwind_map_entry_t in
          let _ = unwindmap#read xstr in
          unwindmap
        else
          raise (BCH_failure
                   (LBLOCK [ STR "get-unwindmaps: String.suffix. length: " ;
                             INT sectionlen ; STR "; offset: ";
                             INT offset ]))) (List.rev (range n))
  | _ -> []

let add_exnhandler 
    ?(voff1=None)
    ?(voff2=None)
    ?(voff3=None)
    ?(voff4=None)
    (sccaddr:doubleword_int option)   (* security_check_cookie *)
    (fhaddr:doubleword_int)           (* framehandler *)
    (exnfinfo:doubleword_int)
    (faddr:doubleword_int)  =
  let name = "__SEHandler_" ^ exnfinfo#to_hex_string ^ "__" in
  let _ = match sccaddr with
    | Some a ->
       let _ = chlog#add
                 "add function"
                 (LBLOCK [ faddr#toPretty ; STR ": " ; a#toPretty ;
                           STR ": security check cookie" ]) in
       (functions_data#add_function a)#add_name "__security_check_cookie__"
    | _ -> () in
  let _ = (functions_data#add_function fhaddr)#add_name "__InternalCxxFrameHandler__" in
  let _ = (functions_data#add_function faddr)#add_name name in
  let _ = chlog#add
            "add function:matched exn handler" 
            (LBLOCK [ faddr#toPretty ; STR ": " ; STR name ; STR "; " ;
                      fhaddr#toPretty ; STR ": __InternalCxxFrameHandler__" ]) in
  let xfinfo = new exn_function_info_t in
  let pesection = pe_sections#get_containing_section exnfinfo in
  match pesection with
  | Some section ->
     let s = section#get_exe_string in
     let sectionlen = String.length s in
     let va = section#get_section_VA in
     let offset = (exnfinfo#subtract va)#to_int in
     if sectionlen > offset then
       let exnfinfo_str = string_suffix s offset in
       let _ = xfinfo#read exnfinfo_str in
       let unwindmaps = get_unwindmaps xfinfo#get_maxstate xfinfo#get_unwindmap in
       let _ = List.iteri (fun i m ->
                   let name = ("__SEHUnwind_" ^ faddr#to_hex_string
                               ^ "_" ^ (string_of_int i) ^ "__") in
                   let _ = chlog#add
                             "add function:SEHUnwind"
                             (LBLOCK [ faddr#toPretty ; STR ": " ; m#get_action#toPretty ;
                                       STR "; " ;  STR name ]) in
	           (functions_data#add_function m#get_action)#add_name name) unwindmaps in
       let exnhandler = new exn_handler_t voff1 voff2 voff3 voff4 xfinfo unwindmaps in
       begin
         H.add exnhandlers faddr#index exnhandler ;
         true
       end
     else
       raise (BCH_failure
                (LBLOCK [ STR "add-exnhandler: String.suffix. Section length: " ;
                          INT sectionlen ; STR "; offset: " ; INT offset ]))
  | _ ->
    begin
      pr_debug [ STR "No section found for " ; exnfinfo#toPretty ; NL ] ;
      false
    end
  
let add_seh_exnhandler (exnfinfo:doubleword_int) (faddr:doubleword_int) =
  let name = "__SEH_" ^ exnfinfo#to_hex_string ^ "__" in
  let _ = (functions_data#add_function faddr)#add_name name in
  let _ = chlog#add "matched exn handler"
    (LBLOCK [ faddr#toPretty ; STR ": " ; STR name ]) in
  let xfinfo = new exn_function_info_t in
  let pesection = pe_sections#get_containing_section exnfinfo in
  match pesection with
  | Some section ->
     let s = section#get_exe_string in
     let sectionlen = String.length s in
     let va = section#get_section_VA in
     let offset = (exnfinfo#subtract va)#to_int in
     if sectionlen > offset then
       let exnfinfo_str = string_suffix s offset in
       let _ = xfinfo#read exnfinfo_str in
       let unwindmaps = get_unwindmaps xfinfo#get_maxstate xfinfo#get_unwindmap in
       let _ = List.iteri (fun i m ->
                   let name = "__SEHUnwind_" ^ faddr#to_hex_string ^ "_" ^ (string_of_int i) ^ "__" in
                   let _ = chlog#add
                             "add function:SEHUnwind"
                             (LBLOCK [ faddr#toPretty ; STR ": " ; m#get_action#toPretty ;
                                       STR "; " ;  STR name ]) in
	           (functions_data#add_function m#get_action)#add_name name) unwindmaps in
       let exnhandler = new exn_handler_t None None None None xfinfo unwindmaps in
       begin
         H.add exnhandlers faddr#index exnhandler ;
         true
       end
     else
       raise (BCH_failure
                (LBLOCK [ STR "add-seh-exnhandler: String.suffix. Section length: " ;
                          INT sectionlen ; STR "; offset: " ; INT offset ]))
  | _ ->
    begin
      pr_debug [ STR "No section found for " ; exnfinfo#toPretty ; NL ] ;
      false
    end

let todw s = 
  string_to_doubleword (littleendian_hexstring_todwstring s)

let todwoff s = 
  ((todw s)#to_signed_numerical)#toInt  (* signed doubleword offset *) 
  
let tooff s =
  let offset = string_to_doubleword ("0x" ^ s) in
  let offset = offset#to_int in
  if offset > 127 then offset - 256 else offset  (* signed byte offset *)

let exnpatterns = [

  (* example: V03c:0x4298fb

  0x4288f6  jmp* 0x42a110      __CxxFrameHandler(pExcept:?, pRN:?, pContext:?, pDC:?)
--------------------------------------------------------------------------------
  0x4298fb  mov eax, 0x42ba78  eax := 4373112
  0x429900  jmp 0x4288f6       goto 0x4288f6
  *)
  { xregex_s = Str.regexp ("ff25\\(........\\)b8\\(........\\)e9\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let imm = todw (Str.matched_group 2 fnbytes) in
      let coff = todw (Str.matched_group 3 fnbytes) in
      let jmpaddr = (faddr#add coff)#add_int 10 in
      let loc = make_location { loc_faddr = faddr ; loc_iaddr = jmpaddr } in
      let floc = get_floc loc in
      floc#has_call_target
        && floc#get_call_target#is_dll_call
        && floc#get_call_target#get_name = "__CxxFrameHandler"
        && add_seh_exnhandler imm faddr
      (*
	(let (_,name) = floc#get_dll_target in name = "__CxxFrameHandler") &&
	add_seh_exnhandler imm faddr *)
  } ;

  { xregex_s = Str.regexp 
      ("558bec83ec08535657fc8945fc33c0505050ff75fcff7514ff7510ff750cff7508e8" ^
       "\\(........\\)83c4208945f85f5e5b8b45f88be55dc3b8\\(........\\)e9" ^
       "\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let coff1 = todw (Str.matched_group 1 fnbytes) in
      let imm = todw (Str.matched_group 2 fnbytes) in
      let coff2 = todw (Str.matched_group 3 fnbytes) in
      let jmpaddr = (faddr#add coff2)#add_int 10 in
      let fhaddr = (jmpaddr#add coff1)#add_int 38 in
      add_exnhandler None fhaddr imm faddr
  } ;

  (* Vc91099:0x10023683
     1  e8<4>    InternalCxxFrameHandler
     2  8d42<2>  voff1
     3  8b4a<2>  voff2
     4  e8<4>    security_check_cookie
     5  b8<4>    mov eax,imm32
     6  e9<4>    jmp
  *)
  { xregex_s = Str.regexp
      ("558bec83ec08535657fc8945fc33c0505050ff75fcff7514ff7510ff750cff7508e8" ^
       "\\(........\\)83c4208945f85f5e5b8b45f88be55dc38b5424088d42\\(..\\)8b4a" ^
       "\\(..\\)33c8e8\\(........\\)b8\\(........\\)e9\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let coff1 = todw (Str.matched_group 1 fnbytes) in
      let voff1 = Some (tooff (Str.matched_group 2 fnbytes)) in
      let voff2 = Some (tooff (Str.matched_group 3 fnbytes)) in
      let coff2 = todw (Str.matched_group 4 fnbytes) in
      let imm = todw (Str.matched_group 5 fnbytes) in
      let coff3 = todw (Str.matched_group 6 fnbytes) in
      let sccaddr = Some ((faddr#add coff2)#add_int 17) in
      let jmpaddr = (faddr#add coff3)#add_int 27 in
      let fhaddr = (jmpaddr#add coff1)#add_int 38 in
      add_exnhandler ~voff1 ~voff2 sccaddr fhaddr imm faddr
  } ;

  (* Vc91099:0x10029908
     1  e8<4>    InternalCxxFrameHandler
     2  8d42<2>  voff1
     3  8b4a<2>  voff2
     4  e8<4>    security_check_cookie
     5  8b4a<2>  voff4
     6  e8<4>    security_check_cookie
     7  b8<4>    mov eax,imm32
     8  e9<4>    jmp
  *)
  { xregex_s = Str.regexp 
      ("558bec83ec08535657fc8945fc33c0505050ff75fcff7514ff7510ff750cff7508e8" ^
       "\\(........\\)83c4208945f85f5e5b8b45f88be55dc38b5424088d42\\(..\\)8b4a" ^
       "\\(..\\)33c8e8\\(........\\)8b4a\\(..\\)33c8e8\\(........\\)b8" ^
       "\\(........\\)e9\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let coff1 = todw (Str.matched_group 1 fnbytes) in
      let voff1 = Some (tooff (Str.matched_group 2 fnbytes)) in
      let voff2 = Some (tooff (Str.matched_group 3 fnbytes)) in
      let coff2 = todw (Str.matched_group 4 fnbytes) in
      let voff4 = Some (tooff (Str.matched_group 5 fnbytes)) in
      let imm = todw (Str.matched_group 7 fnbytes) in
      let coff4 = todw (Str.matched_group 8 fnbytes) in
      let sccaddr = Some ((faddr#add coff2)#add_int 17) in
      let jmpaddr = (faddr#add coff4)#add_int 37 in
      let fhaddr = (jmpaddr#add coff1)#add_int 38 in
      add_exnhandler ~voff1 ~voff2 ~voff4 sccaddr fhaddr imm faddr 
  } ;

  (* Vc91099:0x10023fe1
     1  e8<4>    InternalCxxFrameHandler
     2  8d42<2>  voff1
     3  8b8a<4>  voff2
     4  e8<4>    security_check_cookie
     5  bb4a<2>  voff4
     6  e8<4>    security_check_cookie
     7  b8<4>    mov eax,imm32
     8  e9<4>    jmp
  *)
  { xregex_s = Str.regexp 
      ("558bec83ec08535657fc8945fc33c0505050ff75fcff7514ff7510ff750cff7508e8" ^
       "\\(........\\)83c4208945f85f5e5b8b45f88be55dc38b5424088d42\\(..\\)8b8a" ^
       "\\(........\\)33c8e8\\(........\\)8b4a\\(..\\)33c8e8\\(........\\)b8" ^
       "\\(........\\)e9\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let coff1 = todw (Str.matched_group 1 fnbytes) in
      let voff1 = Some (tooff (Str.matched_group 2 fnbytes)) in
      let voff2 = Some (todwoff (Str.matched_group 3 fnbytes)) in
      let coff2 = todw (Str.matched_group 4 fnbytes) in
      let voff4 = Some (tooff (Str.matched_group 5 fnbytes)) in
      let imm = todw (Str.matched_group 7 fnbytes) in
      let coff4 = todw (Str.matched_group 8 fnbytes) in
      let sccaddr = Some ((faddr#add coff2)#add_int 17) in
      let jmpaddr = (faddr#add coff4)#add_int 37 in
      let fhaddr = (jmpaddr#add coff1)#add_int 38 in
      add_exnhandler ~voff1 ~voff2 ~voff4 sccaddr fhaddr imm faddr 
  } ;

  (* V007:0x45bed6 
     1  e8<4>    InternalCxxFrameHandler
     2  8d82<4>  voff1
     3  8b8a<4>  voff2
     4  e8<4>    security_check_cookie
     5  b8<4>    mov eax,imm32
     6  e9<4>    jmp
  *)
  { xregex_s = Str.regexp 
      ("558bec83ec08535657fc8945fc33c0505050ff75fcff7514ff7510ff750cff7508e8" ^
       "\\(........\\)83c4208945f85f5e5b8b45f88be55dc38b5424088d82\\(........\\)" ^
       "8b8a\\(........\\)33c8e8\\(........\\)b8\\(........\\)e9\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let coff1 = todw (Str.matched_group 1 fnbytes) in
      let voff1 = Some (todwoff (Str.matched_group 2 fnbytes)) in
      let voff2 = Some (todwoff (Str.matched_group 3 fnbytes)) in
      let coff2 = todw (Str.matched_group 4 fnbytes) in
      let imm = todw (Str.matched_group 5 fnbytes) in
      let coff4 = todw (Str.matched_group 6 fnbytes) in
      let sccaddr = Some ((faddr#add coff2)#add_int 23) in
      let jmpaddr = (faddr#add coff4)#add_int 33 in
      let fhaddr = (jmpaddr#add coff1)#add_int 38 in
      add_exnhandler ~voff1 ~voff2 sccaddr fhaddr imm faddr  
  } ;

  (* V007:45b925 
     1 e8<4>    InternalCxxFrameHandler
     2 8d82<4>  voff1
     3 8b8a<4>  voff2
     4 e8<4>    security_check_cookie
     5 83c0<2>  voff3
     6 8b4a<2>  voff4
     7 e8<4>    security_check_cookie
     8 b8<4>    mov eax,imm32
     9 e9<4>    jmp
  *)
  { xregex_s = Str.regexp 
      ("558bec83ec08535657fc8945fc33c0505050ff75fcff7514ff7510ff750cff7508e8" ^
       "\\(........\\)83c4208945f85f5e5b8b45f88be55dc38b5424088d82\\(........\\)" ^
       "8b8a\\(........\\)33c8e8\\(........\\)83c0\\(..\\)8b4a\\(..\\)33c8e8" ^
       "\\(........\\)b8\\(........\\)e9\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let coff1 = todw (Str.matched_group 1 fnbytes) in
      let voff1 = Some (todwoff (Str.matched_group 2 fnbytes)) in
      let voff2 = Some (todwoff (Str.matched_group 3 fnbytes)) in
      let coff2 = todw (Str.matched_group 4 fnbytes) in
      let voff3 = Some (tooff (Str.matched_group 5 fnbytes)) in
      let voff4 = Some (tooff (Str.matched_group 6 fnbytes)) in 
      let imm = todw (Str.matched_group 8 fnbytes) in
      let coff4 = todw (Str.matched_group 9 fnbytes) in
      let sccaddr = Some ((faddr#add coff2)#add_int 23) in
      let jmpaddr = (faddr#add coff4)#add_int 46 in
      let fhaddr = (jmpaddr#add coff1)#add_int 38 in
      add_exnhandler ~voff1 ~voff2 ~voff3 ~voff4 sccaddr fhaddr imm faddr 
  } ;

  (* V2bd:0x1001ddc8
     1 e8<4>    InternalCxxFrameHandler
     2 8d82<2>  voff1
     3 8b8a<2>  voff2
     4 e8<4>    security_check_cookie
     5 83c0<2>  voff3
     6 8b4a<2>  voff4
     7 e8<4>    security_check_cookie
     8 b8<4>    mov eax,imm32
     9 e9<4>    jmp
  *)
  { xregex_s = Str.regexp 
      ("558bec83ec08535657fc8945fc33c0505050ff75fcff7514ff7510ff750cff7508e8" ^
       "\\(........\\)83c4208945f85f5e5b8b45f88be55dc38b5424088d42\\(..\\)8b4a" ^
       "\\(..\\)33c8e8\\(........\\)83c0\\(..\\)8b4a\\(..\\)33c8e8\\(........\\)" ^
       "b8\\(........\\)e9\\(........\\)$") ;

    xregex_f = fun faddr fnbytes ->
      let coff1 = todw (Str.matched_group 1 fnbytes) in
      let voff1 = Some (tooff (Str.matched_group 2 fnbytes)) in
      let voff2 = Some (tooff (Str.matched_group 3 fnbytes)) in
      let coff2 = todw (Str.matched_group 4 fnbytes) in
      let voff3 = Some (tooff (Str.matched_group 5 fnbytes)) in
      let voff4 = Some (tooff (Str.matched_group 6 fnbytes)) in 
      let imm = todw (Str.matched_group 8 fnbytes) in
      let coff4 = todw (Str.matched_group 9 fnbytes) in
      let sccaddr = Some ((faddr#add coff2)#add_int 17) in
      let jmpaddr = (faddr#add coff4)#add_int 40 in
      let fhaddr = (jmpaddr#add coff1)#add_int 38 in
      add_exnhandler  ~voff1 ~voff2 ~voff3 ~voff4 sccaddr fhaddr imm faddr
  }
]


let register_exn_handler (faddr:doubleword_int) (fnbytes:string) =
  let _ = List.fold_left (fun found p ->
    found ||
      ((Str.string_match p.xregex_s fnbytes 0) && (p.xregex_f faddr fnbytes)))
    false exnpatterns in
  ()
