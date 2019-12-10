(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHXmlDocument

(* bchlib *)
open BCHDoubleword
open BCHLibTypes
open BCHUtilities

(* bchlibpe *)
open BCHLibPETypes

type startsize_t = { ss_va: doubleword_int ; ss_size: doubleword_int }
let default_startsize = { ss_va = wordzero ; ss_size = wordzero }
let ss va size = { ss_va = va ; ss_size = size }

class assembly_table_layout_t:assembly_table_layout_int =
object (self)

  val mutable exportDirectory = default_startsize
  val mutable exportAddressTable = default_startsize
  val mutable exportNamePointerTable = default_startsize
  val mutable exportOrdinalTable = default_startsize
  val mutable exportNameTable = default_startsize

  val mutable importDirectory = default_startsize
  val mutable importLookupTables:(startsize_t * string) list = []
  val mutable hintNameTable = default_startsize
  val mutable dllNameTable = default_startsize

  val mutable iat = default_startsize

  val mutable debugData = default_startsize

  val mutable loadConfigDirectory = default_startsize
  val mutable seHandlerTable = default_startsize

  method reset =
    begin
      exportDirectory <- default_startsize ;
      exportAddressTable <- default_startsize ;
      exportNamePointerTable <- default_startsize ;
      exportOrdinalTable <- default_startsize ;
      exportNameTable <- default_startsize ;
      importDirectory <- default_startsize ;
      importLookupTables <- [] ;
      hintNameTable <- default_startsize ;
      dllNameTable <- default_startsize ;
      iat <- default_startsize ;
      debugData <- default_startsize ;
      loadConfigDirectory <- default_startsize ;
      seHandlerTable <- default_startsize
    end

  (* ================================================================== Setters *)

  method add_import_lookup_table va size name = 
    importLookupTables <- ((ss va size),name) :: importLookupTables

  method set_export_directory va size          = exportDirectory <- ss va size
  method set_export_address_table va size      = exportAddressTable <- ss va size
  method set_export_name_pointer_table va size = exportNamePointerTable <- ss va size
  method set_export_ordinal_table va size      = exportOrdinalTable <- ss va size
  method set_export_name_table va size         = exportNameTable <- ss va size

  method set_import_directory va size  = importDirectory <- ss va size
  method set_hint_name_table va size   = hintNameTable <- ss va size
  method set_dll_name_table va size    = dllNameTable <- ss va size
  method set_IAT va size               = iat <- ss va size
  method set_debug_data va size        = debugData <- ss va size

  method set_load_config_directory va size = loadConfigDirectory <- ss va size
  method set_SE_handler_table va size      = seHandlerTable <- ss va size

  method private get_ss_items =
    [ (exportDirectory, "Export directory") ; 
      (exportAddressTable, "Export address table") ; 
      (exportNamePointerTable, "Export name pointer table") ; 
      (exportOrdinalTable, "Export ordinal table") ;
      (exportNameTable, "Export name table") ; 
      (importDirectory, "Import directory") ; 
      (hintNameTable, "Hint/name table") ; 
      (dllNameTable, "DLL name table") ;
      (iat, "Import Address Table") ; 
      (debugData, "Debug data") ; 
      (loadConfigDirectory, "Load configuration directory") ; 
      (seHandlerTable, "SE handler table") ] @ importLookupTables

  method get_fragments_in (va:doubleword_int) (vf:doubleword_int) =
    let fragment (ss,name) = (ss.ss_va, ss.ss_va#add ss.ss_size, name) in
    let includes ss = va#le ss.ss_va && ss.ss_va#lt vf in
    let ss_items = self#get_ss_items in
    List.fold_left
      (fun a (ss,name) -> if includes ss then (fragment (ss,name)) :: a else a) [] ss_items

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let ff t e = 
      let eNode = xmlElement "entry" in
      let set = eNode#setAttribute in
      let setx t x = set t x#to_hex_string in
      begin set "tag" t ; setx "va" e.ss_va ; setx "size" e.ss_size ; eNode end in
    let f t e = let n = ff t e in append [ n ] in
    let fl t l = match l with
      | [] -> ()
      | _ -> 
	let tNode = xmlElement t in
	begin
	  tNode#appendChildren
            (List.map (fun (e,name) ->
                 let safename =
                   if has_control_characters name then "__xx__" ^ (hex_string name) else name in
	         let n = ff "lookup-table" e in begin n#setAttribute "name" safename ; n end) l) ;
	  append [ tNode ]
	end in
    begin 
      f "export-directory" exportDirectory ;
      f "export-address-table" exportAddressTable ; 
      f "export-name-pointer-table" exportNamePointerTable ;
      f "export-ordinal-table" exportOrdinalTable ;
      f "export-name-table" exportNameTable ;
      f "import-directory" importDirectory ;
      fl "import-lookup-tables" importLookupTables ;
      f "hint-name-table" hintNameTable ;
      f "dll-name-table" dllNameTable ;
      f "iat" iat ;
      f "debug-data" debugData ;
      f "load-config-directory" loadConfigDirectory ;
      f "se-handler-table" seHandlerTable
    end

  method toPretty = 
    let pr s = LBLOCK [ STR s.ss_va#to_fixed_length_hex_string ; STR "  " ; 
			STR s.ss_size#to_fixed_length_hex_string ] in
    let rec prl l = match l with
      [] -> STR "" 
    | [(s,name)] ->   LBLOCK [ pr s ; STR "     " ; STR "(" ; STR name ; STR ")" ]
    | (s,name)::tl -> LBLOCK [ pr s ; STR "     " ; STR "(" ; STR name ; STR ")" ; NL ; 
			STR "                                  " ; prl tl ] in
    LBLOCK [
    STR "Export directory                  " ; pr exportDirectory ; NL ; 
    STR "Export address table              " ; pr exportAddressTable ; NL ;
    STR "Export name pointer table         " ; pr exportNamePointerTable ; NL ;
    STR "Export ordinal table              " ; pr exportOrdinalTable ; NL ;
    STR "Export name table                 " ; pr exportNameTable ; NL ; NL ;
    STR "Import directory                  " ; pr importDirectory ; NL ;
    STR "Import lookup tables              " ; prl importLookupTables ; NL ;
    STR "Hint name table                   " ; pr hintNameTable ; NL ;
    STR "Dll name table                    " ; pr dllNameTable ; NL ; NL ;
    STR "IAT                               " ; pr iat ; NL ; NL ;
    STR "Debug data                        " ; pr debugData ; NL ; NL ;
    STR "Load configuration directory      " ; pr loadConfigDirectory ; NL ;
    STR "SE handler table                  " ; pr seHandlerTable ; NL ; NL
  ]

end

let assembly_table_layout = new assembly_table_layout_t
