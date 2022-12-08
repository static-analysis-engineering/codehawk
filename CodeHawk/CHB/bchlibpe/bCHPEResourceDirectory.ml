(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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
   The implementation in this file is based on the document:

   Microsoft Portable Executable and Common Object File Format Specification,
   Revision 8.2 - September 21, 2010.
   ============================================================================= *)

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHTraceResult
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper

(* bchlibpe *)
open BCHLibPETypes

module TR = CHTraceResult


let fail_traceresult (msg: string) (r: 'a traceresult): 'a =
  if Result.is_ok r then
    TR.tget_ok r
  else
    fail_tvalue
      (trerror_record
         (LBLOCK [STR "BCHPEResourceDirectory:"; STR msg]))
      r


(* Note: all RVA's in this module, except for sectionRVA,  are relative to the start of 
   the section rather than to the start of the image
*)


class resource_data_entry_t ?(rID=None) ?(name=None) (rva:doubleword_int) =
object
  val rva = rva
  val rID = rID
  val name = name

  val mutable dataRVA = wordzero
  val mutable size = wordzero
  val mutable codepage = wordzero
  val mutable reserved = wordzero

  method read (byte_string:string) = 
    let offset = if rva#is_highest_bit_set then 
	rva#unset_highest_bit#to_int
      else 
	rva#to_int in
    let ch = make_pushback_stream (string_suffix byte_string offset) in
    begin
      
    (* 0, 4, Data RVA ----------------------------------------------------------
       The address of a unit of resource data in the Resource Data area.
       ------------------------------------------------------------------------- *)
      dataRVA <- ch#read_doubleword ;
      
    (* 4, 4, Size --------------------------------------------------------------
       The size, in bytes, of the resource data that is pointed by the Data RVA
       field.
       ------------------------------------------------------------------------- *)
      size <- ch#read_doubleword ;
      
    (* 8, 4, Codepage ----------------------------------------------------------
       The code page that is used to decode code point values within the 
       resource data. Typically, the code page would be the Unicode code page.
       ------------------------------------------------------------------------- *)
      codepage <- ch#read_doubleword ;
      
    (* 12, 4, Reserved ---------------------------------------------------------
       Must be 0.
       ------------------------------------------------------------------------- *)
      reserved <- ch#read_doubleword ;
      
    end
      
  method toPretty = 
    let identifier = match (rID, name) with
      | (Some id, None) -> 
        LBLOCK [ STR "Integer ID              " ; STR id#to_fixed_length_hex_string ]
      | (None, Some (nameRVA, name)) ->
        LBLOCK [ STR "Name                    " ; STR nameRVA#to_fixed_length_hex_string ; 
		 STR "  (" ; STR name ; STR ")" ]
      | _ -> 
	begin
          chlog#add "loading executable"
            (LBLOCK [ STR "Inconsistent resource data entry: " ; 
		      STR rva#to_fixed_length_hex_string ]) ;
          STR ""
	end in
    LBLOCK [
      identifier ; NL ;
      STR "Data RVA                " ; STR dataRVA#to_fixed_length_hex_string ; NL ;
      STR "Size                    " ; STR size#to_fixed_length_hex_string ; NL ;
      STR "Codepage                " ; STR codepage#to_fixed_length_hex_string ; NL ;
      STR "Reserved                " ; STR reserved#to_fixed_length_hex_string ; NL ]
      
end

type ('a) resource_directory_node_t =
| RDir of 'a * 'a resource_directory_node_t list
| RData of resource_data_entry_t

class type resource_directory_int = 
object ('a)
  method read: string -> 'a resource_directory_node_t list
  method set_section_RVA: doubleword_int -> unit
  method toPretty: pretty_t
end

class resource_directory_t 
  ?(rID=None) 
  ?(name=None) 
  (rva:doubleword_int):resource_directory_int =
object (self)

  val rID = rID
  val name = name
  val rva = rva

  val mutable sectionRVA = wordzero

  val mutable characteristics = wordzero
  val mutable timeDateStamp = wordzero
  val mutable majorVersion = 0
  val mutable minorVersion = 0
  val mutable numberOfNameEntries = 0
  val mutable numberOfIDEntries = 0

  method set_section_RVA (address:doubleword_int) = sectionRVA <- address

  method read (byte_string:string) =
    let offset = if rva#is_highest_bit_set then 
	rva#unset_highest_bit#to_int
      else 
	rva#to_int in
    let ch = make_pushback_stream (string_suffix byte_string offset) in
    begin
      
    (* 0, 4, Characteristics ---------------------------------------------------
       Resource flags. This field is reserved for future use. It is currently 
       set to zero.
       ------------------------------------------------------------------------- *)
      characteristics <- ch#read_doubleword ;

    (* 4, 4, Time/Date Stamp ---------------------------------------------------
       The time that the resource data was created by the resource compiler.
       ------------------------------------------------------------------------- *)
      timeDateStamp <- ch#read_doubleword ;

    (* 8, 2, Major version -----------------------------------------------------
       The major version number.
       ------------------------------------------------------------------------- *)
      majorVersion <- ch#read_ui16 ;

    (* 10, 2, Minor version ----------------------------------------------------
       The minor version number.
       ------------------------------------------------------------------------- *)
      minorVersion <- ch#read_ui16 ;

    (* 12, 2, Number of Name Entries -------------------------------------------
       The number of directory entries immediately following the table that use
       strings to identify Type, Name, or Language entries (depending on the 
       level of the tbale).
       ------------------------------------------------------------------------- *)
      numberOfNameEntries <- ch#read_ui16 ;

    (* 14, 2, Number of ID Entries ---------------------------------------------
       The number of directory entries immediately following the Name entries
       that use numeric that use numeric IDs for Type, Name, or Language entries.
       ------------------------------------------------------------------------- *)
      numberOfIDEntries <- ch#read_ui16 ;

      let children = ref [] in
      for i=1 to numberOfNameEntries do
	begin
	  
	  (* 0, 4, NameRVA -----------------------------------------------------
	     The address of a string that gives the Type, Name, or Language ID
	     entry, depending on the level of the table.
	     ------------------------------------------------------------------- *)
          let subnameRVA = ch#read_doubleword in
          let subname = self#read_name subnameRVA byte_string in 

          let subRVA = ch#read_doubleword in
          if subRVA#is_highest_bit_set then

          (* 4, 4, Subdirectory RVA --------------------------------------------
	     High bit 1. The lower 31 bits are the address of another resource
	     directory table (the next level down).
	     ------------------------------------------------------------------- *)
             let subdir = {< rva=subRVA ; name = Some (subnameRVA, subname) ; rID = None >} in
             let subchildren = subdir#read byte_string in
             children := (RDir (subdir, subchildren)) :: !children

          else
          
          (* 4, 4, Data Entry RVA ----------------------------------------------
	     High bit 0. Address of a Resource Data entry (leaf).
	     ------------------------------------------------------------------- *)
             let entry = new resource_data_entry_t ~name:(Some (subnameRVA,subname)) subRVA in
             begin
               entry#read byte_string ;
               children := (RData entry) :: !children
             end
         end
      done ;
      for i=1 to numberOfIDEntries do
        begin

          (* 0, 4, Integer ID --------------------------------------------------
	     A 32-bit integer that identifies the Type, Name, or Language ID 
	     entry.
	     ------------------------------------------------------------------- *)
          let id = ch#read_doubleword in

          let subRVA = ch#read_doubleword in
          if subRVA#is_highest_bit_set then

          (* 4, 4, Subdirectory RVA --------------------------------------------
	     High bit 1. The lower 31 bits are the address of another resource
	     directory table (the next level down).
	     ------------------------------------------------------------------- *)
             let subdir = {< rva=subRVA ; name = None ; rID = Some id >} in
             let subchildren = subdir#read byte_string in
             children := (RDir (subdir, subchildren)) :: !children

          else
          
          (* 4, 4, Data Entry RVA ----------------------------------------------
	     High bit 0. Address of a Resource Data entry (leaf).
	     ------------------------------------------------------------------- *)
             let entry = new resource_data_entry_t ~rID:(Some id) subRVA in
             begin
               entry#read byte_string ;
               children := (RData entry) :: !children
             end
         end
      done ;
           
      !children
    end

  method private read_name (nameRVA:doubleword_int) (byte_string:string) = 
    let offset = if nameRVA#is_highest_bit_set then 
	nameRVA#unset_highest_bit#to_int 
      else 
	nameRVA#to_int in
    let ch = make_pushback_stream (string_suffix byte_string offset) in
    ch#read_sized_unicode_string 

  method toPretty = 
    let identifier = match (rID, name) with
      (Some id, None) -> 
          LBLOCK [ STR "Integer ID                  " ; STR id#to_fixed_length_hex_string ]
    | (None, Some (nameRVA, name)) ->
          LBLOCK [ STR "Name                        " ; STR nameRVA#to_fixed_length_hex_string ; 
		   STR "  (" ; STR name ; STR ")" ]
    | _ -> 
       begin
         chlog#add "loading executable"
           (LBLOCK [ STR "Inconsistent resource data entry: " ; 
		     STR rva#to_fixed_length_hex_string ]) ;
         STR ""
       end in
    LBLOCK [ identifier ; NL ;
    STR "Characteristics             " ; STR characteristics#to_fixed_length_hex_string ; NL ;
    STR "Time/Date stamp             " ; STR timeDateStamp#to_time_date_string ; NL ;
    STR "Major/minor version         " ; INT majorVersion ; STR "/" ; INT minorVersion ; NL ;
    STR "Number of name entries      " ; INT numberOfNameEntries ; NL ;
    STR "Number of ID entries        " ; INT numberOfIDEntries ; NL ;
  ]

end

let resource_root_directory_node (address:doubleword_int) (byte_string:string) =
  let root_directory = new resource_directory_t ~name:(Some (wordzero,"root")) address in
  let children = root_directory#read byte_string in
  RDir (root_directory, children)


let rec resource_directory_to_pretty node =
  match node with
    RDir (dir, children) ->
      let subpretty = List.fold_left 
	  (fun a c -> LBLOCK [ a ; NL ; resource_directory_to_pretty c ]) (STR "") children in
      LBLOCK [ dir#toPretty ; INDENT (3, subpretty) ]
  | RData entry -> entry#toPretty


class resource_directory_table_t:resource_directory_table_int =
object

  val mutable sectionRVA   = wordzero
  val mutable directoryRVA = wordzero
  val mutable rootnode = RData (new resource_data_entry_t wordzero)

  method reset = 
    begin
      sectionRVA <- wordzero ;
      directoryRVA <- wordzero ;
      rootnode <- RData (new resource_data_entry_t wordzero)
    end

  method set_section_RVA (address:doubleword_int) = sectionRVA <- address

  method set_directory_RVA (address:doubleword_int) = directoryRVA <- address

  method read (byte_string) =
    log_titer
      (mk_tracelog_spec
         ~tag:"disassembly"
         "BCHPEResourceDirectory.resource_directory_table#read")
      (fun address ->
        rootnode <- resource_root_directory_node address byte_string)
      (directoryRVA#subtract sectionRVA)

  method write_xml (node:xml_element_int) =
    let setx t x = node#setAttribute t x#to_hex_string in
    begin
      setx "section-rva" sectionRVA ;
      setx "directory-rva" directoryRVA
    end

  method toPretty = resource_directory_to_pretty rootnode

end


let resource_directory_table = new resource_directory_table_t
