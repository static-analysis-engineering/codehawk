(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHNumRecordTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibelf *)
open BCHELFDictionary
open BCHELFSegment
open BCHELFTypes
open BCHELFUtil

module H = Hashtbl

let raise_dynamic_entry_error
      (tagname:string) (d_un:numerical_t) (msg:pretty_t) =
  let msg = LBLOCK [ STR "Dynamic entry error. d_tag: " ;
                     STR tagname ;
                     STR "; d_un: " ; d_un#toPretty ;
                     STR "; " ; msg ] in
  begin
    ch_error_log#add "dynamic entry"  msg ;
    raise (BCH_failure msg)
  end

class elf_dynamic_segment_entry_t (index:int):elf_dynamic_segment_entry_int =
object (self)

  val mutable d_tag = wordzero
  val mutable d_un = numerical_zero

  method id = index

  method read (ch:pushback_stream_int) =
    try
      begin
        (* 0,4, Tag ------------------------------------------------------------
           Dynamic Array Tag
           --------------------------------------------------------------------- *)
        d_tag <- ch#read_doubleword ;

        (* 4, 4, Value/Address -------------------------------------------------
           d_val These Elf32_Word objects represent integer values with various 
                  interpretations.
           d_ptr  These Elf32_Addr objects represent program virtual addresses. 
                  As mentioned previously, a file’s virtual addresses might not 
                  match the memory virtual addresses during execution. When 
                  interpreting addresses contained in the dynamic structure, 
                  the dynamic linker com- putes actual addresses, based on the 
                  original file value and the memory base address. For consistency, 
                  files do not contain relocation entries to ‘‘correct’’ addresses 
                  in the dynamic structure.
            ----------------------------------------------------------------------- *)
        d_un <- ch#read_num_signed_doubleword 
      end
    with
    | IO.No_more_input ->
       begin
         ch_error_log#add "no more input" (STR "elf_symbol_table_entry_t#read") ;
         raise IO.No_more_input
       end

  method get_d_tag = d_tag

  method get_tag = doubleword_to_dynamic_tag d_tag

  method get_tag_name = doubleword_to_dynamic_tag_name d_tag

  method get_d_un = d_un

  method get_d_ptr =
    let tagval = doubleword_to_dynamic_tag_value d_tag in
    match tagval with
    | DTV_d_ptr | DTV_d_none -> numerical_to_doubleword d_un
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Value of " ; STR self#get_tag_name ;
                      STR " cannot be interpreted as pointer" ]))

  method get_d_val =
    let tagval = doubleword_to_dynamic_tag_value d_tag in
    match tagval with
    | DTV_d_val | DTV_d_none -> d_un
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [ STR "Value of " ; STR self#get_tag_name ;
                      STR " cannot be interpreted as value" ]))

  method is_relocation_table =
    match self#get_tag with DT_Rel -> true | _ -> false

  method get_relocation_table =
    if self#is_relocation_table then
      self#get_d_ptr
    else
      raise_dynamic_entry_error
        self#get_tag_name d_un (STR "get_relocation_table")

  method is_relocation_table_size =
    match self#get_tag with DT_RelSz -> true | _ -> false

  method get_relocation_table_size  =
    if self#is_relocation_table_size then
      self#get_d_val
    else
      raise_dynamic_entry_error
        self#get_tag_name d_un (STR "get_relocation_table_size")

  method is_relocation_table_entry =
    match self#get_tag with  DT_RelEnt -> true | _ -> false

  method get_relocation_table_entry  =
    if self#is_relocation_table_entry then
      self#get_d_val
    else
      raise_dynamic_entry_error
        self#get_tag_name d_un (STR "get_relocationn_table_entry")

  method is_string_table =
    match self#get_tag with DT_StrTab -> true | _ -> false

  method get_string_table =
    if self#is_string_table then
      self#get_d_ptr
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_string_table")
    
  method is_string_table_size =
    match self#get_tag with DT_StrSz -> true | _ -> false

  method get_string_table_size  =
    if self#is_string_table_size then
      self#get_d_val
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_string_table_size")

  method is_symbol_table =
    match self#get_tag with DT_SymTab -> true | _ -> false

  method get_symbol_table =
    if self#is_symbol_table then
      self#get_d_ptr
    else
      raise_dynamic_entry_error self#get_tag_name d_un  (STR "get_symbol_table")

  method is_hash_table =
    match self#get_tag with DT_Hash -> true | _ -> false

  method get_hash_table =
    if self#is_hash_table then
      self#get_d_ptr
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_hash_table")

  method is_gnu_symbol_version_table =
    match self#get_tag with DT_VerSym  -> true | _ -> false

  method get_gnu_symbol_version_table =
    if self#is_gnu_symbol_version_table then
      self#get_d_ptr
    else
      raise_dynamic_entry_error
        self#get_tag_name d_un (STR "get_gnu_symbol_version_table")

  method is_gnu_symbol_version_reqts =
    match self#get_tag with DT_VerNeed ->  true | _ -> false

  method get_gnu_symbol_version_reqts =
    if self#is_gnu_symbol_version_reqts then
      self#get_d_ptr
    else
      raise_dynamic_entry_error
        self#get_tag_name d_un (STR "get_gnu_symbol_version_reqts")

  method is_gnu_symbol_version_reqts_no =
    match self#get_tag with DT_VerNeedNum -> true | _ -> false

  method get_gnu_symbol_version_reqts_no =
    if self#is_gnu_symbol_version_reqts_no then
      self#get_d_val
    else
      raise_dynamic_entry_error
    self#get_tag_name d_un (STR "get_gnu_symbol_version_requts_no")

  method is_init =
    match self#get_tag with DT_Init -> true | _ -> false

  method get_init =
    if self#is_init then
      self#get_d_ptr
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR  "get_init")

  method is_fini =
    match self#get_tag with DT_Fini -> true | _ -> false

  method get_fini =
    if self#is_fini then
      self#get_d_ptr
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_fini")

  method is_rld_map =
    match self#get_tag with DT_MIPS_Rld_Map -> true | _ -> false

  method get_rld_map =
    if self#is_rld_map then
      self#get_d_ptr
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_rld_map")

  method is_got =
    match self#get_tag with DT_PltGot -> true | _ -> false

  method get_got =
    if self#is_got then
      self#get_d_ptr
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_got")

  method is_syment =
    match self#get_tag with DT_SymEnt -> true | _ -> false

  method get_syment =
    if self#is_syment then
      self#get_d_val
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_syment")

  method is_symtabno =
    match self#get_tag with DT_MIPS_SymTabNo -> true | _ -> false

  method get_symtabno =
    if self#is_symtabno then
      self#get_d_val
    else
      raise_dynamic_entry_error self#get_tag_name d_un (STR "get_symtabno")

  method to_rep_record =
    let tagval =
      match doubleword_to_dynamic_tag_value d_tag with
      | DTV_d_ptr | DTV_d_none -> (numerical_to_doubleword d_un)#to_hex_string
      | DTV_d_val -> d_un#toString in
    let args = [ ] in
    let tags = [ self#get_tag_name ;  tagval ] in
    (tags,args)

  method toPretty =
    let tagval =
      match doubleword_to_dynamic_tag_value d_tag with
      | DTV_d_ptr | DTV_d_none -> (numerical_to_doubleword d_un)#to_hex_string
      | DTV_d_val -> d_un#toString in
    LBLOCK [ STR self#get_tag_name ; STR ": " ; STR tagval ]


end
    
class elf_dynamic_segment_t
        (s:string)
        (vaddr:doubleword_int):elf_dynamic_segment_int =
object (self)

  val mutable entries = []

  inherit elf_raw_segment_t s vaddr as super

  method read =
    try
      let entrysize = 8 in
      let ch =
        make_pushback_stream ~little_endian:system_info#is_little_endian s in
      let n = (String.length s) / entrysize in
      let c = ref 0 in
      begin
        while !c < n do
          let entry = new elf_dynamic_segment_entry_t !c in
          begin
            entry#read ch ;
            c :=  !c + 1 ;
            entries <- entry :: entries
          end
        done;
      end
    with
    | IO.No_more_input ->
       ch_error_log#add "no more input"
                        (LBLOCK [ STR "Unable to read the dynamic segment" ])

  method has_reltab_address =
    List.exists (fun e -> e#is_relocation_table) entries

  method get_reltab_address =
    try
      let e = List.find (fun e -> e#is_relocation_table) entries in
      e#get_relocation_table
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_RELA not found in Dynamic Segment" ]))

  method has_reltab_size =
    List.exists (fun e -> e#is_relocation_table_size) entries

  method get_reltab_size =
    try
      let e = List.find (fun e -> e#is_relocation_table_size) entries in
      e#get_relocation_table_size
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_RELASZ not found in Dynamic Segment" ]))

  method has_reltab_ent =
    List.exists (fun e -> e#is_relocation_table_entry) entries

  method get_reltab_ent =
    try
      let e = List.find (fun e -> e#is_relocation_table_entry) entries in
      e#get_relocation_table_entry
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR  "DT_RELAENT not found in Dynamic Segment" ]))

  method has_hash_address = List.exists (fun e -> e#is_hash_table) entries

  method get_hash_address =
    try
      let e = List.find (fun e -> e#is_hash_table) entries in e#get_hash_table
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_HASH not found in Dynamic Segment" ]))

  method has_symtab_address = List.exists (fun e -> e#is_symbol_table) entries

  method get_symtab_address =
    try
      let e = List.find (fun e -> e#is_symbol_table) entries in e#get_symbol_table
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_SYMTAB not found in Dynamic Segment" ]))

  method has_strtab_address = List.exists (fun e -> e#is_string_table) entries

  method get_strtab_address =
    try
      let e = List.find (fun e -> e#is_string_table) entries in e#get_string_table
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_STRTAB not found in Dynamic Segment" ]))

  method has_init_address = List.exists (fun e -> e#is_init) entries

  method get_init_address =
    try
      let e = List.find (fun e -> e#is_init) entries in e#get_init
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_INIT not found in Dynamic Segment" ]))

  method has_fini_address = List.exists (fun e -> e#is_fini) entries

  method get_fini_address =
    try
      let e = List.find (fun e -> e#is_fini) entries in e#get_fini
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_FINI not found in Dynamic Segment" ]))

  method has_rld_map_address = List.exists (fun e -> e#is_rld_map) entries

  method get_rld_map_address =
    try
      let e = List.find (fun e ->  e#is_rld_map) entries in e#get_rld_map
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_MIPS_RLD_MAP not found in Dynamic Segment" ]))

  method has_got_address = List.exists (fun e -> e#is_got) entries

  method get_got_address =
    try
      let e = List.find (fun e -> e#is_got) entries in e#get_got
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_PLTGOT not found in Dynamic Segment" ]))

  method has_gnu_symbol_version_table =
    List.exists (fun e -> e#is_gnu_symbol_version_table) entries

  method get_gnu_symbol_version_table =
    try
      let e = List.find (fun e -> e#is_gnu_symbol_version_table) entries in
      e#get_gnu_symbol_version_table
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_VERSYM not found in Dynamic Segment" ]))

  method has_gnu_symbol_version_reqts =
    List.exists (fun e -> e#is_gnu_symbol_version_reqts) entries

  method get_gnu_symbol_version_reqts =
    try
      let e = List.find (fun e -> e#is_gnu_symbol_version_reqts) entries in
      e#get_gnu_symbol_version_reqts
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_VERNEED not found in Dynamic Segment" ]))

  method has_gnu_symbol_version_reqts_no =
    List.exists (fun e -> e#is_gnu_symbol_version_reqts) entries

  method get_gnu_symbol_version_reqts_no =
    try
      let e = List.find (fun e -> e#is_gnu_symbol_version_reqts_no) entries in
      e#get_gnu_symbol_version_reqts_no
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_VERNEEDNUM not found in Dynamic Segment" ]))

  method has_syment = List.exists (fun e -> e#is_syment) entries

  method get_syment =
    try
      let e = List.find (fun e -> e#is_syment) entries in e#get_syment
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_SYMENT not found in Dynamic Segment" ]))

  method has_symtabno = List.exists (fun e -> e#is_symtabno) entries

  method get_symtabno =
    try
      let e = List.find (fun e -> e#is_symtabno) entries in e#get_symtabno
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_SYMTABNO not found in Dynamic Segment" ]))

  method has_string_table_size = List.exists (fun e -> e#is_string_table_size) entries

  method get_string_table_size =
    try
      let e = List.find (fun e -> e#is_string_table_size) entries in
      e#get_string_table_size
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "DT_STRSZ not found in Dynamic Segment" ]))    

  method write_xml_entries (node:xml_element_int) =
    let table = mk_num_record_table "dynamic-table" in
    begin
      List.iter (fun e -> table#add e#id e#to_rep_record) entries ;
      table#write_xml node
    end

  method toPretty =
    LBLOCK (List.map (fun e -> LBLOCK [ e#toPretty ; NL ]) entries)

end

let mk_elf_dynamic_segment s h vaddr =
  let table = new elf_dynamic_segment_t s vaddr in
  begin
    table#read ;
    table
  end

let read_xml_elf_dynamic_segment (node:xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  let vaddr = string_to_doubleword (node#getAttribute "vaddr") in
  let table = new elf_dynamic_segment_t s vaddr in
  begin
    table#read ;
    table
  end
