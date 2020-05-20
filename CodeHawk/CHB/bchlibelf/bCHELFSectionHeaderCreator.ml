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

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHSectionHeadersInfo

(* bchlibelf *)
open BCHELFSectionHeader
open BCHELFTypes

module H = Hashtbl
module P = Pervasives

let s2d = string_to_doubleword

let has_user_data (sectionname:string) =
  section_header_infos#has_section_header_info sectionname

let get_user_data (sectionname:string):section_header_info_int =
  if has_user_data sectionname then
    section_header_infos#get_section_header_info sectionname
  else
    raise
      (BCH_failure (LBLOCK [ STR "No user data found for " ;
                             STR sectionname ]))

let assumption_violation (p:pretty_t) =
  let msg = LBLOCK [ STR "Section header creation assumption violation: " ; p ] in
  raise (BCH_failure msg)

let warning (p:pretty_t) = chlog#add "section header creation" p

class section_header_creator_t
        (phdrs:(int * elf_program_header_int * elf_segment_t) list)
        (fileheader:elf_file_header_int)  =
object (self)

  val mutable section_headers = []
  val dynamicsegment =
    let s =
      List.fold_left (fun a (_,_,s) ->
          match a with
          | Some _ -> a
          | _ ->
             match s with
             | ElfDynamicSegment s -> Some s
             | _ -> None) None phdrs in
    match s with
    | Some s -> s
    | _ -> 
       raise (BCH_failure (LBLOCK [ STR "Dynamic table not found" ]))
  val loadsegments =
    List.filter (fun (_,h,_) ->
        match h#get_program_header_type with
        | PT_Load -> true
        | _ -> false) phdrs
  val base1 =
    let loadsegments =
      List.filter (fun (_,h,_) ->
        match h#get_program_header_type with
        | PT_Load -> true
        | _ -> false) phdrs in
    match loadsegments with
    | [] -> raise (BCH_failure (LBLOCK [ STR "No Load Segments found" ]))
    | (_,h,_)::_ -> h#get_vaddr

  method private get_offset_1 (vaddr:doubleword_int) =
    try
      vaddr#subtract base1
    with
    | _ ->
       raise (BCH_failure
                (LBLOCK [ STR "Error in computing section header offset-1: " ;
                          STR "base1: " ; base1#toPretty ;
                          STR "; addr: " ; vaddr#toPretty ]))

  method private get_offset_2 (vaddr:doubleword_int) =
    match loadsegments with
    | [] -> raise (BCH_failure (LBLOCK [ STR "No load segments found" ]))
    | [ (_,_,_) ] ->
       assumption_violation (STR "Only one load segment found" )
    | (_,_,_)::(_,ph,_)::_  ->
       let base2 = ph#get_vaddr in
       let offset2 = ph#get_offset in
       try
         (vaddr#subtract base2)#add offset2
       with
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [ STR "Error in computing section header offset-2: " ;
                         STR "base2: " ; base2#toPretty ;
                         STR "; addr: " ; vaddr#toPretty ]))

  method private get_interp_program_header =
    try
      let (_,ph,_) =
        List.find (fun (_,ph,_) ->
            match ph#get_program_header_type with
            | PT_Interpreter -> true
            | _ -> false) phdrs in ph
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK [ STR "PT_INTERP program header not found" ]))

  method private get_dynamic_program_header =
    try
      let (_,ph,_) =
        List.find (fun (_,ph,_) ->
            match ph#get_program_header_type with
            | PT_Dynamic -> true
            | _ -> false) phdrs in ph
    with
    | Not_found ->
       assumption_violation (STR "PT_DYNAMIC program header not found")

  method private has_reginfo_program_header =
    List.exists (fun (_,ph,_) ->
        match ph#get_program_header_type with
        | PT_RegInfo -> true
        | _ -> false) phdrs

  method private get_reginfo_program_header =
    try
      let (_,ph,_) =
        List.find (fun (_,ph,_) ->
            match ph#get_program_header_type with
            | PT_RegInfo -> true
            | _ -> false) phdrs in ph
    with
    | Not_found ->
       raise
         (BCH_failure (LBLOCK  [ STR "PT_REGINFO program header not found" ]))

  method get_section_headers =
    List.mapi
      (fun i sh -> (i,sh))
      (List.sort
         (fun sh1 sh2 -> sh1#get_addr#compare sh2#get_addr) section_headers)

  method create_section_headers =
    begin
      self#create_null_header ;
      self#create_interp_header ;
      self#create_reginfo_header ;
      self#create_dynamic_header ;
      self#create_hash_header ;
      self#create_dynsym_header ;
      self#create_dynstr_header ;
      self#create_gnu_version_header ;
      self#create_gnu_version_r_header ;
      self#create_init_header ;
      self#create_text_header ;
      self#create_fini_header ;
      self#create_rodata_header ;
      self#create_eh_frame_header ;
      self#create_ctors_header ;
      self#create_dtors_header ;
      self#create_jcr_header ;
      self#create_data_rel_ro_header ;
      self#create_data_header ;
      self#create_rld_map_header ;
      self#create_got_header ;
    end

  (* fixed *)
  method private create_null_header =
    let sh = mk_elf_section_header () in
    begin
      sh#set_fields ~sectionname:"" () ;
      section_headers <- sh :: section_headers
    end

  (* inputs: from program header, type PT_Interpreter
   * - offset: ph#get_offset
   * - addr: ph#get_vaddr
   * - align: ph#get_align
   * - size: ph#get_file_size
   *)
  method private create_interp_header =
    let sectionname = ".interp" in    
    let ph = self#get_interp_program_header in
    let sh = mk_elf_section_header () in
    let stype = s2d "0x1" in     (* SHT_ProgBits *)
    let flags = s2d "0x2" in     (* ALLOC *)
    let addr = ph#get_vaddr in
    let offset = ph#get_offset in
    let size = ph#get_file_size in
    let addralign = s2d "0x1" in
    begin
      sh#set_fields ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
      section_headers <- sh :: section_headers
    end

  (* inputs: from program header, type PT_RegInfo
   * - offset: ph#get_offset
   * - addr: ph#get_vaddr
   * - align: ph#get_align
   * - size: ph#get_file_size
   *)
  method private create_reginfo_header =
    let sectionname = ".reginfo" in    
    if self#has_reginfo_program_header then
      let ph = self#get_reginfo_program_header in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x70000006" in
      let flags = s2d "0x2" in
      let addr = ph#get_vaddr in
      let offset = ph#get_offset in
      let size = ph#get_file_size in
      let addralign = ph#get_align in
      begin
        sh#set_fields ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
      
  (* inputs: from program header, type PT_Dynamic
   * - offset: ph#get_offset
   * - addr: ph#get_vaddr
   * - align: ph#get_align
   * - size: ph#get_file_size
   * - link: to be set to .dynstr index
   *)
  method private create_dynamic_header =
    let sectionname = ".dynamic" in    
    let ph = self#get_dynamic_program_header in
    let sh = mk_elf_section_header () in
    let stype = s2d "0x1" in
    let flags = s2d "0x2" in
    let addr = ph#get_vaddr in
    let offset = ph#get_offset in
    let size = ph#get_file_size in
    let entsize = s2d "0x8" in
    let addralign = ph#get_align in
    let link = s2d "0x6" in
    begin
      sh#set_fields
        ~stype ~flags ~addr ~offset ~size ~entsize ~addralign ~link ~sectionname () ;
      section_headers <- sh :: section_headers
    end

  (* inputs: from dynamic table, program header, type PT_Load (1)
   * - addr: DT_HASH
   * - offset: DT_HASH - ph#get_vaddr
   * - size: ?
   * - link: to be set to .dynsym index
   *)
  method private create_hash_header =
    let sectionname = ".hash" in    
    if dynamicsegment#has_hash_address then
      let vaddr = dynamicsegment#get_hash_address in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x5" in
      let flags = s2d "0x2" in
      let addr =  vaddr in
      let offset = self#get_offset_1 vaddr in
      let size = s2d "0xac" in
      let entsize = s2d "0x4" in
      let addralign = s2d "0x4" in
      let link = s2d "0x5" in
      begin
        sh#set_fields ~stype ~flags ~addr ~offset ~size ~entsize ~addralign ~link~sectionname () ;
        section_headers <- sh :: section_headers
      end
      
  (* inputs: from dynamic table, program header, type PT_Load (1)
   * - addr: DT_SYMTAB
   * - offset: DT_SYMTAB - ph#get_vaddr
   * - size: DT_SYMENT * DT_MIPS_SYMTABNO 
   * - link: to be set to .dynstr index
   * - info: ?
   *)
  method private create_dynsym_header =
    let sectionname = ".dynsym" in    
    if dynamicsegment#has_symtab_address
       && dynamicsegment#has_syment
       && dynamicsegment#has_symtabno then
      let vaddr = dynamicsegment#get_symtab_address in
      let syment = dynamicsegment#get_syment in
      let symtabno = dynamicsegment#get_symtabno in
      let symtabsize = numerical_to_doubleword (syment#mult symtabno) in
      let sh = mk_elf_section_header () in
      let stype = s2d "0xb" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_1 vaddr in
      let size = symtabsize in
      let entsize = numerical_to_doubleword syment in
      let addralign = s2d "0x4" in
      let link = s2d "0x6" in
      let info = s2d "0x1" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~entsize ~addralign ~info ~link ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
      assumption_violation (STR "DT_SYMTAB, DT_SYMENT, or DT_SYMTABNO not present")

  (* inputs: from dynamic table, program header, type PT_Load (1)
   * - addr: DT_STRTAB
   * - offset: DT_STRTAB - ph#get_vaddr
   *  -size: DT_STRSZ
   *)
  method private create_dynstr_header =
    let sectionname = ".dynstr" in
    if dynamicsegment#has_strtab_address
       && dynamicsegment#has_string_table_size then
      let vaddr = dynamicsegment#get_strtab_address in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x3" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_1 vaddr in
      let size = numerical_to_doubleword dynamicsegment#get_string_table_size in
      let addralign = s2d "0x1" in
      begin
        sh#set_fields ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
      assumption_violation (STR "DT_STRTAB not present")

  (* inputs: from dynamic table, program header, type PT_Load (1)
   * - addr: DT_VERSYM
   * - offset: DT_VERSYM - ph#get_vaddr
   * - size: 2 * (DT_MIPS_SYMTABNO + 1)
   * - link: to be set to .dynsym index
   * - info: ?
   *)
  method private create_gnu_version_header =
    let sectionname = ".gnu.version" in    
    if dynamicsegment#has_gnu_symbol_version_table
       && dynamicsegment#has_symtabno then
      let vaddr = dynamicsegment#get_gnu_symbol_version_table in
      let symtabno = dynamicsegment#get_symtabno in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x6fffffff" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_1 vaddr in
      let size =
        numerical_to_doubleword
          ((symtabno#add numerical_one)#mult (mkNumerical 2)) in
      let addralign = s2d "0x2" in
      let info = s2d "0x1" in
      let link = s2d "0x5" in
      let entsize = s2d "0x2" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~entsize ~link ~info ~sectionname () ;
        section_headers <- sh :: section_headers
      end

  (* inputs: from dynamic table, program header, type PT_Load (1)
   * - addr: DT_VERNEED
   * - offset: DT_VERNEED - ph#get_vaddr
   * - size: DT_VERNEEDNUM * 20 ?
   * - link: to be set to .dynstr index
   * - info: ?
   *)
  method private create_gnu_version_r_header =
    let sectionname = ".gnu_version_r" in    
    if dynamicsegment#has_gnu_symbol_version_reqts
       && dynamicsegment#has_gnu_symbol_version_reqts_no then
      let vaddr = dynamicsegment#get_gnu_symbol_version_reqts in
      let neednum = dynamicsegment#get_gnu_symbol_version_reqts_no in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x6ffffffe" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_1 vaddr in
      let size = numerical_to_doubleword (neednum#mult (mkNumerical 32)) in
      let addralign = s2d "0x4" in
      let link = s2d "0x6" in
      let info = s2d "0x1" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~link ~info ~sectionname () ;
        section_headers <- sh :: section_headers
      end

  (* inputs: from dynamic table, program header, type PT_Load (1)
   * - addr: DT_INIT
   * - offset: DT_INIT - ph#get_vaddr
   * - size: fh#get_program_entry_point - DT_INIT
   *)
  method private create_init_header =
    let sectionname = ".init" in    
    if dynamicsegment#has_init_address then
      let vaddr = dynamicsegment#get_init_address in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x6" in
      let addr = vaddr in
      let offset = self#get_offset_1 vaddr in
      let size =
        try
          fileheader#get_program_entry_point#subtract vaddr
        with
        | _ -> assumption_violation (STR "program entry point < DT_INIT") in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
      assumption_violation (STR "DT_INIT not present")

  (* inputs: from elf file header, program header, type PT_Load (1)
   * - addr: fh#get_program_entry_point ?
   * - offset: addr - ph#get_vaddr
   * - size: DT_FINI - fh#get_program_entry_point
   *)
  method private create_text_header =
    let sectionname = ".text" in    
    if dynamicsegment#has_fini_address then
      let vaddr = fileheader#get_program_entry_point in
      let finiaddr = dynamicsegment#get_fini_address in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x6" in
      let addr = vaddr in
      let offset = self#get_offset_1 vaddr in
      let size =
        try
          finiaddr#subtract vaddr
        with
        | _ -> assumption_violation (STR "DT_FINI < program entry point") in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
      assumption_violation (STR "DT_FINI not present")

  (* inputs: from dynamic table, program header, type PT_Load (1)
   * - addr: DT_FINI
   * - offset: DT_FINI - ph#get_vaddr
   * - size: ?
   *)
  method private create_fini_header =
    let sectionname = ".fini" in    
    if dynamicsegment#has_fini_address then
      let vaddr = dynamicsegment#get_fini_address in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x6" in
      let addr = vaddr in
      let offset = self#get_offset_1 vaddr in
      let size = s2d "0x4c" in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
      assumption_violation (STR "DT_FINI not present")

  (* inputs: from program header, type PT_Load (1)
   * - addr: ?
   * - offset: addr - ph#get_vaddr
   * - size: ?
   *)
  method private create_rodata_header =
    let sectionname = ".rodata" in    
    if has_user_data sectionname then
      let userdata = get_user_data sectionname in
      if userdata#has_addr && userdata#has_size then
        let vaddr = userdata#get_addr in
        let sh = mk_elf_section_header () in
        let stype = s2d "0x1" in
        let flags = s2d "0x2" in
        let addr = vaddr in
        let offset = self#get_offset_1 vaddr in
        let size = userdata#get_size in
        let addralign = s2d "0x10" in
        begin
          sh#set_fields
            ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
          section_headers <- sh :: section_headers
        end
      else
        assumption_violation (STR "No addr/size information for .rodata")
    else
      assumption_violation (STR "No section header info for .rodata")

  (* inputs: from program header, type PT_Load (1)
   * - addr: ph#get_vaddr + ph#get_file_size - 4
   * - offset: addr - ph#get_vaddr
   * - size: 4?
   *)
  method private create_eh_frame_header =
    let sectionname = ".eh_frame" in    
    let (_,ph,_) = List.hd loadsegments in
    let vaddr = (ph#get_vaddr#add ph#get_file_size)#subtract_int 4 in
    let sh = mk_elf_section_header () in
    let stype = s2d "0x1" in
    let flags = s2d "0x2" in
    let addr = vaddr in
    let offset = self#get_offset_1 vaddr in
    let size = s2d "0x4" in
    let addralign = s2d "0x4" in
    begin
      sh#set_fields
        ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
      section_headers <- sh :: section_headers
    end

  (* inputs: program header, type PT_Load (2)
   * - addr: ph#get_vaddr ?
   * - offset: ph#get_offset
   * - size: 0x8 ?
   *)
  method private create_ctors_header =
    let sectionname = ".ctors" in        
    if (List.length loadsegments) > 1 then
      let (_,ph,_) = List.hd (List.tl loadsegments) in
      let vaddr = ph#get_vaddr in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_2 vaddr in
      let size = s2d "0x8" in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
     assumption_violation (STR "ctors: No second load segment")

  (* inputs: program header, type PT_Load (2)
   * - addr: ph#get_vaddr + size (.ctors) (8)
   * - offset: ph#get_offset + size (.dtors)
   * - size: 0x8 ?
   *)
  method private create_dtors_header =
    let sectionname = ".dtors" in
    if (List.length loadsegments) > 1 then
      let (_,ph,_) = List.hd (List.tl loadsegments) in
      let vaddr = ph#get_vaddr#add_int 8 in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_2 vaddr in
      let size = s2d "0x8" in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
      assumption_violation (STR "dtors: No second load segment")

  (* inputs: program header, type PT_Load (2)
   * - addr: ph#get_vaddr  + size(.ctors) + size(.dtors)  (16)
   * - offset: ph#get_offset + size(.ctors) + size(.dtors)
   * - size: 0x4 ?
   *)
  method private create_jcr_header =
    let sectionname = ".jcr" in
    if (List.length loadsegments) > 1 then
      let (_,ph,_) = List.hd (List.tl loadsegments) in
      let vaddr = ph#get_vaddr#add_int 16 in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_2 vaddr in
      let size = s2d "0x4" in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
    else
      assumption_violation (STR "jcr: No second load segment")

  (* inputs: program header, type PT_Load (2)
   * - addr: ph#get_vaddr + size(.ctors) + size(.dtors) + size(.jcr) (20)
   * - offset: ph#get_offset + size(.ctors) + size(.dtors) + size(.jcr)
   * - size: 0x4 ?
   *)
  method private create_data_rel_ro_header =
    let sectionname = ".data.rel.ro" in
    if (List.length loadsegments) > 1 then
      let (_,ph,_) = List.hd (List.tl loadsegments) in
      let vaddr = ph#get_vaddr#add_int 20 in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_2 vaddr in
      let size = s2d "0x4" in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end

  (* inputs: program header, type PT_Load (2)
   * - addr: ph#get_vaddr + size(.ctors) + size(.dtors) + size(.jcr) + size(data.rel.ro) (24)
   * - offset: ph#get_offset + size(.ctors) + size(.dtors) + size(.jcr) + size(data.rel.ro)
   * - size: 0x4 ?
   *)
  method private create_data_header =
    let sectionname = ".data" in    
    if (List.length loadsegments) > 1 then
      let (_,ph,_) = List.hd (List.tl loadsegments) in
      let vaddr = ph#get_vaddr#add_int 24 in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_2 vaddr in
      let size = s2d "0x10" in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end
      
  (* inputs: dynamic table, program header, PT_Load (2)
   * - addr: DT_MIPS_RLD_MAP
   * - offset: (DT_MIPS_RLD_MAP - ph#get_vaddr) + ph#get_offset
   * - size: ?
   *)
  method private create_rld_map_header =
    let sectionname = ".rld_map" in    
    if dynamicsegment#has_rld_map_address then
      let vaddr = dynamicsegment#get_rld_map_address in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_2 vaddr in
      let size = s2d "0x10" in
      let addralign = s2d "0x4" in
      begin
        sh#set_fields
          ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
        section_headers <- sh :: section_headers
      end

  (* inputs: dynamic table, program header, PT_Load (2)
   * - addr: DT_PLTGOT
   * - offset: (DT_PLTGOT - ph#get_vaddr) + ph#get_offset
   * - size: ph#get_vaddr + ph#get_size  - DT_PLGOT 
   *)
  method private create_got_header =
    let sectionname = ".got" in
    if dynamicsegment#has_got_address
    && (List.length loadsegments) > 1 then
      let (_,ph,_) = List.hd (List.tl loadsegments) in
      let vaddr = dynamicsegment#get_got_address in
      let sh = mk_elf_section_header () in
      let stype = s2d "0x1" in
      let flags = s2d "0x2" in
      let addr = vaddr in
      let offset = self#get_offset_2 vaddr in
      let size = (ph#get_vaddr#add ph#get_file_size)#subtract vaddr in
      let addralign = s2d "0x4" in
    begin
      sh#set_fields
        ~stype ~flags ~addr ~offset ~size ~addralign ~sectionname () ;
      section_headers <- sh :: section_headers
    end

  method toPretty =
    let headers =
      List.sort (fun (i1,_) (i2,_) -> P.compare i1 i2) self#get_section_headers in
    let addressmap =
      List.rev
        (List.fold_left (fun a (i,h) ->
             if i = 0 then
               []
             else if i = 1 then
               [ (h#get_addr, h#get_size, wordzero, false) ]
             else
               let (prevaddr,prevsize) =
                 match a with
                 | (a,s,_,_)::_ -> (a,s)
                 | _ -> (wordzero,wordzero) in
               let endaddr = prevaddr#add prevsize in
               let (gap,neg) =
                 if endaddr#le h#get_addr then
                   (h#get_addr#subtract endaddr,false)
                 else
                   (endaddr#subtract h#get_addr,true) in
               (h#get_addr, h#get_size, gap, neg) :: a) [] headers) in
    LBLOCK [
        LBLOCK (List.map (fun (i,h) ->
                    LBLOCK [ STR "section hedaer " ;  INT i ; NL ;
                             h#toPretty ; NL ]) headers) ; NL ;
        STR "Address Map" ; NL ;
        LBLOCK (List.map (fun (addr,size,gap,  neg) ->
                    LBLOCK [ fixed_length_pretty ~alignment:StrRight addr#toPretty 8 ; STR "  " ;
                             fixed_length_pretty ~alignment:StrRight size#toPretty 8 ; STR "  " ;
                             fixed_length_pretty ~alignment:StrRight gap#toPretty 8 ;
                             (if neg then STR " (neg)" else STR "") ; NL ]) addressmap) ]

                             

end
  


let create_section_headers
      (phdrs:(int * elf_program_header_int * elf_segment_t) list)
      (fileheader:elf_file_header_int):(int * elf_section_header_int) list =
  let creator = new section_header_creator_t phdrs fileheader in
  let _ = creator#create_section_headers in
  let headers = creator#get_section_headers in
  begin
    pr_debug [ STR "section headers" ; NL ; creator#toPretty ; NL ] ;
    headers
  end
