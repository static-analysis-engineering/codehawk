(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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
open CHLanguage
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHNumRecordTable
open CHTraceResult
open CHUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypePretty
open BCHBCTypeUtil
open BCHDemangler
open BCHDoubleword
open BCHLibTypes

module H = Hashtbl
module TR = CHTraceResult

let p2s = CHPrettyUtil.pretty_to_string

let bd = BCHDictionary.bdictionary


let sanitize_function_name (s: string) =
  string_replace '.' "_" s


let regvar_intro_to_string (rvi: regvar_intro_t) =
  let ptype =
    match rvi.rvi_vartype with
    | Some t ->
       let iscast = if rvi.rvi_cast then ", cast" else "" in
       " (" ^ (btype_to_string t) ^ iscast ^ ")"
    | _ -> "" in
  rvi.rvi_iaddr#to_hex_string ^ ": " ^ rvi.rvi_name ^ ptype


let stackvar_intro_to_string (svi: stackvar_intro_t) =
  let ptype =
    match svi.svi_vartype with
    | Some t -> " (" ^ (btype_to_string t) ^ ")"
    | _ -> "" in
  let lc_p = if svi.svi_loopcounter then " (lc)" else "" in
  (string_of_int svi.svi_offset) ^ ": " ^ svi.svi_name ^ ptype ^ lc_p


let reachingdef_spec_to_string (rds: reachingdef_spec_t) =
  let uselocs = "[" ^ (String.concat ", " rds.rds_uselocs) ^ "]" in
  let rdeflocs =  "[" ^ (String.concat ", " rds.rds_rdeflocs) ^ "]" in
  rds.rds_variable ^ ": use: " ^ uselocs ^ "; remove-rdefs: " ^ rdeflocs


let function_annotation_to_string (a: function_annotation_t) =
  let rvintros =
    if (List.length a.regvarintros) > 0 then
      ("Register-variable-introductions: ["
       ^ (String.concat "; " (List.map regvar_intro_to_string a.regvarintros))
       ^ "]")
    else
      "" in
  let svintros =
    if (List.length a.stackvarintros) > 0 then
      ("Stack-variable-introductions: ["
       ^ (String.concat "; " (List.map stackvar_intro_to_string a.stackvarintros))
       ^ "]")
    else
      "" in
  let rdefspecs =
    if (List.length a.reachingdefspecs) > 0 then
      ("Reaching-def-specs: ["
       ^ (String.concat "; " (List.map reachingdef_spec_to_string a.reachingdefspecs))
       ^ "]")
    else
      "" in
  List.fold_left (fun acc s ->
      if s = "" then
        acc
      else if acc = "" then
        s
      else
        acc ^ "\n" ^ s) "" [rvintros; svintros; rdefspecs]


class function_data_t (fa:doubleword_int) =
object (self)

  val faddr = fa
  val mutable names = []
  val mutable non_returning = false
  val mutable incomplete = false
  val mutable ida_provided = false
  val mutable user_provided = false
  val mutable by_preamble = false
  val mutable virtual_function = false
  val mutable classinfo = None
  val mutable functionannotation: function_annotation_t option = None
  val mutable inlined = false
  val mutable library_stub = false
  val mutable inlined_blocks = []
  val mutable functiontype = t_unknown
  val mutable callsites = 0
  val mutable pathcontexts = []  (* (ctxt_iaddress_t, ctxt_iaddress_t list) list *)
  val mutable reglhstypes = []  (* (register_t * iaddr * btype_t option) list *)
  val mutable stacklhstypes = [] (* (offset * btype_t option) list *)

  method set_function_type (ty: btype_t) = functiontype <- ty

  method set_non_returning = non_returning <- true

  method set_inlined = inlined <- true

  method set_by_preamble = by_preamble <- true

  method set_incomplete = incomplete <- true

  method set_ida_provided = ida_provided <- true

  method set_user_provided = user_provided <- true

  method set_virtual = virtual_function <- true

  method set_library_stub = library_stub <- true

  method add_callsite = callsites <- callsites + 1

  method add_path_context (startaddr: string) (sentinels: string list) =
    pathcontexts <- (startaddr, sentinels) :: pathcontexts

  method get_path_contexts = pathcontexts

  method has_path_contexts =
    match pathcontexts with [] -> false | _ -> true

  method remove_callsite =
    if callsites > 0 then
      begin
        callsites <- callsites -1;
        callsites
      end
    else
      0

  method has_callsites = callsites > 0

  method set_reglhs_types (regtypes: (register_t * string * btype_t option) list) =
    reglhstypes <- regtypes

  method get_reglhs_types = reglhstypes

  method get_reglhs_type (reg: register_t) (iaddr: string): btype_t option =
    List.fold_left (fun acc (r, i, t) ->
        match acc with
        | Some _ -> acc
        | _ ->
           if BCHCPURegisters.register_equal reg r && i = iaddr then t else acc)
      None reglhstypes

  method set_stack_offset_types (stacktypes: (int * btype_t option) list) =
    stacklhstypes <- stacktypes

  method get_stack_offset_types = stacklhstypes

  method get_stack_offset_type (offset: int): btype_t option =
    List.fold_left (fun acc (o, t) ->
        match acc with
        | Some _ -> acc
        | _ -> if offset == o then t else acc) None stacklhstypes

  method add_name (s:string) =
    let s = sanitize_function_name s in
    if List.mem s names then
      ()
    else
      names <- s::names

  method set_class_info ~(classname:string) ~(isstatic:bool) =
    classinfo <- Some (classname,isstatic)

  method set_function_annotation (a: function_annotation_t) =
    begin
      functionannotation <- Some a;
      chlog#add
        "function annotation"
        (LBLOCK [STR "function "; faddr#toPretty; STR ": ";
                 STR (function_annotation_to_string a)])
    end

  method has_function_annotation: bool =
    match functionannotation with Some _ -> true | _ -> false

  method get_function_annotation: function_annotation_t option =
    functionannotation

  method get_regvar_intro (iaddr: doubleword_int): regvar_intro_t option =
    match self#get_function_annotation with
    | Some a ->
       List.fold_left (fun acc rvi ->
           match acc with
           | Some _ -> acc
           | _ -> if rvi.rvi_iaddr#equal iaddr then Some rvi else None)
         None a.regvarintros
    | _ -> None

  method get_stackvar_intro (offset: int): stackvar_intro_t option =
    match self#get_function_annotation with
    | Some a ->
       List.fold_left (fun acc svi ->
           match acc with
           | Some _ -> acc
           | _ -> if svi.svi_offset = offset then Some svi else None)
         None a.stackvarintros
    | _ -> None

  method has_regvar_type_annotation (iaddr: doubleword_int): bool =
    match self#get_function_annotation with
    | Some a ->
       List.exists
         (fun rvi -> rvi.rvi_iaddr#equal iaddr && Option.is_some rvi.rvi_vartype)
         a.regvarintros
    | _ -> false

  method has_stackvar_type_annotation (offset: int): bool =
    match self#get_function_annotation with
    | Some a ->
       List.exists
         (fun svi -> svi.svi_offset = offset && Option.is_some svi.svi_vartype)
         a.stackvarintros
    | _ -> false

  method has_regvar_type_cast (iaddr: doubleword_int): bool =
    match self#get_function_annotation with
    | Some a ->
       List.exists
         (fun rvi -> rvi.rvi_iaddr#equal iaddr && rvi.rvi_cast) a.regvarintros
    | _ -> false

  method has_stackvar_type_cast (offset: int): bool =
    match self#get_function_annotation with
    | Some a ->
       List.exists
         (fun svi -> svi.svi_offset = offset && svi.svi_cast) a.stackvarintros
    | _ -> false

  method get_regvar_type_annotation (iaddr: doubleword_int): btype_t traceresult =
    let opttype =
      match self#get_function_annotation with
      | None ->
         Some
           (Error [
                __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                ^ "Function " ^ faddr#to_hex_string ^ " does not have annotations"])
      | Some a ->
         List.fold_left
           (fun acc rvi ->
             match acc with
             | Some _ -> acc
             | _ ->
                if rvi.rvi_iaddr#equal iaddr then
                  match rvi.rvi_vartype with
                  | Some t -> Some (Ok t)
                  | _ ->
                     Some (Error [
                               __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                               ^ "Register var annotation at "
                               ^ iaddr#to_hex_string
                               ^ " does not have a type"])
                else
                  acc) None a.regvarintros in
    match opttype with
    | Some r -> r
    | None ->
       Error [
           __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
           ^ "No register var annotation found at " ^ iaddr#to_hex_string]

  method get_stackvar_type_annotation (offset: int): btype_t traceresult =
    let opttype =
      match self#get_function_annotation with
      | None ->
         Some
           (Error [
                __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                ^ "Function " ^ faddr#to_hex_string ^ " does not have annotations"])
      | Some a ->
         List.fold_left
           (fun acc svi ->
             match acc with
             | Some _ -> acc
             | _ ->
                if svi.svi_offset = offset then
                  match svi.svi_vartype with
                  | Some t -> Some (Ok t)
                  | _ ->
                     Some
                       (Error [
                            __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                            ^ "Stack var annotation at offset "
                            ^ (string_of_int offset)
                            ^ " does not have a type"])
                else
                  acc) None a.stackvarintros in
    match opttype with
    | Some r -> r
    | None ->
       Error [
           __FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
           ^ "No stackvar annotation found at offset " ^ (string_of_int offset)]

  method is_typing_rule_enabled ?(rdef=None) (loc: string) (name: string): bool =
    let rdefloc =
      match rdef with
      | None -> loc
      | Some rdefaddr -> loc ^ ":" ^ rdefaddr in
    match self#get_function_annotation with
    | None -> BCHSystemSettings.system_settings#is_typing_rule_enabled name
    | Some a ->
       let is_user_enabled () =
         List.fold_left
           (fun acc tra ->
             acc ||
               (if tra.tra_action = "enable" && tra.tra_name = name then
                  (List.mem "all" tra.tra_locations)
                  || (List.mem loc tra.tra_locations)
                else
                  false)) false a.typingrules in
       let is_user_disabled () =
         List.fold_left
           (fun acc tra ->
             acc ||
               (if tra.tra_action = "disable" && tra.tra_name = name then
                  (List.mem "all" tra.tra_locations)
                  || (List.mem loc tra.tra_locations)
                  || (List.mem rdefloc tra.tra_locations)
                else
                  false)) false a.typingrules in
       if is_user_enabled () then
         true
       else if is_user_disabled () then
         false
       else
         BCHSystemSettings.system_settings#is_typing_rule_enabled name

  method is_const_global_variable (name: string): bool =
    match self#get_function_annotation with
    | None -> false
    | Some a -> List.mem name a.constglobalvars

  method filter_deflocs
           (iaddr: string) (v: variable_t) (deflocs: symbol_t list): symbol_t list =
    match self#get_function_annotation with
    | None -> deflocs
    | Some a when (List.length a.reachingdefspecs) > 0 ->
       let vname = v#getName#getBaseName in
       let deflocs =
         List.fold_left
           (fun acc sym ->
             let symname = sym#getBaseName in
             if (List.fold_left
                   (fun filteracc rds ->
                     filteracc ||
                       (if rds.rds_variable = vname then
                          (List.mem iaddr rds.rds_uselocs)
                          && (List.mem symname rds.rds_rdeflocs)
                        else
                          false)) false a.reachingdefspecs) then
               let _ =
                 log_result
                   ~msg:("iaddr: " ^ iaddr)
                   ~tag:"filter out reaching def"
                   __FILE__ __LINE__
                   ["v: " ^ (p2s v#toPretty); "s; " ^ symname] in
               acc
             else
               sym :: acc) [] deflocs in
       List.rev deflocs
    | _ -> deflocs

  method add_inlined_block (baddr:doubleword_int) =
    inlined_blocks <- baddr :: inlined_blocks

  method is_inlined_block (baddr:doubleword_int) =
    List.exists (fun a -> a#equal baddr) inlined_blocks

  method get_inlined_blocks = inlined_blocks

  method has_inlined_blocks =
    match inlined_blocks with [] -> false | _ -> true

  method get_names = names

  method get_function_type = functiontype

  method has_function_type =
    match functiontype with
    | TUnknown _ -> false
    | _ -> true

  method get_function_name =
    if self#has_name then
      let make_name name = demangle name in
      let rec aux thisnames =
        match thisnames with
        | [ name ] -> make_name name
        | name :: tl ->
           let name = make_name name in
           if String.contains name '@' then
             aux tl
           else
             name
        | _ -> raise (BCH_failure (STR "Internal error in get_function_name")) in
      aux names
    else
      raise (BCH_failure
               (LBLOCK [
                    STR "Function at address: ";
                    fa#toPretty;
                    STR " does not have a name"]))

  method has_name = (List.length names) > 0

  method is_non_returning = non_returning

  method is_incomplete = incomplete

  method is_virtual = virtual_function

  method is_user_provided = user_provided

  method is_ida_provided = ida_provided

  method is_inlined = inlined

  method is_library_stub = library_stub

  method has_class_info =
    match classinfo with Some _ -> true | _ -> false

  method to_rep_record =
    let args = [] in
    let tags = [] in
    let tags = if non_returning then "nr" :: tags else tags in
    let tags = if incomplete then "nc" :: tags else tags in
    let tags = if ida_provided then "ida" :: tags else tags in
    let tags = if user_provided then "u" :: tags else tags in
    let tags = if virtual_function then "v" :: tags else tags in
    let tags = if self#has_class_info then "c" :: tags else tags in
    let tags = if library_stub then "l" :: tags else tags in
    let tags = if by_preamble then "pre" :: tags else tags in
    let tags = if self#is_inlined then "inlined" :: tags else tags in
    let args =
      match classinfo with
      | Some (cname,isstatic) ->
         args @ [ bd#index_string cname ; (if isstatic then 1 else 0) ]
      | _ -> args in
    let args = args @ (List.map bd#index_string self#get_names) in
    (tags,args)

end


class functions_data_t:functions_data_int =
object (self)

  val table = H.create 5
  val nametable = H.create 5

  method reset =
    begin
      H.clear table;
      H.clear nametable
    end

  method add_function (fa:doubleword_int): function_data_int =
    let ix = fa#index in
    if H.mem table ix then
      H.find table ix
    else
      let fe = new function_data_t fa in
      begin
        H.add table ix fe;
        fe
      end

  method remove_function (fa: doubleword_int) =
    H.remove table fa#index

  method get_function (fa: doubleword_int): function_data_int =
    if self#is_function_entry_point fa then
      H.find table fa#index
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Function data not found for address: "; fa#toPretty]))

  method has_function (fa: doubleword_int) =
    self#is_function_entry_point fa

  method get_functions: function_data_int list =
    H.fold (fun _ v a -> v::a) table []

  method get_inlined_function_entry_points: doubleword_int list =
    self#retrieve_addresses (fun f -> f#is_inlined)

  method get_function_entry_points: doubleword_int list =
    let inlinedfns = self#get_inlined_function_entry_points in
    let otherfns = self#retrieve_addresses (fun f -> not f#is_inlined) in
    (* List inlined functions before other functions, so they are guaranteed
       to have been constructed before the functions that inline them are
       being constructed.*)
    inlinedfns @ otherfns

  method get_library_stubs: doubleword_int list =
    self#retrieve_addresses (fun f -> f#is_library_stub)

  method is_in_function_stub ?(size=3) (va: doubleword_int): bool =
    let libstubs = self#get_library_stubs in
    List.exists (fun s -> s#le va && va#lt(s#add_int (size * 4))) libstubs

  method is_function_entry_point (fa:doubleword_int) = H.mem table fa#index

  method has_function_name (fa:doubleword_int) =
    (H.mem table fa#index)
    && (H.find table fa#index)#has_name

  method private initialize_nametable =
    H.iter (fun k v ->
        if v#has_name then H.add nametable (List.hd v#get_names) k) table

  method has_function_by_name (name: string): doubleword_int option =
    let _ =
      if (H.length nametable) = 0 then
        self#initialize_nametable in
    if H.mem nametable name then
      log_tfold_default
        (mk_tracelog_spec ~tag:"has_function_by_name" name)
        (fun dw -> Some dw)
        None
        (index_to_doubleword (H.find nametable name))
    else
      None

  method private retrieve (f:function_data_int -> bool) =
    H.fold (fun _ v a -> if f v then v::a else a) table []

  method private retrieve_addresses (f:function_data_int -> bool) =
    H.fold (fun ix v a ->
        if f v then
          TR.tfold_default
            (fun r -> r::a)
            a
            (index_to_doubleword ix)
        else
          a) table []

  method private count (f:function_data_int -> bool) =
    H.fold (fun _ v a -> if f v then a+1 else a) table 0

  method get_ida_provided_functions =
    self#retrieve (fun fd -> fd#is_ida_provided)

  method get_ida_provided_function_entry_points =
    self#retrieve_addresses (fun fd -> fd#is_ida_provided)

  method get_user_provided_count =
    self#count (fun fd -> fd#is_user_provided)

  method get_ida_provided_count =
    self#count (fun fd -> fd#is_ida_provided)

  method write_xml (node:xml_element_int) =
    let recordtable = mk_num_record_table "function-entries" in
    begin
      H.iter (fun ix e -> recordtable#add ix e#to_rep_record) table ;
      recordtable#write_xml node
    end

  method read_xml (node:xml_element_int) =
    let recordtable = mk_num_record_table "function-entries" in
    begin
      recordtable#read_xml node ;
      List.iter (fun (ix, (tags, args)) ->
          let fa = TR.tget_ok (index_to_doubleword ix) in
          let fe = self#add_function fa in
          let a = a "function-data" args in
          let setnames l = List.iter (fun i -> fe#add_name (bd#get_string i)) l in
          begin
            (if List.mem "nr" tags then fe#set_non_returning);
            (if List.mem "nc" tags then fe#set_incomplete);
            (if List.mem "ida" tags then fe#set_ida_provided);
            (if List.mem "pre" tags then fe#set_by_preamble);
            (if List.mem "u" tags then fe#set_user_provided);
            (if List.mem "v" tags then fe#set_virtual);
            (if List.mem "l" tags then fe#set_library_stub);
            (if List.mem "inlined" tags then fe#set_inlined);
            (if List.mem "c" tags then
               let classname = bd#get_string (a 0) in
               let isstatic = (a 1) = 1 in
               begin
                 fe#set_class_info ~classname ~isstatic ;
                 setnames (get_list_suffix args 2)
               end
             else
               setnames args)
          end) recordtable#items
    end

end


let functions_data = new functions_data_t


let read_xml_regvar_intro (node: xml_element_int): regvar_intro_t traceresult =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  if not (has "name") then
    Error ["register var intro without name"]
  else if not (has "iaddr") then
    Error ["register var intro without instruction address"]
  else
    TR.tbind
      ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
      (fun dw ->
        let rvi_iaddr = dw in
        let rvi_name = get "name" in
        let (rvi_vartype, rvi_cast) =
          if has "typename" then
            let iscast = (has "cast") && ((get "cast") = "yes") in
            let typename = get "typename" in
            TR.tfold
              ~ok:(fun btype ->
                if has "ptrto" && (get "ptrto") = "yes" then
                  (Some (t_ptrto btype), iscast)
                else
                  (Some btype, iscast))
              ~error:(fun e ->
                begin
                  log_error_result __FILE__ __LINE__ e;
                  (None, false)
                end)
              (convert_string_to_type typename)
          else
            (None, false) in
        Ok {rvi_iaddr = rvi_iaddr;
            rvi_name = rvi_name;
            rvi_cast = rvi_cast;
            rvi_vartype = rvi_vartype})
      (string_to_doubleword (get "iaddr"))


let read_xml_stackvar_intro (node: xml_element_int): stackvar_intro_t traceresult =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  if not (has "offset") then
    Error ["stackvar intro without offset"]
  else if not (has "name") then
    Error ["stackvar intro without name"]
  else
    let svi_offset = (-(geti "offset")) in
    let svi_name = get "name" in
    let svi_loopcounter = has "loopcounter" && (get "loopcounter") = "yes" in
    let (svi_vartype, svi_cast) =
      if has "typename" then
        let typename = get "typename" in
        let iscast = (has "cast") && ((get "cast") = "yes") in
        TR.tfold
          ~ok:(fun btype ->
            if has "ptrto" && (get "ptrto") = "yes" then
              (Some (t_ptrto btype), iscast)
            else if has "arraysize" then
              let arraysize = geti "arraysize" in
              (Some (t_array btype arraysize), iscast)
            else
              (Some btype, iscast))
          ~error:(fun e ->
            begin
              log_error_result __FILE__ __LINE__ e;
              (None, false)
            end)
          (convert_string_to_type typename)
      else
        (None, false) in
    Ok {svi_offset = svi_offset;
        svi_name = svi_name;
        svi_loopcounter = svi_loopcounter;
        svi_vartype = svi_vartype;
        svi_cast = svi_cast}


let read_xml_typing_rule (node: xml_element_int): typing_rule_t traceresult =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  if not (has "name") then
    Error ["typingrule without name"]
  else if not (has "locs") then
    Error ["typingrule without location"]
  else if not (has "action") then
    Error ["typingrule without action"]
  else
    let name = get "name" in
    let action = get "action" in
    let locs = get "locs" in
    let locs = String.split_on_char ',' locs in
    Ok {tra_name = name;
        tra_action = action;
        tra_locations = locs}


let read_xml_reachingdef_spec
      (node: xml_element_int): reachingdef_spec_t traceresult =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  if not (has "var") then
    Error ["rdefspec without var"]
  else if not (has "uselocs") then
    Error ["rdefspec without uselocs"]
  else if not (has "rdeflocs") then
    Error ["rdefspec without rdeflocs"]
  else
    let var = get "var" in
    let uselocs = get "uselocs" in
    let uselocs = String.split_on_char ','  uselocs in
    let rdeflocs = get "rdeflocs" in
    let rdeflocs = String.split_on_char ',' rdeflocs in
    Ok {rds_variable = var;
        rds_uselocs = uselocs;
        rds_rdeflocs = rdeflocs
      }


let read_xml_stackvarintros (node: xml_element_int): stackvar_intro_t list =
  List.fold_left
    (fun acc n ->
      TR.tfold
        ~ok:(fun svi -> svi :: acc)
        ~error:(fun e ->
          begin
            log_error_result __FILE__ __LINE__ e;
            acc
          end)
        (read_xml_stackvar_intro n))
    []
    (node#getTaggedChildren "vintro")


let read_xml_regvarintros (node: xml_element_int): regvar_intro_t list =
  List.fold_left
    (fun acc n ->
      TR.tfold
        ~ok:(fun rvi -> rvi :: acc)
        ~error:(fun e ->
          begin
            log_error_result __FILE__ __LINE__ e;
            acc
          end)
        (read_xml_regvar_intro n))
    []
    (node#getTaggedChildren "vintro")


let read_xml_typingrules (node: xml_element_int): typing_rule_t list =
  List.fold_left
    (fun acc n ->
      TR.tfold
        ~ok:(fun tr -> tr :: acc)
        ~error:(fun e ->
          begin
            log_error_result __FILE__ __LINE__ e;
            acc
          end)
        (read_xml_typing_rule n))
    []
    (node#getTaggedChildren "typingrule")


let read_xml_removerdefs (node: xml_element_int): reachingdef_spec_t list =
  List.fold_left
    (fun acc n ->
      TR.tfold
        ~ok:(fun rds -> rds :: acc)
        ~error:(fun e ->
          begin
            log_error_result __FILE__ __LINE__ e;
            acc
          end)
        (read_xml_reachingdef_spec n))
    []
    (node#getTaggedChildren "remove-var-rdefs")


let read_xml_function_annotation (node: xml_element_int) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let faddr = get "faddr" in
  TR.titer
    ~ok:(fun dw ->
      let fndata =
        if functions_data#has_function dw then
          functions_data#get_function dw
        else
          functions_data#add_function dw in
      let stackvintros =
        if hasc "stackvar-intros" then
          read_xml_stackvarintros (getc "stackvar-intros")
        else
          [] in
      let regvintros =
        if hasc "regvar-intros" then
          read_xml_regvarintros (getc "regvar-intros")
        else
          [] in
      let typingrules =
        if hasc "typing-rules" then
          read_xml_typingrules (getc "typing-rules")
        else
          [] in
      let rdefspecs =
        if hasc "remove-rdefs" then
          read_xml_removerdefs (getc "remove-rdefs")
        else
          [] in
      let constglobals =
        if hasc "const-global-variables" then
          let gnode = getc "const-global-variables" in
          List.map
            (fun n -> n#getAttribute "name") (gnode#getTaggedChildren "gvar")
        else
          [] in
      fndata#set_function_annotation
        {regvarintros = regvintros;
         stackvarintros = stackvintros;
         typingrules = typingrules;
         reachingdefspecs = rdefspecs;
         constglobalvars = constglobals
        })
    ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
    (string_to_doubleword faddr)


let read_xml_function_annotations (node: xml_element_int) =
  List.iter
    read_xml_function_annotation (node#getTaggedChildren "function-annotation")
