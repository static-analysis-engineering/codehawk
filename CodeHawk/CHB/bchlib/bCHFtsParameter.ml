(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHFormatStringParser
open CHLogger
open CHTraceResult
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeTransformer
open BCHBCTypeUtil
open BCHBCTypeXml
open BCHCPURegisters
open BCHDoubleword
open BCHLibTypes
open BCHUtilities


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


let xfail_tvalue
      (node: xml_element_int) (msg: pretty_t) (r: 'a traceresult): 'a =
  match r with
  | Ok v -> v
  | Error e ->
     let msg = LBLOCK [msg; STR " ("; STR (String.concat "; " e); STR ")"] in
     raise_xml_error node msg

(* ----------------------------------------------------------------- printing *)

let calling_convention_to_string =
  function StdCall -> "stdcall" | CDecl -> "cdecl"


let _arg_io_to_string (i:arg_io_t) =
  match i with
  | ArgRead -> "r"
  | ArgWrite -> "w"
  | ArgReadWrite -> "rw"


let _formatstring_type_to_string (t:formatstring_type_t) =
  match t with
  | NoFormat -> "no"
  | PrintFormat -> "print"
  | ScanFormat -> "scan"


let pld_position_to_string (p: pld_position_t) =
  let stri = string_of_int in
  match p with
  | FieldPosition (ckey, foffset, fname) ->
     "F:" ^ (stri ckey) ^ ":" ^ (stri foffset) ^ ":" ^ fname
  | ArrayPosition index -> "A:" ^ (stri index)


let parameter_location_detail_to_string (d: parameter_location_detail_t) =
  let si = string_of_int in
  let p_extract (x: (int * int) option) =
    match x with
    | Some (start, size) -> "size[" ^ (si start) ^ ", " ^ (si size) ^ "]"
    | _ -> "" in
  let p_btype (t: btype_t) =
    match t with
    | TUnknown _ -> ""
    | _ -> ":" ^ (btype_to_string t) in
  let p_pos (l: pld_position_t list) =
    match l with
    | [] -> ""
    | _ ->
       ":[" ^ (String.concat ", " (List.map pld_position_to_string l)) ^ "]" in
  "("
  ^ si d.pld_size
  ^ (p_btype d.pld_type)
  ^ (p_extract d.pld_extract) ^ ")"
  ^ (p_pos d.pld_position)


let parameter_location_to_string (loc: parameter_location_t) =
  let ds = parameter_location_detail_to_string in
  match loc with
  | StackParameter (i, d) -> "s_arg " ^ (string_of_int i) ^ " " ^ (ds d)
  | RegisterParameter (r, d) -> "r_arg " ^ (register_to_string r) ^ " " ^ (ds d)
  | GlobalParameter (g, d) -> "g_arg " ^ g#to_hex_string ^ " " ^ (ds d)
  | UnknownParameterLocation d -> "unknown " ^ (ds d)


let fts_parameter_to_pretty (p: fts_parameter_t) =
  let ploc loc =
    match loc with
    | [l] -> parameter_location_to_string l
    | _ -> "[" ^ String.concat "; " (List.map parameter_location_to_string loc) in
  LBLOCK [
      STR (ploc p.apar_location);
      STR " ";
      STR p.apar_name;
      STR ": ";
      btype_to_pretty p.apar_type]


let fts_parameter_to_string (p: fts_parameter_t) =
  let ploc loc =
    ":[" ^ String.concat "; " (List.map parameter_location_to_string loc) in
  (btype_to_string p.apar_type)
    ^ " "
    ^ p.apar_name
    ^ (ploc p.apar_location)


(* ---------------------------------------------------------------- accessors *)

let get_parameter_signature (p: fts_parameter_t): (string * btype_t) =
  (p.apar_name, p.apar_type)


let get_parameter_type (p: fts_parameter_t): btype_t = p.apar_type


let get_parameter_name (p: fts_parameter_t): string = p.apar_name


let get_stack_parameter_offset (p: fts_parameter_t): int traceresult =
  match p.apar_location with
  | [StackParameter (i, _)] -> Ok i
  | [loc] ->
     Error [
         "get_stack_parameter_offset with location: "
         ^ (parameter_location_to_string loc)]
  | _::_ -> Error ["get_stack_parameter_offset:multiple locations"]
  | [] -> Error ["get_stack_parameter_offset:no locations"]


let get_register_parameter_register
      (p: fts_parameter_t): register_t traceresult =
  match p.apar_location with
  | [RegisterParameter (reg, _)] -> Ok reg
  | [loc] ->
     Error [
         "get_register_parameter_register with location: "
         ^ (parameter_location_to_string loc)]
  | _::_ -> Error ["get_register_parameter_register:multiple locations"]
  | [] -> Error ["get_register_parameter_register:no locations"]



(* --------------------------------------------------------------- comparison *)

let pld_pos_compare (pos1: pld_position_t) (pos2: pld_position_t) =
  match (pos1, pos2) with
  | FieldPosition (ckey1, foffset1, _), FieldPosition (ckey2, foffset2, _) ->
     Stdlib.compare (ckey1, foffset1) (ckey2, foffset2)
  | (FieldPosition _, _) -> -1
  | (_, FieldPosition _) -> 1
  | (ArrayPosition i1, ArrayPosition i2) -> Stdlib.compare i1 i2


let pld_compare
      (pld1: parameter_location_detail_t) (pld2: parameter_location_detail_t) =
  let compare_extract (p1: (int * int) option) (p2: (int * int) option): int =
    match (p1, p2) with
    | (None, None) -> 0
    | (None, _) -> -1
    | (_, None) -> 1
    | (Some (o1, _), Some (o2, _)) -> Stdlib.compare o1 o2 in
  let compare_pos (p1: pld_position_t list) (p2: pld_position_t list) =
    list_compare p1 p2 pld_pos_compare in
  let l1 = compare_extract pld1.pld_extract pld2.pld_extract in
  if l1 = 0 then
    compare_pos pld1.pld_position pld2.pld_position
  else
    l1


let pld_equal
      (pld1: parameter_location_detail_t) (pld2: parameter_location_detail_t) =
  (pld_compare pld1 pld2) = 0


let parameter_location_compare l1 l2 =
  match (l1,l2) with
  | (RegisterParameter (r1, pld1), RegisterParameter (r2, pld2)) ->
     let l1 = register_compare r1 r2 in
     if l1 = 0 then
       pld_compare pld1 pld2
     else
       l1
  | (RegisterParameter _, _) -> -1
  | (_, RegisterParameter _) -> 1
  | (StackParameter (i1, _), StackParameter (i2, _)) -> Stdlib.compare i1 i2
  | (StackParameter _, _) -> -1
  | (_, StackParameter _) -> 1
  | (GlobalParameter (dw1, _), GlobalParameter (dw2, _)) -> dw1#compare dw2
  | (GlobalParameter _, _) -> -1
  | (_, GlobalParameter _) -> 1
  | (UnknownParameterLocation _ , UnknownParameterLocation _) -> 0


let parameter_location_equal
      (l1: parameter_location_t) (l2: parameter_location_t) =
  (parameter_location_compare l1 l2) = 0


let fts_parameter_compare (p1: fts_parameter_t) (p2: fts_parameter_t) =
  list_compare p1.apar_location p2.apar_location parameter_location_compare


let fts_parameter_equal (p1: fts_parameter_t) (p2: fts_parameter_t) =
  (fts_parameter_compare p1 p2) = 0


let read_xml_arg_io (s:string): arg_io_t traceresult =
  match s with
  | "r" -> Ok ArgRead
  | "w" -> Ok ArgWrite
  | "rw" -> Ok ArgReadWrite
  | _ -> Error ["Arg io: " ^ s ^ " not recognized"]


let read_xml_formatstring_type (s:string): formatstring_type_t traceresult =
  match s with
  | "no" -> Ok NoFormat
  | "print" -> Ok PrintFormat
  | "scan" -> Ok ScanFormat
  | _ -> Error ["Formatstring type: " ^ s ^ " not recognized"]


let read_xml_roles (node:xml_element_int) =
  List.map (fun n ->
      let get = n#getAttribute in
      (get "rt", get "rn")) (node#getTaggedChildren "role")


let default_parameter_location_detail ?(ty=t_unknown) (size: int) = {
    pld_type = ty;
    pld_size = size;
    pld_extract = None;
    pld_position = []
  }

let read_xml_parameter_location
      (node:xml_element_int) (btype: btype_t): parameter_location_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let pdef = default_parameter_location_detail ~ty:btype 4 in
  let getx s =
    xfail_tvalue
      node
      (STR ("read_xml_parameter_location: " ^ s))
      (string_to_doubleword s) in
  match get "loc" with
  | "stack" -> StackParameter (geti "nr", pdef)
  | "register" -> RegisterParameter (register_from_string (get "reg"), pdef)
  | "global" -> GlobalParameter (getx (get "dw"), pdef)
  | "unknown" -> UnknownParameterLocation pdef
  | s ->
     raise_xml_error
       node
       (LBLOCK [STR "Parameter location not recognized: "; STR s])


(* Api parameters are numbered with two attributes:
   - nr : stack position (times 4, starting at 1)
   - ix : argument index number
   If ix is missing, it is assumed that the ix is the same as nr
*)
let read_xml_fts_parameter (node:xml_element_int): fts_parameter_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let hasc = node#hasOneTaggedChild in
  let tNode = if hasc "type" then getc "type" else getc "btype" in
  let btype = read_xml_type tNode in
  let get_arg_io s =
    xfail_tvalue
      node (STR ("read_xml_fts_parameter: " ^ s)) (read_xml_arg_io s) in
  let get_fmt s =
    xfail_tvalue
      node
      (STR ("read_xml_fts_parameter: " ^ s))
      (read_xml_formatstring_type s) in
  { apar_index =
      (if has "ix" then
         Some (geti "ix")
       else if has "nr" then
         Some (geti "nr")
       else
         None);
    apar_name = get "name";
    apar_desc = (if has "desc" then get "desc" else "");
    apar_roles = (if hasc "roles" then read_xml_roles (getc "roles") else []);
    apar_io = (if has "io" then get_arg_io (get "io") else ArgReadWrite);
    apar_size = (if has "size" then geti "size" else 4);
    apar_type = btype;
    apar_location = [read_xml_parameter_location node btype];
    apar_fmt = (if has "fmt" then get_fmt (get "fmt") else NoFormat)
  }

(* --------------------------------------------------------------- predicates *)

let is_global_parameter (p: fts_parameter_t) =
  match p.apar_location with [GlobalParameter _] -> true | _ -> false


let is_stack_parameter (p: fts_parameter_t) =
  match p.apar_location with [StackParameter _] -> true | _ -> false


let is_stack_parameter_at_offset (p: fts_parameter_t) (n: int): bool =
  match p.apar_location with
  | [StackParameter (i, _)] -> i = n
  | _ -> false


let is_register_parameter (p: fts_parameter_t) =
  match p.apar_location with [RegisterParameter _] -> true | _ -> false


let is_register_parameter_for_register (p: fts_parameter_t) (reg: register_t) =
  match p.apar_location with
  | [RegisterParameter (r, _)] -> register_equal reg r
  | _ -> false


let is_arg_parameter (p: fts_parameter_t) =
  is_register_parameter p || is_stack_parameter p


let is_formatstring_parameter (p: fts_parameter_t) =
  match p.apar_fmt with
  | NoFormat -> false
  | _ -> true


let is_floating_point_parameter (p: fts_parameter_t) =
  match p.apar_type with
  | TFloat _ -> true
  | _ -> false

(* ---------------------------------------------------------------- operators *)

let default_fts_parameter = {
    apar_index = None;
    apar_name = "unnknown-fts-parameter" ;
    apar_type = t_unknown ;
    apar_roles = [] ;
    apar_desc = "" ;
    apar_io = ArgReadWrite;
    apar_size = 4;
    apar_location =
      [UnknownParameterLocation (default_parameter_location_detail 4)];
    apar_fmt = NoFormat
}


let modify_types_par (f:type_transformer_t) (p: fts_parameter_t) =
  { p with apar_type = modify_type f p.apar_type }


let modify_name_par (name:string) (p: fts_parameter_t) =
  { p with apar_name = name }


let mk_field_position (ckey: int) (offset: int) (name: string): pld_position_t =
  FieldPosition (ckey, offset, name)


let mk_array_position (index: int) = ArrayPosition index


let mk_global_parameter
      ?(btype=t_unknown)
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      ?(fmt=NoFormat)
      (gaddr:doubleword_int) =
  let locdetail = default_parameter_location_detail ~ty:btype size in
  { apar_index = None;
    apar_name = "gv_" ^ gaddr#to_hex_string;
    apar_type = btype;
    apar_desc = desc;
    apar_roles = roles;
    apar_io = io;
    apar_size = size;
    apar_location = [GlobalParameter (gaddr, locdetail)];
    apar_fmt = fmt
  }


let mk_stack_parameter_location
      ?(btype=t_unknown)
      ?(size=4)
      ?(extract=None)
      (offset: int): parameter_location_t =
  let locdetail = default_parameter_location_detail ~ty:btype size in
  StackParameter (offset, locdetail)


(* index starts at 1 (re: counting) *)
let mk_indexed_stack_parameter
      ?(btype=t_unknown)
      ?(name="")
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      ?(fmt=NoFormat)
      ?(locations=[])
      (offset: int)
      (index: int) =
  let locations =
    match locations with
    | [] ->
       (* create a single stack location at the given offset *)
       [mk_stack_parameter_location ~btype ~size offset]
    | _ -> locations in
  { apar_index = Some index;
    apar_name = if name = "" then "arg_" ^ (string_of_int index) else name;
    apar_type = btype;
    apar_desc = desc;
    apar_roles = roles;
    apar_io = io;
    apar_size = size;
    apar_fmt = fmt;
    apar_location = locations
  }


let mk_register_parameter
      ?(name="")
      ?(btype=t_unknown)
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      ?(fmt=NoFormat)
      (reg:register_t) =
  let locdetail = default_parameter_location_detail ~ty:btype size in
  { apar_index = None;
    apar_name =
      if name = "" then "reg_" ^ (register_to_string reg) else name;
    apar_type = btype;
    apar_desc = desc;
    apar_roles = roles;
    apar_io = io;
    apar_size = size;
    apar_fmt = fmt;
    apar_location = [RegisterParameter (reg, locdetail)]
  }


let mk_register_parameter_location
      ?(btype=t_unknown)
      ?(size=4)
      ?(extract=None)
      ?(position=[])
      (reg: register_t): parameter_location_t =
  let locdetail =
    {pld_type = btype;
     pld_size = size;
     pld_extract = extract;
     pld_position = position} in
  RegisterParameter (reg, locdetail)


let mk_indexed_register_parameter
      ?(btype=t_unknown)
      ?(name="")
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      ?(fmt=NoFormat)
      ?(locations=[])
      (reg:register_t)
      (index: int) =
  let locations =
    match locations with
    | [] ->
       (* create a single register location for the given register *)
       [mk_register_parameter_location ~btype ~size reg]
    | _ -> locations in
  { apar_index = Some index;
    apar_name = if name = "" then "arg_" ^ (string_of_int index) else name;
    apar_type = btype;
    apar_desc = desc;
    apar_roles = roles;
    apar_io = io;
    apar_size = size;
    apar_fmt = fmt;
    apar_location = locations
  }


let mk_indexed_multiple_locations_parameter
      ?(btype=t_unknown)
      ?(name="")
      ?(desc="")
      ?(roles=[])
      ?(io=ArgRead)
      ?(size=4)
      (locations: parameter_location_t list)
      (index: int) =
  { apar_index = Some index;
    apar_name = if name = "" then "arg_" ^ (string_of_int index) else name;
    apar_type = btype;
    apar_desc = desc;
    apar_roles = roles;
    apar_io = io;
    apar_size = size;
    apar_fmt = NoFormat;
    apar_location = locations
  }


(* -------------------------------------------------------- format arguments *)

let get_fmt_spec_type (spec:argspec_int):btype_t =
  let conversion = spec#get_conversion in
  match conversion with
  | IntConverter | DecimalConverter ->
     if spec#has_lengthmodifier then
       let ikind = match spec#get_lengthmodifier with
         | NoModifier -> IInt
         | CharModifier -> IChar
         | ShortModifier -> IShort
         | LongModifier -> ILong
         | LongLongModifier -> ILongLong
         | IntMaxModifier -> ILong
         | SizeModifier -> IULong
         | PtrDiffModifier -> IULong
         | LongDoubleModifier -> ILong in
       TInt (ikind,[])
     else
       TInt (IInt,[])
  | UnsignedOctalConverter | UnsignedDecimalConverter | UnsignedHexConverter _ ->
     if spec#has_lengthmodifier then
       let ikind = match spec#get_lengthmodifier with
         | NoModifier -> IUInt
         | CharModifier -> IUChar
         | ShortModifier -> IUShort
         | LongModifier -> IULong
         | LongLongModifier -> IULongLong
         | IntMaxModifier -> IULong
         | SizeModifier -> IULong
         | PtrDiffModifier -> IULong
         | LongDoubleModifier -> IULong in
       TInt (ikind,[])
     else
       TInt (IUInt,[])
  | FixedDoubleConverter _
    | ExpDoubleConverter _
    | FlexDoubleConverter _
    | HexDoubleConverter _ ->
     if spec#has_lengthmodifier then
       let fkind = match spec#get_lengthmodifier with
         | LongDoubleModifier -> FLongDouble
         | _ -> FDouble in
       TFloat (fkind, FScalar,[])
     else
       TFloat (FDouble, FScalar,[])
  | UnsignedCharConverter -> TInt (IUChar,[])
  | StringConverter -> TPtr (TInt (IChar, []),[])
  | PointerConverter -> TPtr (TVoid [],[])
  | OutputArgument -> TPtr (TInt (IInt, []),[])


(* Convert a format string specification to an api_parameter *)
let convert_fmt_spec_arg
      (index:int)         (* index of argument, zero-based *)
      (spec:argspec_int): fts_parameter_t =
  let ftype = get_fmt_spec_type spec in
  let locdetail = default_parameter_location_detail ~ty:ftype 4 in
  { apar_index = Some (index + 1);
    apar_name = "vararg_" ^ (string_of_int index);
    apar_type = ftype;
    apar_desc = "vararg";
    apar_roles = [];
    apar_io =
      (match spec#get_conversion with
      | OutputArgument -> ArgWrite
      | _ -> ArgRead);
    apar_fmt = NoFormat;
    apar_size = 4;
    apar_location = [StackParameter (index + 1, locdetail) ]
  }
