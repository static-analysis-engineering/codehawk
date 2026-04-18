(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2026 Aarno Labs LLC

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
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHBCSumTypeSerializer
open BCHBCTypes
open BCHBCTypeUtil

module H = Hashtbl


let raise_error (node: xml_element_int) (msg: pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


let ch_named_struct_types = [
    "ch__addrinfo";
    "ch__DIR";
    "ch__dirent";
    "ch__fd_set";    (* used in select *)
    "ch__FILE";
    "ch__fpos_t";    (* this may or may not be a struct, depending on arch *)
    "ch__group";     (* used in getgrgid *)
    "ch__hostent";
    "ch__in_addr";
    "ch__iovec";     (* used in writev *)
    "ch__msghdr";    (* used in recvmsg, sendmsg *)
    "ch__netent";
    "ch__passwd";    (* used in getpwnam *)
    "ch__pollfd";
    "ch__pthread_attr_t";
    "ch__pthread_cond_t";
    "ch__pthread_mutex_t";
    "ch__pthread_mutexattr_t";
    "ch__pthread_start_routine";
    "ch__pthread_t";
    "ch__rlimit";    (* used in getrlimit *)
    "ch__rusage";    (* used in getrusage *)
    "ch__sigaction"; (* used in sigaction *)
    "ch__sigset_t";  (* used in sigaddset *)
    "ch__sockaddr";
    "ch__spwd";      (* used in getspname *)
    "ch__stat";
    "ch__statfs";
    "ch__sysinfo";
    "ch__termios";   (* used in tcgetattr *)
    "ch__timespec";  (* used in nanosleep *)
    "ch__timeval";
    "ch__timezone";
    "ch__tm"
  ]

let register_ch_named_struct_types () =
  List.iter BCHBCFiles.bcfiles#add_ch_named_struct_type ch_named_struct_types


(* Convert some standard type names as used in the legacy summaries to
   btype enumerations*)
let get_standard_txt_type (t: string): btype_t option =
  match t with
  | "__uClibc_main_fptr" ->
     Some (TPtr (TFun (TInt (IInt, []),
                       Some [("argc", TInt (IInt, []), []);
                             ("argv", TPtr (TPtr (TInt (IUChar, []), []),  []), [])],
                             false, []), []))
  | "atexit_fptr" -> Some (TPtr (TFun (TVoid [], Some [], false, []), []))
  | "BOOL" -> Some (TInt (IBool, []))
  | "Boolean" -> Some (TInt (IBool, []))
  | "BSTR" -> Some (TPtr (TInt (IWChar, []), []))
  | "byte" -> Some (TInt (IUChar, []))
  | "BYTE" -> Some (TInt (IUChar, []))
  | "char" -> Some (TInt (IChar, []))
  | "clock_t" -> Some (TInt (IInt, []))
  | "comparison_fptr" ->                       (* used in bsearch *)
     Some (TFun (TInt (IInt, []),
                 Some [("x1", TPtr (TVoid [], []), []);
                       ("x2", TPtr (TVoid [], []), [])],
                 false, []))
  | "dir_select_fptr" ->
     Some (TFun (TInt (IInt, []),
                       Some [("direntry", TPtr (TNamed ("ch__dirent", []), []), [])],
                              false, []))
  | "float" -> Some (TFloat (FFloat, FScalar, []))
  | "double" -> Some (TFloat (FDouble, FScalar, []))
  | "DWORD" -> Some (TInt (IUInt, []))
  | "gid_t" -> Some (TInt (IUInt, []))
  | "id_t" -> Some (TInt (IUInt, []))     (* used in getpriority *)
  | "in_addr_t" ->
     (* equivalent to the type uint32_t, see
        https://pubs.opengroup.org/onlinepubs/9699919799/ *)
     Some (TInt (IUInt, []))
  | "int" -> Some (TInt (IInt, []))
  | "Integer" -> Some (TInt (IInt, []))
  | "long" -> Some (TInt (ILong, []))
  | "LONG" -> Some (TInt (ILong, []))
  | "long_long" -> Some (TInt (ILongLong, []))
  | "long long" -> Some (TInt (ILongLong, []))
  | "mode_t" -> Some (TInt (IInt, []))    (* used in chmod *)
  | "nfds_t" -> Some (TInt (IUInt, []))   (* used in poll *)
  | "off_t" -> Some (TInt (IULong, []))
  | "OLECHAR" -> Some (TInt (IWChar, []))
  | "pid_t" -> Some (TInt (IUInt, []))
  | "pthread_start_routine" ->
     Some (TPtr (TFun (TVoid [], Some [], false, []), []))
  | "sem_t" -> Some (TInt (IInt, []))     (* used in semaphore functions *)
  | "size_t" -> Some (TInt (IUInt, []))
  | "SIZE_T" -> Some (TInt (IUInt, []))
  | "socklen_t" -> Some (TInt (IInt, []))  (* may also be unsigned *)
  | "speed_t" -> Some (TInt (IUInt, []))   (* used in cfgetispeed *)
  | "ssize_t" -> Some (TInt (ILong, []))
  | "time_t" -> Some (TInt (ILong, []))
  | "uid_t" -> Some (TInt (IUInt, []))
  | "UINT" -> Some (TInt (IUInt, []))
  | "uint16_t" -> Some (TInt (IUShort, []))
  | "uint32_t" -> Some (TInt (IUInt, []))
  | "u_long" -> Some (TInt (IULong, []))
  | "u_long_long" -> Some (TInt (IULongLong, []))
  | "unknown" -> Some (TUnknown [])
  | "UNKNOWN" -> Some (TUnknown [])
  | "void" -> Some (TVoid ([]))
  | "VOID" -> Some (TVoid ([]))
  | "wchar_t" -> Some (TInt (IWChar, []))
  | _ ->
     if List.mem t ch_named_struct_types then
       begin
         log_result
           ~tag:"get_standard_txt_type:provided by typedef"
           __FILE__ __LINE__
           [t];
         None
       end
     else
       begin
         log_result
           ~tag:"get_standard_txt_type:legacy type not covered"
           __FILE__ __LINE__
           [t];
         None
       end


let read_xml_summary_type (node: xml_element_int): btype_t =
  let rec aux n =
    if n#hasText then
      let txt = n#getText in
      match get_standard_txt_type txt with
      | Some ty -> ty
      | _ -> TNamed (txt, [])
    else
      let nn = n#getChild in
      match nn#getTag with
      | "float" -> t_float
      | "ptr" -> TPtr (aux nn, [])
      | "array" ->
	 let size =
           if nn#hasNamedAttribute "size" then
	     Some
               (Const
                  (CInt (Int64.of_string (nn#getAttribute "size"), IInt, None)))
	  else
	    None in
	TArray (aux nn, size,[])
      | "vararg" -> TVarArg []
      | "struct" -> t_named (nn#getAttribute "name")
      | s ->
	raise_error node
	  (LBLOCK [ STR s ; STR " not recognized as a summary type" ]) in
  aux node


let compinfo_key = ref 10000
let new_compinfo_key () =
  begin
    compinfo_key := !compinfo_key + 1;
    !compinfo_key
  end


let read_xml_summary_fieldinfo
      (ckey: int) (node: xml_element_int) : bfieldinfo_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let geti = node#getIntAttribute in
  let tNode = getc "type" in
  {
    bfckey = ckey;
    bfname = get "name";
    bftype = read_xml_summary_type tNode;
    bfbitfield = None;
    bfattr = [];
    bfloc = {line = 0; file = ""; byte = 0};
    bfieldlayout =
      if has "offset" && has "size" then
        Some (geti "offset", geti "size")
      else
        None
  }


let read_xml_summary_struct (node: xml_element_int): bcompinfo_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let ckey = new_compinfo_key () in
  {
    bcname = get "name";
    bckey = ckey;
    bcstruct = true;
    bcfields =
      List.map
        (read_xml_summary_fieldinfo ckey)
        ((getc "fields")#getTaggedChildren "field");
    bcattr = []
  }


let read_xml_restricted_btype (node: xml_element_int): btype_t =
  let get = node#getAttribute in
  match get "ttag" with
  | "tvoid" -> TVoid []
  | "tint" -> TInt (ikind_mfts#fs (get "ikind"), [])
  | "tnamed" -> TNamed (get "tname", [])
  | s -> raise_error node (LBLOCK [STR s; STR " no recognized as type tag"])


let read_xml_type (node: xml_element_int) =
  if node#getTag = "btype" || node#getTag = "typ" then
    read_xml_restricted_btype node
  else
    read_xml_summary_type node


and read_xml_returntype (node: xml_element_int) =
  if node#getTag = "returnbtype" then
    read_xml_restricted_btype node
  else
    read_xml_summary_type node


let get_standard_char_type_replacements (char_type: string) =
  if char_type = "ansi" || char_type = "A" then
    [ ("LPCTSTR", "LPCSTR");
      ("LPTSTR", "LPSTR");
      ("TCHAR", "char")]
  else if char_type = "unicode" || char_type = "W" then
    [ ("LPCTSTR", "LPCWSTR");
      ("LPTSTR", "LPWSTR");
      ("TCHAR", "wchar_t")]
  else
    raise (BCH_failure
             (LBLOCK [
                  STR char_type;
		  STR " is not a valid ansi/unicode designation. ";
		  STR "Use A/W or ansi/unicode"]))


let read_xml_type_transformer (node: xml_element_int) =
  let get = node#getAttribute in
  let getcc = node#getTaggedChildren in
  let has = node#hasNamedAttribute in
  let replacements = List.map (fun n ->
    let get = n#getAttribute in (get "src", get "tgt")) (getcc "replace-type") in
  let replacements = if has "char-type" then
      (get_standard_char_type_replacements (get "char-type")) @ replacements
    else
      replacements in
  let replace s =
    try let (_,t) = List.find (fun (x,_) -> x = s) replacements in t with
      Not_found -> s in
  replace
