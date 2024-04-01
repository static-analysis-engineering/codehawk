(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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
open CHUtils

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHLibTypes


module H = Hashtbl


let bcd = BCHBCDictionary.bcdictionary


let btype_equal (t1: btype_t) (t2: btype_t) =
  let i1 = bcd#index_typ t1 in
  let i2 = bcd#index_typ t2 in
  i1 = i2


class type_definitions_t: type_definitions_int =
object (self)

  (* ~~~ builtin types are loaded by default; they are not saved as part of the
     ~~~ analysis data *)
  val builtin_typeinfos = H.create 3 (* string -> btype_t *)
  val builtin_compinfos = H.create 3 (* string -> btype_t *)
  val builtin_enuminfos = H.create 3 (* string -> btype_t *)

  method add_builtin_typeinfo (name:string) (ty:btype_t) =
    if H.mem builtin_typeinfos name then
      chlog#add "duplicate builtin typeinfo" (STR name)
    else
      H.add builtin_typeinfos name ty

  method add_builtin_compinfo (name:string) (c:bcompinfo_t) =
    if H.mem builtin_compinfos name then
      chlog#add "duplicate builtin compinfo" (STR name)
    else
      H.add builtin_compinfos name c

  method add_builtin_enuminfo (name:string) (e:benuminfo_t) =
    if H.mem builtin_enuminfos name then
      chlog#add "duplicate builtin enuminfo" (STR name)
    else
      H.add builtin_enuminfos name e

  (* ~~~ types that are added from user data or from library function summaries;
     ~~~ they are saved as part of the analysis data. These type names override
     ~~~ the builtin type names.
   *)
  val typeinfos = H.create 3        (* string -> btype_t *)
  val compinfos = H.create 3        (* string -> compinfo_t *)
  val enuminfos = H.create 3        (* string -> enuminfo_t *)

  method add_typeinfo (name:string) (ty:btype_t) =
    if H.mem typeinfos name then
      if btype_equal (H.find typeinfos name) ty then
        ()
      else
	ch_error_log#add
          "type definition"
	  (LBLOCK [
               STR "Ignoring type definition of ";
               STR name;
               STR " to ";
	       STR (btype_to_string ty);
               STR "; keeping previous definition ";
	       STR (btype_to_string (H.find typeinfos name))])
    else
      H.add typeinfos name ty

  method add_compinfo (name:string) (c:bcompinfo_t) =
    if H.mem compinfos name then
      ch_error_log#add
        "compinfo definition"
	(LBLOCK [STR "Ignoring compinfo definition of "; STR name])
    else
      H.add compinfos name c

  method add_enuminfo (name:string) (e:benuminfo_t) =
    if H.mem enuminfos name then
      ch_error_log#add
        "enuminfo definition"
	(LBLOCK [STR "Ignoring enuminfo definition of "; STR name])
    else
      H.add enuminfos name e

  method get_type (name:string): btype_t =
    if H.mem typeinfos name then
      H.find typeinfos name
    else if H.mem builtin_typeinfos name then
      H.find builtin_typeinfos name
    else
      raise
        (BCH_failure
           (LBLOCK [STR "No type definition found for "; STR name]))

  method get_compinfo (name:string): bcompinfo_t =
    if H.mem compinfos name then
      H.find compinfos name
    else if H.mem builtin_compinfos name then
      H.find builtin_compinfos name
    else
      raise (BCH_failure (LBLOCK [STR "No compinfo found for "; STR name]))

  method get_enuminfo (name:string): benuminfo_t =
    if H.mem enuminfos name then
      H.find enuminfos name
    else if H.mem builtin_enuminfos name then
      H.find builtin_enuminfos name
    else
      raise (BCH_failure (LBLOCK [STR "No enuminfo found for "; STR name]))

  (* ~~~ if a request is made for a particular type info (type name), compinfo,
     ~~~ or enuminfo, for which the corresponding type is not found, the name is
     ~~~ logged for information *)
  val no_typeinfos = new StringCollections.set_t  (* missing type infos *)
  val no_compinfos = new StringCollections.set_t  (* missing comp infos *)
  val no_enuminfos = new StringCollections.set_t  (* missing enum infos *)

  method has_type (name:string) =
    (H.mem typeinfos name || H.mem builtin_typeinfos name)
    || (let _ = no_typeinfos#add name in false)

  method has_compinfo (name:string) =
    (H.mem compinfos name || H.mem builtin_compinfos name)
    || (let _ = no_compinfos#add name in false)

  method has_enuminfo (name:string) =
    (H.mem enuminfos name || H.mem builtin_enuminfos name)
    || (let _ = no_enuminfos#add name in false)

  method write_xml (node:xml_element_int) =
    let tinfos = H.fold (fun k v a -> (k,v)::a) typeinfos [] in
    let cinfos = H.fold (fun k v a -> (k,v)::a) compinfos [] in
    let einfos = H.fold (fun k v a -> (k,v)::a) enuminfos [] in
    let tnode = xmlElement "type-infos" in
    let cnode = xmlElement "comp-infos" in
    let enode = xmlElement "enum-infos" in
    begin
      tnode#appendChildren
        (List.map (fun (name, tinfo) ->
             let n = xmlElement "n" in
             begin
               n#setAttribute "n" name;
               bcd#write_xml_typ n tinfo;
               n
             end) tinfos);
      cnode#appendChildren
        (List.map (fun (name, cinfo) ->
             let n = xmlElement "n" in
             begin
               n#setAttribute "n" name;
               bcd#write_xml_compinfo n cinfo;
               n
             end) cinfos);
      enode#appendChildren
        (List.map (fun (name, einfo) ->
             let n = xmlElement "n" in
             begin
               n#setAttribute "n" name;
               bcd#write_xml_enuminfo n einfo;
               n
             end) einfos);
        node#appendChildren [tnode; cnode; enode]
    end

  method read_xml (node:xml_element_int) =
    let getcc t = (node#getTaggedChild t)#getTaggedChildren "n" in
    begin
      List.iter (fun n  ->
          let name = n#getAttribute "n" in
          let tinfo = bcd#read_xml_typ n in
          self#add_typeinfo name tinfo) (getcc "type-infos") ;
      List.iter (fun n ->
          let name = n#getAttribute "n" in
          let cinfo = bcd#read_xml_compinfo n in
          self#add_compinfo name cinfo) (getcc "comp-infos") ;
      List.iter (fun n ->
          let name = n#getAttribute "n" in
          let einfo = bcd#read_xml_enuminfo n in
          self#add_enuminfo name einfo) (getcc "enum-infos")
    end

  method toPretty =
    LBLOCK [
      STR "type definitions  : "; INT (H.length typeinfos); NL;
      STR "struct definitions: "; INT (H.length compinfos); NL;
      STR "enum definitions  : "; INT (H.length enuminfos); NL]

end


let type_definitions = new type_definitions_t


let handle name = THandle (name,[])
let named name = TNamed (name,[])


let pe_types = [
    ("BSTR", TPtr (named "OLECHAR", []));    (* string type in COM framework *)

    ("HANDLER_FUNCTION",
     (* callback function for the RegisterServiceCtrlHandler function *)
     TFun (TVoid [], Some [("fdwControl", named "DWORD", [])], false, []));

    ("HCRYPTHASH", (* handle to a cryptographic hash *)
     handle "CRYPTHASH");

    ("HCRYPTKEY", (* handle to a cryptographic key *)
     handle "CRYPTKEY");

    ("HCRYPTPROV", (* handle to a cryptographic service provider *)
     handle "CRYPTPROV");

    ("DLGPROC", (* dialog window callback procedure *)
     TFun (named "INT_PTR",
	   Some [("hwndDlg", named "HWND", []);
		 ("uMsg", named "UINT", []);
		 ("wParam ", named "WPARAM", []);
		 ("lParam", named "LPARAM", [])], false, []));

    ("DESKTOPENUMPROC",
     TFun (named "BOOL",
	   Some [ ("lpszDesktop", named "LPSTR", []);
		  ("lParam", named "LPARAM", []) ], false, []));

    ("DWORD", TInt (IUInt, []));

    ("EnumObjectsProc",
     TFun (named "int",
	   Some [("lpLogObject", named "LPVOID", []);
		 ("lpData", named "LPARAM", [])], false, []));

    ("EnumCalendarInfoProc",
     TFun (named "BOOL",
	   Some [("lpCalendarInfoString", named "LPTSTR", [])], false, []));

    ("ENUMRESLANGPROC",
     TFun (named "BOOL",
	   Some [("hModule", named "HMODULE", []);
		 ("lpszType", named "LPCTSTR", []);
		 ("lpszName", named "LPCTSTR", []);
		 ("wIDLanguage", named "WORD", []);
		 ("lParam", named "LONG_PTR", [])], false, []));

    ("EnumResNameProc",
     TFun (named "BOOL",
	   Some [("hModule", named "HMODULE", []);
		 ("lpszType", named "LPCTSTR", []);
		 ("lpszName", named "LPTSTR", []);
		 ("lParam", named "LONG_PTR", [])], false, []));

    ("EnumResTypeProc",
     TFun (named "BOOL",
	   Some [("hModule", named "HMODULE", []);
		 ("lpszType", named "LPSTR", []);
		 ("lParam", named "LONG_PTR", [])], false, []));

    ("FARPROC" , (* call back function *)
     TFun (TInt (IInt,[]), Some [], false,[]));

    ("FONTENUMPROC",  (* call back function to enumerating fonts *)
     TFun (named "int",
	   Some [("lpelfe", t_ptrto (t_named "LOGFONT"), []);
		 ("lpntme", t_ptrto (t_named "TEXTMETRIC"), []);
		 ("FontType", t_named "DWORD", []);
		 ("lParam", t_named "LPARAM", []) ], false, []));

    ("HACCEL", handle "ACCEL");            (* handle to an accelerator table *)
    ("HANDLE", TPtr (TVoid [], []));
    ("HBITMAP", handle "BITMAP");
    ("HBRUSH", handle "BRUSH");
    ("HCERTCHAINENGINE", handle "CERTCHAINENGINE");
    ("HCERTSTORE", handle "CERTSTORE");
    ("HCURSOR", handle "CURSOR");
    ("HDC", handle "DC");                        (* handle to device context *)
    ("HDESK", handle "DESK");                       (* handle to the desktop *)
    ("HENHMETAFILE", handle "ENHMETAFILE");  (* handle to enhanced meta file *)
    ("HDROP", handle "DROP");    (* handle to a drag and drop mouse location *)
    ("HFILE", handle "FILE");
    ("HGDIOBJ", handle "GDIOBJ");
    ("HGLOBAL", handle "GLOBAL");                 (* handle to global memory *)
    ("HGLRC", handle "GLRC");                    (* opengl rendering context *)
    ("HHOOK", handle "HOOK");
    ("HIC", handle "IC");                      (* handle to input compressor *)
    ("HICON", handle "ICON");
    ("HIMAGELIST", handle "IMAGELIST");
    ("HIMC", handle "IMC");             (* handle to an input method context *)
    ("HINSTANCE", handle "INSTANCE");
    ("HINTERNET", handle "INTERNET");
    ("HKEY", handle "KEY");                (* handle to windows registry key *)
    ("HKL", handle "KL");                       (* handle to keyboard layout *)
    ("HLOCAL", handle "LOCAL");  (* handle to memory allocated by LocalAlloc *)
    ("HMENU", handle "MENU");
    ("HMETAFILE", handle "METAFILE"); (* handle to a windows-format meta file *)
    ("HMIXER", handle "MIXER");                  (* handle to a mixer device *)
    ("HMODULE", handle "MODULE");
    ("HOLEMENU",        (* handle to an OLE MENU (composite menu descriptor) *)
     handle "OLEMENU");
    ("HMONITOR", handle "MONITOR");

    ("HOOKPROC",
     TFun (named "IntPtr",
	   Some [("hWnd", named "IntPtr", []);
		 ("msg", named "int", []);
		 ("wparam", named "IntPtr", []);
		 ("lparam", named "IntPtr", [])], false, []));

    ("HPALETTE", handle "PALETTE");
    ("HRGN", handle "RGN");                            (* handle to a region *)
    ("HRSRC", handle "RSRC");                        (* handle to a resource *)
    ("HSECTION", handle "SECTION");
    ("HWAVEIN", handle "WAVEIN" );    (* handle to a wave-audio input device *)
    ("HWINSTA", handle "WINSTA" );               (* handle to window station *)
    ("HWND", handle "WND");                            (* handle to a window *)
    ("HDWP", handle "WDP");          (* handle to a deferred window position *)

    ("INTERNET_STATUS_CALLBACK",
     TFun (TVoid [],
	   Some [("hInternet", named "HINTERNET", []);
		 ("dwContext", named "DWORD_PTR", []);
		 ("dwInternetStatus", named "DWORD", []);
		 ("lpvStatusInformation", named "LPVOID", []);
		 ("dwStatusInformationLength", named "DWORD", [])], false, []));

    ("LOCALE_ENUMPROC",              (* callback function to process locales *)
     TFun (named "BOOL", Some [("lpLocaleString", named "LPTSTR", [])], false,[]));

    ("LPCH", TPtr (named "char",[]));
    ("LPCLSID", TPtr (named "CLSID",[]));             (* pointer to class ID *)
    ("LPCOLESTR", TPtr (named "wchar_t", []));    (* string type used in COM *)
    ("LPCSTR", t_ptrto(t_named "char"));
    ("LPCTSTR", TPtr (named "TCHAR", []));     (* pointer to constant string *)
    ("LPCVOID", TPtr (TVoid [], []));
    ("LPDWORD", TPtr (named "DWORD", []));
    ("LPCWSTR", TPtr (named "wchar_t", [])); (* pointer a constant wide string *)
    ("LPWSTR", TPtr (named "wchar_t", []));
    ("LPTCH", TPtr (named "TCHAR", []));
    ("LPSTR", t_ptrto (t_named "char"));
    ("LPTSTR", TPtr (named "TCHAR", []));

    ("LPUNKNOWN",          (* pointer to the IUnknown interface of an object *)
     TPtr (named "UNKNOWN", []));

    ("LPVOID", TPtr (TVoid [], []));
    ("LPWCH", TPtr (named "wchar_t", []));
    ("LPWORD", TPtr (named "WORD", []));
    ("PCSTR", TPtr (TInt (IChar, []), []));
    ("PCTSTR", TPtr (named "TCHAR", []));
    ("PCWSTR", TPtr (named "wchar_t", []));
    ("PDWORD_PTR", TPtr (named "DWORD_PTR", []));
    ("PHANDLE" , TPtr (named "HANDLE", []));

    ("PROGRESS_ROUTINE",     (* callback function to monitor copy operations *)
     TFun (named "DWORD",
	   Some [("TotalFileSize", named "LARGE_INTEGER", []);
	         ("TotalBytesTransferred", named "LARGE_INTEGER", []);
	         ("StreamSize", named "LARGE_INTEGER", []);
	         ("StreamBytesTransferred", named "LARGE_INTEGER", []);
	         ("dwStreamNumber", named "DWORD", []);
	         ("dwCallbackReason", named "DWORD", []);
	         ("hSourceFile", named "HANDLE", []);
	         ("hDestinationFile", named "HANDLE", []);
	         ("lpData", named "LPVOID", [])], false, []));

    ("PTSTR", TPtr (named "TCHAR", []));
    ("PVOID", TPtr (TVoid [], []));
    ("PWSTR", TPtr (named "wchar_t", []));
    ("SC_HANDLE", TPtr (TVoid [],[]));       (* service configuration handle *)
    ("SERVICE_STATUS_HANDLE", handle "SERVICE_STATUS");

    ("THREAD_START_ROUTINE",
     TFun (named "DWORD", Some [("lpParameter", named "LPVOID", [])], false, []));

    ("TIMERPROC",      (* callback function that processes WM_TIMER messages *)
     TFun (TVoid [],
	   Some [("hwnd", named "HWND", []);
	         ("uMsg", named "UINT", []);
	         ("idEvent", named "UINT_PTR", []);
	         ("dwTime", named "DWORD", [])], false, []));

    ("WAITORTIMERCALLBACK",
     TFun (TVoid [],
           Some [("lpParameter", TPtr ((TVoid []),[]), []);
                 ("TimerOrWaitFired", TInt (IBool, []), [])],false, []));

    ("WNDENUMPROC",             (* callback function for enumerating windows *)
     TFun (named "BOOL",
	   Some [("hwnd", named "HWND", []);
		 ("lParam", named "LPARAM", [])],false, []));

    ("WNDPROC",  (* callback unction that processes messages sent to a window *)
     TFun (named "LRESULT",
	   Some [("hwnd", named "HWND", []);
		 ("uMsg", named "UINT", []);
		 ("wParam", named "WPARAM", []);
		 ("lParam", named "LPARAM", [])], false, []));

    ("WSOVERLAPPED_COMPLETION_ROUTINE",
     TFun (TVoid [],
	   Some [("dwErrorCode", named "DWORD", []);
		 ("dwNumberOfBytesTransfered", named "DWORD", []);
		 ("lpOverlapped", TPtr (named "OVERLAPPED", []), [])], false, []))
  ]


let function_types = [
    ("comparisonfunction",
     TFun (TInt (IInt,[]),
           Some [("p1", TPtr (TVoid [],[]), []);
		 ("p2", TPtr (TVoid [],[]), [])], false, []));

    ("exitfunction", TFun (TVoid [], Some [], false, []));

    ("matherrfunction",
     TFun (TInt (IInt,[]),
           Some [("except", TPtr (named "_exception",[]), [])], false, []));

    ("signalfunction",
     TFun (TVoid [], Some [("sig", TInt (IInt,[]), [])], false, []));

    ("unknownfunction", TFun (t_unknown, None, false, []))
]


let jni_types = [
  ("jboolean", t_uchar) ;
  ("jbyte", t_uchar) ;
  ("jchar", t_wchar) ;
  ("jshort", t_short) ;
  ("jint", t_int) ;
  ("jlong", t_long) ;
  ("jfloat", t_float) ;
  ("jdouble", t_double) ;
  ("jsize", t_uint) ;

  ("javaVM", t_ptrto t_voidptr) ;
  ("JNIEnv", t_voidptr) ;

  ("jobject", t_voidptr) ;
  ("jclass", t_voidptr) ;
  ("jstring", t_voidptr) ;
  ("jarray", t_voidptr) ;
  ("jvalue", t_unknown) ;
  ("jthrowable", t_voidptr) ;

  ("jmethodID" , t_voidptr) ;
  ("jfieldID", t_voidptr) ;
  ("jweak", t_voidptr) ;

  ("jobjectArray", t_voidptr) ;
  ("jbooleanArray", t_voidptr) ;
  ("jbyteArray", t_voidptr) ;
  ("jcharArray", t_voidptr) ;
  ("jshortArray", t_voidptr) ;
  ("jintArray", t_voidptr) ;
  ("jlongArray", t_voidptr) ;
  ("jfloatArray", t_voidptr) ;
  ("jdoubleArray", t_voidptr)
]


let _ =
  List.iter
    (fun (name,ty) -> type_definitions#add_typeinfo name ty)
    (pe_types @ function_types @ jni_types)


let get_size_of_type_definition (s: string) =
  match s with
  | "byte" | "BYTE" | "char" -> Some 1
  | "UINT" -> Some 4
  | "INT" -> Some 4
  | _ -> None


let get_size_of_type (t: btype_t) =
  match t with
  | TNamed (s,_) -> get_size_of_type_definition s
  | _ -> Some (size_of_btype t)


let resolve_type (t: btype_t) =
  match t with
  | TNamed (tname,_) -> if type_definitions#has_type tname then
      type_definitions#get_type tname
    else
      t
  | _ -> t
