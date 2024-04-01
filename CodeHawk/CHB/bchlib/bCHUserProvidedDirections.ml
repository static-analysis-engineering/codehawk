(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchlib *)
open BCHPreFileIO
open BCHUtilities

module H = Hashtbl

class type user_provided_directions_int =
object
  
  (* setters *)
  method load_dll_ordinal_mappings: string -> unit
  method set_dll_ordinal_mappings : string -> (int * string) list -> unit

  (* getters *)
  method get_dll_ordinal_mapping : string -> int -> string

  (* predicates *)
  method are_DS_and_ES_the_same_segment: bool

  (* xml *)
  method write_xml_ordinal_table : xml_element_int -> string -> unit
end

class user_provided_directions_t:user_provided_directions_int =
object (self)

  val dll_ordinal_mappings = H.create 1
  val ds_es_are_the_same_segment = true

  method load_dll_ordinal_mappings (dllname:string) =
    let filename = String.lowercase_ascii (replace_dot dllname) in
    match load_export_ordinal_table filename with
    | Some node ->
      let mapping = self#read_xml_ordinal_table node in
      begin
	self#set_dll_ordinal_mappings dllname mapping ;
	chlog#add
          "ordinal table"
	  (LBLOCK [
               STR dllname;
               STR ": ";
               INT (List.length mapping);
               STR " entries"])
      end
    | _ -> 
       chlog#add
         "ordinal table"
	 (LBLOCK [STR "No ordinal table found for "; STR dllname])

  method private read_xml_ordinal_table (node:xml_element_int) =
    List.map
      (fun eNode -> (eNode#getIntAttribute "ordinal", eNode#getAttribute "name"))
      (node#getTaggedChildren "entry")

  method set_dll_ordinal_mappings (dllname:string) (l:(int * string) list) =
    let table = if H.mem dll_ordinal_mappings dllname then
	H.find dll_ordinal_mappings dllname
      else
	let t = H.create 5 in
	begin
	  H.add dll_ordinal_mappings dllname t;
	  t
	end in
    List.iter (fun (hint,fname) -> H.add table hint fname) l

  method get_dll_ordinal_mapping (dllname:string) (hint:int) =
    if H.mem dll_ordinal_mappings dllname then
      try 
	H.find (H.find dll_ordinal_mappings dllname) hint
      with 
	Not_found -> "_ordinal_" ^ (string_of_int hint)
    else
      ""

  method are_DS_and_ES_the_same_segment = ds_es_are_the_same_segment

  method write_xml_ordinal_table (node:xml_element_int) (name:string) =
    let append = node#appendChildren in
    if H.mem dll_ordinal_mappings name then
      let table = H.find dll_ordinal_mappings name in
      let l = ref [] in
      let _ = H.iter (fun k v -> l := (k,v) :: !l) table in
      let l = List.sort (fun (k1,_) (k2,_) -> Stdlib.compare k1 k2) !l in
      begin
	append (List.map (fun (k,v) ->
	  let eNode = xmlElement "entry" in
	  begin
	    eNode#setIntAttribute "ordinal" k ;
	    eNode#setAttribute "name" v ;
	    eNode
	  end) l) ;
	node#setIntAttribute "size" (List.length l)
      end

end
      
let user_provided_directions = new user_provided_directions_t

let _ = user_provided_directions#set_dll_ordinal_mappings "COMCTL32.dll"
  [ (13, "MakeDragList");
    (14, "LBItemFromPt");
    (15, "DrawInsert");
    (16, "CreateUpDownControl");
    (17, "InitCommonControls");
  ]

let _ = user_provided_directions#set_dll_ordinal_mappings "ODBC32.dll"
  [ (1,   "SQLAllocConnect") ;
    (2,   "SQLAllocEnv") ;
    (3,   "SQLAllocStmt") ;
    (4,   "SQLBindCol") ; 
    (5,   "SQLCancel") ; 
    (6,   "SQLColAttributes") ; 
    (7,   "SQLConnect") ;
    (8,   "SQLDescribeCol") ;
    (9,   "SQLDisconnect") ;
    (10,  "SQLError") ;
    (11,  "SQLExecDirect") ;
    (12,  "SQLExecute") ;
    (13,  "SQLFetch") ;
    (14,  "SQLFreeConnect") ;
    (15,  "SQLFreeEnv") ;
    (16,  "SQLFreeStmt") ;
    (17,  "SQLGetCursorName") ;
    (18,  "SQLNumResultCols") ;
    (19,  "SQLPrepare") ;
    (20,  "SQLRowCount") ; 
    (21,  "SQLSetCursorName") ;
    (23,  "SQLTransact") ; 
    (27,  "SQLColAttribute") ;
    (30,  "SQLFetchScroll") ;
    (38,  "SQLGetStmtAttr") ;
    (40,  "SQLColumns") ;
    (41,  "SQLDriverConnect") ;
    (42,  "SQLGetConnectOption") ;
    (43,  "SQLGetData") ;
    (45,  "SQLGetInfo") ;
    (46,  "SQLGetStmtOption") ;
    (47,  "SQLGetTypeInfo") ;
    (48,  "SQLParamData") ;
    (49,  "SQLPutData") ;
    (50,  "SQLSetConnectOption") ;
    (51,  "SQLSetStmtOption") ;
    (52,  "SQLSpecialColumns") ;
    (53,  "SQLStatistics") ;
    (54,  "SQLTables") ;
    (55,  "SQLBrowseConnect") ; 
    (56,  "SQLColumnPrivileges") ;
    (58,  "SQLDescribeParam") ; 
    (60,  "SQLForeignKeys") ;
    (61,  "SQLMoreResults") ;
    (62,  "SQLNativeSql") ;
    (63,  "SQLNumParams") ;
    (65,  "SQLPrimaryKeys") ;
    (66,  "SQLProcedureColumns") ; 
    (67,  "SQLProcedures") ;
    (68,  "SQLSetPos") ; 
    (70,  "SQLTablePrivileges") ; 
    (72,  "SQLBindParameter") ; 
    (76,  "SQLSetStmtAttr") ;
  ]


let _ = user_provided_directions#set_dll_ordinal_mappings "OLEAUT32.dll"
  [ (2,   "SysAllocString") ;
    (4,   "SysAllocStringLen") ;
    (6,   "SysFreeString") ;
    (7,   "SysStringLen") ;
    (8,   "VariantInit") ;
    (9,   "VariantClear") ;
    (10,  "VariantCopy") ;
    (12,  "VariantChangeType") ;
    (149, "SysStringByteLen") ;
    (150, "SysAllocStringByteLen") ;
    (161, "LoadTypeLib") ;
    (162, "LoadRegTypeLib") ;
    (163, "RegisterTypeLib");
    (186, "UnregisterTypeLib") ;
    (277, "VarUI4FromStr") ;
    (417, "OleCreatePropertyFrame") ;
    (420, "OleCreateFontIndirect") 
  ]

let _ = user_provided_directions#set_dll_ordinal_mappings "oledlg.dll"
  [ (1, "OleUIAddVerbMenua") ;
    (6, "OleUIChangeIconA") ;
    (8, "OleUIBusyA")
  ]

(* source: https://www.geoffchappell.com/studies/windows/shell/shell32/api/index.htm *)
let _ = user_provided_directions#set_dll_ordinal_mappings
          "SHELL32.dll"
          [ (2, "SHChangeNotifyRegister") ;
            (4, "SHChangeNotifyDeregister") ;
            (5, "SHChangeNotifyUpdateEntryList") ;
            (9, "PifMgr_OpenProperties") ;
            (10, "PifMgr_GetProperties") ;
            (11, "PifMgr_SetProperties") ;
            (13, "PifMgr_CloseProperties") ;
            (15, "ILGetDisplayName") ;
            (16, "ILFindLastID") ;
            (17, "ILRemoveLastID") ;
            (18, "ILClone") ;
            (19, "ILCloneFirst") ;
            (20, "ILGlobalClone") ;
            (21, "ILIsEqual") ;
            (22, "DAD_DragEnterEx2") ;
            (23, "ILIsParent") ;
            (24, "ILFindChild") ;
            (25, "ILCombine") ;
            (26, "ILLoadFromStream") ;
            (27, "ILSaveToStream") ;
            (28, "SHILCreateFromPath") ;
            (29, "PathIsRoot") ;
            (30, "PathBuildRoot") ;
            (31, "PathFindExtension") ;
            (32, "PathAddBackslash") ;
            (33, "PathRemoveBlanks") ;
            (34, "PathFindFileName") ;
            (35, "PathRemoveFileSpec") ;
            (36, "PathAppend") ;
            (37, "PathCombine") ;
            (38, "PathStripPath") ;
            (39, "PathIsUNC") ;
            (40, "PathIsRelative") ;
            (41, "IsLFNDriveA") ;
            (42, "IsLFNDriveW") ;
            (43, "PathIsExe") ;
            (44, "Control_RunDLLNoFallback") ;
            (45, "PathFileExists") ;
            (46, "PathMatchSpec") ;
            (47, "PathMakeUniqueName") ;
            (48, "PathSetDlgItemPath") ;
            (49, "PathQualify") ;
            (50, "PathStripToRoot") ;
            (51, "PathResolve") ;
            (52, "PathGetArgs") ;
            (53, "IsSuspendAllowed") ;
            (54, "LogoffWindowsDialog") ;
            (55, "PathQuoteSpaces") ;
            (56, "PathUnquoteSpaces") ;
            (57, "PathGetDriveNumber") ;
            (58, "ParseField") ;
            (59, "RestartDialog") ;
            (60, "ExitWindowsDialog") ;
            (61, "RunFileDlg") ;
            (62, "PickIconDlg") ;
            (63, "GetFileNameFromBrowse") ;
            (64, "DriveType") ;
            (65, "InvalidateDriveType") ;
            (66, "IsNetDrive") ;
            (68, "SHGetSetSettings") ;
            (69, "SHGetNetResource") ;
            (70, "SHCreateDefClassObject") ;
            (75, "PathYetAnotherMakeUniqueName") ;
            (76, "DragQueryInfo") ;
            (78, "OleStrToStrN") ;
            (82, "DDECreatePostNotify") ;
            (83, "CIDLData_CreateFromIDArray") ;
            (84, "SHIsBadInterfacePtr") ;
            (85, "OpenRegStream") ;
            (89, "SHCloneSpecialIDList") ;
            (92, "PathGetShortPath") ;
            (99, "SetAppStartingCursor") ;
            (101, "FileMenu_HandleNotify") ;
            (102, "SHCoCreateInstance") ;
            (104, "FileMenu_DeleteAllItems") ;
            (105, "FileMenu_DrawItem") ;
            (106, "FileMenu_FindSubMenuByPidl") ;
            (107, "FileMenu_GetLastSelectedItemPidls") ;
            (108, "FileMenu_HandleMenuChar") ;
            (109, "FileMenu_InitMenuPopup") ;
            (110, "FileMenu_InsertUsingPidl") ;
            (111, "FileMenu_Invalidate") ;
            (112, "FileMenu_MeasureItem") ;
            (113, "FileMenu_ReplaceUsingPidl") ;
            (114, "FileMenu_Create") ;
            (115, "FileMenu_AppendItem") ;
            (116, "FileMenu_TrackPopupMenuEx") ;
            (117, "FileMenu_DeleteItemByCmd") ;
            (118, "FileMenu_Destroy") ;
            (119, "IsLFNDrive") ;
            (120, "FileMenu_AbortInitMenu") ;
            (121, "SHFlushClipboard") ;
            (122, "RunDll_CallEntry16") ;
            (123, "SHFreeUnusedLibraries") ;
            (124, "FileMenu_AppendFilesForPidl") ;
            (125, "FileMenu_AddFilesForPidl") ;
            (128, "DllGetClassObject") ;
            (129, "DAD_AutoScroll") ;
            (130, "DAD_DragEnter") ;
            (131, "DAD_DragEnterEx") ;
            (132, "DAD_DragLeave") ;
            (134, "DAD_DragMove") ;
            (136, "DAD_SetDragImage") ;
            (137, "DAD_ShowDragImage") ;
            (139, "Desktop_UpdateBriefcaseOnEvent") ;
            (140, "FileMenu_DeleteItemByIndex") ;
            (141, "FileMenu_DeleteMenuItemByFirstID") ;
            (142, "FileMenu_DeleteSeparator") ;
            (143, "FileMenu_EnableItemByCmd") ;
            (144, "FileMenu_GetItemExtent") ;
            (145, "PathFindOnPath") ;
            (146, "RLBuildListOfPaths") ;
            (147, "SHCLSIDFromString") ;
            (151, "SHLoadOLE") ;
            (152, "ILGetSize") ;
            (153, "ILGetNext") ;
            (154, "ILAppendID") ;
            (155, "ILFree") ;
            (156, "LGlobalFree") ;
            (157, "ILCreateFromPath") ;
            (158, "PathGetExtension") ;
            (159, "PathIsDirectory") ;
            (165, "SHCreateDirectory") ;
            (167, "SHAddFromPropSheetExtArray") ;
            (168, "SHCreatePropSheetExtArray") ;            
            (171, "PathCleanupSpec") ;
            (172, "SHCreateLinks") ;
            (175, "SHGetSpecialFolderPathW") ;
            (177, "DAD_SetDragImageFromListView") ;
            (179, "SHGetNewLinkInfoA") ;
            (180, "SHGetNewLinkInfoW") ;
            (181, "RegisterShellHook") ;
            (182, "ShellMessageBoxW") ;
            (183, "ShellMessageBoxA") ;
            (186, "ILGetDisplayNameEx") ;
            (187, "ILGetPseudoNameW") ;
            (189, "ILCreateFromPathA") ;
            (190, "ILCreateFromPathW") ;
            (193, "SHHandleUpdateImage") ;
            (195, "SHFree") ;
            (196, "SHAlloc") ;
            (198, "SHAbortInvokeCommand") ;
            (200, "SHCreateDesktop") ;
            (202, "DDEHandleViewFolderNotify") ;
            (205, "Printer_LoadIconsW") ;
            (206, "Link_AddExtraDataSection") ;
            (207, "Link_ReadExtraDataSection") ;
            (208, "Link_RemoveExtraDataSection") ;
            (209, "Int64ToString") ;
            (210, "LargeIntegerToString") ;
            (211, "Printers_GetPidl") ;
            (212, "Printer_AddPrinterPropPages") ;
            (213, "Printers_RegisterWindowW") ;
            (214, "Printers_UnregisterWindow") ;
            (216, "FileMenu_IsFileMenu") ;
            (217, "FileMenu_ProcessCommand") ;
            (218, "FileMenu_InsertItem") ;
            (219, "FileMenu_InsertSeparator") ;
            (220, "FileMenu_GetPidl") ;
            (221, "FileMenu_EditMode") ;
            (222, "FileMenu_HandleMenuSelect") ;
            (223, "FileMenu_IsUnexpanded") ;
            (224, "FileMenu_DelayedInvalidate") ;
            (225, "FileMenu_IsDelayedInvalid") ;
            (227, "FileMenu_CreateFromMenu") ;
            (230, "FirstUserLogon") ;
            (233, "SHGetUserPicturePathW") ;
            (239, "PathIsSlowW") ;
            (240, "PathIsSlowA") ;
            (241, "SHGetUserDisplayName") ;
            (242, "SHGetProcessDword") ;
            (246, "SHInvokePrivilegedFunctionW") ;
            (248, "SHGetUserSessionId") ;
            (249, "PathParseIconLocation") ;
            (250, "PathRemoveExtension") ;
            (251, "PathRemoveArgs") ;
            (252, "PathIsURL") ;
            (253, "SHIsCurrentProcessConsoleSession") ;
            (254, "DisconnectWindowsDialog") ;
            (257, "SHGetShellFolderViewCB") ;
            (258, "LinkWindow_RegisterClass") ;
            (259, "LinkWindow_UnregisterClass") ;
            (260, "CreateInfoTipFromItem") ;
            (261, "SHGetUserPicturePath") ;
            (264, "CreateInfoTipFromItem2") ;
            (520, "SHAllocShared") ;
            (524, "RealDriveType") ;
            (525, "RealDriveTypeFlags") ;
            (640, "NTSHChangeNotifyRegister") ;
            (641, "NTSHChangeNotifyDeregister") ;
            (643, "SHChangeNotifyReceive") ;
            (644, "SHChangeNotification_Lock") ;
            (645, "SHChangeNotification_Unlock") ;
            (646, "SHChangeRegistrationReceive") ;
            (647, "ReceiveAddToRecentDocs") ;
            (650, "PathIsSameRoot") ;
            (651, "OldReadCabinetState") ;
            (653, "PathProcessCommand") ;
            (654, "ReadCabinetState") ;
            (680, "IsUserAnAdmin") ;
            (700, "CDefFolderMenu_Create") ;
            (701, "CDefFolderMenu_Create2") ;
            (702, "CDefFolderMenu_MergeMenu") ;
            (703, "GUIDFromStringA") ;
            (704, "GUIDFromStringW") ;
            (708, "SHGetSetFolderCustomSettingsA") ;
            (709, "SHGetSetFolderCustomSettingsW") ;
            (711, "CheckWinIniForAssocs") ;
            (712, "SHCopyMonikerToTemp") ;
            (713, "PathIsTemporaryA") ;
            (714, "PathIsTemporaryW") ;
            (715, "SHCreatePropertyBag") ;
            (720, "MakeShellURLFromPathA") ;
            (721, "MakeShellURLFromPathW") ;
            (722, "SHCreateInstance") ;
            (725, "GetFileDescriptor") ;
            (726, "CopyStreamUI") ;
            (730, "RestartDialogEx") ;
            (733, "CheckDiskSpace") ;
            (740, "SHCreateFileDataObject") ;
            (743, "SHCreateFileExtractIconW") ;
            (744, "Create_IEnumUICommand") ;
            (745, "Create_IUIElement") ;
            (753, "CheckStagingArea") ;
            (755, "PathIsEqualOrSubFolder") ;
            (756, "DeleteFileThumbnail") ;
            (757, "DisplayNameOfW") ;
            (760, "SHConfirmOperation") ;
            (761, "SHChangeNotifyDeregisterWindow") ;
            (762, "Create_IUICommandFromDef") ;
            (763, "Create_IEnumUICommandFromDefArray") ;
            (764, "AssocCreateElement") ;
            (766, "SHCopyStreamWithProgress") ;
            (767, "AssocCreateListForClasses") ;
            (778, "AssocGetPropListForExt") ;
            (781, "SHApplyPropertiesToItem") ;
            (786, "SHCreateCategoryEnum") ;
            (814, "SHCreateLeafConditionEx") ;
            (815, "SHCreateAndOrConditionEx") ;
            (816, "SHCreateAndOrCondition") ;
            (817, "SHCreateLeafCondition") ;
            (818, "SHCreateFilter") ;
            (820, "SHCreateAutoList") ;
            (825, "SHCombineMultipleConditions") ;
            (826, "SHCreateAutoListWithID") ;
            (828, "DrawMenuItem") ;
            (829, "MeasureMenuItem") ;
            (830, "SHCreateNotConditionEx") ;
            (831, "SHCreateFilterFromFullText") ;
            (839, "CreateSingleVisibleInList") ;
            (840, "PathGetPathDisplayName") ;
            (844, "SHCreateNotCondition") ;
            (845, "CreateConditionRange") ;
            (847, "SHCombineMultipleConditionsEx") ;
            (849, "SHCreateConditionFactory") ;
            (850, "PathComparePaths") ;
            (854, "IsShellItemInSearchIndex") ;
            (856, "CPL_ExecuteTask") ;
            (858, "POOBE_CreateIndirectGraphic") ;
            (862, "SHCompareIDsFull") ;
            (863, "GetTryHarderIDList") ;
            (865, "sElevationRequired") ;
            (867, "CreateVisibleInDescription") ;
            (868, "CreateVisibleInList") ;
            (869, "PathGetPathDisplayNameAlloc") ;
            (870, "DUI_Shell32_StartDeferUninitialization") ;
            (871, "DUI_Shell32_EndDeferUninitialization") ;
            (872, "SHCreateKindFilter") ;
            (874, "LegacyEnumTasks") ;
            (875, "LegacyEnumSpecialTasksByType") ;
            (876, "EnumCommonTasks") ;
            (877, "PlaceTasksUnderHeader") ;
            (878, "GetDataIndexFromFolderType") ;
            (880, "CreateAutoListParser") ;
            (883, "PrepareURLForDisplayUTF8W") ;
            (885, "RunInstallUninstallStubs") ;
            (889, "InitializeStartMenuItem") ;
            (890, "ClearStartMenuItem") ;
            (891, "RefreshBrowserLayout") ;
            (892, "GetSqmableFileName") ;
            (893, "SetWindowRelaunchProperties") ;
            (894, "MakeDestinationItem") ; 
            (895, "GetAppPathFromLink") ;
            (896, "ClearDestinationsForAllApps") ;
            (897, "SaveTopViewSettings") ;
            (898, "SHCreateLinksEx") ;
            (899, "SetExplorerServerMode") ;
            (900, "GetAppIDRoot") ;
            (902, "IsSearchEnabled") 
          ]

(* from: https://www.geoffchappell.com/studies/windows/shell/shlwapi/history/ords471.htm?tx=79-81,
   https://www.geoffchappell.com/studies/windows/shell/shlwapi/history/ords500.htm?tx=77,80,81
 *)
let _ =
  user_provided_directions#set_dll_ordinal_mappings "SHLWAPI.dll"
    [(37, "CallWindowProcWrapW");
     (52, "CreateFileWrapW");
     (53, "CreateFontIndirectWrapW");
     (55, "CreateWindowExWrapW");
     (56, "DefWindowProcWrapW");
     (59, "DialogBoxParamWrapW");
     (61, "DrawTextWrapW");
     (68, "FormatMessageWrapW");
     (74, "GetDlgItemTextWrapW");
     (75, "GetFileAttributesWrapW");
     (91, "GetTextExtentPoint32WrapW");
     (93, "GetTextMetricsWrapW");
     (94, "GetWindowLongWrapW");
     (95, "GetWindowTextWrapW");
     (102, "LoadCursorWrapW");
     (107, "LoadStringWrapW");
     (136, "SendMessageWrapW");
     (138, "SetDlgItemTextWrapW");
     (141, "SetWindowLongWrapW");
     (143, "SetWindowTextWrapW");
     (215, "SHAnsiToUnicode");   (* no summary *)
     (217, "SHUnicodeToAnsi");   (* no summary *)
     (295, "SHSetIniStringW");   (* no summary *)
     (298, "WritePrivateProfileStringWrapW");
     (312, "GetPrivateProfileStringWrapW");
     (340, "MessageBoxWrapW");
     (437, "IsOS")   (* no summary *)
    ]

let _ = user_provided_directions#set_dll_ordinal_mappings "WSOCK32.dll"
  [ (2,  "bind") ;
    (3,  "closesocket") ;
    (4,  "connect") ;
    (6,  "getsockname") ;
    (7,  "getsockopt") ;
    (8,  "htonl") ;
    (9,  "htons") ;
    (10, "inet_addr") ;
    (11, "inet_ntoa") ;
    (12, "ioctlsocket") ; 
    (13, "listen") ;
    (14, "ntohl") ;
    (15, "ntohs") ;
    (16, "recv") ; 
    (18, "select") ;
    (19, "send") ;
    (22, "shutdown") ;
    (23, "socket") ; 
    (51, "gethostbyaddr") ;
    (52, "gethostbyname") ;
    (111, "WSAGetLastError") ;
    (115, "WSAStartup") ;
    (116, "WSACleanup") ;
    (151, "__WSAFDisSet") 
  ]



let _ = user_provided_directions#set_dll_ordinal_mappings "WS2_32.dll"
  [ (1, "accept") ;
    (2, "bind") ;
    (3, "closesocket") ;
    (4, "connect") ;
    (5, "getpeername") ;
    (6, "getsockname") ;
    (7, "getsockopt") ;
    (8, "htonl") ;
    (9, "htons") ;
    (10, "ioctlsocket") ;
    (11, "inet_addr") ;
    (12, "inet_ntoa") ;
    (13, "listen") ;
    (14, "ntohl") ;
    (15, "ntohs") ;
    (16, "recv") ;
    (17, "recvfrom") ;
    (18, "select") ;
    (19, "send") ;
    (20, "sendto") ;
    (21, "setsockopt") ;
    (22, "shutdown") ;
    (23, "socket") ;
    (51, "gethostbyaddr") ;
    (52, "gethostbyname") ;
    (53, "getprotobyname") ;
    (54, "getprotobynumber") ;
    (55, "getservbyname") ;
    (56, "getservbyport") ;
    (57, "gethostname") ;
    (111, "WSAGetLastError") ;
    (112, "WSASetLastError") ;
    (113, "WSACancelBlockingCall") ;
    (114, "WSAIsBlocking") ;
    (115, "WSAStartup") ;
    (116, "WSACleanup") ;
    (151, "__WSAFDIsSet") ]

