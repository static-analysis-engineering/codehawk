(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* bchlibx86 *)
open BCHFunctionSummaryLibrary
open BCHLibx86Types
open BCHPredefinedUtil

module H = Hashtbl

(* -----------------------------------------------------------------------------
   System::SysUtils::AnsiStrLIComp (s)
   System::SysUtils::CompareStr (s)
   System::SysUtils::CreateDir (s)
   System::SysUtils::FileOpen (s)
   System::SysUtils::FileWrite (s)
   System::SysUtils::StrCharLength (s)
   System::SysUtils::StrComp (s)
   System::SysUtils::StrCopy (s)
   System::SysUtils::StrEnd (s)
   System::SysUtils::StrIComp (s)
   System::SysUtils::StrLComp (s)
   System::SysUtils::StrLen (s)
   System::SysUtils::StrLIComp (s)
   System::SysUtils::StrMove (s)
   System::SysUtils::StrNextChar (s)
   System::SysUtils::StrPos (s)

 * --------------------------------------------------------------------------- *)

let table = H.create 11

let pkgs = [ "System" ; "SysUtils" ]

let load_rtl_sysutils_functions () =
  List.iter (fun m -> add_libfun table pkgs m)
    ["CompareStr";
     "StrComp";
     "StrCopy";
     "StrEnd";
     "StrIComp";
     "StrLComp";
     "StrLen";
     "StrLIComp";
     "StrPos"]

(* ===================================================== SysUtils::AnsiStrLIComp
   example: V01a: 0x408610

  0x408610   [ 0 ]    push ebx          save ebx
  0x408611   [ -4 ]   push esi          save esi
  0x408612   [ -8 ]   push edi          save edi
  0x408613  [ -12 ]   mov ebx, ecx      ebx := ecx = ecx_in
  0x408615  [ -12 ]   mov edi, edx      edi := edx = edx_in
  0x408617  [ -12 ]   mov esi, eax      esi := eax = eax_in
  0x408619  [ -12 ]   push ebx          [CompareStringA : cchCount2 = ebx ]
  0x40861a  [ -16 ]   push edi          [CompareStringA : lpString2 = edi ]
  0x40861b  [ -20 ]   push ebx          [CompareStringA : cchCount1 = ebx ]
  0x40861c  [ -24 ]   push esi          [CompareStringA : lpString1 = esi ]
  0x40861d  [ -28 ]   push 0x1          [CompareStringA : dwCmpFlag = 1 ]
  0x40861f  [ -32 ]   push 0x400        [CompareStringA : Locale = 1024 ]
  0x408624  [ -36 ]   call 0x406518     CompareStringA(Locale:1024,
                                                       dwCmpFlag:1,
                                                       lpString1:eax_in,
                                                       cchCount1:ecx_in,
                                                       lpString2:edx_in,
                                                       cchCount2:ecx_in) (adj 24)
  0x408629  [ -12 ]   sub eax, 0x2      eax := eax - 2 = (CompareStringA_rtn_0x408624 - 2)
  0x40862c  [ -12 ]   pop edi           restore edi
  0x40862d   [ -8 ]   pop esi           restore esi
  0x40862e   [ -4 ]   pop ebx           restore ebx
  0x40862f   [ 0 ]    ret               return

*)


(* ======================================================== SysUtils::CreateDir
   example: V01a:0x409038

  0x409038   [ 0 ]    push ebx        save ebx
  0x409039   [ -4 ]   mov ebx, eax    ebx := eax = eax_in
  0x40903b   [ -4 ]   push 0x0        [CreateDirectoryA: lpSecurityAttributes = 0]
  0x40903d   [ -8 ]   mov eax, ebx    eax := ebx = eax_in
  0x40903f   [ -8 ]   call 0x404678   __System::NullToNullStr__(&(eax_in)[0])
  0x409044   [ -8 ]   push eax        [CreateDirectoryA: lpPathname = eax]
  0x409045  [ -12 ]   call 0x406520   CreateDirectoryA(lpPathname:eax_in,
                                                   lpSecurityAttributes:0) (adj 8)
  0x40904a   [ -4 ]   cmp eax, 0x1    cmp eax, 0x1
  0x40904d   [ -4 ]   sbb eax, eax    eax := 0 or -1
  0x40904f   [ -4 ]   inc eax         eax := eax + 1
  0x409050   [ -4 ]   pop ebx         restore ebx
  0x409051   [ 0 ]    ret             return
*)


(* ============================================================ SysUtils::StrComp
   example: V01a:0x409130
   md5hash: 63b4b8dfcb10353c6824b4965e6620c1

  0x409130   [ 0 ]    push edi               save edi
  0x409131   [ -4 ]   push esi               save esi
  0x409132   [ -8 ]   mov edi, edx           edi := edx = edx_in
  0x409134   [ -8 ]   mov esi, eax           esi := eax = eax_in
  0x409136   [ -8 ]   mov ecx, 0xffffffff    ecx := 4294967295
  0x40913b   [ -8 ]   xor eax, eax           eax := 0
  0x40913d   [ -8 ]   repne scas             (Edi): (edx_in)[0]_in;
                                                Ecx: 4294967295 (width: 1)
  0x40913f   [ -8 ]   not ecx                not ecx
  0x409141   [ -8 ]   mov edi, edx           edi := edx = edx_in
  0x409143   [ -8 ]   xor edx, edx           edx := 0
  0x409145   [ -8 ]   repe cmps              (Edi):(edx_in)[0]_in;
                                                (Edi): (eax_in)[0]_in;
                                                Ecx: ecx (width: 1)
  0x409147   [ -8 ]   mov al, -0x1(esi)      al :=  ?  (tmpN)
  0x40914a   [ -8 ]   mov dl, -0x1(edi)      dl :=  ?  (tmpN)
  0x40914d   [ -8 ]   sub eax, edx           eax := eax - edx
  0x40914f   [ -8 ]   pop esi                restore esi
  0x409150   [ -4 ]   pop edi                restore edi
  0x409151   [ 0 ]    ret                    return
*)


(* =========================================================== SysUtils::StrLComp
   example: V01a:0x409194
   md5hash: ffa9864bee9d1134fc0dd756ec2eeb6a (22 instrs)

  0x409194   [ 0 ]    push edi           save edi
  0x409195   [ -4 ]   push esi           save esi
  0x409196   [ -8 ]   push ebx           save ebx
  0x409197  [ -12 ]   mov edi, edx       edi := edx = edx_in
  0x409199  [ -12 ]   mov esi, eax       esi := eax = eax_in
  0x40919b  [ -12 ]   mov ebx, ecx       ebx := ecx = ecx_in
  0x40919d  [ -12 ]   xor eax, eax       eax := 0
  0x40919f  [ -12 ]   or ecx, ecx        ecx := ecx | ecx
  0x4091a1  [ -12 ]   jz 0x4091b7        if (ecx_in = 0) then goto 0x4091b7
--------------------------------------------------------------------------------
  0x4091a3  [ -12 ]   repne scas         (Edi): (edx_in)[0]_in; Ecx: ecx (width: 1)
  0x4091a5  [ -12 ]   sub ebx, ecx       ebx := ebx - ecx = (ecx_in - ecx)
  0x4091a7  [ -12 ]   mov ecx, ebx       ecx := ebx
  0x4091a9  [ -12 ]   mov edi, edx       edi := edx = edx_in
  0x4091ab  [ -12 ]   xor edx, edx       edx := 0
  0x4091ad  [ -12 ]   repe cmps          (Edi):(edx_in)[0]_in;
                                           (Edi): (eax_in)[0]_in;
                                           Ecx: ecx (width: 1)
  0x4091af  [ -12 ]   mov al, -0x1(esi)  al :=  ?  (tmpN)
  0x4091b2  [ -12 ]   mov dl, -0x1(edi)  dl :=  ?  (tmpN)
  0x4091b5  [ -12 ]   sub eax, edx       eax := eax - edx
--------------------------------------------------------------------------------
  0x4091b7  [ -12 ]   pop ebx            restore ebx
  0x4091b8   [ -8 ]   pop esi            restore esi
  0x4091b9   [ -4 ]   pop edi            restore edi
  0x4091ba   [ 0 ]    ret                return
H
*)


(* ============================================================ SysUtils::StrEnd
   example: V01a:0x40906c
   md5hash: eb49e9275eff6fafbda2e909b3b4db58

  0x40906c   [ 0 ]    mov edx, edi          edx := edi = edi_in
  0x40906e   [ 0 ]    mov edi, eax          edi := eax = eax_in
  0x409070   [ 0 ]    mov ecx, 0xffffffff   ecx := 4294967295
  0x409075   [ 0 ]    xor al, al            al := 0
  0x409077   [ 0 ]    repne scas            (Edi): (eax_in)[0]_in;
                                               Ecx: 4294967295 (width: 1)
  0x409079   [ 0 ]    lea eax, -0x1(edi)    eax := (edi - 1) = (eax_in - 1)
  0x40907c   [ 0 ]    mov edi, edx          edi := edx = edi_in
  0x40907e   [ 0 ]    ret                   return
*)

(* ============================================================ SysUtils::StrLen
   example: V01a:0x409054
   md5hash: 9419f994914d56ea50d48092f35e095c

  0x409054   [ 0 ]    mov edx, edi         edx := edi = edi_in
  0x409056   [ 0 ]    mov edi, eax         edi := eax = eax_in
  0x409058   [ 0 ]    mov ecx, 0xffffffff  ecx := 4294967295
  0x40905d   [ 0 ]    xor al, al           al := 0
  0x40905f   [ 0 ]    repne scas           (Edi): (eax_in)[0]_in;
                                              Ecx: 4294967295 (width: 1)
  0x409061   [ 0 ]    mov eax, 0xfffffffe  eax := 4294967294
  0x409066   [ 0 ]    sub eax, ecx         eax := eax - ecx = -1
  0x409068   [ 0 ]    mov edi, edx         edi := edx = edi_in
  0x40906a   [ 0 ]    ret                  return
*)

(* ============================================================== SysUtils::StrMove
   example: V01a:0x409080

  0x409080   [ 0 ]    push esi        save esi
  0x409081   [ -4 ]   mov esi, eax    esi := eax = eax_in
  0x409083   [ -4 ]   xchg eax, edx   tmp := edx; edx := eax; eax := tmp
  0x409084   [ -4 ]   call 0x4028d8   __System::Move__(Source:edx_in,
                                                Dest:eax_in,Count:ecx_in)
  0x409089   [ -4 ]   mov eax, esi    eax := esi = eax_in
  0x40908b   [ -4 ]   pop esi         restore esi
  0x40908c   [ 0 ]    ret             return
*)


let delphi_rtl_sysutils_functions () =
  H.fold (fun k v a -> a @ (get_fnhashes k v)) table []


let delphi_rtl_sysutils_patterns = [

  (* AnsiStrLIComp (V01a:0x408610) *)
    { regex_s =
        Str.regexp ("5356578bd98bfa8bf0535753566a\\(..\\)68\\(........\\)e8" ^
                      "\\(........\\)83e8025f5e5bc3$");

    regex_f = fun faddr fnbytes fnhash ->
      let flags = toimm2 (Str.matched_group 1 fnbytes) in
      let locale = todw (Str.matched_group 2 fnbytes) in
      if is_named_dll_call faddr 20 "CompareStringA" then
	let fname = "AnsiStrLIComp" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 18 in
	  let msg =
            LBLOCK [
                STR " with flags "; INT flags; STR " and locale ";
		locale#toPretty] in
	  sometemplate ~msg sem
	else None
      else None
  };

  (* CreateDir (V01a:0x409038) *)
  { regex_s = Str.regexp
      ("538bd86a008bc3e8\\(........\\)50e8\\(........\\)83f8011bc0405bc3$");

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_inlined_call faddr 7 "__System::LStrToPChar__" &&
	is_named_dll_call faddr 13 "CreateDirectoryA" then
	let fname = "CreateDir" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 12 in
	  sometemplate sem
	else None
      else None
  };

  (* FileOpen (V01a:0x408b08) *)
  { regex_s =
      Str.regexp (
          "5356578bda8bf883c8ff8bf383e60383fe02773f8bd381e2f0000"
          ^ "00083fa4077326a0068\\(........\\)6a\\(..\\)6a\\(..\\)"
          ^ "8bc325f0000000c1e8048b0485\\(........\\)508b04b5"
          ^ "\\(........\\)508bc7e8\\(........\\)50e8\\(........\\)"
          ^ "5f5e5bc3$");

    regex_f = fun faddr fnbytes fnhash ->
      let flags = todw (Str.matched_group 1 fnbytes) in
      let disp = toimm2 (Str.matched_group 2 fnbytes) in
      let secr = toimm2 (Str.matched_group 3 fnbytes) in
      let fmConst1 = todw (Str.matched_group 4 fnbytes) in
      let fmConst2 = todw (Str.matched_group 5 fnbytes) in
      if is_named_inlined_call faddr 72 "__System::LStrToPChar__"
         && is_named_dll_call faddr 78 "CreateFileA" then
	let fname = "FileOpen" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 33 in
	  let msg =
            LBLOCK [
                STR " with flags "; flags#toPretty;
		STR " and creation disposition "; INT disp;
		STR " and security attributes "; INT secr;
		STR " and fmconst1 "; fmConst1#toPretty;
		STR " and fmconst2 "; fmConst2#toPretty] in
	  sometemplate ~msg sem
	else None
      else None
  };

  (* FileWrite (V01a:0x408bb8) *)
  { regex_s =
      Str.regexp
        ("535657518bf98bf28bd86a008d44240450575653e8\\(........\\)85c07507c70424"
         ^ "ffffffff8b04245a5f5e5bc3$");

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_dll_call faddr 20 "WriteFile" then
	let fname = "FileWrite" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 23 in
	  sometemplate sem
	else None
      else None
  };

  (* GetLocaleChar (V01a:0x40ba64) *)
  { regex_s =
      Str.regexp
        ("535657518bd98bf28bf86a028d442404505657e8\\(........\\)85c07e058a0424eb"
         ^ "028bc35a5f5e5bc3$");

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_dll_call faddr 19 "GetLocaleInfoA" then
	let fname = "GetLocaleChar" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 23 in
	  sometemplate sem
	else None
      else None
  };

  (* StrCharLength (V01a:040cde0) *)
  { regex_s = Str.regexp
      ("538bd8803d50\\(........\\)740a53e8\\(........\\)2bc35bc3b8010000005bc3$");

    regex_f = fun faddr fnbytes fnhash ->
      if is_named_dll_call faddr 13 "CharNextA" then
	let cmpsite = todw (Str.matched_group 1 fnbytes) in
	let fname = "StrCharLength" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 12 in
	  let msg = LBLOCK [STR " with comparison site "; cmpsite#toPretty] in
	  sometemplate ~msg sem
	else None
      else None
  };

  (* StrMove (V01a:0x409080) *)
  { regex_s = Str.regexp ("568bf092e8\\(........\\)8bc65ec3$");

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_lib_call faddr 4 "Move" then
	let fname = "StrMove" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 7 in
	  sometemplate sem
	else None
      else None
  };

  (* StrMove (V1da:0x408a60) *)
  { regex_s = Str.regexp ("5189042492e8\\(........\\)8b04245ac3$");
    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_lib_call faddr 5 "Move" then
	let fname = "StrMove" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 7 in
	  sometemplate sem
	else None
      else None
  };



  (* StrNextChar (V01a:0x40ce00) *)
  { regex_s = Str.regexp "50e8\\(........\\)c3$";

    regex_f = fun faddr _fnbytes fnhash ->
      if is_named_dll_call faddr 1 "CharNextA" then
	let fname = "StrNextChar" in
	if function_summary_library#has_lib_function pkgs fname then
	  let sem = mk_libfun_semantics pkgs fname fnhash 3 in
	  sometemplate sem
	else None
      else None
  }

]
