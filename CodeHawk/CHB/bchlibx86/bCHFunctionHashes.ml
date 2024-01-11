(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny Sipma
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

(* chutil *)
open CHLogger

module H = Hashtbl

let table = H.create 23

let fnhashes = [

  ("CPtoLCID",
   [ ("eb7c383baa08d746ee75aa138d3f99de", 18)]);            (* V007: 0x445132 *)

  ("FindPESection",
   [ ("3306fea76897df3c506584532e5a8ea8", 33);              (* V494: 0x40b7b0 *)
     ("68056bd08d9d0eeaaffe7e437e429d2f", 33);
     ("96fdfa25cb16807090c1a60eabf4a5b4", 33);              (* V02c: 0x40c4f0 *)
     ("fac3566ba1c13ed740d3be79166016b5", 33);
     ("364e6b5ae8e1f535efce7ef26f845399", 29)]);         (* V0521d9: 0x453ff0 *)

  ("GetPrimaryLen",
   [ ("e542c4d73d3653aa7aad8247b36b6a8a", 13);           (* Vc416ff: 0x46f864 *)
     ("1a7f0a1faff957a7ede49827e79a7c07", 23);              (* V09e: 0x43e4c3 *)
     ("d8517e969c34a65dcff13ef2eb5d0bc9", 18)]);         (* V108d14: 0x41e7ba *)

  ("_LcidFromHexString",
   [ ("3854e799372886972ead9cdfeeaec226", 33)]);            (* V008: 0x42000e *)

  ("MD5Init",
   [ ("25a433d4e250827c2343dad4d689e476", 8)]);             (* V030: 0x806cd1 *)

  ("System::AStrCmp", (* Delphi *)
   [ ("185e45d24958ad6c5099b5c25a309299", 56)]);            (* V01a: 0x402cd4 *)

  ("System::_CLenToPasStr",  (* Delphi *)
   [ ("7a05fc3f003bcbede77d6c3015447139", 18)]);            (* V1da: 0x402fd0 *)

  ("System::Copy",  (* Delphi *)
   [ ("a4fe2a5cfa56103792f2f24fb5ba1561", 32)]);            (* V01a: 0x402874 *)

  ("System::EXP",   (* Delphi *)
   [ ("6854a056ae0804a99ba6a3a9eb7d7b67", 12)]);            (* V01a: 0x402ae8 *)

  ("System::FillChar", (* Delphi *)
   [ ("01495b7398e0d596fdb2cfe8aeaeea61", 15)]);            (* V01a: 0x402d44 *)

  ("System::Get8087CW",  (* Delphi *)
   [ ("4419e9eee8a3958c8f13aa2d92620a39", 4)]);             (* V01a: 0x402ae0 *)

  ("System::InitImports",  (* Delphi *)
   [ ("983a85c93a0722b0964f271fe4094cfd", 18)]);            (* V1da: 0x404034 *)

  ("System::IntfAddRef",  (* Delphi *)
   [ ("9de067dd7ba0341cf026d6a88bd2de5c", 6)]);             (* V01a: 0x405b84 *)

  ("System::IntfCopy",   (* Delphi *)
   [ ("e97ccd25e34e32a714d3d1ee73d31b4c", 25)]);            (* V01a: 0x405b28 *)

  ("System::LStrAddRef",   (* Delphi *)
   [ ("e2e4a17e3d634dee00cf9744452c6233", 8)]);             (* V1da: 0x40479c *)

  ("System::LStrCmp", (* Delphi *)
   [ ("23bf95961be3ce25595b58665e1a6c77", 75)]);            (* V01a: 0x4045c4 *)

  ("System::LStrPos", (* Delphi *)
   [ ("ec79e63dcb8db41e93ceb2a005c196c4", 42)]);            (* V01a: 0x4047bc *)

  ("System::Move", (* Delphi *)
   [ ("c8082197dc6b9a2f24d973ce16683d8c", 32)]);            (* V8af: 0x40265c *)

  ("System::PStrCmp", (* Delphi *)
   [ ("4ca3ef6fccd4199e35265b3f8508458f", 66)]);            (* V01a: 0x402c50 *)

  ("System::ROUND", (* Delphi *)
   [ ("d69492e88a5718b71d5b34099ad3d8f5", 6)]);             (* V01a: 0x402b00 *)

  ("System::SetElem",   (* Delphi *)
   [ ("d504a9f352a457dc0d87511db895f1a6", 19)]);            (* V01a: 0x402e68 *)

  ("System::SetEq",  (* Delphi *)
   [ ("b1ed2ec21524c71591df3025a7749ad9", 9)]);             (* V01a: 0x402ee4 *)

  ("System::SetRange",   (* Delphi *)
   [ ("3bd32b5d959220e1bef2573d50bd3834", 44)]);            (* V01a: 0x402e8c *)

  ("System::SetSub",   (* Delphi *)
   [ ("000b732597e71a2121a1d0d4fb3f4c7b", 8)]);             (* V01a: 0x402f04 *)

  ("System::SetUnion",   (* Delphi *)
   [ ("d4e3bccc7b882275fbe7b0aa0b368941", 7)]);             (* V01a: 0x402ef8 *)

  ("System::StrLen",   (* Delphi *)
   [ ("3f3d245fd827b42ff75949bd77c119a9", 4)]);              (* V8af:0x403f28 *)

  ("System::TRUNC",   (* Delphi *)
   [ ("4e4ee118240f2366fc39b5ca67f65c5f", 13)]);            (* V01a: 0x402b0c *)

  ("System::UpCase",   (* Delphi *)
   [ ("90d9188460c5a66c5b0cc7a0619838db", 6)]);             (* V01a: 0x402ac4 *)

  ("System::ValLong",   (* Delphi *)
   [ ("53624ad4bcd014d5276ab05b392555a0", 100);             (* V01a: 0x402d64 *)
     ("644742ee88c6dd793699e1f27ac89d5a", 97)]);            (* V073: 0x403390 *)

  ("System::WStrCmp",   (* Delphi *)
   [ ("5bf4432a4b3e10f024087649e3a041bc", 61)]);            (* V01a: 0x404a58 *)

  ("System::WStrLen",   (* Delphi *)
   [ ("ff41d3d352405142c298ae47b896cc85", 5)]);             (* V01a: 0x404a04 *)

  ("System::SysUtils::CompareStr",    (* Delphi *)
   [ ("7a90551eb102fa8f7a6ad62cebc12cb1", 23)]);            (* V01a: 0x408458 *)

  ("System::SysUtils::StrComp",    (* Delphi *)
   [ ("63b4b8dfcb10353c6824b4965e6620c1", 17)]);            (* V01a: 0x409130 *)

  ("System::SysUtils::StrCopy",    (* Delphi *)
   [ ("50373700d2c604092a111f304c1488ed", 28)]);            (* V01a: 0x4090b8 *)

  ("System::SysUtils::StrEnd",     (* Delphi *)
   [ ("eb49e9275eff6fafbda2e909b3b4db58", 8)]);             (* V01a: 0x40906c *)

  ("System::SysUtils::StrIComp",   (* Delphi *)
   [ ("0ab9f09f7596e858ee0545d74b7f9746", 29)]);            (* V01a: 0x409154 *)

  ("System::SysUtils::StrLComp",   (* Delphi *)
   [ ("ffa9864bee9d1134fc0dd756ec2eeb6a", 22)]);            (* V01a: 0x409194 *)

  ("System::SysUtils::StrLen",     (* Delphi *)
   [ ("9419f994914d56ea50d48092f35e095c", 9);               (* V01a: 0x409054 *)
     ("6175baf5f0053dea6023a7747de5b25e", 9)]);             (* V073: 0x4081bc *)

  ("System::SysUtils::StrLIComp",  (* Delphi *)
   [ ("b52548768589f2a8b3a69efce1b9f51b", 34)]);            (* V01a: 0x4091bc *)

  ("System::SysUtils::StrPos",     (* Delphi *)
   [ ("123eda6b3977f23a981c362b482e22a9", 42)]);            (* V01a: 0x409214 *)

  ("System::TObject::ClassDestroy",  (* Delphi *)
   [ ("d437f4bf44fa0bb27199419f6c3b6160", 3)]);             (* V01a: 0x40373c *)

  ("System::TObject::ClassInfo",  (* Delphi *)
   [ ("4020d9c4822c883c2691b57c1556b5ae", 3);               (* V01a: 0x403608 *)
     ("cb28eb932c6141fe85601f9ab9c125dd", 7)]);             (* V1da: 0x403728 *)

  ("System::TObject::ClassName",  (* Delphi *)
   [ ("ebf081e491df4e8fe9656504ee72ff82", 11)]);            (* V01a: 0x403318 *)

  ("System::TObject::ClassNameIs",   (* Delphi *)
   [ ("ef64d08fcc97d880fd0536e23d046fb0", 20)]);            (* V1da: 0x403440 *)

  ("System::TObject::ClassParent",  (* Delphi *)
   [ ("a6a2ad420473d03034a96615269bdcd2", 5)]);             (* V01a: 0x403354 *)

  ("System::TObject::ClassType",    (* Delphi *)
   [ ("af33672e73e4d302616d909157181d3e", 6);               (* V1da: 0x403420 *)
     ("bd859b45cdc0733e946c7ef7150db33e", 4)]);             (* V01a: 0x403310 *)

  ("System::TObject::FieldAddress", (* Delphi *)
   [ ("cbad81eec6ccf221d2d526f1a67b91ff", 40)]);            (* V01a: 0x40369c *)

  ("System::TObject::Free",   (* Delphi *)
   [ ("4537bb06f56667f04f3d0f8621b29854", 6)]);             (* V01a: 0x4033c8 *)

  ("System::TObject::GetInterfaceEntry", (* Delphi *)
   [ ("024f377b9d3c8ea9500882cd1d8866db", 32)]);            (* V1da: 0x403630 *)

  ("System::TObject::InheritsFrom",  (* Delphi *)
   [ ("d501e41fd3827af8eeee89cb472d780c", 10)]);            (* V01a: 0x4035f4 *)

  ("System::TObject::InitInstance", (* Delphi *)
   [ ("b7e35f2a517c821f9cccf1d60ef43ea9", 45)]);            (* V01a: 0x4033d4 *)

  ("System::TObject::InstanceSize",  (* Delphi *)
   [ ("2b2aadb0511a8ec0ec3effa09cb05fef", 3)]);             (* V01a: 0x403390 *)

  ("System::TObject::MethodAddress", (* Delphi *)
   [ ("8103e4610d57ff4dbd658d08fafbc306", 38)]);            (* V01a: 0x40364c *)

  ("System::TObject::MethodName", (* Delphi *)
   [ ("47b875c77c83d89c2d0a0eac51c7e3a9", 33)]);            (* V5b7: 0x403d40 *)

  ("System::Types::Rect",    (* Delphi *)
   [ ("4dbf97e160dabf26a77f709da5a78fe1", 12)]);            (* V01a: 0x406358 *)

  ("ValidateImageBase",
   [ ("1b6947e7b97b1d83c19651ab6a9a7b24", 19);              (* Vc13: 0x40ad80 *)
     ("b969cdbaa720e3eb29aaba2725e5a774", 21)]);            (* V007: 0x44ba20 *)

  ("_abstract_cw",
   [ ("a22f9bae3086502da1f3ba19916eccb3", 59);             (* nginx: 0x589dd7 *)
     ("cdd3c9cbdff71e17bb8a70db0de0a469", 60)]);           (* nginx: 0x589dd5 *)

  ("_abstract_sw",
   [ ("431d85e6aa67a9fed5bcd590ad3e8a71", 28);             (* nginx: 0x589f02 *)
     ("b101a1fb490712464343488b508ea06b", 27)]);           (* nginx: 0x58a087 *)

  ("alldiv",
   [ ("650b1c3a88bc03163222fbfd32e81d04", 70)]);         (* V03be08: 0x4048c0 *)

  ("alldvrm",
   [ ("f4d85c5e935cb43e4dfa60c577592078", 91)]);            (* Vb4b: 0x409be0 *)

  ("allmul",
   [ ("f3428811d26780c07ca0d255ff45ff0b", 19)]);            (* V02c: 0x40db20 *)

  ("alloca",
   [ ("11e41922ff27869c267f0226b448d937", 19);              (* Vb4b: 0x40dc40 *)
     ("3cf883d8801ed5ce98d7a358fe01e0c8", 19); (* bind9:libirs.dll:0x10005230 *)
     ("d9fd5da9ba4d793a57eec03378c22267", 17);              (* V225: 0x402390 *)
     ("ea9e1808f313809c4630d7c5daab76d4", 17)]);            (* V944: 0x403c30 *)

  ("allrem",
   [ ("1661afbabd6431a8181f385f68edb67e", 69)]);         (* V03be08: 0x4094e0 *)

  ("allshl",
   [ ("86aee56a335d8d457990da457cbb4642", 15)]);           (* putty: 0x44bd80 *)

  ("allshr",
   [ ("238b0ab55789e99faaf18e055db162b0", 15)]);            (* V102: 0x41d000 *)

  ("ascii_stricmp",
   [ ("b7d09b2b5fe193689c79b65e5c675823", 40);           (* V03be08: 0x40b1e0 *)
     ("c7e37a670642508aeabd1d3d63a5ad30", 28);
     ("e4f380ab6325a85ce6791b7c0d1241a3", 24)]);         (* V0521d9 :0x46240d *)

  ("ascii_strnicmp",
   [ ("0959f39b148a9c7c71b7af2ed512c574", 48);           (* V03be08: 0x40c1d0 *)
     ("20b7f8fee14db3a23a80237e8274ddaf", 48)]);            (* V02c: 0x4081a0 *)

  ("aulldiv",
   [ ("10de0f56a97ab5b92ce16346c2542ca3", 43)]);            (* V02c: 0x40b7f0 *)

  ("aulldvrm",
   [ ("e81e3deeaf3801a6c1588a7f198b3150", 58)]);            (* V0c3: 0x43c9e0 *)

  ("aullshr",
   [ ("ec54a0b1e2e82119be88dea7b5eeeef7", 15)]);            (* Vb4b: 0x409cc0 *)

  ("_clrfp",
   [ ("2ed21a8a2ff8825288a9b999a82acb40", 8);              (* nginx: 0x58b05c *)
     ("40484c4aaa13a8572dc4a949c96d1bd7", 9);               (* V008: 0x41932d *)
     ("a18959dbb70bf0b7899cc2c26c16f0d4", 9)]);             (* V007: 0x44f677 *)

  ("_ctrlfp",
   [ ("0ff85ac05254e15c97fe4c70dd560c1f", 18);              (* V008: 0x41933e *)
     ("c7283de5e11dc9d2055214e9385d9990", 18);              (* V007: 0x44f688 *)
     ("d4a49637115a0b84efdd68d2adf0e670", 17)]);             (* nginx: 58b06d *)

  ("__checkTOS_withFB",
   [ ("22f90aa4f7f5ba46f6d5ee6273f6bae7", 7)]);             (* V008: 0x41cb78 *)

  ("dtold",
   [ ("50edff60cab0694f86fd34a910e73852", 75);              (* V008: 0x420d57 *)
     ("0e33506a13ad6b31e08d2595bf566671", 73);              (* V007: 0x452383 *)
     ("b4db47b34c4090086dac2b048b5b0ea8", 69)]);           (* nginx: 0x5845ef *)

  ("_errcode",
   [ ("fde85c41db9b9dfa4c774d70e91b5f91", 29)]);            (* V007: 0x44f31c *)

  ("fastcopy_I",
   [ ("b89d9fdf956ad1e6ede97f78381b98b0", 35)]);          (* V2bd: 0x10011c9e *)

  ("fastzero_I",
   [ ("eec093ed846285d92d0134521623aa9b", 24)]);          (* V2bd: 0x10017a66 *)

  ("__fload_withFB",
   [ ("1359245be0243c37e1d78e9c27a11b3b", 21)]);            (* V008: 0x41cb35 *)

  ("_frnd",
   [ ("6849b8ef90cf574e537c8b7f30407ab2", 11)]);            (* V007: 0x44f50e *)

  ("ftol",
   [ ("350e22b1dd8384e07c8791407f97b5e2", 16)]);            (* V3f7: 0x447f78 *)

  ("ftol2",
   [ ("c0247487f14c543d5604b51e258f5b64", 37)]);            (* V007: 0x4541c6 *)

  ("hw_cw",
   [ ("251e0d2baacbf7ae5e58f3d2bc859e33", 49);             (* putty: 0x452a1b *)
     ("32dd72fd7de15972185c1ea6fae115c0", 49);            (* V2bd: 0x1001c18d *)
     ("642263f504362662deabb4f620676373", 53);              (* V01e: 0x4160f3 *)
     ("faff52876c9ae8f07774c91215bc2d70", 55)]);            (* V008: 0x4239eb *)

  ("hw_cw_sse2",
   [ ("8ae682317791f0be64beacf6546728c8", 62);              (* V008: 0x423640 *)
     ("d0bcda2758e75868d3b0d31fd10b6836", 56);            (* V2bd: 0x1001c21b *)
     ("6dc29bb0345ccd6b4feb5520dbdfb6d0", 56)]);         (* V0521d9: 0x463a01 *)

  ("_initterm",
   [ ("58f5baa6ba59685323a1ffd6ee587ab0", 15);              (* V8c4: 0x408a0a *)
     ("211c736b3f55b913c8d8fed0bb4229e8", 12)]);       (* Vf953df: 0x100014d4 *)

  ("__load_CW",
   [ ("0ac550beba4719178d68b5bd7e2c35a6", 6)]);             (* V008: 0x41cb05 *)

  ("lstrcpyn",
   [ ("eefb6c0917de2d0977ef7546f7567d7a", 10)]);          (* Vf92: 0x100028d4 *)

  ("memchr0",
   [ ("a70dfa1636e4cd9d801d636f6fe4bebe", 76)]);   (* cdecl, V2bd: 0x1000d530 *)

  ("memchr",
   [ ("856d3128f58d97dc4b6b32dee24ee48c", 76)]);            (* V01e: 0x40e820 *)

  ("memcmp",
   [ ("199624450972643104cf6afd5a5b80c1", 78);             (* putty: 9x44bba0 *)
     ("1b1abb4aa433874bf9bbc96c4804dac7", 1935);            (* V007: 0x4416f2 *)
     ("450e930a82a38fda82bd0a47bdb89bdd", 78);              (* V808: 0x405470 *)
     ("615966c6c20b535aef2b346fef2eb975", 1935);            (* V03e: 0x412ef3 *)
     ("91e789f5783d29cea0b878fec8efeabe", 1773);            (* V068: 0x42ce04 *)
     ("e21bea52cb57ba5a0482d0d33d7a6104", 1773);            (* V008: 0x413ab8 *)
     ("8b551f2749d120f7f34c2248a0b41ebc", 1934);            (* V07b: 0x44dd9a *)
     ("2b38742e62c920a66e6d9c5024a608b7", 1934);         (* V098f4f: 0x44f41a *)
     ("8bc829abe1650b3488120aa821971488", 1786);         (* V0988d3: 0x414eb4 *)
     ("2010d705ca81170bec84460239f4b786", 1773);            (* V09e: 0x41ee2b *)
     ("8acf793120442457c37b8849cc87d034", 1935);            (* V102: 0x41a2f4 *)
     ("5c0d956aba98c0a5dcb40589f6c15d6b", 1773)]);       (* V108d14: 0x4125c8 *)

  ("memcpy",
   [ ("2462fbafd355d1f65d985cfa863781e8", 153);            (* putty: 0x449850 *)
     ("441339b407be6fc32f2dcda895354fb8", 153);          (* V00bcd1: 0x409ea0 *)
     ("50099ebb7bffdca7cf630df3a4cacefc", 258);             (* V02c: 0x40af70 *)
     ("514049de37f11387a5d6531f830045bc", 153);        (* Vf95d3f: 0x10003000 *)
     ("67dc58b619573f2d8dda67e6d936d943", 153);          (* Vf27414: 0x403af0 *)
     ("a50efeaebc31658417acfb35223492c8", 153);          (* V03be08: 0x402a80 *)
     ("abf9195957257359a860f3c8c8416a17", 153);        (* Vf95d3f: 0x100049e0 *)
     ("b8d5d14518439cff545a3afa8367005c", 153);             (* V304: 0x405600 *)
     ("bc081ce6a93b1786b421ebdc3ddad2c4", 153);        (* Vfc160a: 0x10002ba0 *)
     ("c23bebcf4a5d2fdc5ae00be62154a9e7", 153);          (* V03be08: 0x402dc0 *)
     ("c962606e940fb8d2a9946df762eb17e3", 153);             (* V3f7: 0x448a90 *)
     ("d7d7613900c19d1e2dbdafcc9c906c72", 153);             (* V01e: 0x40dcd0 *)
     ("f44fbf506f56758246b36ba31a1a5de9", 153);        (* Vfc160a: 0x100034d0 *)
     ("f1654b0ca57c1676ea5a5c79bd3e0557", 258);          (* V0988d4: 0x407b41 *)
     ("50420105d115c9ce65b3fde045500b0a", 258);           (* V0a390: 0x40a390 *)
     ("142a815a8506f23ae5a7863c30fd6f81", 258);             (* V10b: 0x404f60 *)
     ("218488954e972958d3d81e5de8c09a0d", 258)]);           (* V10b: 0x409600 *)

  ("memmove",
   [ ("1249acff9495a06b5d94901436e31a32", 360);             (* V3f7: 0x40a640 *)
     ("b0dca794c7d242aa09e7a488341cf8cf", 360);             (* V494: 0x40d0d0 *)
     ("b5b646fc09507e00a2e89336316627d7", 360);             (* V068: 0x424810 *)
     ("957e156100d94566238b6d76a57215f8", 360);             (* V09e: 0x4205b0 *)
     ("eeb7ea8b97c04be628a8cef97b5958e2", 360);             (* V09e: 0x420e80 *)
     ("8381a41e7e248712b9ce4ee5e605e75d", 360);          (* V108d14: 0x40de90 *)
     ("7efda9fd637bc30117f13a70c2c5fb1e", 360)]);        (* V108d14: 0x40e660 *)

  ("memset0",
   (* cdecl, m:mwc-00:V2bf: 0x405260 *)
   [ ("288307bd8761ce8527a61a8f71ac0e69", 127)]);

  ("memset",
   [ ("12dc057baa861b87aeb4b927fd04c2ee", 40) ;             (* V808: 0x406c40 *)
     ("1ce7dfeca1ed9b17f56b357a2cf68ade", 127);             (* V494: 0x40cec0 *)
     ("4c9ae5a57493337f2a1c46f5d63dd86e", 127);             (* V068: 0x426470 *)
     ("7e274e19ab90d366dc4747f1702e2d8a", 40) ;            (* putty: 0x4494e0 *)
     ("67237c2da175f8af2a30190b4bed997e", 127);             (* Vc13: 0x40c380 *)
     ("b537a659e179804e76958868b649af87", 127);          (* V0a29ae: 0x408c30 *)
     ("cab98610abdb1129785e2b41a5da426f", 127);             (* V3fc: 0x40a430 *)
     ("ce42dc85dbc958313854bfbfe7891b16", 127);             (* V008: 0x410890 *)
     ("eac8f9396de99ae2de11ebc06d492fc1", 120);             (* V02c: 0x40aef0 *)
     ("e1fe66d1eb7c176482f57cd0611b6120", 120);          (* V0988d4: 0x40fa20 *)
     ("e94d28eac265939b3d32acc7c1d11d07", 127);             (* V098: 0x420c80 *)
     ("1410ad22e56313e23f11b0856d33b8b2", 127);          (* V108d14: 0x40f4d0 *)
     ("4bc83e70c97d48e20b18e01122aa77b7", 120)]);           (* V10b: 0x4091c0 *)

  ("__mtold12",
   [ ("c67b024c9be62edb6b8be1cf5e00cc3e", 197);             (* V008: 0x423c84 *)
     ("fb26d20397d976a2c53b7514178d1836", 180)]);          (* nginx: 0x58ae30 *)

  ("positive",
   [ ("4ebe2d447ab0e0fc6dc188fc15474c79", 15);              (* V008: 0x41be08 *)
     ("667d05c1fbdeccb515b2ffbe0b302c9d", 15)]);            (* V007: 0x450c12 *)

  ("_statfp",
   [ ("157ff034acb738930a10ff87185e0a69", 9 );              (* V008: 0x4193c1 *)
     ("425c79712f8aaedfb063f4ad5a7513a7", 9 );              (* V007: 0x44f667 *)
     ("2358f0d649ddfc0ef768ddf4fabc5813", 8 )]);           (* nginx: 0x58b04c *)

  ("_statusfp",
   [ ("a4c1231c7cecb5e179575fc23af7690c", 63)]);           (* nginx: 0x58a0d6 *)

  ("sbh_resize_block",
   [ ("293320db45cefa03202b79e448bc1181", 256);           (* V2bd: 0x10012618 *)
     ("30486aaad11020265ecbc23f734fba98", 255);             (* V304: 0x404055 *)
     ("e37ceafcb435401fab40e04e75081f86", 259)]);           (* V01e: 0x413741 *)

  ("_set_exp",
   [ ("f83ec2230eb501dfba776a5d413bcafd", 18);              (* V008: 0x418d77 *)
     ("9d7be0dcf8281559c05c3e33cc005436", 17)]);            (* V007: 0x44f522 *)

  ("_sptype",
   [ ("4909c8a65caa86e672da218faa8dac64", 39)]);            (* V007: 0x44f54e *)

  ("strcat",
   [ ("1b2b812ac9ec10c1888b1879cae22f35", 84);              (* V808: 0x40d9e0 *)
     ("d35fe4a1203f8e416910459870d1823b", 85)]);           (* putty: 0x44a130 *)

  ("strchr",
   [ ("54e1c94b6879eb9f1cb9f145c72308f8", 89);             (* putty: 0x449ba0 *)
     ("ada00dfc9885d8f2dcd331624834974e", 89);              (* V37f: 0x449790 *)
     ("da60d8112d9a7e8d7785aa032d0c8c23", 89)]);            (* Vcf8: 0x4297c0 *)

  ("strcmp",
   [ ("0a5163f221b0080776353bbb28835c9e", 53);           (* V0a29ae: 0x40e0a0 *)
     ("0b6acc4094170c3cad10bde435545dae", 54);             (* putty: 0x449c60 *)
     ("b702a01ecf0fb81ffeb8280f653c53ce", 54)]);            (* V01e: 0x414200 *)

  ("strcpy",
   [ ("7f343d3840a8289fcc9bb7f0b8e71356", 52);              (* V808: 0x40d9d0 *)
     ("b3719d0637c2b150f6e3e83d55a90bc3", 52)]);         (* V4aa27f: 0x44f5c0 *)

  ("strcspn",
   [ ("3bf2d07e65df5ed0bd31107f6b1aea76", 35);              (* V3f7: 0x44a250 *)
     ("83ea2383f90007e360b05ab193cd9bf9", 35)]);            (* V02c: 0x40d6f0 *)

  ("strlen",
   [ ("3aafcfeb55235bb8c618974f1a87a022", 44);              (* V3f7: 0x44a900 *)
     ("9573ef6241907f0e26e51a7b9c53eed1", 46)]);            (* V4b4: 0x403110 *)

  ("strncat",
   [ ("1b8dea6c4eff6ddab1f38b5ec7ee35c2", 123)]);          (* putty: 0x44d730 *)

  ("strncmp",
   [ ("076a2b11b47898c3acf581883d474e48", 78);           (* Vc416ff: 0x472bb8 *)
     ("1d2df6827659662bd8c39b7bcf7128f4", 44);              (* V068: 0x454db0 *)
     ("217fda5a7d49f50d5291d27b4c5359d8", 80);              (* V02c: 0x404a11 *)
     ("50e42474c2b4996f79a5d6e8c4ba5704", 31);              (* V3f7: 0x447e70 *)
     ("6d6bdf93c5b8553546c754b5df6c7601", 30);             (* putty: 0x449700 *)
     ("d3ea1670b713fd7c9434d27c1b7a87c9", 79)]);           (* V008:  0x443409 *)

  ("_strncnt",
   [ ("15edfddaa2e1f039cf2466c77dfb5928", 17);               (* V007 0x5437c2 *)
     ("27e6ee7413f1b58f140bd5d5217b24bf", 14);             (* putty: 0x4531dc *)
     ("6b95d0f085a963944e3c09cab553890d", 16);             (* nginx: 0x5836a7 *)
     ("c0ee367f01ccdf0129798df1adc1b782", 20);              (* V01e: 0x4154e5 *)
     ("c9f687d158782b620b9e499143ae457b", 25)]);         (* Vf27414: 0x402fb0 *)

  ("strncpy",
   [ ("59ca5fb0bf25953bb8e687cf5c6fdde2", 109);             (* V808: 0x405520 *)
     ("89c267f43b37e68a0db43a954146fea0", 109)]);          (* putty: 0x4495d0 *)

  ("strnlen",
   [ ("e181fe35a7a77ef19c0b2be1ea956ad2", 14);              (* V09e: 0x422cdd *)
     ("3ec12e9fc5a83266b1d83f90d2a91c7c", 11)]);            (* V12f: 0x41f8b9 *)

  ("strpbrk",
   [ ("fd53ff895d6d86d74ca9895710ec56e4", 33)]);            (* V02c: 0x40d740 *)

  ("strrchr",
   [ ("6c353eecb6d0f5556c09a507f0f42b3f", 116);             (* V008: 0x420b70 *)
     ("9865c1ee43a79fc3df08fe799ae67f05", 23);           (* Vc416ff: 0x46b600 *)
     ("acff7ac4410c4365808aa886fe9a2d41", 116);             (* V068: 0x443420 *)
     ("cd1854a5619dc83888f2d40cf916ce7c", 23);              (* V3f7: 0x449860 *)
     ("1a55972c9995966c964e246a986613c4", 116);             (* V09e: 0x43dad0 *)
     ("abb70ae77ad6f2db61c7c39185a81fd3", 116)]);        (* V108d14: 0x41f680 *)

  ("strspn",
   [ ("6bd75da91439945f314ac9ed9c3f184d", 35)]);         (* V03be08: 0x408790 *)

  ("strstr",
   [ ("11af324759972d345dd0a54f22e06cef", 153);             (* V007: 0x55b400 *)
     ("326b529f7803075f75c94a6180299ab1", 307);             (* V068: 0x437400 *)
     ("33dd3c50a37686c5fddb438bab787bf4", 153);             (* V053: 0x404060 *)
     ("3d90fbbe124957416430a7554d983e0e", 153);             (* V01e: 0x416b20 *)
     ("85ad2ac5707981a90014a22985e609c3", 153);             (* V3f7: 0x449660 *)
     ("b10532afd37a0444067d218747a71e26", 153);             (* V02c: 0x404300 *)
     ("20fbb8fb7960e6f688305a4347db7ce5", 307);             (* V09e: 0x42fcf0 *)
     ("8fb65994d41102a5689804458d346ee1", 153)]);           (* V12f: 0x4120b0 *)

  ("__wchartodigit",
    [ ("bd5768aaebfb148a078e98a4277f9691", 98);          (* V098864: 0x45f357 *)
      ("36f0e5f7888726f5871e4bf513a3b53c", 121)]);       (* V108d14: 0x41f062 *)

  ("wcscat",
   [ ("54d9dc44f95382351f28dd8063c7a06b", 20);           (* V4aa27f: 0x44d352 *)
     ("a6110e724eb3ae6b43223a7a0cca6677", 24)]);            (* V03e: 0x4129f3 *)

  ("wcscmp",
   [ ("1786e9e6a9b97b33fdf927586b3254a2", 26);           (* V098f4f: 0x44ef27 *)
     ("9c9d965fd9ca5d0fd132b8404e70bed7", 30);              (* V09e: 0x422cf8 *)
     ("a1037cad4abea940f11fbf712c6a5c5e", 31)]);            (* V102: 0x419e90 *)

  ("wcsncmp",
   [ ("517107f756504d3c539c43ef7523fd72", 26);              (* V07b: 0x44d98e *)
     ("a413c2f90ba0ed62a35d5c3eb0d7d98f", 25);           (* V0988d4: 0x41931e *)
     ("0b653cdf7333c9f9c66c7da6d5ec795d", 26);              (* V09e: 0x43e314 *)
     ("42b9b4285009f892cf84729310bd37a1", 27)]) ;           (* V102: 0x41c0d9 *)

  ("wcschr",
   [ ("169b7819146c74112a46b793b4d4aa25", 18);              (* V03e: 0x416abd *)
     ("32ebc747f4875a890ff811672c51c689", 64);              (* V068: 0x451722 *)
     ("36f1e038ec7b95d338160852a8cf7492", 64);              (* V008: 0x42177f *)
     ("76baa0de4769e222c64a229e8060d00a", 17);              (* V943: 0x434871 *)
     ("866afd91196c72a09c18bef7e27b1b1d", 14);           (* V0521d9: 0x4515a9 *)
     ("392b55921e25fc7859277b0d2f3322da", 64);              (* V09e: 0x44b8bd *)
     ("ae93a0a8020a6e0164c7f066538823e5", 64)]);         (* V108d14: 0x42028f *)

  ("wcscpy",
   [ ("0d974ad1c3493e66b8d2ed5df9906d20", 12);           (* V4aa27f: 0x44d37c *)
     ("96bc7f1b9125c3c5a10c1fd8b8a2246b", 16)]);            (* V03e: 0x412a21 *)

  ("wcscspn",
   [ ("13910752a3aed5af0e109050652fe000", 35)]);            (* V008: 0x41f340 *)

  ("wcsncat",
   [ ("e2f18f0f539349321b0ffadb4b634649", 30);           (* V098864: 0x44ff2f *)
     ("226b50922057c687493c5e68b0d35c6b", 32)]);            (* V102: 0x41cd55 *)

  ("wcsncpy",
   [ ("2ca7cf781e59b13c4cc73daa5e46536d", 31);           (* V098f4f: 0x45158d *)
     ("ace77338d9dac2916fc0610d7eede4f8", 39)]);            (* V102: 0x41c08f *)

  ("wcslen",
   [ ("087a932340912d201551af0a40a01357", 13);              (* V943: 0x433b6f *)
     ("0acc07fe6db2681c0d8cab1cfae499bf", 10);           (* Vc416ff: 0x479832 *)
     ("aa163f0ddb54c72b16e0d440cebbb069", 14);              (* V007: 0x444c0d *)
     ("c72f5862b51f1b13b20e1bbd6221f648", 12);           (* V0a29ae: 0x411512 *)
     ("ffc40a450081d3656e864cd696e5ec74", 13)]) ;           (* V3f7: 0x44a795 *)

  ("wcsnicmp_ascii",
   [ ("80cd08aa5a259f87cfacbc0f14dde29e", 51)]);            (* V3fc: 0x40a5c6 *)

  ("wcsspn",
   [ ("c4578bd4c27e9e9587f8f628a3304ad9", 32)]);            (* V09e: 0x422dfc *)

  ("wcsstr",
   [ ("c70b3039018190dc3f5089ad1dacc6f4", 41);              (* V07b: 0x44dc06 *)
     ("2572f81f5eb3e4543db53f162b0d945e", 221);             (* V09e: 0x4226b2 *)
     ("e8fb0b8d04ad4783a92da9a46ffe6b7a", 221);          (* V108d14: 0x40ff79 *)
     ("6175c9d7449ac3f8c4c98c38f8528798", 41)]);            (* V12f: 0x46e097 *)

  ("wcsnlen",
   [ ("2dcc70be604deab2c27a2e0a7725505c", 15);           (* V0a29ae: 0x40851b *)
     ("e9b86118a2ee7302f6dcfefd29c07eed", 15)]);         (* V0988d4: 0x416aa6 *)

  ("wcspbrk",
   [ ("b48044a42f2c7eb229e75fa545fe60d4", 30);           (* V098864: 0x4515cb *)
     ("ac8d2219f8ee3558fb88e572aef0e75e", 31);           (* V108d14: 0x41ded1 *)
     ("1f69364c81180fc2768ea803dc44c4b1", 34)]);            (* V102: 0x41c1e9 *)

  ("wcsrchr",
   [ ("dedda078411ec5699ff6e7a9584df903", 21);           (* V098864: 0x45160a *)
     ("6c03509d5fd735e260cf12b1df9e301c", 22)]);            (* V102: 0x41c252 *)

  ("wmemset",
   [ ("209f6689f33899e4d2d7813b930d8fa7", 20);           (* V0a29ae: 0x4087b0 *)
     ("e2c6bb53696a0828cd2e131b803fc6f6", 21)])             (* V943: 0x43377d *)
]


let _ = List.iter (fun (name,lst) -> H.add table name lst) fnhashes


let get_function_hashes (name:string) =
  if H.mem table name then H.find table name else
    begin
      chlog#add "function hashes" (LBLOCK [ STR name; STR " not found"]);
      []
    end
