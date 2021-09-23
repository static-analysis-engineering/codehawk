(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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
open CHCommon
open CHPretty

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHParse

(* jchpre *)
open JCHApplication
open JCHBcPattern
open JCHClassLoader
open JCHPreAPI
open JCHPreFileIO
open JCHPreSumTypeSerializer
open JCHSystemSettings

module H = Hashtbl


let methodcount = ref 0
let maxlog = ref 24
let maxmatch = ref 24
let outputname = ref ""
let md5 = ref ""
let jarname = ref ""
let native_method_count = ref 0

let speclist =
  [("-o", Arg.String (fun s -> outputname := s), "name of outputfile");
   ("-md5", Arg.String (fun s -> md5 := s), "md5 hash of jarfile") ;
   ("-maxmatch", Arg.Int (fun i -> maxmatch := i),
    "maximum length of method to be matched");
   ("-maxlog", Arg.Int (fun i -> maxlog := i),
    "maximum length of method to be logged")]

let usage_msg = "chj_patterns -md5 <md5 of jarfile> -o <outputfile> <jarfile>"

let read_args () = Arg.parse speclist   (fun s -> jarname := s) usage_msg

let _ = system_settings#disable_logging_missing_classes
  
let categorize_patterns plist =
  let basicvalues = ref [] in
  let objectvalues = ref [] in
  let actions = ref [] in
  let patterns = ref [] in
  let exceptions_ignored = H.create 3 in
  let add_exception e =
    let entry =
      if H.mem exceptions_ignored e#index then
        H.find exceptions_ignored e#index
      else
        0 in
    H.replace exceptions_ignored e#index (entry + 1) in
  let get_exceptions_ignored () =
    let lst =
      H.fold
        (fun k v a -> ((retrieve_cn k)#name, v) :: a) exceptions_ignored [] in
    List.sort (fun (_,v1) (_,v2) -> Stdlib.compare v1 v2) lst in
  let exceptions_handled = H.create 3 in
  let add_exception_handled e =
    let entry =
      if H.mem exceptions_handled e#index then
        H.find exceptions_handled e#index
      else
        0 in
    H.replace exceptions_handled e#index (entry + 1) in
  let get_exceptions_handled () =
    let lst =
      H.fold
        (fun k v a -> ((retrieve_cn k)#name, v) :: a) exceptions_handled [] in
    List.sort (fun (_,v1) (_,v2) -> Stdlib.compare v1 v2) lst in
  let rec add_basic_value a =
    let _ = basicvalues := a :: !basicvalues in
    match a with
    | BcvArrayElement (_,base,index) ->
       begin add_object_value base ; add_basic_value index end
    | BcvThatField (_,_,base) -> add_object_value base
    | BcvArrayLength base -> add_object_value base
    | BcvInstanceOf (_,base) -> add_object_value base
    | BcvBinOpResult (_,a1,a2) ->
       begin add_basic_value a1 ; add_basic_value a2 end
    | BcvUnOpResult (_,a) -> add_basic_value a
    | BcvQResult (_,aa,fa,ta) ->
       begin
         List.iter add_value aa ;
         add_basic_value ta ;
         add_basic_value fa
       end
    | BcvConvert (_,a1) -> add_basic_value a1
    | BcvCallRv c -> add_call_result c
    | _ -> ()
  and add_object_value a =
    let _ = objectvalues := a :: !objectvalues in
    match a with
    | BcoNewObject (_,args) -> List.iter add_value args
    | BcoNewArray (_,len) -> add_basic_value len
    | BcoMultiNewArray (_,dims) -> List.iter add_basic_value dims
    | BcoArrayElement (_,base,index) ->
       begin add_object_value base ; add_basic_value index end
    | BcoThatField (_,_,base) -> add_object_value base
    | BcoCheckCast (_,base) -> add_object_value base
    | BcoQResult (_,aa,fa,ta) ->
       begin
         List.iter add_value aa ;
         add_object_value ta ;
         add_object_value fa
       end
    | BcoCallRv c -> add_call_result c
    | _ -> ()
  and add_value a =
    match a with
    | BcObject v -> add_object_value v
    | BcBasic v -> add_basic_value v
  and add_call_result c =
    begin
      (match c.bcp_base_object with Some b -> add_object_value b | _ -> ()) ;
      List.iter add_value c.bcp_args
    end
  and add_action a =
    let _ = actions := a :: !actions in
    match a with
    | BcNewObject (_,args) -> List.iter add_value args
    | BcDropValues vv -> List.iter add_value vv
    | BcPutThisField (_,_,v) -> add_value v
    | BcPutThatField (_,_,b,v) ->
       begin add_object_value b ; add_value v end
    | BcPutStaticField (_,_,v) -> add_value v
    | BcArrayStore (_,b,i,v) ->
       begin add_object_value b ; add_basic_value i ; add_value v end
    | BcConditionalAction (_,vl,aa1,aa2) ->
       begin
         List.iter add_value vl ;
         List.iter add_action aa1 ;
         List.iter add_action aa2
       end
    | BcWrapCall c -> add_call_result c
    | BcThrow v -> add_object_value v
    | _ -> ()
  and  add_pattern p =
    let _ = patterns := p :: !patterns in
    match p with
    | BcpAction aa -> List.iter add_action aa
    | BcpResult (aa,v) ->
       begin List.iter add_action aa ; add_value v end
    | BcpThrow (aa,v) ->
       begin List.iter add_action aa ; add_object_value v end
    | BcpInfiniteLoop aa -> List.iter add_action aa
    | BcpResultExcept (e,aa,v1,v2) ->
       begin
         add_exception e ;
         List.iter add_action aa ;
         add_value v1 ;
         add_value v2
       end
    | BcpResultExceptThrow (e,aa,v1,v2) ->
       begin
         add_exception_handled e ;
         List.iter add_action aa ;
         add_value v1 ;
         add_object_value v2
       end
    | BcpActionExcept (e,aa) ->
       begin add_exception e ; List.iter add_action aa end
    | BcpActionExceptThrow (e,aa,v) ->
       begin
         add_exception_handled e ;
         List.iter add_action aa ;
         add_object_value v
       end
    | _ -> () in
  let _ = List.iter add_pattern plist in
  let countlist l serializer =
    let t = H.create 3 in
    let _ =
      List.iter (fun a ->
          let tag = serializer#to_string a in
          let entry = if H.mem t tag then H.find t tag else 0 in
          H.replace t tag (entry + 1)) l in
    let counts = H.fold (fun k v a -> (k,v) :: a)  t [] in
    List.sort (fun (_,v1) (_,v2) -> Stdlib.compare v1 v2) counts in
  (countlist !basicvalues bc_basicvalue_serializer,
   countlist !objectvalues bc_objectvalue_serializer,
   countlist !actions bc_action_serializer,
   countlist !patterns bc_pattern_serializer,
   get_exceptions_ignored (),
   get_exceptions_handled ())
  
let write_xml_values node values =
  node#appendChildren
    (List.map (fun (k,v) ->
         let n = xmlElement "n" in
         begin
           n#setAttribute "k" k ;
           n#setIntAttribute "v" v ;
           n
         end) values)

let write_xml_method_counts node =
  let lst = ref [] in
  let patterncount = ref 0 in
  let _ = for i = 1 to !maxmatch do
            let x = get_methodsize_count i in
            let y = get_methodsize_no_pattern_count i in
            let y = x - y in
            let _ = patterncount := !patterncount + y in
            lst := (i,x,y) :: !lst
          done in
  begin
    node#appendChildren
      (List.map (fun (i,t,p) ->
           let n = xmlElement "n" in
           let seti = n#setIntAttribute in
           begin
             seti "i" i ;
             seti "t" t ;
             seti "p" p ;
             n
           end) (List.rev !lst)) ;
    node#setIntAttribute "patterns" !patterncount
  end

let write_xml_unknown_attributes node =
  let lst = get_unknown_attributes () in
  node#appendChildren
    (List.map (fun (k,v) ->
         let n = xmlElement "n" in
         begin
           n#setAttribute "k" k ;
           n#setIntAttribute "v" v ;
           n
         end) lst)

let write_xml_packages node =
  let thispackages = get_this_packages () in
  let callpackages = get_call_packages () in
  let jnode = xmlElement "this-jar" in
  let cnode = xmlElement "calls" in
  let writelist pn l =
    pn#appendChildren (List.map (fun (k,v) ->
        let n = xmlElement "n" in
        begin
          n#setAttribute "k" k ;
          n#setIntAttribute "v" v ;
          n
        end) l) in
  begin
    writelist jnode thispackages ;
    writelist cnode callpackages ;
    node#appendChildren [ jnode ; cnode ]
  end                      

let write_xml_patterns node count patterns =
  let (basicvalues,objectvalues,actions,patterns,xi,xh) =
    categorize_patterns patterns in
  let loopcount = get_loop_count () in
  let dyncount = get_dynamiccount () in
  let bnode = xmlElement "basic" in
  let onode = xmlElement "object" in
  let anode = xmlElement "actions" in
  let pnode = xmlElement "patterns" in
  let xnode = xmlElement "x-ignored" in
  let hnode = xmlElement "x-handled" in
  let unode = xmlElement "unknown-attributes" in
  let cnode = xmlElement "method-counts" in
  let pknode = xmlElement "packages" in
  begin
    write_xml_values bnode basicvalues ;
    write_xml_values onode objectvalues ;
    write_xml_values anode actions ;
    write_xml_values pnode patterns ;
    write_xml_values xnode xi ;
    write_xml_values hnode xh ;
    write_xml_method_counts cnode ;
    write_xml_unknown_attributes unode ;
    write_xml_packages pknode ;
    cnode#setIntAttribute "total" count ;
    (if !native_method_count > 0 then
       cnode#setIntAttribute "native" !native_method_count) ;
    (if loopcount > 0 then
       cnode#setIntAttribute "hasloops" loopcount) ;
    (if dyncount > 0 then
       cnode#setIntAttribute "dynamic" dyncount) ;
    node#appendChildren
      [ bnode ; onode ; anode ; pnode ; xnode ; hnode ; cnode ; unode ; pknode ]
  end

let save_jar_patterns f count patterns =
  let doc = xmlDocument () in
  let root = get_jch_root "patterns" in
  let filename = !outputname ^ "_px.xml" in
  let node = xmlElement "patterns" in
  begin
    doc#setNode root ;
    write_xml_patterns node count patterns ;
    root#appendChildren [ node ] ;
    node#setAttribute "md5" !md5 ;
    node#setAttribute "jarname" (Filename.basename f) ;
    file_output#saveFile filename doc#toPretty
  end

let process_jar f =
  let _ = app#reset in
  let _ = load_classes_in_jar f in
  let _ = pr_debug [ STR "Process classes ..." ; NL ] in
  let _ = process_classes () in
  let (count,patterns) =
    List.fold_left (fun (acc,accp) mInfo ->
        if mInfo#has_bytecode then
          let cn = mInfo#get_class_name in
          let cInfo = app#get_class cn in
          match get_pattern ~maxlog:!maxlog ~maxmatch:!maxmatch f mInfo cInfo with
          | Some a -> (acc+1,a::accp)
          | _ -> (acc+1,accp)
        else if mInfo#is_native then
          let _ = native_method_count := !native_method_count + 1 in
          (acc,accp)
        else
          (acc,accp)) (0,[]) app#get_methods in
  if count > 0 then
    save_jar_patterns f count patterns
  else
    pr_debug [ STR "No methods with bytecode found" ; NL ]

let noteworthy_to_pretty () =
  let noteworthy = get_noteworthy () in
  let p (m:(string *method_info_int)):pretty_t =
    let (jar,mInfo) = m in
    let cms = mInfo#get_class_method_signature in
    let opcodes = mInfo#get_bytecode#get_code in
    let instrs =
      let lst = ref [] in
      let _ = opcodes#iteri (fun _ opc -> lst := opc :: !lst) in
      List.rev !lst in
    LBLOCK [
        cms#toPretty;
        STR " (";
        STR jar;
        STR ")";
        STR " (";
        INT cms#index;
        STR ")";
        NL;
        LBLOCK
          (List.map
             (fun p ->
               LBLOCK [STR "   "; opcode_to_pretty p; NL]) instrs);
        NL] in
  LBLOCK [
      STR "Noteworthy methods: ";
      NL;
      NL;
      LBLOCK
        (List.map
           (fun (msg,mInfos) ->
             LBLOCK [
                 STR msg;
                 NL;
                 INDENT (3, LBLOCK (List.map p mInfos)); NL]) noteworthy);
      NL]

let interesting_to_pretty () =
  let interesting = get_interesting () in
  let p (m:(string * pretty_t)):pretty_t = LBLOCK [ snd m ; NL ] in
  LBLOCK [
      STR "Interesting methods: ";
      NL;
      NL;
      LBLOCK
        (List.map (fun (msg,txts) ->
             LBLOCK [
                 STR msg;
                 NL;
                 INDENT (3, LBLOCK (List.map p txts)); NL]) interesting);
      NL]


let main () =
  try
    begin
      read_args () ;
      (if !outputname = "" then
         begin
           pr_debug [ STR "Please specify an outputfilename with -o" ; NL ] ;
           exit 1
         end) ;
      (if !md5 = "" then
         begin
           pr_debug [ STR "Please specify an md5 with -md5" ; NL ] ;
           exit 1
         end) ;           
      process_jar !jarname ;
      file_output#saveFile
        (!outputname ^ ".chlog")
        (LBLOCK [ noteworthy_to_pretty () ; interesting_to_pretty () ;
                  chlog#toPretty  ]) ;
      (if ch_error_log#size > 0 then
         file_output#saveFile (!outputname ^ ".ch_error_log") ch_error_log#toPretty) 
    end
  with
  | JCH_failure p -> pr_debug [ STR "Failure: " ; p ; NL ] 

let _ = Printexc.print main ()
                  
