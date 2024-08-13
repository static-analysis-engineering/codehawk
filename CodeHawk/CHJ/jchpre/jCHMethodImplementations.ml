(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHFunctionSummaryLibrary
open JCHPreAPI
open JCHXmlUtil

module H = Hashtbl


let ms_implementers_init = {
  mscn_classes = [];
  mscn_stubs = [];
  mscn_native = []
}

let add_to_list k l = if List.mem k l then l else k :: l

let add_implementer_class implementers (cn:class_name_int) =
  { implementers with mscn_classes = add_to_list cn#index implementers.mscn_classes }

let add_implementer_stub implementers (cn:class_name_int) =
  { implementers with mscn_stubs = add_to_list cn#index implementers.mscn_stubs }

let add_implementer_native implementers (cn:class_name_int) =
  { implementers with mscn_native = add_to_list cn#index implementers.mscn_native }

let get_implementing_classes implementers =
  implementers.mscn_classes @ implementers.mscn_stubs @ implementers.mscn_native


let _get_size implementers =
  (List.length implementers.mscn_classes)
  + (List.length implementers.mscn_stubs)
  + (List.length implementers.mscn_native)


class method_signature_implementations_t:method_signature_implementations_int =
object (self)

  val table = H.create 3
  val revtable = H.create 3
  val msregistry = H.create 3    (* ms#index -> count *)

  method register_signature (ms:method_signature_int) =
    let entry =
      if H.mem msregistry ms#index then H.find msregistry ms#index else 0 in
    H.replace msregistry ms#index (entry + 1)

  method private has_signature (ms:method_signature_int) =
    H.mem msregistry  ms#index

  method private get_implementers (ms:method_signature_int) =
    if H.mem table ms#index then H.find table ms#index else ms_implementers_init

  method get_ms_index (name:string) (ssig:string) =
    if H.mem revtable (name,ssig) then
      H.find revtable (name,ssig)
    else
      raise (JCH_failure (LBLOCK [STR "No method signature index found for ";
                                   STR name; STR ssig]))

  method initialize =
    let _ =
      List.iter (fun ms ->
          begin
            (* if two distinct signatures exist with one being static, only
               keep the signature that is static *)
            if H.mem revtable (ms#name,ms#to_signature_string) then
              if ms#is_static then
                let objectmsix =
                  H.find revtable (ms#name,ms#to_signature_string) in
                begin
                  H.replace revtable (ms#name,ms#to_signature_string) ms#index;
                  H.add table ms#index ms_implementers_init;
                  H.remove table objectmsix
                end
              else
                ()
            else
              H.add revtable (ms#name,ms#to_signature_string) ms#index
          end)
                common_dictionary#get_method_signatures in
    let add_bc ms cn =
      H.replace
        table ms#index (add_implementer_class (self#get_implementers ms) cn) in
    let add_nm ms cn =
      H.replace
        table ms#index (add_implementer_native (self#get_implementers ms) cn) in
    let add_stub ms cn =
      H.replace
        table ms#index (add_implementer_stub (self#get_implementers ms) cn) in
    app#iter_classes (fun cInfo ->
        let cn = cInfo#get_class_name in
        let msLst = cInfo#get_methods_defined in
        let inheritedMethods = get_inherited_methods cn in
        if cInfo#is_stubbed then
          begin
	    List.iter (fun ms ->
	        let cms = make_cms cn ms in
	        if function_summary_library#has_method_summary cms then
	          let summary = function_summary_library#get_method_summary cms in
                  if summary#is_inherited then
                    if app#has_method cms then
                      let m = app#get_method cms in
                      add_stub ms m#get_class_method_signature#class_name
                    else
                      if summary#has_defining_method then
                        let defCms = summary#get_defining_method in
                        if function_summary_library#has_method_summary defCms then
                          if app#has_method defCms then
                            begin
                              app#add_method_link cms defCms;
                              add_stub ms defCms#class_name
                            end
                          else
                            let summary =
                              function_summary_library#get_method_summary defCms in
                            begin
                              app#add_stub summary;
                              add_stub ms defCms#class_name
                             end
                        else
                          chlog#add
                            "missing inherited method"
                            (LBLOCK [cms#toPretty])
                      else
                        chlog#add
                          "missing declaration of parent method"
                          (LBLOCK [cms#toPretty])

                  else
	            if summary#is_abstract then
                      ()
                    else
	              add_stub ms cn
                else
                  if function_summary_library#has_method_summary
                       ~anysummary:true cms then
                    let summary =
                      function_summary_library#get_method_summary
                        ~anysummary:true cms in
                    if self#has_signature ms
                       && (cInfo#is_interface
                           || summary#get_visibility = Public) then
                      chlog#add "missing summary (invalid)" cms#toPretty
                    else
                      ()
                  else
                    chlog#add "missing summary" cms#toPretty) msLst;

            List.iter (fun (ms,cImpl) ->
                let cms = make_cms cn ms in
                let cImplms = make_cms cImpl ms in
                if function_summary_library#has_method_summary cImplms then
                  let summary =
                    function_summary_library#get_method_summary cImplms in
                  begin
                    (if app#has_method cImplms then () else app#add_stub summary);
                    (if app#has_method cms then
                       ()
                     else
                       app#add_method_link cms cImplms);
                    add_stub ms cImpl
                  end
                else
                  chlog#add
                    "missing  inherited method"
                    (LBLOCK  [cms#toPretty; STR " from "; cImpl#toPretty]))
              inheritedMethods
          end
        else
          begin
	    List.iter (fun ms ->
                let cms =  make_cms cn ms in
	        let m = cInfo#get_method ms in
	        if m#is_concrete then
	          match m#get_implementation with
	          | Native -> add_nm ms cn
	          | Bytecode _ -> add_bc ms cn
                else if app#has_method cms then
                  let mInfo = app#get_method cms in
                  if mInfo#is_stubbed then
                    add_stub  ms m#get_class_method_signature#class_name) msLst;
            List.iter (fun (ms,cImpl) ->
                let cms = make_cms cn ms in
                if app#has_class cImpl then
                  let cImplInfo = app#get_class cImpl in
                  let cImplms = make_cms cImpl ms in
                  if cImplInfo#is_stubbed then
                    if function_summary_library#has_method_summary cImplms then
                      let summary =
                        function_summary_library#get_method_summary cImplms in
                      begin
                        (if app#has_method cImplms then
                           ()
                         else
                           app#add_stub summary);
                        (if app#has_method cms then
                           ()
                         else
                           app#add_method_link cms cImplms);
                        add_stub ms cImpl
                      end
                    else
                      chlog#add
                        "missing inherited method"
                        (LBLOCK [
                             STR "application method ";
                             cms#toPretty;
                             STR " from stub ";
                             cImpl#toPretty])
                  else
                    let cms = make_cms cn ms in
                    let cImplms = make_cms cImpl ms in
                    let cImplm = cImplInfo#get_method ms in
                    begin
                      (if app#has_method cImplms then
                         ()
                       else
                         app#add_method cImplm);
                      (if app#has_method cms then
                         ()
                       else
                         app#add_method_link cms cImplms);
                      if cImplm#is_concrete then
                        match cImplm#get_implementation with
                        | Native -> add_nm ms cImpl
                        | Bytecode _ -> add_bc ms cImpl
                    end) inheritedMethods
          end)

  method get_implementations (ms:method_signature_int) =
    try
      List.map retrieve_cn (get_implementing_classes (self#get_implementers ms))
    with
    | JCH_failure  p ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Error in retrive_cn for ";
                 ms#toPretty;
                 STR " with implementers: ";
                 pretty_print_list
                   (get_implementing_classes (self#get_implementers ms))
                   (fun i -> INT i) " [" "," "]";
                 STR ": ";
                 p]))

  method get_interface_implementations
           (interface: class_name_int) (ms: method_signature_int) =
    List.filter (fun cn ->
      if app#has_class cn then
	(app#get_class cn)#implements_interface interface
      else
	true) (self#get_implementations ms)

  method write_xml (node:xml_element_int) =
    let seti = node#setIntAttribute in
    let nativeTgts = ref 0 in
    let bcsizes = H.create 3 in
    let _ = H.iter (fun _ v ->
      let len = (List.length v.mscn_classes) + (List.length v.mscn_stubs) in
      let e = if H.mem bcsizes len then H.find bcsizes len else 0 in
      begin
	H.replace bcsizes len (e+1);
	(match v.mscn_native with [] -> () | _ -> nativeTgts := !nativeTgts + 1)
      end) table in

    let get_size_count i = if H.mem bcsizes i then H.find bcsizes i else 0 in
    let maxTgts = H.fold (fun k _ acc -> if k > acc then k else acc) bcsizes 0 in
    let exc10 = H.fold (fun k v acc -> if k > 10 then acc + v else acc) bcsizes 0 in

    let tLst = ref [] in
    let _ = H.iter (fun k v -> tLst := (k,v) :: !tLst) table in
    begin
      node#appendChildren (List.map (fun (k,v) ->
	let msNode = xmlElement "ms" in
	let append = msNode#appendChildren in
	let set = msNode#setAttribute in
	let seti = msNode#setIntAttribute in
	let ms = retrieve_ms k in
	begin
	  (match v.mscn_classes with [] -> () | l ->
	    let bcNode = xmlElement "bc" in
	    begin
	      write_xml_indices bcNode l;
	      append [bcNode]
	    end);
	  (match v.mscn_stubs with [] -> () | l ->
	    let nmNode = xmlElement "stubs" in
	    begin
	      write_xml_indices nmNode l;
	      append [nmNode]
	    end);
	  (match v.mscn_native with [] -> () | l ->
	    let nmNode = xmlElement "native" in
	    begin
	      write_xml_indices nmNode l;
	      append [nmNode]
	    end);
	  seti "ix" k;
	  set "name" ms#name;
	  (if ms#is_static then set "static" "yes");
	  set "sig" ms#to_signature_string;
	  msNode
	end) !tLst);
      seti "native-targets" !nativeTgts;
      for i = 0 to 10 do
        seti ("tgts-" ^ (string_of_int i)) (get_size_count i)
      done;
      seti "max-targets" maxTgts;
      seti "exceeeds-10" exc10;
      seti "size" (List.length !tLst)
    end

end


let method_signature_implementations = new method_signature_implementations_t
