(* =============================================================================
   CodeHawk Java Analyzer
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
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHClassLoader
open JCHSystemSettings

(* jchfeatures *)
open JCHExprFeatureExtraction


let input_file = ref ""
let output_directory = ref "."
let feature_sets = ref []

let versioninfo = "1.0 (May 4, 2017)"

let append_feature f = feature_sets := f :: !feature_sets

let speclist = [
    ("-o", Arg.Set_string output_directory, "directory to save the results");
    ("-log",
     Arg.String system_settings#set_logfile, "log file to record error messages");
    ("-feature",
     Arg.String append_feature, "adds feature to list of features to generate")
  ]


let usage_msg =
  "\n"
  ^ (string_repeat "-~" 40)
  ^ "\nCodeHawk Java Analyzer Feature Generator "
  ^ versioninfo
  ^ "\n" ^ (string_repeat "-~" 40)
  ^ "\n\nInvoke with"
  ^ "\n  chj_features -o <outputdir> "
  ^ "-feature <featuresetname> <jar or class file>"
  ^ "\n\n  The -feature argument specifies a featureset to be generated; there "
  ^ "\n   can be multiple -feature command-line arguments. "
  ^ "Valid featureset names "
  ^ "\n   are:"
  ^ "\n      method_bc"
  ^ "\n      method_bc2"
  ^ "\n      method_bc3"
  ^ "\n      method_libcalls"
  ^ "\n      method_libcalls_sig"
  ^ "\n      method_api_types"
  ^ "\n      method_op_types"
  ^ "\n      method_literals"
  ^ "\n      method_attrs"
  ^ "\n      method_sizes"
  ^ "\n      method_branch_conditions"
  ^ "\n      method_assignments"
  ^ "\n\n Note: only the last four are suitable for performing search\n"


let read_args () = Arg.parse speclist (fun s -> input_file := s) usage_msg


let _is_sym d =
  try
    (Unix.lstat d).Unix.st_kind = Unix.S_LNK
  with Unix.Unix_error (Unix.ENOENT, _, _) -> true


let _is_dir d =
  try
    (Unix.stat d).Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error (Unix.ENOENT, _, _) -> false


let _is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _,_) -> false


let get_jch_root (info:string):xml_element_int =
  let root = xmlElement "kt-java-feature-extraction" in
  let hNode = xmlElement "header" in
  begin
    hNode#setAttribute "info" info;
    hNode#setAttribute "time" (current_time_to_string ());
    root#appendChildren [hNode];
    root
  end


let check_directory dir =
  if dir = "" then
    ()
  else
    let sys_command s = ignore (Sys.command s) in
    if Sys.file_exists dir then () else sys_command ("mkdir " ^ dir)


let create_filename (_cn: class_name_int) (md5:string) =
  let dir = !output_directory in
  let _ = check_directory dir in
  let md5dirs = [
      String.sub md5 0 1;
      String.sub md5 1 1;
      String.sub md5 2 1;
      String.sub md5 3 1] in
  let md5dirs =
    List.fold_left (fun acc u ->
        match acc with
        | [] -> u::acc
        | h::_ -> (h ^ "/" ^ u) :: acc) [] (md5dirs) in
  let _ =
    List.iter (fun d -> check_directory (dir ^ "/" ^ d)) (List.rev md5dirs) in
  let md5dir = dir ^ "/" ^ (List.hd md5dirs) in
  md5dir ^ "/" ^ md5 ^ ".xml"


let _report_unrecognized_classfile_names () =
  let pairs = common_dictionary#list_unrecognized_class_names in
  List.iter (fun (s1,s2) ->
    chlog#add "unrecognized class file name"
      (LBLOCK [STR s1; STR " substituted by "; STR s2])) pairs


let _report_converted_method_names () =
  let pairs = common_dictionary#list_converted_method_names in
  List.iter (fun (s1,s2) ->
    chlog#add "converted method name"
      (LBLOCK [STR s1; STR " substituted by "; STR s2])) pairs


let save_class_xml_file
      (cn:class_name_int)(filename:string) (_md5:string) (node:xml_element_int) =
  try
    let doc = xmlDocument () in
    let root = get_jch_root "class-features" in
    begin
      doc#setNode root;
      root#appendChildren [node];
      file_output#saveFile filename doc#toPretty
    end
  with
  | CHFailure p
    | JCH_failure p ->
     system_settings#log_error
       (LBLOCK [
            STR "Unable to save class xml file ";
            cn#toPretty;
            STR " in file ";
            STR filename;
            STR ": ";
            p])
  | _ ->
     system_settings#log_error
       (LBLOCK [
            STR "Unable to save class xml file ";
            cn#toPretty;
            STR " in file ";
            STR filename])


let extract_expr_features cInfo =
  if cInfo#has_md5_digest then
    try
      let md5 = cInfo#get_md5_digest in
      let filename = create_filename cInfo#get_class_name md5 in
      if Sys.file_exists filename then
        ()
      else
        let _ =
          pr_debug [
              STR "Extract features: "; cInfo#get_class_name#toPretty; NL] in
        let node = xmlElement "class" in
        begin
          write_xml_class_expr_features node cInfo;
          save_class_xml_file cInfo#get_class_name filename md5 node
        end
    with
    | CHFailure p
      | JCH_failure p ->
       system_settings#log_error
         (LBLOCK [
              STR "Failure (";
              cInfo#get_class_name#toPretty;
              STR "): ";
              p;
              NL])
    | _ ->
       system_settings#log_error
         (LBLOCK [
              STR "unknown failure ("; cInfo#get_class_name#toPretty; STR ")"])


let process_jar () =
  begin
    ignore (load_classes_in_jar !input_file);
    process_classes ();
    app#iter_classes extract_expr_features
  end


let process_class () =
  let cn  = IO.input_channel (open_in_bin !input_file) in
  let md5 = Digest.file !input_file in
  let c = JCHParse.parse_class_low_level cn !input_file md5 in
  begin
    IO.close_in cn;
    app#add_class (JCHRaw2IF.low2high_class c);
    app#iter_classes extract_expr_features
  end


let main () =
  let _ = read_args () in
  let _ = JCHBasicTypes.set_permissive true in
  let dir = if !output_directory = "" then "jch_features" else !output_directory in
  let _ = (if not (Sys.file_exists dir) then Unix.mkdir dir 0o750) in
  if Filename.check_suffix !input_file ".jar" then
    process_jar ()
  else if Filename.check_suffix !input_file ".class" then
    process_class ()
  else
    pr_debug [
        STR "Filename extension of "; STR !input_file; STR " not recognized."; NL]


let _ = Printexc.print main ()
