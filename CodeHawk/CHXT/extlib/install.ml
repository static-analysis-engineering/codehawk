(*
 * Install - ExtLib installation
 * Copyright (C) 2003 Nicolas Cannasse
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

open Printf

type path =
  | PathUnix
  | PathDos

let modules_min = [
  "extBytes";
  "enum";
  "bitSet";
  "dynArray";
  "extArray";
  "extHashtbl";
  "extList";
  "extString";
  "global";
  "extBuffer";
  "IO";
  "option";
  "pMap";
  "std";
  "base64";
  "refList";
  "optParse";
  "dllist";
]

let modules_compat = [
  "uChar";
  "uTF8";
  "unzip";
]

(* ocaml/mingw uses unix extensions but will have Sys.os_type = "Win32" :( *)
let obj_ext , lib_ext , cp_cmd , path_type = match Sys.os_type with
  | "Unix" | "Cygwin" | "MacOS" -> ".o" , ".a" , "cp", PathUnix
  | "Win32" -> ".obj" , ".lib" , "copy", PathDos
  | _ -> failwith "Unknown OS"

let run cmd =
  print_endline cmd;
  let ecode = Sys.command cmd in
  if ecode <> 0 then failwith (sprintf "Exit Code %d - Stopped" ecode)

let copy file dest =
  if dest <> "" && dest <> "." then begin
    print_endline ("Installing " ^ file);
    let path = dest ^ file in
    (try Sys.remove path with _ -> ());
    try
      Sys.rename file path;
    with
      _ -> failwith "Aborted"
  end

let get_version () =
  let ch = open_in "../Makefile" in
  let rec loop () =
    let s = input_line ch in
    try
      Scanf.sscanf s " RELEASE := %s %!" (fun s -> s)
    with
      _ -> loop ()
  in
  try
    let s = loop () in close_in_noerr ch; s
  with _ ->
    close_in_noerr ch;
    failwith "No RELEASE present in ../Makefile"

let complete_path p =
  if p = "" then
    p
  else
    let c = p.[String.length p - 1] in
    if c = '/' || c = '\\' then
      p
    else
      p ^ (match path_type with PathUnix -> "/" | PathDos -> "\\")

let remove file =
  try
    Sys.remove file
  with
    _ -> prerr_endline ("Warning : failed to delete " ^ file)

let is_findlib() =
  let findlib = Sys.command (if Sys.os_type = "Win32" then "ocamlfind printconf 2>NUL" else "ocamlfind printconf") = 0 in
  if findlib then  print_endline "Using Findlib";
  findlib

type install_dir = Findlib | Dir of string

let install() =
  let autodir = ref None in
  let autodoc = ref None in
  let autobyte = ref false in
  let autonative = ref false in
  let autofull = ref None in
  let version = get_version () in
  let usage = sprintf "ExtLib installation program v%s\n(C) 2003 Nicolas Cannasse" version in
  Arg.parse [
    ("-d", Arg.String (fun s -> autodir := Some s) , "<dir> : install in target directory");
    ("-b", Arg.Unit (fun () -> autobyte := true) , ": byte code installation");
    ("-n", Arg.Unit (fun () -> autonative := true) , ": native code installation");
    ("-min", Arg.Unit (fun () -> autofull := Some false) , ": exclude potentially conflicting modules (recommended)");
    ("-full", Arg.Unit (fun () -> autofull := Some true) , ": include all modules (compatibility)");
    ("-doc", Arg.Unit (fun () -> autodoc := Some true) , ": documentation installation");
    ("-nodoc", Arg.Unit (fun () -> autodoc := Some false) , ": disable documentation installation");
  ] (fun s -> raise (Arg.Bad s)) usage;
  let findlib = is_findlib () in
  let install_dir = (
    match !autodir with
    | Some dir ->
      if not !autobyte && not !autonative && !autodoc = None then failwith "Nothing to do.";
      Dir (complete_path dir)
    | None ->
      let byte, native =
        if !autobyte || !autonative then
          (!autobyte, !autonative)
        else begin
      printf "Choose one of the following :\n1- Bytecode installation only\n2- Native installation only\n[3]- Both Native and Bytecode installation\n> ";
        (match read_line() with
        | "1" -> true, false
        | "2" -> false, true
        | "" | "3"  -> true, true
        | _ -> failwith "Invalid choice, exit.")
        end
      in
      let dest =
        if not findlib then begin
          printf "Choose installation directory :\n> ";
          let dest = complete_path (read_line()) in
          (try
            close_out (open_out (dest ^ "test.file"));
            Sys.remove (dest ^ "test.file");
          with
            _ -> failwith ("Directory " ^ dest ^ " does not exists or cannot be written."));
          Dir dest;
        end else Findlib in
      autobyte := byte;
      autonative := native;
      dest
  ) in
  let modules =
    let full =
      match !autofull with
      | Some f -> f
      | None ->
        printf "Do you want to exclude potentially conflicting modules (Unzip UChar UTF8) from build ([Y]/N) ?\n> ";
        (match read_line() with
        | "" | "y" | "Y" -> false
        | "n" | "N" -> true
        | _ -> failwith "Invalid choice, exit.")
    in
    match full with
    | true -> modules_min @ modules_compat
    | false -> modules_min
  in
  let m_list suffix = String.concat " " (List.map (fun m -> m ^ "." ^ suffix) modules) in
  let doc =
    match !autodoc with
    | Some doc -> doc
    | None ->
      printf "Do you want to generate ocamldoc documentation ([Y]/N) ?\n> ";
      (match read_line() with
      | "" | "y" | "Y" -> true
      | "n" | "N" -> false
      | _ -> failwith "Invalid choice, exit.")
  in
  let doc_dir =
    match install_dir with
    | Findlib -> "doc"
    | Dir install_dir -> Filename.concat install_dir "extlib-doc"
  in
  if doc && not (Sys.file_exists doc_dir) then run (sprintf "mkdir %s" doc_dir);
  (* generate *)
  let defines =
    let version = Scanf.sscanf Sys.ocaml_version "%d.%d." (fun major minor -> major * 100 + minor) in
    sprintf "-D 'OCAML %d' %s" version (if Sys.word_size = 32 then "-D WORD_SIZE_32 " else "");
  in
  let pp = sprintf "-pp \"cppo %s\"" defines in
  let ocamlc fmt = ksprintf (fun s -> run (sprintf "ocamlc %s %s" pp s)) fmt in
  let ocamlopt fmt = ksprintf (fun s -> run (sprintf "ocamlopt %s %s" pp s)) fmt in
  ocamlc "-i extBytes.ml > extBytes.mli";
  (* compile mli *)
  ocamlc "-c %s" (m_list "mli");
  (* compile ml *)
  if !autobyte then begin
    List.iter (fun m -> ocamlc "-g -c %s.ml" m) modules;
    ocamlc "-g -a -o extLib.cma %s extLib.ml" (m_list "cmo");
    List.iter (fun m -> remove (m ^ ".cmo")) modules;
    remove "extLib.cmo";
  end;
  if !autonative then begin
    List.iter (fun m -> ocamlopt "-g -c %s.ml" m) modules;
    ocamlopt "-g -a -o extLib.cmxa %s extLib.ml" (m_list "cmx");
    List.iter (fun m -> remove (m ^ obj_ext)) modules;
    remove ("extLib" ^ obj_ext);
  end;
  if doc then begin
    run (sprintf "ocamldoc %s -sort -html -d %s %s" pp doc_dir (m_list "mli"));
    if doc_dir <> "doc" then (* style.css is already there *)
      run ((match path_type with
        | PathDos -> sprintf "%s doc\\style.css %s\\style.css";
        | PathUnix -> sprintf "%s doc/style.css %s/style.css") cp_cmd doc_dir);
  end;
  match install_dir with
    Findlib ->
      let files = Buffer.create 0 in
      List.iter (fun m ->
        Buffer.add_string files (m ^ ".cmi ");
        Buffer.add_string files (m ^ ".mli "))
        modules;
      Buffer.add_string files "extLib.cmi ";
      if !autobyte then Buffer.add_string files "extLib.cma ";
      if !autonative then begin
        Buffer.add_string files "extLib.cmxa extLib.cmx ";
        List.iter (fun m -> Buffer.add_string files (m ^ ".cmx ")) modules;
        end;
      let optional = if !autonative then "-optional extLib.lib extLib.a" else "" in
      let files = Buffer.contents files in
      run (sprintf "ocamlfind install -patch-version %s extlib META %s %s" version files optional);
  | Dir install_dir ->
      List.iter (fun m ->
      copy (m ^ ".cmi") install_dir;
      if !autonative then copy (m ^ ".cmx") install_dir
    ) ("extLib" :: modules);
      if !autobyte then copy "extLib.cma"  install_dir;
      if !autonative then begin
        copy "extLib.cmxa" install_dir;
        copy ("extLib" ^ lib_ext) install_dir;
      end;
;;
try
  print_endline "\nATTENTION! install.ml is deprecated and will be removed in next release. Please use Makefile instead.\n";
  install();
  print_endline "Done.";
with
  Failure msg ->
    prerr_endline msg;
    exit 1
