open Printf

let show_bytes s =
    let (_:int) = Sys.command (sprintf "ocamlfind query -format %s bytes" (Filename.quote s)) in ()

let () =
  match Sys.argv with
  | [|_;"-cppo-args"|] ->
    let version = Scanf.sscanf Sys.ocaml_version "%d.%d." (fun major minor -> major * 100 + minor) in
    printf "-D \\\"OCAML %d\\\"\n" version;
    print_endline (if Sys.word_size = 32 then "-D WORD_SIZE_32 " else "");
    show_bytes "-D WITH_BYTES";
    exit 0
  | [|_;"-compile-args"|] ->
    if Sys.ocaml_version >= "4.00.0" then print_endline "-bin-annot";
    show_bytes "-package bytes";
    exit 0
  | _ -> failwith "not gonna happen"
