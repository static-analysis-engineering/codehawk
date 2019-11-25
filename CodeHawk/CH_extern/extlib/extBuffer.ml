open ExtBytes

module Buffer = struct

  include Buffer
(*
#if OCAML < 402
  (* The uses of unsafe_{of,to}_string above are not semantically
     justified, as the Buffer implementation may very well capture and
     share parts of its internal buffer, or of input string given as
     input.

     They are however correct with respect to the implementation being
     used in OCaml 4.02.0; this implementation must be revisited if
     the string representation changes. *)
  let to_bytes b =
    Bytes.unsafe_of_string (contents b)

  let add_subbytes b s offset len =
    add_substring b (Bytes.unsafe_to_string s) offset len

  let add_bytes b s = add_string b (Bytes.unsafe_to_string s)
#endif
 *)
end
