(*
 * ExtBuffer - extra functions over buffers.
 * Copyright (C) 2014 Gabriel Scherer
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

(** Extra functions over text buffers.

   We in fact provide the exact same interface as Buffer on 4.02 OCaml
   versions, with the implementation for the 4.02-and-above
   bytes-specific functions backported.
*)

open ExtBytes

module Buffer : sig

type t = Buffer.t

val create : int -> t

val contents : t -> string

val to_bytes : t -> Bytes.t

val sub : t -> int -> int -> string

val blit : t -> int -> Bytes.t -> int -> int -> unit

val nth : t -> int -> char

val length : t -> int

val clear : t -> unit

val reset : t -> unit

val add_char : t -> char -> unit

val add_string : t -> string -> unit

val add_bytes : t -> Bytes.t -> unit

val add_substring : t -> string -> int -> int -> unit

val add_subbytes : t -> Bytes.t -> int -> int -> unit

val add_substitute : t -> (string -> string) -> string -> unit

val add_buffer : t -> t -> unit

val add_channel : t -> in_channel -> int -> unit

val output_buffer : out_channel -> t -> unit

(* #if OCAML >= 405 *)

val truncate : t -> int -> unit

(* #endif

#if OCAML >= 406  *)

val add_utf_8_uchar : t -> Stdlib.Uchar.t -> unit
val add_utf_16le_uchar : t -> Stdlib.Uchar.t -> unit
val add_utf_16be_uchar : t -> Stdlib.Uchar.t -> unit

(* #endif

#if OCAML >= 407 *)
(** [*_seq] functions were introduced in OCaml 4.07.0, and are _not_ implemented in extlib for older OCaml versions *)
val to_seq : t -> char Seq.t
val to_seqi : t -> (int * char) Seq.t
val add_seq : t -> char Seq.t -> unit
val of_seq : char Seq.t -> t
                             (* #endif  *)

end
