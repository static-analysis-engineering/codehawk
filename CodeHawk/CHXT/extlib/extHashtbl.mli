(* 
 * ExtHashtbl - extra functions over hashtables.
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
 
(** Extra functions over hashtables. *)

module Hashtbl :
  (** The wrapper module *)
  sig

  type ('a,'b) t = ('a,'b) Hashtbl.t
  (** The type of a hashtable. *)

  (** {6 New Functions} *)

  val exists : ('a,'b) t -> 'a -> bool
  (** [exists h k] returns true is at least one item with key [k] is
    found in the hashtable. *)

  val keys : ('a,'b) t -> 'a Enum.t
  (** Return an enumeration of all the keys of a hashtable.
      If the key is in the Hashtable multiple times, all occurrences
      will be returned.  *)

  val values : ('a,'b) t -> 'b Enum.t
  (** Return an enumeration of all the values of a hashtable. *)

  val enum : ('a, 'b) t -> ('a * 'b) Enum.t
  (** Return an enumeration of (key,value) pairs of a hashtable. *)

  val of_enum : ('a * 'b) Enum.t -> ('a, 'b) t
  (** Create a hashtable from a (key,value) enumeration. *)

  val find_default : ('a,'b) t -> 'a -> 'b -> 'b
    (** Find a binding for the key, and return a default
      value if not found *)

  val find_opt : ('a,'b) Hashtbl.t -> 'a -> 'b option
  (** Find a binding for the key, or return [None] if no
    value is found *)

  val find_option : ('a,'b) Hashtbl.t -> 'a -> 'b option
  (** compatibility, use [find_opt] *)

  val remove_all : ('a,'b) t -> 'a -> unit
  (** Remove all bindings for the given key *)

  val map : ('b -> 'c) -> ('a,'b) t -> ('a,'c) t
  (** [map f x] creates a new hashtable with the same
      keys as [x], but with the function [f] applied to
    all the values *)

  val length : ('a,'b) t -> int
  (** Return the number of elements inserted into the Hashtbl 
    (including duplicates) *)

  (* #if OCAML >= 400  *)
  val reset : ('a,'b) t -> unit
  val randomize : unit -> unit

  type statistics = Hashtbl.statistics = {
    num_bindings: int;
    num_buckets: int;
    max_bucket_length: int;
    bucket_histogram: int array;
  }

  val stats : ('a,'b) t -> statistics

  val seeded_hash_param : int -> int -> int -> 'a -> int
  val seeded_hash : int -> 'a -> int
                                   (* #endif  *)

  (* #if OCAML >= 403  *)
  val is_randomized : unit -> bool
  val filter_map_inplace : ('a -> 'b -> 'b option) -> ('a, 'b) t -> unit
  (* #endif  *)

  (** {6 Older Functions} *)

  (** Please refer to the Ocaml Manual for documentation of these
    functions. *)

  (** @before 4.00.0 [random] is ignored *)
  val create : ?random:bool -> int -> ('a, 'b) t
  val clear : ('a, 'b) t -> unit
  val add : ('a, 'b) t -> 'a -> 'b -> unit
  val copy : ('a, 'b) t -> ('a, 'b) t
  val find : ('a, 'b) t -> 'a -> 'b
  val find_all : ('a, 'b) t -> 'a -> 'b list
  val mem : ('a, 'b) t -> 'a -> bool
  val remove : ('a, 'b) t -> 'a -> unit
  val replace : ('a, 'b) t -> 'a -> 'b -> unit
  val iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit
  val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
  val hash : 'a -> int
  val hash_param : int -> int -> 'a -> int

  (* #if OCAML >= 407  *)
  (** [*_seq] functions were introduced in OCaml 4.07.0, and are _not_ implemented in extlib for older OCaml versions *)
  val to_seq : ('a,'b) t -> ('a * 'b) Seq.t
  val to_seq_keys : ('a,_) t -> 'a Seq.t
  val to_seq_values : (_,'b) t -> 'b Seq.t
  val add_seq : ('a,'b) t -> ('a * 'b) Seq.t -> unit
  val replace_seq : ('a,'b) t -> ('a * 'b) Seq.t -> unit
  val of_seq : ('a * 'b) Seq.t -> ('a, 'b) t
                                           (* #endif  *)

(** Functor interface forwards directly to stdlib implementation (i.e. no enum functions) *)

  (* #if OCAML >= 407  *)

module type HashedType = Hashtbl.HashedType
module type S = Hashtbl.S
module Make = Hashtbl.Make

module type SeededHashedType = Hashtbl.SeededHashedType
module type SeededS = Hashtbl.SeededS
module MakeSeeded = Hashtbl.MakeSeeded

(* #else

module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
   end

module type S =
  sig
    type key
    type 'a t
    val create : int -> 'a t
    val clear : 'a t -> unit
#if OCAML >= 400
    val reset : 'a t -> unit
#endif
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
#if OCAML >= 405
    val find_opt : 'a t -> key -> 'a option
#endif
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
#if OCAML >= 403
    val filter_map_inplace: (key -> 'a -> 'a option) -> 'a t -> unit
#endif
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
#if OCAML >= 400
    val stats: 'a t -> statistics
#endif
  end

module Make (H : HashedType) : S with type key = H.t

#if OCAML >= 400
module type SeededHashedType =
  sig
    type t
    val equal: t -> t -> bool
    val hash: int -> t -> int
  end

module type SeededS =
  sig
    type key
    type 'a t
    val create : ?random:bool -> int -> 'a t
    val clear : 'a t -> unit
    val reset : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
#if OCAML >= 405
    val find_opt : 'a t -> key -> 'a option
#endif
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
#if OCAML >= 403
    val filter_map_inplace: (key -> 'a -> 'a option) -> 'a t -> unit
#endif
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
    val stats: 'a t -> statistics
  end

module MakeSeeded (H : SeededHashedType) : SeededS with type key = H.t
#endif

#endif  *)

  end
