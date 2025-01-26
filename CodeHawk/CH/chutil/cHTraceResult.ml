(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2025  Aarno Labs LLC

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


type 'a traceresult = ('a, string list) result


let tvalue (r: 'a traceresult) ~(default: 'a) = Result.value r ~default


let tget_ok (r: 'a traceresult) =
  match r with
  | Ok v -> v
  | Error e -> raise (Invalid_argument (String.concat "; " e))


let tget_error (r: 'a traceresult) = Result.get_error r


let tmap ?(msg="") (f: 'a -> 'c) (r: 'a traceresult) =
  match r with
  | Ok v -> Ok (f v)
  | Error e when msg = "" -> Error e
  | Error e -> Error (msg :: e)


let tmap2
      ?(msg1="")
      ?(msg2="")
      (f: 'a -> 'b  -> 'c)
      (r1: 'a traceresult)
      (r2: 'b traceresult): 'c traceresult =
  match r1, r2 with
  | Ok v1, Ok v2 -> Ok (f v1 v2)
  | Error e1, Ok _ -> Error (msg1 :: e1)
  | Ok _, Error e2 -> Error (msg2 :: e2)
  | Error e1, Error e2 -> Error (msg1 :: msg2 :: (e1 @ e2))


let tmap3
      ?(msg1="")
      ?(msg2="")
      ?(msg3="")
      (f: 'a -> 'b -> 'c -> 'd)
      (r1: 'a traceresult)
      (r2: 'b traceresult)
      (r3: 'c traceresult): 'd traceresult =
  match r1, r2, r3 with
  | Ok v1, Ok v2, Ok v3 -> Ok (f v1 v2 v3)
  | Error e1, Ok _, Ok _ -> Error (msg1 :: e1)
  | Ok _, Error e2, Ok _ -> Error (msg2 :: e2)
  | Ok _, Ok _, Error e3 -> Error (msg3 :: e3)
  | Error e1, Error e2, Ok _ -> Error (msg1 :: msg2 :: (e1 @ e2))
  | Error e1, Ok _, Error e3 -> Error (msg1 :: msg3 :: (e1 @ e3))
  | Ok _, Error e2, Error e3 -> Error (msg2 :: msg3 :: (e2 @ e3))
  | Error e1, Error e2, Error e3 -> Error (msg1 :: msg2 :: msg3 :: (e1 @ e2 @ e3))


let tbind ?(msg="") (f: 'a -> 'c traceresult) (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | Error e when msg = "" -> Error e
  | Error e -> Error (msg :: e)


let tfold ~(ok:'a -> 'c) ~(error:string list -> 'c) (r: 'a traceresult): 'c =
  match r with
  | Ok v -> ok v
  | Error e -> error e


let tfold_default (ok: 'a -> 'c) (d: 'c) (r: 'a traceresult): 'c =
  match r with
  | Ok v -> ok v
  | Error _ -> d


let tprop (r: 'a traceresult) (msg: string): 'a traceresult =
  match r with
  | Ok v -> Ok v
  | Error e -> Error (msg :: e)


let titer ~(ok:'a -> unit) ~(error: string list -> unit) (r: 'a traceresult) =
  match r with
  | Ok v -> ok v
  | Error e -> error e


let titer_default (f: 'a -> unit) (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | Error _ -> ()


let tfold_list ~(ok: 'c -> 'a -> 'c) (initacc: 'c) (rl: ('a traceresult) list) =
  List.fold_left (fun acc r ->
      match r with
      | Ok v -> ok acc v
      | Error _ -> acc) initacc rl


let tfold_list_default
      ~(ok: 'c -> 'a -> 'c)
      ~(err: 'c -> 'c)
      (initacc: 'c)
      (rl: ('a traceresult) list): 'c =
  List.fold_left (fun acc r ->
      match r with
      | Ok v -> ok acc v
      | Error _ -> err acc) initacc rl


let tfold_list_fail
      (ok: 'c -> 'a -> 'c)
      (initacc: 'c traceresult)
      (rl: ('a traceresult) list): 'c traceresult =
  List.fold_left (fun acc r ->
      match acc with
      | Error e -> Error e
      | Ok accv ->
         match r with
         | Error e -> Error e
         | Ok v -> Ok (ok accv v)) initacc rl


let to_bool (f: 'a -> bool) (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | _ -> false


let to_option (r: 'a traceresult) =
  match r with
  | Ok v -> Some v
  | _ -> None
