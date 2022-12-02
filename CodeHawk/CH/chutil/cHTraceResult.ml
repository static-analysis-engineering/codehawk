(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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


let tmap ?(msg="") (f: 'a -> 'c) (r: 'a traceresult) =
  match r with
  | Ok v -> Ok (f v)
  | Error e when msg = "" -> Error e
  | Error e -> Error (msg :: e)


let tbind ?(msg="") (f: 'a -> 'c traceresult) (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | Error e when msg = "" -> Error e
  | Error e -> Error (msg :: e)


let titer (f: 'a -> unit) (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | Error _ -> ()


let tfold_list ~(ok: 'c -> 'a -> 'c) (initacc: 'c) (rl: ('a traceresult) list) =
  List.fold_left (fun acc r ->
      match r with
      | Ok v -> ok acc v
      | Error _ -> acc) initacc rl


let to_bool (f: 'a -> bool) (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | _ -> false


let to_option (r: 'a traceresult) =
  match r with
  | Ok v -> Some v
  | _ -> None
