(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* tchlib *)
open TCHTestApi

module H = Hashtbl


(* Generation of titles *)

let counter = ref 0

let get_title () =
  begin
    incr counter;
    "untitled no " ^ (string_of_int !counter)
  end


let return (x: 'a) = fun () -> x


let return_unit = return ()


let make_assert_test
      ?(title=get_title ())
      (set_up: unit -> 'a)
      (f: 'a -> 'b)
      (tear_down: 'b -> unit): testcase_t =
  (title,
   (fun () ->
     try
       let t = Unix.gettimeofday () in
       begin
         tear_down (f (set_up ()));
         Passed ((Unix.gettimeofday ()) -. t)
       end
     with
     | TCHAssertion.Failed f -> Failed f
     | e -> Uncaught (e, Printexc.get_backtrace ())))


let make_simple_test ?(title=get_title ()) (f: 'a -> 'b): testcase_t =
  make_assert_test ~title:title return_unit f ignore


let default_classifier _ = ""


let default_reducer _ = []


let default_smaller _ _ = true


let dummy_spec =
  let dummy_pre _ = false in
  let dummy_post _ = false in
  { s_pre = dummy_pre; s_post = dummy_post }


let rec extract x = function
  | hd :: tl -> if hd.s_pre x then hd else extract x tl
  | [] -> dummy_spec


let rec reduce_candidates n red spec x f =
  let candidates = red x in
  let candidates =
    List.filter
      (fun c ->
        (spec.s_pre c)
        && not (spec.s_post (c, f c)))
      candidates in
  if n > 0 then
    List.flatten
      (List.map
         (fun c -> reduce_candidates (pred n) red spec c f) candidates)
  else
    candidates


let reduce smaller n red spec x f =
  if (n > 0) && (red != default_reducer) then
    begin
      match reduce_candidates n red spec x f with
      | hd :: tl ->
         let min =
           List.fold_left
             (fun acc elem ->
               if smaller elem acc then
                 elem
               else
                 acc)
             hd
             tl in
         Some min
      | [] -> None
    end
  else
    None


let make_random_test_with_wrapper
      ?(title=get_title ())
      ?(nb_runs=100)
      ?(nb_tries=10*nb_runs)
      ?(classifier=default_classifier)
      ?(reducer=default_reducer)
      ?(reduce_depth=4)
      ?(reduce_smaller=default_smaller)
      ?(random_src=TCHGenerator.make_random ())
      ((gen, prn): 'a generator_t)
      (f:'a -> 'b)
      (spec:(('a, 'b) specification_t) list)
      wrap =
  let _ = if nb_runs <= 0 then invalid_arg "CHT.TCHTest.make_random_test" in
  let _ = if nb_tries <= 0 then invalid_arg "CHT.TCHTest.make_random_test" in
  let _ = if reduce_depth < 0 then invalid_arg "CHT.TCHTest.make_random_test" in
  (title,
   (fun () ->
     let starttime = Unix.gettimeofday () in
     let valid = ref 0 in
     let uncaught = ref 0 in
     let actual_runs = ref 0 in
     let counterexamples = ref [] in
     let categories = H.create 16 in
     begin
       for _i = 1 to nb_runs do
         let x = ref (gen random_src) in
         let pre_post = ref (extract !x spec) in
         let tries = ref nb_tries in
         begin
           while (!pre_post == dummy_spec) && (!tries > 0) do
             let tmp = gen random_src in
             begin
               x := tmp;
               pre_post := extract tmp spec;
               decr tries
             end
           done;
           if !pre_post != dummy_spec then
             begin
               incr actual_runs;
               try
                 let y = wrap f !x in
                 let cat = classifier !x in
                 let curr = try H.find categories cat with _ -> 0 in
                 begin
                   H.replace categories cat (succ curr);
                   if (!pre_post).s_post (!x, y) then
                     incr valid
                   else
                     let x' = prn !x in
                     let reduced =
                       reduce
                         reduce_smaller
                         reduce_depth
                         reducer
                         !pre_post
                         !x
                         (wrap f) in
                     let x' = match reduced with
                       | Some r -> x' ^ "reduced to " ^ (prn r)
                       | None -> x' in
                     if not (List.mem x' !counterexamples) then
                       counterexamples := x' :: !counterexamples
                 end
               with _ -> incr uncaught
             end
         end
       done;
       let categories' = H.fold (fun k v acc -> (k, v) :: acc) categories [] in
       let timeused = (Unix.gettimeofday ()) -. starttime in
       Report (
           !valid,
           !actual_runs,
           !uncaught,
           (List.rev !counterexamples),
           categories',
           timeused)
     end))
  


let no_wrap f x = f x


let make_random_test
      ?(title=get_title ())
      ?(nb_runs=100)
      ?(nb_tries=10*nb_runs)
      ?(classifier=default_classifier)
      ?(reducer=default_reducer)
      ?(reduce_depth=4)
      ?(reduce_smaller=default_smaller)
      ?(random_src=TCHGenerator.make_random ())
      ((gen, prn): 'a generator_t)
      (f:'a -> 'b)
      (spec:(('a, 'b) specification_t) list) =
  make_random_test_with_wrapper
    ~title
    ~nb_runs
    ~nb_tries
    ~classifier
    ~reducer
    ~reduce_depth
    ~reduce_smaller
    ~random_src
    (gen, prn) f spec no_wrap
