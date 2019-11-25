(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(** Utility to keep track of CPU time used on various tasks *)

(* chlib *)
open CHPretty

(* chutil *)
open CHPrettyUtil

class type timing_int =
object
  method getStartTime: float
  method start_timing: unit
  method end_timing  : unit
  method update_task_time : string -> unit
  method toPretty    : pretty_t
end

class timing_t:timing_int =
object

  val mutable start_time = 0.0
  val mutable last_time  = 0.0
  val mutable total_time = 0.0
  val task_timings = Hashtbl.create 13

  method getStartTime = start_time

  method start_timing =
    begin start_time <- Unix.gettimeofday () ; last_time <- start_time end

  method end_timing = 
    begin last_time <- Unix.gettimeofday () ; total_time <- last_time -. start_time end

  method update_task_time (task:string) =
    let t = Unix.gettimeofday () in
    let ttime = t -. last_time in
    begin
      if Hashtbl.mem task_timings task then
	let prev = Hashtbl.find task_timings task in
	Hashtbl.replace task_timings task (prev +. ttime)
      else
	Hashtbl.add task_timings task ttime ;
      last_time <- t
    end

  method toPretty =
    Hashtbl.fold 
      (fun k v a ->
        LBLOCK [ a ; NL ; fixed_length_pretty (STR k) 30 ; STR ": " ; 
		 STR (Printf.sprintf "%f" v) ]) task_timings
      (LBLOCK [ fixed_length_pretty (STR "Total time") 30 ; STR ": " ;
		STR (Printf.sprintf "%f" total_time) ])
end


let chtimer = new timing_t

class timer_t = 
  object 
    val start_times = Array.make 10 0.
    val total_times = Array.make 10 0.

    method start i = 
      start_times.(i) <- Unix.gettimeofday () 
    method stop i = 
      let time = Unix.gettimeofday () -. start_times.(i) in
      total_times.(i) <- total_times.(i) +. time 

    method toPretty = 
      LBLOCK [STR "Total times : "; NL; 
	      pretty_print_list
                (Array.to_list total_times)
                (fun f -> STR (Printf.sprintf "%f" f)) "[| " "; " " |]"; NL]

  end

let atimer = new timer_t
