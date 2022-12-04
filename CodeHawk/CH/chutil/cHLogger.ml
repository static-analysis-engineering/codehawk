(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(** Facility to record problems during a run of the analyzer. 

    Typical use is to catch an exception, record the type of exception thrown 
    with additional data in the logger:

    chlog#add "Invalid_Argument" <reason for invalid argument>

    and continue execution at an appropriate point. At the end of the run
    print out all exceptions that were thrown to the run with

    pr_debug [chlog#toPretty]

    To distinguish between informational log messages and error log messages
    use the ch_info_log and ch_error_log with the same API
*)

(* chlib *)
open CHPretty

(* chutil *)
open CHTraceResult


module H = Hashtbl

let diagnostics = ref false

let activate_diagnostics () = diagnostics := true
let deactivate_diagnostics () = diagnostics := false
let collect_diagnostics () = !diagnostics


class log_message_t (index:int) (tag:string) (msg:pretty_t) =
object (self: 'a)
    
  val index = index
  val tag = tag
  val msg = msg

  method getIndex = index
  method getTag = tag
  method getMsg = msg

  method compare (m: 'a) = Stdlib.compare index m#getIndex
  method toPretty = LBLOCK [ STR tag ; STR ": " ; msg ]

end


class type logger_int =
  object
    method set_max_entry_size: int -> unit
    method add: string -> pretty_t -> unit
    method reset: unit
    method size: int
    method tagsize: string -> int
    method toPretty: pretty_t
  end


class logger_t:logger_int =
object (self)

  val store = H.create 3
  val order = H.create 3
  val mutable index = 0
  val mutable max_entry_size = 0
  val mutable tags_discontinued = []

  method set_max_entry_size n = max_entry_size <- n

  method add (tag:string) (msg:pretty_t) =
    if List.mem tag tags_discontinued then
      ()
    else
      let _ =
        if H.mem store tag then
          ()
        else
	  begin
            H.add order tag index;
            index <- index + 1
          end in
      let entry =
        if H.mem store tag then
          H.find store tag
        else
          [] in
      if max_entry_size > 0 && (List.length entry) > (max_entry_size -2) then
	begin
	  tags_discontinued <- tag :: tags_discontinued;
	  H.replace store tag ((STR "DISCONTINUED") :: entry)
	end
      else  
	H.replace store tag (msg :: entry)

  method reset = H.clear store

  method size = H.fold (fun _ v a -> a + (List.length v)) store 0

  method tagsize (tag:string) = 
    if H.mem store tag then List.length (H.find store tag) else 0

  method toPretty = 
    let tags = ref [] in
    let _ = H.iter (fun k _ -> tags := (k, H.find order k) :: !tags) store in
    let tags = List.sort (fun (_, i1) (_, i2) -> Stdlib.compare i2 i1) !tags in
    let pp = ref [] in
    let _ =
      List.iter (fun (t, _) ->
          let entry = H.find store t in
          let ppl = ref [] in
          let _ =
            List.iter
              (fun p -> ppl := (LBLOCK [STR "     "; p; NL]) :: !ppl) entry in
          pp :=
            (LBLOCK [
                 NL;
                 STR "~~~~~~~~~~";
                 STR t;
                 STR " (";
		 INT (List.length entry);
                 STR ")";
		 STR " ~~~~~~~~~~";
                 NL;
                 LBLOCK !ppl;
                 NL]) :: !pp) tags in
    LBLOCK [
        (if max_entry_size > 0 then
	   LBLOCK [STR "Maximum entry size: "; INT max_entry_size; NL; NL]
         else
           STR ""); LBLOCK !pp; NL]

end
      
    
let mk_logger () = new logger_t

let chlog = new logger_t
let ch_info_log = new logger_t
let ch_error_log = new logger_t
let ch_diagnostics_log = new logger_t


let log_traceresult_value
      (logger: logger_int) (tag: string) (r: 'a traceresult) ~(default: 'a) =
  match r with
  | Ok v -> v
  | Error lst ->
     let msg = String.concat "; " lst in
     begin
       logger#add tag (STR msg);
       default
     end


let log_traceresult
      (logger: logger_int) (tag: string) (f:('a -> unit)) (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | Error lst ->
     let msg = String.concat "; " lst in
     logger#add tag (STR msg)


let log_traceresult_list
      (logger: logger_int)
      (tag: string)
      (f: ('a -> 'b list))
      (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | Error lst ->
     let msg = String.concat "; " lst in
     begin
       logger#add tag (STR msg);
       []
     end


let log_traceresult_string
      (logger: logger_int)
      (tag: string)
      (f: ('a -> string))
      (r: 'a traceresult) =
  match r with
  | Ok v -> f v
  | Error lst ->
     let msg = String.concat "; " lst in
     begin
       logger#add tag (STR msg);
       ""
     end


let log_traceresult2
      (logger: logger_int)
      (tag: string)
      (f: ('a -> 'b -> unit))
      (r1: 'a traceresult)
      (r2: 'b traceresult) =
  let do_log (l: string list) = logger#add tag (STR (String.concat "; " l)) in
  match (r1, r2) with
  | (Ok v1, Ok v2) -> f v1 v2
  | (Ok v1, Error e2) -> do_log e2
  | (Error e1, Ok v2) -> do_log e1
  | (Error e1, Error e2) -> do_log (e1 @ e2)


let log_traceresult2_list
      (logger: logger_int)
      (tag: string)
      (f: ('a -> 'b -> 'c list))
      (r1: 'a traceresult)
      (r2: 'b traceresult): 'c list =
  let do_log (l: string list) =
    begin
      logger#add tag (STR (String.concat "; " l));
      []
    end in
  match (r1, r2) with
  | (Ok v1, Ok v2) -> f v1 v2
  | (Ok v1, Error e2) -> do_log e2
  | (Error e1, Ok v2) -> do_log e1
  | (Error e1, Error e2) -> do_log (e1 @ e2)
