(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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

(** Utility to log events and timing *)

open Printf


type log_level_t =
  | CHLog_None
  | CHLog_Debug
  | CHLog_Info
  | CHLog_Warning
  | CHLog_Error
  | CHLog_Critical


let level_to_string (lvl: log_level_t) =
  match lvl with
  | CHLog_None -> ""
  | CHLog_Debug -> "DEBUG"
  | CHLog_Info -> "INFO"
  | CHLog_Warning -> "WARNING"
  | CHLog_Error -> "ERROR"
  | CHLog_Critical -> "CRITICAL"


let string_to_level (s: string) =
  match s with
  | "NONE" -> CHLog_None
  | "DEBUG" -> CHLog_Debug
  | "INFO" -> CHLog_Info
  | "WARNING" -> CHLog_Warning
  | "ERROR" -> CHLog_Error
  | "CRITICAL" -> CHLog_Critical
  | _ -> CHLog_None


let int_of_level (lvl: log_level_t) =
  match lvl with
  | CHLog_None -> 0
  | CHLog_Debug -> 1
  | CHLog_Info -> 2
  | CHLog_Warning -> 3
  | CHLog_Error -> 4
  | CHLog_Critical -> 5


let output = ref stderr
let level = ref CHLog_Warning
let prefix = ref ""

let set_level (lvl: log_level_t) = level := lvl

let set_output (out: out_channel) = output := out


let set_timestamp (lvl: log_level_t) =
    let ts = Unix.gettimeofday() in
    let tm = Unix.localtime ts in
    let us, _s = modf ts in
    sprintf
      (* "%04d.%02d.%02d %02d:%02d.%02d.%03d:chk:%s%s: "
      (1900 + tm.Unix.tm_year)
      (1 + tm.Unix.tm_mon)
      tm.Unix.tm_mday *)
      "%02d:%02d.%02d.%03d:chk:%s%s: "      
      tm.Unix.tm_hour
      tm.Unix.tm_min
      tm.Unix.tm_sec
      (int_of_float (1_000. *. us))
      (level_to_string lvl)
      !prefix


let log lvl fmt =
  if int_of_level lvl >= int_of_level !level then
    let logstr = set_timestamp lvl in
    fprintf !output ("%s" ^^ fmt ^^ "\n%!") logstr
  else
    ifprintf !output fmt


let set_log_level lvl = set_level (string_to_level lvl)

let set_log_output output = set_output output


let log_debug fmt = log CHLog_Debug fmt

let log_info fmt = log CHLog_Info fmt

let log_warning fmt = log CHLog_Warning fmt

let log_error fmt = log CHLog_Error fmt

let log_critical fmt = log CHLog_Critical fmt
