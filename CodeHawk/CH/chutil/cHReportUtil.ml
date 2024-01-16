(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

open Unix

(* chlib *)
open CHPretty

(* chutil *)
open CHPrettyUtil


(* Convert standard Unix time representation to a string *)
let time_to_string (f:float):string =
  let tm = Unix.localtime f in
  let sp ip = if ip < 10 then LBLOCK [STR "0"; INT ip] else INT ip in
  let p =
    LBLOCK [
        sp (tm.tm_mon + 1);
        STR "/";
        sp tm.tm_mday;
	STR "/";
        sp (tm.tm_year + 1900);
	STR " "; sp tm.tm_hour;
	STR ":"; sp tm.tm_min;
	STR ":"; sp tm.tm_sec] in
  pretty_to_string p


let current_time_to_string ():string = time_to_string (Unix.gettimeofday ())


let get_report_header
      ?(analysistime=(-1.0))
      ?(prefix="")
      (analyzer:string)
      (version:string)
      (reportname:string)
      (programname:string) =
  let sTime = if analysistime < 0.1 then
      Printf.sprintf "%.4f" analysistime
    else if analysistime < 1.0 then
      Printf.sprintf "%.3f" analysistime
    else if analysistime < 10.0 then
      Printf.sprintf "%.2f" analysistime
    else if analysistime < 100.0 then
      Printf.sprintf "%.1f" analysistime
    else  string_of_int (int_of_float analysistime) in
  LBLOCK [
      STR prefix;
      STR (string_repeat "=" 80);
      NL;
      STR prefix;
      STR "CodeHawk ";
      STR analyzer;
      STR " (version ";
      STR version;
      STR ") ";
      STR prefix;
      STR reportname;
      NL;
      STR prefix;
      STR "Program analyzed: ";
      STR programname;
      NL;
      (if analysistime > 0.0 then
	 LBLOCK [
             STR prefix; STR "Analysis time   : "; STR sTime; STR " secs"; NL]
       else
	 STR "");
      STR prefix;
      STR "Date            : ";
      STR (current_time_to_string ());
      NL;
      STR prefix;
      STR (string_repeat "=" 80);
      NL]
