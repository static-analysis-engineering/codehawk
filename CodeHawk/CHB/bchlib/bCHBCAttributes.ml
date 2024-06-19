(* =============================================================================
   CodeHawk Binary Analyzer
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

open BCHBCTypes


let gcc_attributes_to_precondition_attributes
      (attrs: b_attributes_t): precondition_attribute_t list =
  List.fold_left (fun acc a ->
      match a with
      | Attr ("access", params) ->
         (match params with
          | [ACons ("read_only", []); AInt refindex] ->
             (APCReadOnly (refindex, None)) :: acc
          | [ACons ("read_only", []); AInt refindex; AInt sizeindex] ->
             (APCReadOnly (refindex, Some sizeindex)) :: acc
          | [ACons ("write_only", []); AInt refindex] ->
             (APCWriteOnly (refindex, None)) :: acc
          | [ACons ("write_only", []); AInt refindex; AInt sizeindex] ->
             (APCWriteOnly (refindex, Some sizeindex)) :: acc
          | [ACons ("read_write", []); AInt refindex] ->
             (APCReadWrite (refindex, None)) :: acc
          | [ACons ("read_write", []); AInt refindex; AInt sizeindex] ->
             (APCReadWrite (refindex, Some sizeindex)) :: acc
          | _ -> acc)
      | _ -> acc) [] attrs


let precondition_attributes_t_to_gcc_attributes
      (preattrs: precondition_attribute_t list): b_attributes_t =
  let get_params (refindex: int) (optsizeindex: int option) =
    match optsizeindex with
    | Some sizeindex -> [AInt refindex; AInt sizeindex]
    | _ -> [AInt refindex] in
  let get_access (mode: string) (params: b_attrparam_t list) =
    Attr ("access", [ACons (mode, [])] @ params) in
  List.fold_left (fun acc p ->
      match p with
      | APCReadOnly (refindex, optsizeindex) ->
         (get_access "read_only" (get_params refindex optsizeindex)) :: acc
      | APCWriteOnly (refindex, optsizeindex) ->
         (get_access "write_only" (get_params refindex optsizeindex)) :: acc
      | APCReadWrite (refindex, optsizeindex) ->
         (get_access "read_write" (get_params refindex optsizeindex)) :: acc
      | _ -> acc) [] preattrs

                                                                           


                                     
