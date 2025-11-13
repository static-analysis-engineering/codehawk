(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2025  Aarno Labs LLC

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

module A = TCHAssertion

let expect_safe_detail
      ?(msg="")
      ~(po: CCHPreTypes.proof_obligation_int)
      ~(xdetail: string)
      ~(expl: string)
      () =
  match po#get_status with
  | Green ->
     (match po#get_explanation with
      | Some x ->
         let dmatch = (expl = "") || (expl = x.smsg_msg) in
         if not dmatch then
           A.equal_string ~msg:"Explanation is different" expl x.smsg_msg
         else
           (match x.smsg_loc with
            | Some ocode ->
               A.equal_string ~msg xdetail ocode.ocode_detail
            | _ ->
               A.fail_msg "Received explanation without location detail")
      | _ ->
         A.fail_msg "Received proof obligation without explanation")
  | s ->
     A.fail_msg
       ("Received proof obligation with status "
        ^ (CCHPreSumTypeSerializer.po_status_mfts#ts s))


let expect_violation_detail
      ?(msg="")
      ~(po: CCHPreTypes.proof_obligation_int)
      ~(xdetail: string)
      ~(expl: string)
      () =
  match po#get_status with
  | Red ->
     (match po#get_explanation with
      | Some x ->
         let dmatch = (expl = "") || (expl = x.smsg_msg) in
         if not dmatch then
           A.equal_string ~msg:"Explanation is different" expl x.smsg_msg
         else
           (match x.smsg_loc with
            | Some ocode ->
               A.equal_string ~msg xdetail ocode.ocode_detail
            | _ ->
               A.fail_msg "Received explanation without location detail")
      | _ ->
         A.fail_msg "Received proof obligation without explanation")
  | s ->
     A.fail_msg
       ("Received proof obligation with status "
        ^ (CCHPreSumTypeSerializer.po_status_mfts#ts s))
