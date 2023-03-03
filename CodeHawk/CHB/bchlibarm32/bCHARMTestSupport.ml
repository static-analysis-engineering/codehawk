(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs, LLC

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


(* chlib *)
open CHLanguage

(* chutil *)
open CHTraceResult

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes

module H = Hashtbl

type testdatatype_t =
  | Tst_instrx_data of variable_t list * xpr_t list
  | Tst_instrx_tags of string list
  | Tst_chif_conditionxprs of
      arm_assembly_instruction_int * arm_assembly_instruction_int * xpr_t list


class testsupport_t: testsupport_int =
object (self)

  val testdata = H.create 3

  method request_instrx_data = H.add testdata "instrx_data" (H.create 3)

  method request_instrx_tags = H.add testdata "instrx_tags" (H.create 3)

  method request_chif_conditionxprs =
    H.add testdata "chif_conditionxprs" (H.create 3)

  method requested_instrx_data = H.mem testdata "instrx_data"

  method requested_instrx_tags = H.mem testdata "instrx_tags"

  method requested_chif_conditionxprs = H.mem testdata "chif_conditionxprs"

  method submit_instrx_data
           (iaddr: doubleword_int)
           (vars: variable_t list)
           (xprs: xpr_t list) =
    if H.mem testdata "instrx_data" then
      H.add
        (H.find testdata "instrx_data")
        iaddr#to_hex_string
        (Tst_instrx_data (vars, xprs))

  method submit_instrx_tags
           (iaddr: doubleword_int)
           (tags: string list) =
    if H.mem testdata "instrx_tags" then
      H.add
        (H.find testdata "instrx_tags")
        iaddr#to_hex_string
        (Tst_instrx_tags tags)

  method retrieve_instrx_data (iaddr: string) =
    if H.mem testdata "instrx_data" then
      if H.mem (H.find testdata "instrx_data") iaddr then
        match (H.find (H.find testdata "instrx_data") iaddr) with
        | Tst_instrx_data (vars, xprs) -> Ok (vars, xprs)
        | _ -> Error ["retrieve_instrx_data: internal error"]
      else
        Error ["no data submitted for instrx_data for iaddr: " ^ iaddr]
    else
      Error ["no request made for instrx_data "]

  method retrieve_instrx_tags (iaddr: string) =
    if H.mem testdata "instrx_tags" then
      if H.mem (H.find testdata "instrx_tags") iaddr then
        match (H.find (H.find testdata "instrx_tags") iaddr) with
        | Tst_instrx_tags sl -> Ok sl
        | _ -> Error ["retrieve_instrx_tags: internal error"]
      else
        Error ["no data submitted for instrx_tags for iaddr: " ^ iaddr]
    else
      Error ["no request made for instrx_tags"]

  method submit_chif_conditionxprs
           (consumer: arm_assembly_instruction_int)
           (producer: arm_assembly_instruction_int)
           (xprs: xpr_t list) =
    if H.mem testdata "chif_conditionxprs" then
      H.add
        (H.find testdata "chif_conditionxprs")
        consumer#get_address#to_hex_string
        (Tst_chif_conditionxprs (consumer, producer, xprs))

  method retrieve_chif_conditionxprs (iaddr: string) =
    if H.mem testdata "chif_conditionxprs" then
      if H.mem (H.find testdata "chif_conditionxprs") iaddr then
        match (H.find (H.find testdata "chif_conditionxprs") iaddr) with
        | Tst_chif_conditionxprs (consumer, producer, xprs) ->
           Ok (consumer, producer, xprs)
        | _ -> Error ["retrieve_chif_conditionxprs: internal error"]
      else
        let keys = H.fold (fun k _ v -> k::v) (H.find testdata "chif_conditionxprs") [] in
        Error [
            "no data submitted for chif_conditionxprs for iaddr: "
            ^ iaddr
            ^ " (values found: ["
            ^ (String.concat "," keys)
            ^ ")]"]
    else
      Error ["no request made for chif_conditionxprs"]

end


let testsupport = new testsupport_t
