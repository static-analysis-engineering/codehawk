(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
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

(* chutil *)
open CHTimingLog

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty
   

let convert_attribute_to_function_conditions
      (name: string)
      (attr: attribute):(xpredicate_t list * xpredicate_t list * xpredicate_t list) =

  let arg (i: int) = ArgValue (ParFormal i, ArgNoOffset) in

  match attr with
  | Attr (("access" | "chkc_access"), attrparams) ->
     let (pre, side) =
       (match attrparams with
        | [ACons ("read_only", []); AInt refindex] ->
           ([XBuffer (arg refindex, RuntimeValue)], [])

        | [ACons ("read_only", []); AInt refindex; AInt sizeindex] ->
           ([XBuffer (arg refindex, arg sizeindex)], [])

        | [ACons (("write_only" | "read_write"), []); AInt refindex] ->
           ([XBuffer (arg refindex, RuntimeValue)],
            [XBlockWrite (arg refindex, RuntimeValue)])

        | [ACons (("write_only" | "read_write"), []);
           AInt refindex; AInt sizeindex] ->
           ([XBuffer (arg refindex, arg sizeindex)],
            [XBlockWrite (arg refindex, arg sizeindex)])

        | _  ->
           begin
             log_info
               "attribute conversion for %s: attribute parameters %s not recognized"
               name
               (String.concat ", " (List.map attrparam_to_string attrparams));
             ([], [])
           end) in
       
     (pre, [], side)

  | Attr ("aconst", []) ->
     ([], [XFunctional], [XFunctional])

  | Attr ("format", attrparams) ->
     let pre =
       (match attrparams with
        | [ACons ("printf", []); AInt stringindex; AInt _firsttocheck] ->
           [XOutputFormatString (arg stringindex)]
        | [ACons ("scanf", []); AInt stringindex; AInt _firsttocheck] ->
           [XInputFormatString (arg stringindex)]
        | _ ->
           begin
             log_info
               "attribute conversion for %s: attribute parameters %s not recognized"
               name
               (String.concat ", " (List.map attrparam_to_string attrparams));
             []
           end) in
     (pre, [], [])

  | Attr ("malloc", attrparams) ->
     let post =
       (match attrparams with
        | []
          | [ACons ("free", [])]
          | [ACons ("free", []); AInt 1]->
           [XNewMemory ReturnValue;
            XHeapAddress ReturnValue;
            XAllocationBase ReturnValue]
        | _ ->
           begin
             log_info
               "attribute conversion for %s: attribute parameters %s not recognized"
               name
               (String.concat ", " (List.map attrparam_to_string attrparams));
             []
           end) in
     ([], post, [])

  | Attr ("nonnull", attrparams) ->
     let pre =
       List.fold_left (fun acc attrparam ->
           match attrparam with
           | AInt i -> (XNotNull (arg i)) :: acc
           | _ ->
              begin
                log_info
                  ("attribute conversion for %s: parameter %s not recognized "
                   ^^ "(excluded)")
                  name
                  (attrparam_to_string attrparam);
                acc
              end) [] attrparams in
     (pre, [], [])

  | Attr ("noreturn", []) ->
     ([], [XFalse], [])

  | Attr ("null_terminated_string_arg", attrparams) ->
     let pre =
       List.fold_left (fun acc attrparam ->
           match attrparam with
           | AInt i -> (XNullTerminated (arg i)) :: acc
           | _ ->
              begin
                log_info
                  ("attribute conversion for %s: parameter %s not recognized "
                   ^^ "(excluded)")
                  name
                  (attrparam_to_string attrparam);
                acc
              end) [] attrparams in
     (pre, [], [])

  | Attr ("pure", []) ->
     ([], [], [XPreservesAllMemory; XPreservesNullTermination])

  | Attr ("returns_nonnull", []) ->
     ([], [XNotNull ReturnValue], [])

  | Attr ("chkc_returns_null_terminated_string", []) ->
     ([], [XNullTerminated ReturnValue], [])

  | Attr ("chkc_preserves_all_memory", []) ->
     ([], [], [XPreservesAllMemory])

  | Attr ("chkc_preserves_memory", attrparams) ->
     let se =
       List.fold_left (fun acc attrparam ->
           match attrparam with
           | AInt i -> (XPreservesMemory (arg i)) :: acc
           | _ ->
              begin
                log_info
                  ("attribute conversion for %s: parameter %s not recognized "
                   ^^ "(excluded)")
                  name
                  (attrparam_to_string attrparam);
                acc
              end) [] attrparams in
     ([], [], se)
          
  | _ -> ([], [], [])


let attribute_update_globalvar_contract
      (gvarc: globalvar_contract_int) (attr: attribute) =
  match attr with
  | Attr ("chkc_le", [AInt i]) -> gvarc#set_upper_bound i
  | Attr ("chkc_lt", [AInt i]) -> gvarc#set_upper_bound (i-1)
  | Attr ("chkc_ge", [AInt i]) -> gvarc#set_lower_bound i
  | Attr ("chkc_gt", [AInt i]) -> gvarc#set_lower_bound (i+1)
  | Attr ("chkc_value", [AInt i]) -> gvarc#set_value i
  | Attr ("chkc_static", []) -> gvarc#set_static
  | Attr ("chkc_const", []) -> gvarc#set_const
  | Attr ("chkc_not_null", []) -> gvarc#set_not_null
  | Attr (s, attrparams) ->
     log_info
       "global variable attribute %s for %s with %d parameters not recognized"
       s
       gvarc#get_name
       (List.length attrparams)
              
