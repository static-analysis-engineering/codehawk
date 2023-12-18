(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023  Aarno Labs LLC

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
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypeUtil
open BCHGlobalState
open BCHLibTypes
open BCHLocation


let x2p = xpr_formatter#pr_expr


class memory_recorder_t
        (finfo: function_info_int)
        (iaddr: ctxt_iaddress_t): memory_recorder_int =
object (self)

  val finfo = finfo
  val iaddr = iaddr

  method finfo = finfo

  method private faddr: doubleword_int = self#finfo#get_address

  method private env = self#finfo#env

  method iaddr = iaddr

  method private loc: location_int =
    ctxt_string_to_location self#faddr self#iaddr

  method private get_gvalue (x: xpr_t) =
    match x with
    | XConst (IntConst n) -> GConstant n
    | XVar v when self#env#is_return_value v ->
       let callSite = self#env#get_call_site v in
       GReturnValue (ctxt_string_to_location self#faddr callSite)
    | XVar v when self#env#is_sideeffect_value v ->
       let callSite = self#env#get_call_site v in
       let argdescr = self#env#get_se_argument_descriptor v in
       GSideeffectValue (ctxt_string_to_location self#faddr callSite, argdescr)
    | XVar v when self#env#is_stack_parameter_variable v ->
       begin
         try
	   match self#env#get_stack_parameter_index v with
	   | Some index -> GArgValue (self#faddr, index, [])
	   | _ -> GUnknownValue
         with
         | BCH_failure p ->
            raise
              (BCH_failure (LBLOCK [STR "memory recorder:get_gvalue: "; p]))
       end
    | _ -> GUnknownValue

  method record_assignment
           (lhs: variable_t)
           (rhs: xpr_t)
           ?(size=None)
           ?(vtype=t_unknown)
           () =
    begin
      self#record_assignment_lhs lhs rhs size vtype;
      self#record_assignment_rhs rhs size vtype;
    end

  method private record_assignment_lhs
                   (lhs: variable_t)
                   (rhs: xpr_t)
                   (size: int option)
                   (vtype: btype_t) =
    if self#env#is_global_variable lhs
       && (self#env#has_global_variable_address lhs) then
      global_system_state#add_writer
        ~ty:vtype
        ~size
        (self#get_gvalue rhs)
        (self#env#get_global_variable_address lhs)
        self#loc
    else if self#env#is_stack_variable lhs then
      let offset = self#env#get_memvar_offset lhs in
      match offset with
      | ConstantOffset (n, NoOffset) ->
         self#finfo#stackframe#add_store
           ~offset:n#toInt ~size ~typ:(Some vtype) ~xpr:(Some rhs) lhs iaddr
      | _ ->
         chlog#add
           "stack assignment lhs not recorded"
           (LBLOCK [self#loc#toPretty; STR ": "; lhs#toPretty])      
    else
      chlog#add
        "assignment lhs not recorded"
        (LBLOCK [self#loc#toPretty; STR ": "; lhs#toPretty; STR " := "; x2p rhs])

  method private record_assignment_rhs
                   (rhs: xpr_t) (size: int option) (vtype: btype_t) =
    let vars = variables_in_expr rhs in
    List.iter (fun v ->
        if self#env#is_global_variable v
           && (self#env#has_global_variable_address v) then
          global_system_state#add_reader
            ~ty:vtype
            ~size
            (self#env#get_global_variable_address v)
            self#loc
        else if self#env#is_stack_variable v then
          let offset = self#env#get_memvar_offset v in
          match offset with
          | ConstantOffset (n, NoOffset) ->
             self#finfo#stackframe#add_load
               ~offset:n#toInt ~size ~typ:(Some vtype) v iaddr
          | _ ->
             chlog#add
               "stack assignment rhs not recorded"
               (LBLOCK [self#loc#toPretty; STR ": "; v#toPretty])
        else
          chlog#add
            "assignment rhs not recorded"
            (LBLOCK [self#loc#toPretty; STR ": "; v#toPretty])) vars

  method record_load
           ~(addr: xpr_t)
           ~(var: variable_t)
           ~(size: int)
           ~(vtype: btype_t) =
    if self#env#is_stack_variable var then
      let offset = self#env#get_memvar_offset var in
      match offset with
      | ConstantOffset (n, NoOffset) ->
         self#finfo#stackframe#add_load
           ~offset:n#toInt ~size:(Some size) ~typ:(Some vtype) var iaddr
      | _ ->
         chlog#add
           "stack load not recorded"
           (LBLOCK [
                self#loc#toPretty;
                STR ": ";
                x2p addr;
                STR " (";
                var#toPretty;
                STR ")"])
    else
      chlog#add
        "memory load not recorded"
        (LBLOCK [
             self#loc#toPretty;
             STR "; ";
             x2p addr;
             STR " (";
             var#toPretty;
             STR ")"])

  method record_store
           ~(addr: xpr_t)
           ~(var: variable_t)
           ~(size: int)
           ~(vtype: btype_t)
           ~(xpr: xpr_t) =
    if self#env#is_stack_variable var then
      let offset = self#env#get_memvar_offset var in
      match offset with
      | ConstantOffset (n, NoOffset) ->
         self#finfo#stackframe#add_store
           ~offset:n#toInt
           ~size:(Some size)
           ~typ:(Some vtype)
           ~xpr:(Some xpr)
           var
           iaddr
      | _ ->
         chlog#add
           "stack store not recorded"
           (LBLOCK [
                self#loc#toPretty;
                STR ": ";
                x2p addr;
                STR " (";
                var#toPretty;
                STR "): ";
                x2p xpr])
    else
      chlog#add
        "memory store not recorded"
        (LBLOCK [
             self#loc#toPretty;
             STR ": ";
             x2p addr;
             STR " (";
             var#toPretty;
             STR "): ";
             x2p xpr])

  method record_call_sideeffect
           (addr: xpr_t)
           (rhs: xpr_t)
           ?(size=None)
           ?(vtype=t_unknown)
           () =
    ()

end


let mk_memory_recorder = new memory_recorder_t
