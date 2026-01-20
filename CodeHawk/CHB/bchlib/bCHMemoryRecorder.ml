(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2025  Aarno Labs LLC

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
open CHTraceResult

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes

(* bchlib *)
open BCHBCTypes
open BCHBCTypePretty
open BCHBCTypeUtil
open BCHDoubleword
open BCHGlobalState
open BCHLibTypes
open BCHLocation
open BCHMemoryReference

module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)

let x2s_r x_r =
  match x_r with
  | Ok x -> x2s x
  | Error e -> "Error: " ^ (String.concat "; " e)


(* Emit log message only in the last run of the analyzer. *)
let log_dc_error_result
      ?(msg="")
      ?(tag="")
      (filename: string)
      (linenumber: int)
      (msgs: string list) =
  if BCHSystemSettings.system_settings#collect_data then
    log_error_result ~msg ~tag filename linenumber msgs


let mmap = BCHGlobalMemoryMap.global_memory_map


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
       TR.tfold
         ~ok:(fun callSite ->
           GReturnValue (ctxt_string_to_location self#faddr callSite))
         ~error:(fun e ->
           begin
             log_diagnostics_result
               ~msg:(p2s self#loc#toPretty)
               ~tag:"memrecorder:get_gvalue"
               __FILE__ __LINE__ (e @ ["invalid callsite"]);
             GUnknownValue
           end)
         (self#env#get_call_site v)
    | XVar v when self#env#is_sideeffect_value v ->
       TR.tfold
         ~ok: (fun callSite ->
           TR.tfold
             ~ok:(fun argdescr ->
               GSideeffectValue
                 (ctxt_string_to_location self#faddr callSite, argdescr))
             ~error:(fun e ->
               begin
                 log_diagnostics_result
                   ~msg:(p2s self#loc#toPretty)
                   ~tag:"memrecorder:get_gvalue"
                   __FILE__ __LINE__ (e @ ["invalide side-effect descriptor"]);
                 GUnknownValue
               end)
             (self#env#get_se_argument_descriptor v))
         ~error:(fun e ->
           begin
             log_diagnostics_result
               ~msg:(p2s self#loc#toPretty)
               ~tag:"memrecorder:get_gvalue"
               __FILE__ __LINE__ (e @ ["invalide side-effect value"]);
             GUnknownValue
           end)
         (self#env#get_call_site v)
    | XVar v when self#env#is_stack_parameter_variable v ->
       (match self#env#get_stack_parameter_index v with
	| Some index -> GArgValue (self#faddr, index, [])
	| _ -> GUnknownValue)
    | _ -> GUnknownValue

  method record_argument
           ?(btype = t_unknown)
           (argvalue: xpr_t)
           (argindex: int): global_location_int option =
    match argvalue with
    | XConst (IntConst n)
         when mmap#is_global_data_address (numerical_mod_to_doubleword n) ->
       mmap#add_gaddr_argument self#faddr iaddr argvalue argindex btype
    | _ ->
       None

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
      TR.tfold
        ~ok:(fun gaddr ->
          global_system_state#add_writer
            ~ty:vtype ~size (self#get_gvalue rhs) gaddr self#loc)
        ~error:(fun e ->
          log_error_result
            ~tag:"record_assignment_lhs"
            ~msg:(p2s self#loc#toPretty)
            __FILE__ __LINE__
            (["invalid global address for: " ^ (p2s lhs#toPretty)] @ e))
        (self#env#get_global_variable_address lhs)
    else if self#env#is_stack_variable lhs then
      TR.tfold
        ~ok:(fun stackoffset ->
          match stackoffset with
          | ConstantOffset (n, offset) ->
             self#finfo#stackframe#add_store
               ~baseoffset:n#toInt
               ~offset
               ~size
               ~typ:(Some vtype)
               ~xpr:(Some rhs)
               lhs
               iaddr
          | _ ->
             log_diagnostics_result
               ~tag:"record_assignment_lhs"
               ~msg:(p2s self#loc#toPretty)
               __FILE__ __LINE__
               ["stack assignment lhs not recorded";
                "lhs: " ^ (p2s lhs#toPretty)])
        ~error:(fun e ->
          log_error_result
            ~tag:"record_assignment_lhs"
            ~msg:(p2s self#loc#toPretty)
            __FILE__ __LINE__
            (["invalid offset for: " ^ (p2s lhs#toPretty)] @ e))
        (self#env#get_memvar_offset lhs)
    else
      log_diagnostics_result
        ~tag:"record_assignment_lhs"
        ~msg:(p2s self#loc#toPretty)
        __FILE__ __LINE__
        ["assignment lhs not recorded";
         "lhs: " ^ (p2s lhs#toPretty);
         "rhs: " ^ (x2s rhs)]

  method private record_assignment_rhs
                   (rhs: xpr_t) (size: int option) (vtype: btype_t) =
    let vars = variables_in_expr rhs in
    List.iter (fun v ->
        if self#env#is_global_variable v
           && (self#env#has_global_variable_address v) then
          TR.tfold
            ~ok:(fun gaddr ->
              global_system_state#add_reader ~ty:vtype ~size gaddr self#loc)
            ~error:(fun e ->
              log_error_result
                ~tag:"record_assignment_rhs"
                ~msg:(p2s self#loc#toPretty)
                __FILE__ __LINE__
                (["invalid global address for: " ^ (x2s rhs)] @ e))
            (self#env#get_global_variable_address v)
        else if self#env#is_stack_variable v then
          TR.tfold
            ~ok:(fun stackoffset ->
              match stackoffset with
              | ConstantOffset (n, offset) ->
                 self#finfo#stackframe#add_load
                   ~baseoffset:n#toInt
                   ~offset
                   ~size
                   ~typ:(Some vtype)
                   v
                   iaddr
              | _ ->
                 log_diagnostics_result
                   ~tag:"record_assignment_rhs"
                   ~msg:(p2s self#loc#toPretty)
                   __FILE__ __LINE__
                   ["stack assignment rhs not recorded";
                    "v: " ^ (p2s v#toPretty);
                    "rhs: " ^ (x2s rhs)])
            ~error:(fun e ->
              log_error_result
                ~tag:"record_assignment_rhs"
                ~msg:(p2s self#loc#toPretty)
                __FILE__ __LINE__
                (["invalid offset for: " ^ (x2s rhs)] @ e))
            (self#env#get_memvar_offset v)
        else
          log_diagnostics_result
            ~tag:"record_assignment_rhs"
            ~msg:(p2s self#loc#toPretty)
            __FILE__ __LINE__
            ["assignment not recorded";
             "v: " ^ (p2s v#toPretty);
             "rhs: " ^ (x2s rhs)]) vars

  method record_load
           ~(signed: bool)
           ~(addr: xpr_t)
           ~(var: variable_t)
           ~(size: int)
           ~(vtype: btype_t) =
    log_dc_error_result
      ~msg:(p2s self#loc#toPretty)
      ~tag:"deprecated: record_load"
      __FILE__ __LINE__
      ["memory_recorder#record_load is deprecated. ";
       "To be replaced with record_load_r";
       "signed: " ^ (if signed then "T" else "F");
       "addr: " ^ (x2s addr);
       "var: " ^ (p2s var#toPretty);
       "size: " ^ (string_of_int size);
       "vtype: " ^ (btype_to_string vtype)]
      (*
    if self#env#is_stack_variable var then
      self#record_stack_variable_load ~signed ~var ~size ~vtype
    else if self#env#is_basevar_memory_variable var then
      log_dc_error_result
        ~msg:(p2s self#loc#toPretty)
        ~tag:"record memory load"
        __FILE__ __LINE__
        ["Recording of basevar loads not yet supported. Var: "
         ^ (p2s var#toPretty)
         ^ ". Addr: " ^ (x2s addr)]
    else
      match mmap#add_gload self#faddr iaddr addr size signed with
      | Ok () -> ()
      | Error e ->
         log_dc_error_result
           ~msg:(p2s self#loc#toPretty)
           ~tag:"record_load"
           __FILE__ __LINE__ e
       *)

  method private record_stack_variable_load
                   ~(signed: bool)
                   ~(var: variable_t)
                   ~(size: int)
                   ~(vtype: btype_t) =
    TR.tfold
      ~ok:(fun stackoffset ->
        match stackoffset with
        | ConstantOffset (n, offset) ->
           self#finfo#stackframe#add_load
             ~baseoffset:n#toInt
             ~offset
             ~size:(Some size)
             ~typ:(Some vtype)
             var
             iaddr
        | _ ->
           log_dc_error_result
             ~tag:"record_stack_variable_load"
             ~msg:(p2s self#loc#toPretty)
             __FILE__ __LINE__
             ["offset: " ^ (BCHMemoryReference.memory_offset_to_string stackoffset);
              "signed: " ^ (if signed then "yes" else "no")])
      ~error:(fun e -> log_dc_error_result __FILE__ __LINE__ e)
      (self#env#get_memvar_offset var)

  method private record_global_variable_load
                   ~(signed: bool)
                   ~(var: variable_t)
                   ~(size: int) =
    TR.tfold
      ~ok:(fun globaloffset ->
        match globaloffset with
        | ConstantOffset (n, offset) ->
           let gaddr = numerical_mod_to_doubleword n in
           mmap#add_location_gload self#faddr iaddr gaddr offset size signed t_unknown
        | _ ->
           log_error_result
             ~msg:(p2s self#loc#toPretty)
             ~tag:"record_global_variable_load"
             __FILE__ __LINE__
             ["Unexpected offset for global variable " ^ (p2s var#toPretty)
              ^ ": " ^ (memory_offset_to_string globaloffset)])
      ~error:(fun e ->
        log_dc_error_result
          ~msg:(p2s self#loc#toPretty)
          ~tag:"record_global_variable_load"
          __FILE__ __LINE__
          (e @ ["Unable to obtain offset from variable " ^ (p2s var#toPretty)]))
    (self#env#get_memvar_offset var)

  method record_load_r
           ~(signed: bool)
           ~(addr_r: xpr_t traceresult)
           ~(var_r: variable_t traceresult)
           ~(size: int)
           ~(vtype: btype_t) =
    TR.tfold
      ~ok:(fun var ->
        if self#env#is_stack_variable var then
          self#record_stack_variable_load ~signed ~var ~size ~vtype
        else if self#env#is_global_variable var then
          self#record_global_variable_load ~signed ~var ~size
        else if self#env#is_basevar_memory_variable var then
          log_dc_error_result
            ~msg:(p2s self#loc#toPretty)
            ~tag:"record_load_r"
            __FILE__ __LINE__
            ["Recording of basevar loads not yet supported. Var: "
             ^ (p2s var#toPretty)
             ^ ". Addr: " ^ (x2s_r addr_r)]
        else
          TR.tfold
            ~ok:(fun addr ->
              log_dc_error_result
                ~msg:(p2s self#loc#toPretty)
                ~tag:"record_load_r"
                __FILE__ __LINE__
                ["Unable to record memory load for variable " ^ (p2s var#toPretty)
                 ^ " with address " ^ (x2s addr)])
            ~error:(fun e ->
              log_dc_error_result
                ~msg:(p2s self#loc#toPretty)
                ~tag:"record_load_r"
                __FILE__ __LINE__
                (["Unable to record memory load for variable " ^ (p2s var#toPretty)]
                 @ e))
                (*
          TR.tfold
            ~ok:(fun addr ->
              match mmap#add_gload self#faddr iaddr addr size signed with
              | Ok () -> ()
              | Error e ->
                 log_dc_error_result
                   ~msg:(p2s self#loc#toPretty)
                   ~tag:"record_load"
                   __FILE__ __LINE__ e)
            ~error:(fun e -> log_error_result __FILE__ __LINE__ e)*)
            addr_r)
      ~error:(fun e -> log_dc_error_result __FILE__ __LINE__ e)
      var_r

  method record_store
           ~(addr: xpr_t)
           ~(var: variable_t)
           ~(size: int)
           ~(vtype: btype_t)
           ~(xpr: xpr_t) =
    if self#env#is_stack_variable var then
      self#record_stack_variable_store ~var ~size ~vtype ~xpr_r:(Ok xpr)
    else if self#env#is_basevar_memory_variable var then
      log_dc_error_result
        ~msg:(p2s self#loc#toPretty)
        ~tag:"record memory store"
        __FILE__ __LINE__
        ["Recording of basevar loads not yet supported. Var: "
         ^ (p2s var#toPretty)
         ^ ". Addr: " ^ (x2s addr)]
    else
      let optvalue =
        match xpr with
        | XConst (IntConst n) -> Some n
        | _ -> None in
      let add_gstore gaddr =
        match mmap#add_gstore self#faddr iaddr gaddr size optvalue with
        | Ok () -> ()
        | Error e ->
           log_dc_error_result
             ~msg:(p2s self#loc#toPretty)
             ~tag:"record_store"
             __FILE__ __LINE__
             (["addr: " ^ (x2s addr); "var: " ^ (p2s var#toPretty)] @ e) in
                     (*
      match addr with
      | XOp ((Xf "addressofvar"), [XVar v]) when self#env#is_global_variable v ->
         TR.tfold
           ~ok:add_gstore
           ~error:(fun e ->
             begin
               log_dc_error_result
                 ~msg:(p2s self#loc#toPretty)
                 ~tag:"record_store"
                 __FILE__ __LINE__
                 (["addr: " ^ (x2s addr); "var: " ^ (p2s var#toPretty)] @ e);
               ()
             end)
           (self#env#get_global_variable_address v)
      | _ -> *) add_gstore addr

  method private record_stack_variable_store
                   ~(var: variable_t)
                   ~(size: int)
                   ~(vtype: btype_t)
                   ~(xpr_r: xpr_t traceresult) =
    TR.tfold
      ~ok:(fun stackoffset ->
        match stackoffset with
        | ConstantOffset (n, offset) ->
           self#finfo#stackframe#add_store
             ~baseoffset:n#toInt
             ~offset
             ~size:(Some size)
             ~typ:(Some vtype)
             ~xpr:(TR.tfold_default (fun x -> Some x) None xpr_r)
             var
             iaddr
        | _ ->
           log_dc_error_result
             ~msg:(p2s self#loc#toPretty)
             ~tag:"record_store"
             __FILE__ __LINE__
             ["var: " ^ (p2s var#toPretty);
              "stack offset: "
              ^ BCHMemoryReference.memory_offset_to_string stackoffset])
      ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
      (self#env#get_memvar_offset var)

  method record_store_r
           ~(addr_r: xpr_t traceresult)
           ~(var_r: variable_t traceresult)
           ~(size: int)
           ~(vtype: btype_t)
           ~(xpr_r: xpr_t traceresult) =
    TR.tfold
      ~ok:(fun var ->
        if self#env#is_stack_variable var then
          self#record_stack_variable_store ~var ~size ~vtype ~xpr_r
        else if self#env#is_basevar_memory_variable var then
          log_dc_error_result
            ~msg:(p2s self#loc#toPretty)
            ~tag:"record memory store"
            __FILE__ __LINE__
            ["Recording of basevar loads not yet supported. Var: "
             ^ (p2s var#toPretty)
             ^ ". Addr: " ^ (x2s_r addr_r)]
        else
          TR.tfold
            ~ok:(fun addr ->
              let optvalue =
                match xpr_r with
                | Ok (XConst (IntConst n)) -> Some n
                | _ -> None in
              match mmap#add_gstore self#faddr iaddr addr size optvalue with
              | Ok () -> ()
              | Error e ->
                 log_dc_error_result
                   ~msg:(p2s self#loc#toPretty)
                   ~tag:"record store"
                   __FILE__ __LINE__ e)
            ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
            addr_r)
      ~error:(fun e -> log_dc_error_result __FILE__ __LINE__ e)
      var_r

end


let mk_memory_recorder = new memory_recorder_t
