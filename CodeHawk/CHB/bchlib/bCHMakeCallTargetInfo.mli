(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2020       Henny B. Sipma
   Copyright (c) 2021-2024  Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes


(** Utility functions to create call targets for individual call sites.*)


(** Returns an unknown target with name "unknown" and no parameters.

    {b Note}: An unknown target, unlike other types of targets, is continually
    attempted to be resolved, and, if successfully resolved, replace with
    another type of target.*)
val mk_unknown_target: unit -> call_target_info_int


(** [mk_app_target ~fintft faddr] returns an application function target.
    If no function interface [fintf] is specified the function interface is
    extracted from the analysis results present in the function info for
    function address [faddr]. If a function interface [fintf] is given
    this function interface is used with a default function semantics (that is,
    no further analysis results are used).

    {b Note}: An app target may be updated at a later stage when more analysis
    data is available; e.g., it can be updated to include a stack adjustment.*)
val mk_app_target:
  ?fintf:function_interface_t option -> doubleword_int -> call_target_info_int


(** [mk_dll_target dll name] returns a function stub target for the (MSWindows, PE)
    library function obtained from dynamically linked library [dll] with
    function name [name]. If a summary is available for this library function,
    the summary function signature and semantics (preconditions, postconditions,
    etc) are included in the call target. If not, only the name is available in
    the stub target.*)
val mk_dll_target: string -> string -> call_target_info_int


(** [mk_so_target name] returns a function stub target for a standard library
    function (usually, but not necessarily, libc) (ELF) with name [name]. If
     a function summary for [name] is available in the [so_functions] directory,
     or if a function prototype has been provided via a header file, the
     function signature and semantics (in case of a summary) are included in
     the call target. If not, only the name is available in the stub target.*)
val mk_so_target: string -> call_target_info_int


(** [mk_syscall_target index] returns a function stub target for the Linux system
    call function with index [index]. If a function summary for [index] is
    available in the [syscalls] directory, the function signature and
    function semantics from the summary are included in the call target. If
    not, only the name ([Linux-syscall-<index>]) is available in the stub target.
 *)
val mk_syscall_target: int -> call_target_info_int


(** [mk_jni_target index] returns a function stub target for a JNI (Java Native
    Method Interface) function with index [index]. If a function summary for
    [index] is available in the [jni] directory, the function signature and
    function semantics from the summary are included in the call target. If
    not, only the name ([jni_<index>]) is available in the stub target.*)
val mk_jni_target: int -> call_target_info_int


(** [mk_virtual_target fintf] returns a default call target with the name
    taken from the function interface [fintf] and target [VirtualTarget fintf].*)
val mk_virtual_target: function_interface_t -> call_target_info_int


(** [mk_inlined_app target faddr name] returns an [InlinedAppTarget] call
    target with name [name] for the application function with address [faddr].

    {b Note}: At present it does not inherit the function interface and
    semanics from the application function, so it only provides the name.*)
val mk_inlined_app_target: doubleword_int -> string -> call_target_info_int


(** [mk_static_dll_stub_target faddr dll name] returns a static stub target
    for the (MSWindows, PE) library function otherwise obtained from dll [dll]
    with function name [name]. In this case the function has been statically
    linked in (and has been recognized as such). By using a static stub target
    the call target info can take advantage of the function signature and
    semantics provided in the corresponding library function summary.*)
val mk_static_dll_stub_target:
  doubleword_int -> string -> string -> call_target_info_int


(** [mk_static_pck_stub_target faddr lib pkgs name] returns a static stub
    target for a C++ function identified with package names [pkgs] and name
    [name].*)
val mk_static_pck_stub_target:
  doubleword_int -> string -> string list -> string -> call_target_info_int


(** [mk_wrapped_target faddr fintf tgt params] returns a target that wraps
    another call target to the application function with address faddr and
    new function interface [fintf], original call target [tgt] and parameter
    mapping [params].

    {b Note}: This functionality is intended to allow some partial evaluation;
    currently only used in x86 (PE).*)
val mk_wrapped_target:
  doubleword_int
  -> function_interface_t
  -> call_target_t
  -> (fts_parameter_t * bterm_t) list
  -> call_target_info_int


(** [mk_call_target_info ctgt] returns a default call-target-info structure
    depending on the type of call target.*)
val mk_call_target_info: call_target_t -> call_target_info_int


(** [update_target_interface ctinfo] returns a calltarget that is identical
    to [ctinfo] except for the function interface, which is updated to be
    [fintf].

    {b Note:} It is the caller's responsibility to ensure that the semantics
    is still consistent with the updated function interface.*)
val update_target_interface:
  call_target_info_int -> function_interface_t -> call_target_info_int
