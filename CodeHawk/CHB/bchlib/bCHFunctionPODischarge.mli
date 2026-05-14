(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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


(** Post-analysis proof-obligation discharge for a single function.

    This module contains the principal implementation for discharging proof
    obligations at the function level. Several passes may be made through the
    function if proof obligations are delegated to other instructions within
    the code using reaching definitions.

    Three discharge strategies are applied, in order of locality:

    1. {b Direct discharge (stmt)}: The PO can be closed using information
       available with the instruction itself. This may include function
       arguments obtained through invariant propagation.

    2. {b Intra-procedural delegation}: The PO on a call or call argument is
       delegated to another instruction or to another argument in the same
       call. The PO considered is closed and a new (open) PO is created for
       the target of the delegation, to be possibly discharged in the next
       pass.

       Intra-instruction delegation is typically enabled by call target side
       effects. An example is: the PO [XPOTrustedOsCmdString(cmd)] on the
       destination buffer of a (v)s(n)printf call can be transferred to a
       PO [XPOTrustedOsCmdFmtString(fmt,.,.)] on the format string.

       Inter-instruction delegation is typically enabled by reaching
       definitions rather than invariants. Invariants would already be
       available at the instruction itself. Reaching definitions allow
       POs to be transferred to, for example, multiple joining branches,
       where invariants would lose information.

    3. {b Inter-procedural delegation}: If all arguments to the PO are
       received as arguments to the calling function (as established by
       invariants), the PO is delegated to the function api and converted
       into a precondition of the function. These preconditions will then
       be converted into POs on the callers of the function in the next
       analysis round.

    {b Proof obligations currently supported:}

    - [XPOTrustedOsCmdString(cmd)]: [cmd] is safe to use as an argument to
      [system]

    - [XPOTrustedOsCmdFmtString(fmt, kind, size)]: the format string [fmt]
      constructs a string that is safe to use as an argument to [system].
      The [kind] determines the location of the format arguments: [VA_LIST]
      (as in [vsprintf]) or [FMT_ARGS] (as in [sprintf]). The [size] argument
      is optional; if present it denotes the maximum length of the string
      that can be formed.
      A format string [fmt] is considered to construct a string that is safe
      to pass to a call to [system] if it does not contain any %s format
      specifiers.

    - [XPOOutputFormatString(fmt)]: the format string [fmt] is a constant
      string.

    - [XPOBlockWrite (ty, buffer, size)]: at least [size] bytes can be safely
      written to [buffer].

    - [XPOBuffer (ty, buffer, size)]: at least [size] bytes can be safely
      read from [buffer].

    - [XPONotNull (ptr)]: [ptr] is not null.

    - [XPONullTerminated (ptr)]: the string address [ptr] points to a string
      that is null-terminated.

    - [XPOInitializedRange (ty, ptr, size)]: the address [ptr] points to a
      buffer that has been initialized to at least [size] bytes.

    {b Side effects:}

    The discharge of proof obligations has the following side effects on other
    parts of the code:

    1. Update of the status of the proof obligation in the proof obligations
       storage in [BCHProofObligations] if the status changes.

    2. Addition of a function parameter to the calling function api for all
       parameters that occur in a delegated PO (in [BCHFunctionInfo]). This has
       no effect if the function api was derived externally (e.g., from a header
       file), or if the parameter was added before.

    3. Creation of a precondition on the calling function api if a PO is
       delegated to the function api (in [BCHFunctionInfo]).

    4. Creation of an [XXBlockWrite] side effect on the calling function api
       if an [XPOBlockWrite] PO is delegated to the function function api
       (in [BCHFunctionInfo]).
 *)

(** Main entry point for discharging proof obligations. [max_passes] denotes
    the maximum number of passes made to resolve proof obligations delegated
    locally within the function. The default value is 8. In practice a fixed
    point will be reached with a value of at most 3 and iteration will stop
    at that point.*)
val discharge_function_proofobligations:
  ?max_passes:int -> BCHLibTypes.function_info_int -> unit
