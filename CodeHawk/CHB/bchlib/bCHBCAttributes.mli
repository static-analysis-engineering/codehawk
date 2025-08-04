(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2025  Aarno Labs LLC

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
open BCHLibTypes


(** {1 Function attributes} *)

(** Function declarations in C can be decorated with attributes. These attributes
    are generally used to allow certain compiler optimizations
    (https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html). Here
    we use them to communicate preconditions about dynamically linked library
    functions.

    For many standard libc library functions the analyzer has comprehensive
    collection of (hand-made) function summaries that include pre- and
    postconditions, side effects, etc, represented in xml.
    However, binaries may of course be dynamically linked to a wide variety of
    other libraries, for which it is not directly feasible to create these
    summaries (e.g., because suitable binaries are not available for analysis).
    One possibility is for the user to manually create the xml function summaries
    for all functions of interest. A more user-friendly means of providing
    similar information is through function prototypes decorated with suitable
    attributes, as described here.

    We use the same syntax as presented in
    (https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html).
    Currently the following attributes are supported:

    {[
    (access (access-mode, ref-index))
    (access (access-mode, ref-index, size-index))
    (nonnull (ref-indices))
    ]}

    Access modes supported are [read_only], [read_write], and [write_only]; the
    [ref-index] is an integer denoting the (1-based) index of the pointer
    argument being accessed, and [size-index] is an integer denoting the
    (1-based) index of an argument that provides a maximum size (in bytes)
    for the memory region accessed.

    As an example, for [memcpy] this would be decorated as:

    {[
    __attribute__ ((access (read_only, 2, 3)),
                   (access (write_only, 1, 3)), (nonnull (1, 2)))
    void* memcpy (void *dst, const void *src, size_t len);
    ]}

    (Note that the analyzer has a comprehensive function summary for memcpy, so
    it is only shown here as an example, because of its familiar semantics.)

    A prototype thus decorated will automatically generate a function interface
    with the function semantics that include the corresponding preconditions
    (and, in case of write_only, the corresponding side effect) for the given
    library function, resulting in the appropriate proof obligations at their
    call sites.
 *)

val convert_b_attributes_to_function_conditions:
  string
  -> function_interface_t
  -> b_attributes_t
  -> (xxpredicate_t list * xxpredicate_t list * xxpredicate_t list)
