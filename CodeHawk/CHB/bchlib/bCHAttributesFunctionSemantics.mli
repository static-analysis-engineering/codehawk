(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2026  Aarno Labs LLC

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

(** Function declarations in C can be decorated with attributes to communicate
    preconditions, side effects, and postconditions about dynamically linked
    library functions to the analyzer.

    For many standard libc library functions the analyzer has a comprehensive
    collection of (hand-made) function summaries that include pre- and
    postconditions, side effects, etc., represented in XML. However, binaries
    may be dynamically linked to a wide variety of other libraries for which
    it is not feasible to create such summaries. A more user-friendly means of
    providing this information is through function prototypes decorated with
    suitable attributes, as described here.

    {2 Attribute policy}

    Two categories of attributes are accepted on input. Only [chk_pre],
    [chk_se], and [chk_post] are emitted in generated output headers; the
    GCC compatibility attributes are read-only (see
    bCHFunctionSemanticsAttributes.ml for the output path).

    {3 GCC compatibility attributes (read-only)}

    These attributes are accepted so that existing annotated system headers
    (e.g., glibc) can be consumed without modification.

    {4 access}

    Syntax (GCC standard):
    {[
    __attribute__ ((access (access-mode, ref-index)))
    __attribute__ ((access (access-mode, ref-index, size-index)))
    ]}

    Access modes: [read_only] -> {!XXBuffer}; [write_only] -> {!XXBlockWrite};
    [read_write] -> both. [ref-index] is the 1-based index of the pointer
    argument; [size-index] is the 1-based index of the argument giving the
    size in bytes. [write_only] and [read_write] also produce an
    {!XXBlockWrite} side effect.

    {4 nonnull}

    Syntax:
    {[
    __attribute__ ((nonnull))
    __attribute__ ((nonnull (ref-index, ...)))
    ]}

    Bare form: all pointer-typed parameters must be non-null -> {!XXNotNull}
    for each. Indexed form: listed parameters must be non-null -> {!XXNotNull}
    per index.

    {4 format}

    Syntax:
    {[
    __attribute__ ((format (archetype, string-index, first-to-check)))
    ]}

    [printf] and [gnu_printf] archetypes -> {!XXOutputFormatString} on the
    format string parameter. [scanf] and [gnu_scanf] archetypes ->
    {!XXInputFormatString} on the format string parameter. Other archetypes
    are accepted but produce no precondition.

    {4 noreturn}

    Syntax:
    {[
    __attribute__ ((noreturn))
    ]}

    Sets [fq_noreturn = Some true] in {!function_qualifiers_t}. Indicates
    that the function does not return to the caller.

    {4 pure}

    Syntax:
    {[
    __attribute__ ((pure))
    ]}

    Sets [fq_functional = Some FPure] in {!function_qualifiers_t}. The
    function has no side effects but its return value may depend on global
    state or memory passed via pointers (e.g., [strlen]).

    {4 const}

    Syntax:
    {[
    __attribute__ ((const))
    ]}

    Sets [fq_functional = Some FConst] in {!function_qualifiers_t}. The
    function reads only its direct arguments and has no side effects
    (e.g., [abs], [sqrt]). Strictly stronger than [pure].

    {4 warn_unused_result}

    Syntax:
    {[
    __attribute__ ((warn_unused_result))
    ]}

    Sets [fq_must_use_return = Some true] in {!function_qualifiers_t}. The
    caller is obligated to inspect the return value. Equivalent to
    [chk_qual(must_use_return)] for headers that use the GCC standard form.

    {3 CodeHawk-specific attributes}

    These are the canonical forms used in hand-written CodeHawk header files
    and in generated output headers. All use the [chk_pre] attribute name
    with a sub-tag as the first parameter identifying the predicate kind.

    All argument indices are 1-based. Index 0 refers to the return value
    (relevant for postconditions via [chk_post]).

    {4 Buffer and memory region predicates}

    {[
    __attribute__ ((chk_pre (deref_read, ref-index)))
    __attribute__ ((chk_pre (deref_read, ref-index, size-index)))
    __attribute__ ((chk_pre (deref_read (size), ref-index)))
    __attribute__ ((chk_pre (deref_read (ntp), ref-index)))
    ]}
    -> {!XXBuffer}: pointer argument [ref-index] must be readable for at
    least the given number of bytes ([size-index] argument, constant [size],
    or up to the null terminator [ntp]).

    {[
    __attribute__ ((chk_pre (deref_write, ref-index)))
    __attribute__ ((chk_pre (deref_write, ref-index, size-index)))
    __attribute__ ((chk_pre (deref_write (size), ref-index)))
    ]}
    -> {!XXBlockWrite}: pointer argument [ref-index] must be writable for at
    least the given number of bytes.

    {[
    __attribute__ ((chk_pre (initialized_range (ntp), ref-index)))
    ]}
    -> {!XXInitializedRange}: memory starting at [ref-index] is initialized
    up to the null terminator.

    {[
    __attribute__ ((chk_pre (no_overlap, ref-index-1, ref-index-2)))
    ]}
    -> {!XXNoOverlap}: the memory regions pointed to by the two arguments
    must not overlap.

    {4 Null and zero predicates}

    {[
    __attribute__ ((chk_pre (not_null, ref-index)))
    ]}
    -> {!XXNotNull}: argument must not be null.

    {[
    __attribute__ ((chk_pre (null_terminated, ref-index)))
    ]}
    -> {!XXNullTerminated}: argument points to a null-terminated string.

    {[
    __attribute__ ((chk_pre (not_zero, ref-index)))
    ]}
    -> {!XXNotZero}: argument must not be zero.

    {[
    __attribute__ ((chk_pre (non_negative, ref-index)))
    ]}
    -> {!XXNonNegative}: argument must not be negative.

    {4 Relational predicates}

    {[
    __attribute__ ((chk_pre (relational_expr (op), ref-index-1, ref-index-2)))
    ]}
    -> {!XXRelationalExpr}: the two arguments satisfy the given relation.
    Operators: [eq], [lt], [leq], [gt], [geq], [neq].

    {4 Format string predicates}

    {[
    __attribute__ ((chk_pre (output_format_string, ref-index)))
    ]}
    -> {!XXOutputFormatString}: argument is a printf-style format string.

    {[
    __attribute__ ((chk_pre (input_format_string, ref-index)))
    ]}
    -> {!XXInputFormatString}: argument is a scanf-style format string.

    {4 Trusted string and allocation predicates}

    {[
    __attribute__ ((chk_pre (allocation_base, ref-index)))
    ]}
    -> {!XXAllocationBase}: argument is the base address of a dynamically
    allocated region.

    {[
    __attribute__ ((chk_pre (trusted_string, ref-index)))
    ]}
    -> {!XXTrustedString}: argument is a trusted string value.

    {[
    __attribute__ ((chk_pre (trusted_os_cmd_string, ref-index)))
    ]}
    -> {!XXTrustedOsCmdString}: argument is safe to pass to [system(3)].

    {[
    __attribute__ ((chk_pre (trusted_os_cmd_fmt_string (kind, size), ref-index)))
    ]}
    -> {!XXTrustedOsCmdFmtString}: the string constructed from this format
    argument is safe to pass to [system(3)].

    {3 chk_qual: CodeHawk function qualifiers}

    These are the canonical forms for non-predicate function properties that
    have no GCC-standard attribute equivalent. Unlike [chk_pre] (preconditions)
    and [chk_se] (side effects), [chk_qual] qualifiers carry no argument
    indices — they are properties of the function itself.

    {[
    __attribute__ ((chk_qual (sets_errno)))
    ]}
    Sets [fq_sets_errno = Some true] in {!function_qualifiers_t}. The function
    sets [errno] to indicate the specific error when it fails. This is a
    property documented in the C standard and POSIX, distinct from any
    observable memory side effect.

    {[
    __attribute__ ((chk_qual (must_use_return)))
    ]}
    Sets [fq_must_use_return = Some true] in {!function_qualifiers_t}. The
    caller is obligated to inspect the return value (e.g., to check for an
    error code). Implied by the presence of an error-postcondition in a
    function summary; provided here for use in hand-written CodeHawk headers.

    {2 Example}

    For [memcpy]:
    {[
    __attribute__ ((access (read_only, 2, 3)),
                   (access (write_only, 1, 3)),
                   (nonnull (1, 2)))
    void *memcpy (void *dst, const void *src, size_t len);
    ]}

    (The analyzer has a comprehensive built-in summary for [memcpy]; this
    is shown only as an illustration of the attribute syntax.)
 *)

val convert_b_attributes_to_function_conditions:
  function_interface_t
  -> b_attributes_t
  -> (xxpredicate_t list
      * xxpredicate_t list
      * xxpredicate_t list
      * function_qualifiers_t)
