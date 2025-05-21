(* =============================================================================
   CodeHawk C Analyzer
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

open CCHBasicTypes
open CCHLibTypes


(** {1 Function Attributes} *)

(** Function declarations in C can be decorated with attributes. These attributes
    are generally used to allow certain compiler optimizations
    (https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html). Here
    we use them to specify function contracts, by converting them into
    preconditions, postconditions, and side effects.

    The CodeHawk-C analyzer has comprehensive function summaries (represented
    in xml) for most standard
    library functions, which are used to
    (1) generate primary proof obligations for the arguments passed to calls to
        those functions according to the preconditions,
    (2) discharge proof obligations against the postcondition guarantees, and
    (3) adjust the semantics of the call in case of side effects.

    However, applications may be dynamically linked to other
    libraries for which such summaries are not available in the C analyzer. One
    option is for the user to construct these summaries in xml and supply them
    to the analyzer as an additional set of summaries. While this may be the
    preferred option if the library in question is a frequently used one (e.g.,
    openssl), but in most cases, writing function summaries in xml is not
    attractive.

    Another, more convenient, option is to annotate the function signatures
    in the header or c files with function attributes that can be interpreted
    as preconditions, postconditions, and/or side effects.

    Gcc provides a large collection of function attributes used for various
    purposes (https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html),
    and many libraries have already been annotated with these attributes. In
    this case the C-analyzer can directly take advantage of those.

    To avoid conflicts the C-analyzer provides for all of the standard gcc
    attributes a corresponding chkc_-version of the same attribute, if, for
    some reason, the user does not want to affect the compilation process in
    the given way, but still needs the pre- and postconditions.

    Below we describe the attributes currently supported, and their conversion
    into preconditions, postconditions, and side effects. We first describe
    current gcc function attributes whose meaning closely resembles the
    conditions generated, followed by attributes that have no corresponding
    gcc attribute, or whose meaning is sufficiently different in the CH
    context that re-using the same name may be misleading.

*)

(** {2 Gcc Attributes}

    {3 access}

    The [access] attribute is applicable to functions that are passed a
    pointer to a buffer that may be read or written to in the function.

    {[
    (__access__ (access-mode, ref-index))
    (__access__ (access-mode, ref-index, size-index))
    ]}

    Access modes supported are [read_only], [read_write], and [write_only];
    the [ref-index] is an integer denoting the (1-based) index of the pointer
    argument being accessed, and [size-index] is an integer denoting the
    (1-based) index of an argument that provides a maximum size (in bytes)
    for the memory region accessed.

    As an example, for [memcpy] this would be decorated as:

    {[
    __attribute__ ((__access__ (__read_only__, 2, 3)),
                   (__access__ (__write_only__, 1, 3)))
    void* memcpy (void *dst, const void *src, size_t len);
    ]}

    (Note that the analyzer has a comprehensive function summary for memcpy, so
    it is only shown here as an example, because of its familiar semantics.)

    - both [read_only] and [write_only] give rise to precondition proof obligations
      that argument [ref-index] points at a buffer that is at least the size
      provided by argument [size-index];
    - the [write_only] attribute additionally gives rise to a side effect of the
      given number of bytes written to argument [ref-index].
 *)

(** {3 const}

    The [const] attribute is applicable to functions that are purely functional,
    that is, their return value is solely determined by their arguments (and
    not by the rest of the program state), and they are side-effect free.

    Example:

    {[ __attribute__ ((__const__)) int square(int x) ]}

    This attribute will give rise to the postcondition (and side effect)
    [XFunctional], which can be used to answer postcondition requests that
    memory was not freed (among other things).
 *)

(** {3 format}

    The format attribute is applicable to functions that take a format string
    as an argument with additional arguments that are to be checked against
    that format string.

    {[
    (__format__ (archetype, string-index, first-to-check))
    ]}

    The archetype specifies the type of format string. Current archetypes
    supported are [printf] and [scanf].

    Example:

    {[
    extern int my_printf (void *dst, const char *fmt, ...)
       __attribute__ ((__format__(printf, 2, 3)));
    ]}

    The format argument with [printf] and [scanf] archetype gives rise to an
    XOutputFormatString and XInputFormatString precondition, respectively.
 *)

(** {3 malloc}

    The malloc attribute can be used for malloc-like functions that return a
    newly allocated pointer that is guaranteed not to alias with any existing
    pointer.

    {[
    (__malloc__)
    (__malloc__ (deallocator))
    (__malloc__ (deallocator, ptr-index))
    ]}

    Optionally it can have one or two arguments, where [deallocator] is the
    name of the function that can be used to deallocate the resource (default
    [free]), and [ptr-index] is the (1-based) index of the argument of the
    deallocator function that receives the pointer (default: 1).

    The attribute will generate the postconditions [XNewMemory] and, in case
    of deallocator [free], the postconditions [XHeapAddress] and
    [XAllocationBase].

    Note: the gcc documentation
    (https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html)
    states that the malloc attribute can also be used for other resources than
    memory, e.g., for file pointers. Their example is:

    {[
    int fclose (FILE* );

     __attribute__ ((malloc, malloc (fclose, 1)))
       FILE* fdopen (int, const char * );
    ]}

    This use of the [malloc] attribute is not yet supported.
 *)

(** {3 nonnull}

    The [nonnull] attribute can be used for a function to indicate that one or
    more pointer arguments to the function must not be null.

    Example:

    {[
    extern void *
    my_memcpy (void *dst, void *src, size_t len)
        __attribute__((__nonnull__ (1, 2)));
    ]}

    This attribute will generate [XNotNull] preconditions on the function for
    all arguments included.
 *)

(** {3 noreturn}

    The [noreturn] attribute can be used to indicate that a call to the function
    does not return. The attribute will result in the postcondition [XFalse]
    for the function.
 *)

(** {3 null_terminated_string_arg}

    The [null_terminated_string_arg] can be used to indicate that one or more
    pointer arguments must, if not null, point to a null-terminated string.

    Example:

    {[
    char * my_strcpy (char *dst, char *src)
        __attribute__((__null_terminated_string_arg (2)));
    ]}

    This attribute will generate [XNullTerminated] preconditions on the function
    for all arguments included.
 *)

(** {3 pure}

    The [pure] attribute is used for functions that have no observable effect
    on the program state except for the value they return. It differs from
    the [const] attribute in that it may read values from the program state
    and so successive calls to the function with the same argument may,
    unlike functions with the [const] attribute, have different return
    values.

    This attribute will generate the [XPreservesAllMemory] and
    [XPreservesNullTermination] side effects.
 *)

(** {3 returns_nonnull}

    The returns_nonnull attribute specifies that the function must return a
    non-null pointer.

    Example:

    {[
    extern void* myalloc (size_t len) __attribute__ ((returns_nonnull));
    ]}

    This attribute will generate the [XNotNull] postcondition for the function.
 *)

(** {2 CH-specific Attributes}

    {3 chkc_preserves_all_memory}

    The [chkc_preserves_all_memory] applies to functions that do not free
    any memory (i.e., the function, nor its descendants make any call to
    [free]). This attribute will generate a [XPreservesAllMemory] side
    effect.

    {3 chkc_preserves_memory}

    The [chkc_preserves_memory] can be used to specify that the memory pointed
    to by arguments given to the function is not freed. Note that this is a weaker
    requirement than the [chkc_preserves_all_memory] which requires no [free]
    at all in the downstream callgraph.

    Example:

    {[
    extern char* my_strcpy(char *dst, char *src)
       __attribute__ ((__chkc_preserves_memory (1, 2)));
    ]}

    This attribute will generate [XPreservesMemory] side effects for all
    arguments specified.

    {3 chkc_returns_null_terminated_string}

    The [chkc_returns_null_terminated_string] attribute specifies that the
    function must return a null-terminated string.

    Example:

    {[
    extern char* my_strcpy (char *dst, char *src)
        __attribute__ ((returns_null_terminated_string));
    ]}

    This attribute will generate the [XNullTerminated] postcondition for the
    function.

    Note: the [XNullTerminated] postcondition is currently not used in the
    discharge of proof obligations.
 *)


val convert_attribute_to_function_conditions:
  string
  -> attribute
  -> (xpredicate_t list * xpredicate_t list * xpredicate_t list)


(** {1 Global Variable Attributes}

    {2 CH-specific Attributes}

    {3 chkc_le}

    {[__chkc_le__ (upper-bound)]}

    The [chkc_le] attribute specifies that the value of a global variable is
    less than or equal to [upper-bound].

    This attribute can be used to discharge upper-bound proof obligations on
    global variables and may itself also give rise to new proof obligations.

    Example:

    {[ int globalvar __attribute__ ((__chkc_le__ (100))); ]}

    {3 chkc_lt}

    {[__chkc_lt__ (upper-bound)]}

    The [chkc_lt] attribute specifies that the value of a global variable is
    less than [upper-bound].

    {3 chkc_ge}

    {[__chkc_ge__ (lower-bound)]}

    The [chkc_ge] attribute specifies that the value of a global variable is
    greater than or equal to [lower-bound].

    {3 chkc_gt}

    {[__chkc_gt__ (lower-bound)]}

    the [chkc_gt] attribute specifies that the value of a global variable is
    greater than [lower-bound].

    {3 chkc_value}

    {[__chkc_value__ (value)]}

    The [chkc_value] attribute (usually used in combination with the [chkc_const]
    attribute) specifies that the global variable has value [value] (currently
    limited to integer values).

    {3 chkc_const}

    {[__chkc_const__]}

    The [chkc_const] attribute specifies that the value of the global variable
    does not change.

    {3 chkc_static}

    {[__chkc_static__]}

    The [chkc_static] attribute specifies that the visibility of the global
    variable is limited to the current compilation unit.

    {3 chkc_not_null__]}

    The [chkc_not_null] attribute specifies that the value of the global 
    variable is not null.
 *)
  
val attribute_update_globalvar_contract:
  globalvar_contract_int -> attribute -> unit
