(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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
open CHPretty

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


(**
   {[
   ==============================================================================
   Grammar
   ==============================================================================

   mangled-name:
     ? base-name @ function-type-code storage-class

  base-name:
     ? operator-code name-string
     name-string @

  function-type-code:
    function-access returntype argument-list

  storage-class:
     A    : normal storage
     B    : volatile storage
     C    : const storage
     Z    : executable storage

  operator-code:
     0    : constructor
     1    : destructor
     2    : operator new
     3    : operator delete
     4    : operator=
     5    : operator>>
     6    : operator<<
     7    : operator!
     8    : operator==
     9    : operator!=
     A    : operator[]
     B    : operator int
     D    : operator*
     E    : operator++
     F    : operator--
     G    : operator-
     H    : operator+
     I    : operator&
     M    : operator<
     N    : operator<=
     O    : operator>
     P    : operator>=
     R    : operator()
     S    : operator~
     U    : operator|
     X    : operator*=
     Y    : operator+=
     Z    : operator-=
     _0   : operator/=
     _4   : operator&=
     _5   : operator|=
     _6   : operator^=
     _7   : vftable
     _8   : vbtable
     _V   : operator delete[]

  function-access:
     (x-access-qualifier const-qualifier | s-access-qualifier) calling-convention

  x-access-qualifier
     A    private
     E    private virtual
     I    protected
     M    protected virtual
     Q    public
     U    public virtual

  const-qualifier
     A    non-const
     B    const

  s-access-qualifier
     C    private static
     K    protected static
     S    public static
     Y    default

  calling-convention:
     A  __cdecl
     E  __thiscall
     G  __stdcall
     I  __fastcall

   returntype :
     type-code

   argument-list
     ( type-code ) *

   type-code:
     ( s-data-type | complex-type )

   type-modifier
     | A    non-const
     | B    const

   complex-type:
     | P type-modifier complex-type
     | s-data-type

   s-data-type:
     C    signed char
     D    char
     E    unsigned char
     F    short
     G    unsigned short
     H    int
     I    unsigned int
     J    long
     K    unsigned long
     M    float
     N    double
     X    void
     Z    ellipsis
     _J   __int64
     _K    unsigned __int64
     _N   BOOL
     _W   wchar_t

   x-data-type:
     A    ref
     P    pointer
     Q    array
     U    struct
     V    class
     W    enum
  ]}

  currently not supported yet:
    - fields
    - function pointers

 *)

val demangle: string -> string
val has_demangled_name: string -> bool
val get_demangled_name: string -> demangled_name_t
val report_demangling_failures: unit -> unit
val retrieve_demangling_failures: unit -> (string * pretty_t) list

val templated_btype_to_name: btype_t -> int -> string
