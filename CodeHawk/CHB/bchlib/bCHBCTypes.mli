(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHTraceResult
open CHXmlDocument


type constantstring = string * bool * int


type ikind_t =
| IChar       (** [char] *)
| ISChar      (** [signed char] *)
| IUChar      (** [unsigned char] *)
| IWChar      (** [Windows, not in cil] *)
| IBool       (** [_Bool (C99)] *)
| IInt        (** [int] *)
| IUInt       (** [unsigned int] *)
| IShort      (** [short] *)
| IUShort     (** [unsigned short] *)
| ILong       (** [long] *)
| IULong      (** [unsigned long] *)
| ILongLong   (** [long long] (or [_int64] on Microsoft Visual C) *)
| IULongLong  (** [unsigned long long] (or [unsigned _int64] on Microsoft
                  Visual C) *)
| IInt128     (** added in goblint-cil *)
| IUInt128    (** added in goblint-cil *)
| INonStandard of bool * int
(** [local to binary analyzer, not in cil: signed, size in bytes] *)


type signedness_t = Signed | Unsigned | SignedNeutral


(** Various kinds of floating-point numbers*)
type fkind_t =
| FFloat      (** [float] *)
| FDouble     (** [double] *)
| FLongDouble (** [long double] *)
| FComplexFloat (** added in goblint-cil *)
| FComplexDouble (** added in goblint-cil *)
| FComplexLongDouble (** added in goblint-cil *)

type frepresentation_t = FScalar | FPacked


type bstorage_t =
| NoStorage
| Static
| Register
| Extern
| Opaque of int


type unop_t =
| Neg
| BNot
| LNot


type binop_t =
| PlusA
| PlusPI
| IndexPI
| MinusA
| MinusPI
| MinusPP
| Mult
| Div
| Mod
| Shiftlt
| Shiftrt
| Lt
| Gt
| Le
| Ge
| Eq
| Ne
| BAnd
| BXor
| BOr
| LAnd
| LOr

type varuse_t = string * int      (* vname, vid *)

type fielduse_t = string * int    (* fname, fckey *)

(** Offset and size (in bytes) of a struct field.*)
type fieldlayout_t = int * int

type type_transformer_t = string -> string

(** {1 Types and attributes} *)

(** {2 Precondition attributes}

    Function declarations in C can be decorated with attributes. These attributes
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

type precondition_attribute_t =
  | APCReadOnly of int * int option (* ref-index, size-index, both 1-based *)
  | APCWriteOnly of int * int option (* ref-index, size-index, (both 1-based) *)
  | APCReadWrite of int * int option (* ref-index, size-index, (both 1-based) *)
  | APCNull of int list  (* parameter indices, 1-based *)


and btype_t =
| TVoid of b_attributes_t
| TInt of ikind_t * b_attributes_t
| TFloat of fkind_t * frepresentation_t * b_attributes_t
| TPtr of btype_t * b_attributes_t
| TRef of btype_t * b_attributes_t   (* not in cil *)
| THandle of string * b_attributes_t    (* not in cil *)
| TArray of btype_t * bexp_t option * b_attributes_t
| TFun of btype_t * bfunarg_t list option * bool * b_attributes_t
| TNamed of string * b_attributes_t
| TComp of int * b_attributes_t
| TEnum of string * b_attributes_t
| TCppComp of tname_t * tname_t list * b_attributes_t  (* C++ name spaces *)
| TCppEnum of tname_t * tname_t list * b_attributes_t  (* C++ name spaces *)
| TClass of tname_t * tname_t list * b_attributes_t  (* C++ name spaces, not in cil *)
| TBuiltin_va_list of b_attributes_t
| TVarArg of b_attributes_t
| TUnknown of b_attributes_t

and tname_t =
| SimpleName of string
| TemplatedName of tname_t * btype_t list

and bfunarg_t = string * btype_t * b_attributes_t

and b_attribute_t = Attr of string * b_attrparam_t list

and b_attributes_t = b_attribute_t list

and b_attrparam_t =
| AInt of int
| AStr of string
| ACons of string * b_attrparam_t list
| ASizeOf of btype_t
| ASizeOfE of b_attrparam_t
| ASizeOfS of btypsig_t
| AAlignOf of btype_t
| AAlignOfE of b_attrparam_t
| AAlignOfS of btypsig_t
| AUnOp of unop_t * b_attrparam_t
| ABinOp of binop_t * b_attrparam_t * b_attrparam_t
| ADot of b_attrparam_t * string
| AStar of b_attrparam_t
| AAddrOf of b_attrparam_t
| AAssign of b_attrparam_t * b_attrparam_t
| AIndex of b_attrparam_t * b_attrparam_t
| AQuestion of b_attrparam_t * b_attrparam_t * b_attrparam_t

and bcompinfo_t = {
  bcstruct: bool;
  bcname: string;
  bckey: int;
  bcfields: bfieldinfo_t list;
  bcattr: b_attributes_t;
}

and bfieldinfo_t = {
  bfckey: int;   (* key of the containing compinfo *)
  bfname: string;
  bftype: btype_t;
  bfbitfield: int option;
  bfattr: b_attributes_t;
  bfloc: b_location_t;
  bfieldlayout: fieldlayout_t option
}

and beitem_t = string * bexp_t * b_location_t

and benuminfo_t = {
  bename: string;
  beitems: beitem_t list;
  beattr: b_attributes_t;
  bekind: ikind_t;
}

and btypeinfo_t = {
  btname: string;
  bttype: btype_t;
}

and bvarinfo_t = {
  bvname: string;
  bvtype: btype_t;
  bvstorage: bstorage_t;
  bvglob: bool;
  bvinline: bool;
  bvdecl: b_location_t;
  bvinit: binitinfo_t;
  bvid: int;
  bvattr: b_attributes_t;
  bvaddrof: bool;
  bvparam: int    (* 0 for local/global variables, seqnr for parameters *)
}

and bexp_t =
| Const of bconstant_t
| Lval of blval_t
| SizeOf of btype_t
| Real of bexp_t
| Imag of bexp_t
| SizeOfE of bexp_t
| SizeOfStr of string
| AlignOf of btype_t
| AlignOfE of bexp_t
| UnOp of unop_t * bexp_t * btype_t
| BinOp of binop_t * bexp_t * bexp_t * btype_t
| Question of bexp_t * bexp_t * bexp_t * btype_t
| CastE of btype_t * bexp_t
| AddrOf of blval_t
| AddrOfLabel of int
| StartOf of blval_t
| FnApp of
    b_location_t * bexp_t * (bexp_t option) list (* program function application *)
| CnApp of
    string
    * bexp_t option list
    * btype_t  (* constant, predefined function application *)

and bconstant_t =
| CInt of int64 * ikind_t * string option
| CStr of string
| CWStr of int64 list
| CChr of char
| CReal of float * fkind_t * string option
| CEnum of bexp_t * string * string

and blval_t = blhost_t * boffset_t

and blhost_t =
| Var of varuse_t
| Mem of bexp_t

and boffset_t =
| NoOffset
| Field of fielduse_t * boffset_t
| Index of bexp_t * boffset_t

and binit_t =
| SingleInit of bexp_t
| CompoundInit of btype_t * (boffset_t * binit_t) list

and binitinfo_t = binit_t option

and bblock_t = {
  battrs: b_attributes_t;
  bstmts: bstmt_t list
}

and bstmt_t = {
  labels: blabel_t list;
  skind: bstmtkind_t;
  sid: int;
  succs: int list;
  preds: int list
}

and blabel_t =
| Label of string * b_location_t * bool
| Case of bexp_t * b_location_t
| CaseRange of bexp_t * bexp_t * b_location_t
| Default of b_location_t

and bstmtkind_t =
| Instr of binstr_t list
| Return of bexp_t option * b_location_t
| Goto of int * b_location_t
| ComputedGoto of bexp_t * b_location_t
| Break of b_location_t
| Continue of b_location_t
| If of bexp_t * bblock_t * bblock_t * b_location_t
| Switch of bexp_t * bblock_t * (int list) * b_location_t
| Loop of
    bblock_t
    * b_location_t
    * (int option)
    * (int option) (* continue stmt, break stmt *)
| Block of bblock_t
| TryFinally of bblock_t * bblock_t * b_location_t
| TryExcept of bblock_t * (binstr_t list * bexp_t) * bblock_t * b_location_t

and b_asm_output_t = string option * string * blval_t (* name, constraint, lval *)

and b_asm_input_t = string option * string * bexp_t (* name, constraint, bexp_t *)

and binstr_t =
| Set of blval_t * bexp_t * b_location_t
| Call of blval_t option * bexp_t * bexp_t list * b_location_t
| VarDecl of varuse_t * b_location_t  (* added by goblint-cil *)
| Asm of
    b_attributes_t
    * string list
    * b_asm_output_t list
    * b_asm_input_t list
    * string list
    * b_location_t

and b_location_t = {
  line: int ;
  file: string ;
  byte: int
}

and btypsig_t =
| TSArray of btypsig_t * int64 option * b_attribute_t list
| TSPtr of btypsig_t * b_attribute_t list
| TSComp of bool * string * b_attribute_t list
| TSFun of btypsig_t * btypsig_t list option * bool * b_attribute_t list
| TSEnum of string * b_attribute_t list
| TSBase of btype_t


type bcfundec_t = {
    bsvar: bvarinfo_t;
    bsformals: bvarinfo_t list;
    bslocals: bvarinfo_t list;
    bsbody: bblock_t
  }


type bglobal_t =
| GType of btypeinfo_t * b_location_t
| GCompTag of bcompinfo_t * b_location_t
| GCompTagDecl of bcompinfo_t * b_location_t
| GEnumTag of benuminfo_t * b_location_t
| GEnumTagDecl of benuminfo_t * b_location_t
| GVarDecl of bvarinfo_t * b_location_t
| GVar of bvarinfo_t * binitinfo_t * b_location_t
| GFun of bcfundec_t * b_location_t
| GAsm of string * b_location_t
| GPragma of b_attribute_t * b_location_t
| GText of string


type bcfile_t = {
    bfilename: string;
    bglobals: bglobal_t list
  }


class type bcdictionary_int =
  object

    method index_attrparam: b_attrparam_t -> int
    method index_attribute: b_attribute_t -> int
    method index_attributes: b_attributes_t -> int
    method index_constant: bconstant_t -> int
    method index_exp: bexp_t -> int
    method index_funarg: bfunarg_t -> int
    method index_funargs: bfunarg_t list -> int
    method index_lhost: blhost_t -> int
    method index_lval: blval_t -> int
    method index_opt_lval: blval_t option -> int
    method index_offset: boffset_t -> int
    method index_typ: btype_t -> int
    method index_typsig: btypsig_t -> int
    method index_string: string -> int
    method index_location: b_location_t -> int
    method index_tname: tname_t -> int

    method index_typeinfo: btypeinfo_t -> int
    method index_varinfo: bvarinfo_t -> int
    method index_init_opt: binit_t option -> int
    method index_init: binit_t -> int
    method index_offset_init: (boffset_t * binit_t) -> int
    method index_fieldinfo: bfieldinfo_t -> int
    method index_compinfo: bcompinfo_t -> int
    method index_enumitem: beitem_t -> int
    method index_enuminfo: benuminfo_t -> int

    method get_attrparam: int -> b_attrparam_t
    method get_attribute: int -> b_attribute_t
    method get_attributes: int -> b_attributes_t
    method get_attrparam: int -> b_attrparam_t
    method get_constant: int -> bconstant_t
    method get_exp: int -> bexp_t
    method get_funarg: int -> bfunarg_t
    method get_funargs: int -> bfunarg_t list
    method get_lhost: int -> blhost_t
    method get_lval: int -> blval_t
    method get_opt_lval: int -> blval_t option
    method get_offset: int -> boffset_t
    method get_typ: int -> btype_t
    method get_typsig: int -> btypsig_t
    method get_string: int -> string
    method get_location: int -> b_location_t

    method get_varinfo: int -> bvarinfo_t
    method get_init: int -> binit_t
    method get_offset_init: int -> (boffset_t * binit_t)
    method get_enuminfo: int -> benuminfo_t
    method get_enumitem: int -> beitem_t
    method get_compinfo: int -> bcompinfo_t
    method get_fieldinfo: int -> bfieldinfo_t
    method get_typeinfo: int -> btypeinfo_t

    method write_xml_attributes:
             ?tag:string -> xml_element_int -> b_attributes_t -> unit
    method read_xml_attributes:
             ?tag:string -> xml_element_int -> b_attributes_t
    method write_xml_exp:
             ?tag:string -> xml_element_int -> bexp_t -> unit
    method read_xml_exp:
             ?tag:string -> xml_element_int -> bexp_t
    method write_xml_funarg_list:
             ?tag:string -> xml_element_int -> bfunarg_t list -> unit
    method read_xml_funarg_list:
             ?tag:string -> xml_element_int -> bfunarg_t list
    method write_xml_lval:
             ?tag:string -> xml_element_int -> blval_t -> unit
    method read_xml_lval:
             ?tag:string -> xml_element_int -> blval_t
    method write_xml_offset:
             ?tag:string -> xml_element_int -> boffset_t -> unit
    method read_xml_offset:
             ?tag:string -> xml_element_int -> boffset_t
    method write_xml_typ:
             ?tag:string -> xml_element_int -> btype_t -> unit
    method read_xml_typ:
             ?tag:string -> xml_element_int -> btype_t
    method write_xml_string:
             ?tag:string -> xml_element_int -> string -> unit

    method write_xml_typeinfo:
             ?tag:string -> xml_element_int -> btypeinfo_t -> unit
    method read_xml_typeinfo:
             ?tag:string -> xml_element_int -> btypeinfo_t
    method write_xml_varinfo:
             ?tag:string -> xml_element_int -> bvarinfo_t -> unit
    method read_xml_varinfo:
             ?tag:string -> xml_element_int -> bvarinfo_t
    method write_xml_init:
             ?tag:string -> xml_element_int -> binit_t -> unit
    method read_xml_init:
             ?tag:string -> xml_element_int -> binit_t
    method write_xml_fieldinfo:
             ?tag:string -> xml_element_int -> bfieldinfo_t -> unit
    method read_xml_fieldinfo:
             ?tag:string -> xml_element_int -> bfieldinfo_t
    method write_xml_compinfo:
             ?tag:string -> xml_element_int -> bcompinfo_t -> unit
    method read_xml_compinfo:
             ?tag:string -> xml_element_int -> bcompinfo_t
    method write_xml_enumitem:
             ?tag:string -> xml_element_int -> beitem_t -> unit
    method write_xml_enuminfo:
             ?tag:string -> xml_element_int -> benuminfo_t -> unit
    method read_xml_enuminfo:
             ?tag:string -> xml_element_int -> benuminfo_t
    method write_xml_location:
             ?tag:string -> xml_element_int -> b_location_t -> unit
    method read_xml_location:
             ?tag:string -> xml_element_int -> b_location_t

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type bcfundeclarations_int =
  object

    method index_formal: bvarinfo_t -> int -> int
    method index_local: bvarinfo_t -> int

    method write_xml_formal:
             ?tag:string -> xml_element_int -> bvarinfo_t -> int -> unit
    method write_xml_local:
             ?tag:string -> xml_element_int -> bvarinfo_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


(** Principal access structure for CIL-parsed c files.*)
class type bcfiles_int =
  object

    (** {1 Initialization}*)

    (** [add_bcfile f] adds a parsed file [f] to the storage.*)
    method add_bcfile: bcfile_t -> unit

    (** [add_fundef name type] adds an otherwise constructed function
        definition to the storage (i.e., not parsed).*)
    method add_fundef: string -> btype_t -> unit

    (** [update_global c] allows for updates in global entries after
        initial parsing. Currently this is used only to update compinfo
        definitions and declarations with field layouts.*)
    method update_global: bglobal_t -> unit

    (** {1 Services}*)

    (** Resolves a btype to its basic form, i.e., it expands all typedefs.*)
    method resolve_type: btype_t -> btype_t traceresult

    (** {1 Access}*)

    (** {2 Functions}*)

    method get_gfun_names: string list
    method get_gfun: string -> bcfundec_t
    method has_gfun: string -> bool

    (** {2 Variables}*)

    (** [get_varinfo name] returns the varinfo with name [name].

        @raise BCH_failure if no varinfo exists with name [name].*)
    method get_varinfo: ?prefix:bool -> string -> bvarinfo_t

    (** [has_varinfo name] returns true if there exists either a defined or
        declared variable with name [name]. Note that this includes function
        names.*)
    method has_varinfo: ?prefix:bool -> string -> bool

    method list_varinfos: string list

    (** {2 Type definitions}*)

    (** [get_typedef name] returns the (not necessarily fully expanded) type
        definition associated with [name].

        @raise BCH_failure if no typedef exists with name [name].
     *)
    method get_typedef: string -> btype_t

    (** [has_typedef name] returns true if there exists a typedef with name
        [name].*)
    method has_typedef: string -> bool

    (** Returns a list of (name, type) pairs of all stored typedefs. Note that
        the types are not fully expanded.*)
    method typedefs: (string * btype_t) list


    (** {2 Compinfo's en enuminfo's}*)

    (** [get_compinfo key] returns the compinfo structure associated with
        (CIL-assigned) key [key].

        @raise BCH_failure if no compinfo definition or declaration exists
        with key [key].
     *)
    method get_compinfo: int -> bcompinfo_t

    method get_compinfo_by_name: string -> bcompinfo_t

    (** [has_compinfo key] returns true if a compinfo definition or declaration
        exists with (CIL-assigned) key [key].*)
    method has_compinfo: int -> bool

    method has_compinfo_by_name: string -> bool

    (** [get_enuminfo name] returns the enuminfo structure with name [name].

        @raise BCH_failure if no enuminfo definition or declaration exists with
        name [name]
     *)
    method get_enuminfo: string -> benuminfo_t

    (** [has_enuminfo name] returns true if an enuminfo definition or declaration
        exists with name [name].*)
    method has_enuminfo: string -> bool

    (** {1 Save and restore}*)

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end
