(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024-2026 Aarno Labs LLC

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

(* ============================================================================== *
 * The data types used here are very close to the CIL data types. Some fields or  *
 * selectors that seem to be primarily used for transformation have been removed. *
 * ============================================================================== *)

(* chutil *)
open CHTraceResult
open CHXmlDocument

(** Data types mirroring CIL data types *)

(** {1 CIL Types}

    The data types listed in these file are derived from the CIL data types.
    Some fields or selectors that seem to be be primarily used for transformation
    in CIL have been removed.

    C Programs are parsed by CIL, which is included as a library in the wrapper
    code contained in the CHC/cchcil directory. The code CHC/cchcil serializes
    the CIL data structures into xml, which is then saved per file (for file-level
    declarations) and per function (for function AST and local declarations).

    The code in this directory is a consumer of that data; it does not change
    any of the data produced by CIL.
 *)


(** {2 Basic types} *)

(** Integer kinds *)
type ikind =
| IChar       (** [char] *)
| ISChar      (** [signed char] *)
| IUChar      (** [unsigned char] *)
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
| IInt128     (** added by Goblint-Cil *)
| IUInt128    (** added by Goblint-Cil *)


(** Various kinds of floating-point numbers *)
type fkind =
| FFloat      (** [float] *)
| FDouble     (** [double] *)
| FLongDouble (** [long double] *)
| FComplexFloat
| FComplexDouble
| FComplexLongDouble


(** Storage of variables *)
type storage =
| NoStorage
| Static
| Register
| Extern
| Opaque of int


(** Unary operators *)
type unop =
| Neg
| BNot
| LNot


(** Binary operators *)
type binop =
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


(** Name and vid of CIL variables (varinfo's): a unique and more concise
    representation of variables.*)
type varuse = string * int      (* vname, vid *)


(** Name and compinfo key of CIL struct fields: a unique and more concise
    representation of struct fields.*)
type fielduse = string * int    (* fname, fckey *)


(** CIL type.*)
type typ =
| TVoid of attributes
| TInt of ikind * attributes
| TFloat of fkind * attributes
| TPtr of typ * attributes
| TArray of typ * exp option * attributes
| TFun of typ * funarg list option * bool * attributes
| TNamed of string * attributes
| TComp of int * attributes
| TEnum of string * attributes
| TBuiltin_va_list of attributes

(** Function argument: name, type, and attributes.*)
and funarg = string * typ * attributes

and attribute = Attr of string  * attrparam list

and attributes = attribute list

and attrparam =
| AInt of int
| AStr of string
| ACons of string * attrparam list
| ASizeOf of typ
| ASizeOfE of attrparam
| ASizeOfS of typsig
| AAlignOf of typ
| AAlignOfE of attrparam
| AAlignOfS of typsig
| AUnOp of unop * attrparam
| ABinOp of binop * attrparam * attrparam
| ADot of attrparam * string
| AStar of attrparam
| AAddrOf of attrparam
| AIndex of attrparam * attrparam
| AQuestion of attrparam * attrparam * attrparam
| AAssign of attrparam * attrparam


(** CIL data structure for a struct definition.*)
and compinfo = {
    cstruct: bool;  (** struct: true, union: false *)
    cname: string;  (** name of the struct *)
    ckey: int;  (** unique identification of the struct *)
    cfields: fieldinfo list;  (** fields of the struct, in order *)
    cattr: attributes; (** Gcc attributes associated with the struct definition *)
}


(** CIL data structure for a struct/union field.*)
and fieldinfo = {
  fckey: int;   (** key of the containing compinfo *)
  fname: string;  (** name of the field *)
  ftype: typ;  (** type of the field *)
  fbitfield: int option;
  fattr: attributes; (** Gcc attributes asssociated with the field definition *)
  floc: location  (** location in the file where this field is defined *)
}


(** CIL data structure for an enum item:
    - name of the item
    - Gcc attributes associated with the item definition
    - expression denoting the (integer) value of the enum item
    - location in the file where the enum item is defined
 *)
and eitem = string * attributes * exp * location


(** CIL data structure for an enum definition.*)
and enuminfo = {
    ename: string ;  (** name of the enum type *)
    eitems: eitem list;  (** list of the enum items defined as part of the enum *)
    eattr: attributes;  (** Gcc attributes associated with the enum definition *)
    ekind: ikind;  (** integer kind of the enum items *)
}


(** CIL data structure for a typedef *)
and typeinfo = {
    tname: string;  (** name given to the type *)
    ttype: typ;  (** type denoted by the typedef *)
}


(** CIL data structure for a local or global variable (including function
    parameters).*)
and varinfo = {
    vname: string;  (** variable name *)
    vtype: typ;  (** variable type *)
    vstorage: storage;  (** type of variable storage *)
    vglob: bool;  (** true if variable is global or static *)
    vinline: bool;
    vdecl: location;  (** location in the file where the variable is defined *)
    vinit: initinfo;  (** variable initializer *)
    vid: int;  (** unique identifier of the variable *)
    vattr: attributes;  (** Gcc attributes associated with the variable definition *)
    vaddrof: bool;  (**  true if address is taken of this variable *)
    vparam: int  (** 0 for local/global variables, seqnr for parameters *)
}


(** Program expression *)
and exp =
| Const of constant
| Lval of lval
| SizeOf of typ
| SizeOfE of exp
| SizeOfStr of string
| AlignOf of typ
| AlignOfE of exp
| UnOp of unop * exp * typ
| BinOp of binop * exp * exp * typ
| Question of exp * exp * exp * typ
| CastE of typ * exp
| AddrOf of lval
| AddrOfLabel of int
| StartOf of lval  (** Used for arrays, to align with AddrOf for pointers *)
| FnApp of location * exp * (exp option) list
(** program function application, not part of CIL *)

| CnApp of string * exp option list * typ
(** constant, predefined function application, not part of CIL *)


and constant =
| CInt of int64 * ikind * string option
| CStr of string
| CWStr of int64 list
| CChr of char
| CReal of float * fkind * string option
| CEnum of exp * string * string


(** Left-hand-side value: a combination of a variable or dereference and an offset *)
and lval = lhost * offset


(** Base location of a left-hand-side value: variable or dereference *)
and lhost =
| Var of varuse
| Mem of exp


(** Offset from a base location *)
and offset =
| NoOffset
| Field of fielduse * offset
| Index of exp * offset


(** Variable initializer *)
and init =
| SingleInit of exp
| CompoundInit of typ * (offset * init) list


and initinfo = init option


(** {2 Program AST constructs} *)


(** Basic block *)
and block = {
    battrs: attributes;  (** Gcc attributes associated with the block definition *)
    bstmts: stmt list  (** Statements contained in the block *)
}

(** Program statement *)
and stmt = {
    labels: label list; (** labels associated with the statement *)
    skind: stmtkind;  (** statement details *)
    sid: int;  (** statement id: unique identifier of the statement *)
    succs: int list; (** stmt id's of the successors of this statement *)
    preds: int list  (** stmt id's of the predecessors of this statement *)
}


(** Statement label *)
and label =
  | Label of string * location * bool
  (** name of the label, the location in the file, indicator whether the label
      appears in the program or was introduced by CIL *)

  | Case of exp * location  (** case statement label *)
  | CaseRange of exp * exp * location  (** case statement range of cases *)
  | Default of location  (** case statement default case *)


(** Statement details *)
and stmtkind =
| Instr of instr list
| Return of exp option * location
| Goto of int * location
| ComputedGoto of exp * location
| Break of location
| Continue of location
| If of exp * block * block * location
| Switch of exp * block * (int list) * location
| Loop of block * location * (int option) * (int option)
(* a while (1) statement with the enclosing block denoting the body of the
   loop. The first optional stmt id points at the stmt containing the continue
   label of the loop; the second optional stmt id points at the stmt containing
   the break label of the loop. *)

| Block of block
| TryFinally of block * block * location
| TryExcept of block * (instr list * exp) * block * location


and asm_output_t = string option * string * lval (** name, constraint, lval *)


and asm_input_t = string option * string * exp (** name, constraint, exp *)


and instr =
| Set of lval * exp * location
| Call of lval option * exp * exp list * location
| VarDecl of varinfo * location
| Asm of
    attributes
    * int list
    * asm_output_t list
    * asm_input_t list
    * int list
    * location

(** {2 Location} *)
and location = {
  line : int ;
  file : string ;
  byte : int
  }


(** {2 Type signatures} *)

and typsig =
| TSArray of typsig * int64 option * attribute list
| TSPtr of typsig * attribute list
| TSComp of bool * string * attribute list
| TSFun of typsig * typsig list option * bool * attribute list
| TSEnum of string * attribute list
| TSBase of typ


(** {2 Global declarations} *)

type global =
| GType of typeinfo * location
| GCompTag of compinfo * location
| GCompTagDecl of compinfo * location
| GEnumTag of enuminfo * location
| GEnumTagDecl of enuminfo * location
| GVarDecl of varinfo *location
| GVar of varinfo * initinfo * location
| GFun of varinfo * location
| GAsm of string * location
| GPragma of attribute * location
| GText of string


(** {2 Function declarations} *)

(** The function declaration object provides access to the local variable
    declarations of a function, including its formal parameters. Variables
    can be retrieved both by vid (varinfo identification, unique in a file),
    by name (varinfo vname, unique in a function, not necessarily in a file),
    and by index (index of a varinfo in the, file-based, cdictionary).
*)
class type cfundeclarations_int =
  object

    (** returns the name of the function *)
    method functionname: string

    (** [get_formal n] returns the nth formal parameter of the function
        (starting from 1)

        @raise CCHFailure if no such parameter exists
     *)
    method get_formal: int -> varinfo

    (** returns a list of all formal parameters of the function (not necessarily
        in order) *)
    method get_formals: varinfo list

    (** returns a list of all local variables of the function *)
    method get_locals: varinfo list

    (** [get_varinfo_by_name name] returns the local variable or formal parameter
        with name [name]. If no variable with [name] is found it attempts to
        find a variable with that name in the cdeclarations (file-level
        declarations).

        returns [Error] if the name cannot be found in either the function's or the
        file's declarations
     *)
    method get_varinfo_by_name: string -> varinfo traceresult

    (** [get_varinfo index] returns the variable that is indexed with [index] in
        the function declarations variable table. Note that this index is different
        from the [vid].
     *)
    method get_varinfo: int -> varinfo       (* index *)

    (** [get_varinfo_by_vid vid] returns the variable with id [vid]. If such a
        variable cannot be found in the function variable table, an attempt is
        made to retrieve it from the file environment.
     *)
    method get_varinfo_by_vid: int -> varinfo traceresult (* vid *)

    (** [is_formal vid] returns true if the variable with vid [vid] is a formal
        parameter of the function. It returns false if the variable is a local
        variable or if it cannot be found. *)
    method is_formal: int -> bool

    (** [is_local vid] returns true if the variable with vid [vid] is a local
        variable (not a parameter) of the function. It returns false if the variable
        is a parameter or if it cannot be found *)
    method is_local: int -> bool

    (** [has_varinfo vid] returns true if the function declarations have a variable
        with vid [vid] *)
    method has_varinfo: int -> bool

    (** reads in the indexed variable table from the xml representation embedded
        in the _cfun.xml file. From this variable table it creates a vid table.*)
    method read_xml: xml_element_int -> unit

  end


(** Function declaration *)
type fundec = {
    svar: varinfo;  (** varinfo for the signature of the function *)
    sdecls: cfundeclarations_int;  (** declarations of local variables *)
    sbody: block   (** function body *)
}


(** {2 File declarations} *)

(** Aggregate of all global definitions and declarations in a compilation unit *)
type file = {
  fileName: string ;
  globals: global list
}
