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

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeTransformer
open BCHBCTypeUtil
open BCHLibTypes


module H = Hashtbl

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

let templated_btype_to_name (ty: btype_t) (index: int) =
  let rec tn_string tn =
    match tn with
    | SimpleName name -> name
    | TemplatedName (base,_) -> "t" ^ (tn_string base) in
  let rec aux t =
    match t with
    | TVoid _ -> "void"
    | TInt _ -> "i"
    | TFloat _ -> "f"
    | TPtr (t,_) -> "p" ^ (aux t)
    | TRef (t,_) -> "r" ^ (aux t)
    | THandle (s,_) -> "h" ^ s
    | TArray (t,_,_) -> "a" ^ (aux t)
    | TFun _ -> "fp"
    | TNamed (s,_) -> s
    | TComp (ckey, _) -> "struct" ^ (string_of_int ckey)
    | TCppComp (tn, _, _) -> "cpp-struct" ^ (tn_string tn)
    | TEnum (ename, _) -> "enum" ^ ename
    | TCppEnum (tn, _, _) -> "cpp-enum" ^ (tn_string tn)
    | TVarArg _ -> "vararg"
    | TBuiltin_va_list _ -> "builtin-va-list"
    | TClass (tn, _, _) -> "class" ^ (tn_string tn)
    | TUnknown _ -> "arg" in
  (aux ty) ^ "_" ^ (string_of_int index)


let _demangled_name_to_pretty dm =
  if dm.dm_vftable then STR "vftable"
  else if dm.dm_vbtable then STR "vbtable"
  else
  LBLOCK [ 
    (if dm.dm_accessibility = "" then 
	STR "" 
     else 
	LBLOCK [ STR dm.dm_accessibility ; STR ": " ]) ;
    (if dm.dm_virtual then STR "virtual " else STR "") ;
    (if dm.dm_static then STR "static " else STR "") ;
    (match dm.dm_returntype with 
      Some t -> LBLOCK [ STR (btype_to_string t) ; STR " " ] | _ -> STR "") ;
    STR dm.dm_calling_convention ; STR " " ;
    pretty_print_list dm.dm_name_space (fun s -> STR (tname_to_string s)) "" "::" "" ;
    (match dm.dm_name_space with [] -> STR "" | _ -> STR "::") ; 
    STR (tname_to_string dm.dm_name) ; 
    pretty_print_list dm.dm_parameter_types
      (fun t -> STR (btype_to_string t)) "(" "," ")" ;
    (if dm.dm_const then STR "const" else STR "") ]

let demangled_name_to_string dm =
  if dm.dm_vftable then "vftable"
  else if dm.dm_vbtable then "vbtable"
  else
    let s_acc =
      if dm.dm_accessibility = "" then "" else (dm.dm_accessibility ^ ": ") in
  let s_virtual = if dm.dm_virtual then "virtual " else "" in
  let s_static = if dm.dm_static then "static " else "" in
  let s_returntype = match dm.dm_returntype with
      Some t -> (btype_to_string t) ^ " " | _ -> "" in
  let s_calling_convention = dm.dm_calling_convention ^ " " in
  let s_namespace = 
    String.concat
      "" (List.map (fun s -> (tname_to_string s) ^ "::") dm.dm_name_space) in
  let s_name = tname_to_string dm.dm_name in
  let s_parameters =
    String.concat "," (List.map btype_to_string dm.dm_parameter_types) in
  let s_const = if dm.dm_const then "const" else "" in
  s_acc
  ^ s_virtual
  ^ s_static
  ^ s_returntype
  ^ s_calling_convention
  ^ s_namespace
  ^ s_name
  ^ "("
  ^ s_parameters
  ^ ")"
  ^ s_const
    

class cppname_t = 
object (self)
  val mutable name_space = []
  val mutable method_name = SimpleName ""
  val mutable calling_convention = ""
  val mutable accessibility = ""
  val mutable par_types = []
  val mutable is_constructor = false
  val mutable is_destructor = false
  val mutable is_operator = false
  val mutable is_virtual = false
  val mutable returntype = None
  val mutable is_const = false
  val mutable is_static = false
  val mutable storage_class = "executable" 
  val mutable is_vftable = false
  val mutable is_vbtable = false

  method to_demangled_name = {
    dm_name = method_name  ;
    dm_name_space = name_space ;
    dm_parameter_types = List.rev par_types ;
    dm_returntype = returntype ;
    dm_calling_convention = calling_convention ;
    dm_accessibility = accessibility ;
    dm_storage_class = storage_class ;
    dm_constructor = is_constructor ;
    dm_destructor = is_destructor ;
    dm_static     = is_static ;
    dm_virtual    = is_virtual ;
    dm_operator   = is_operator ;
    dm_const      = is_const ;
    dm_vbtable    = is_vbtable ;
    dm_vftable    = is_vftable
  }

  method add_name_space s = name_space <- s :: name_space

  method set_method_name s = method_name <- s

  method set_calling_convention s = calling_convention <- s

  method add_par_type t = par_types <- t :: par_types

  method set_constructor = is_constructor <- true

  method set_destructor = is_destructor <- true

  method set_vbtable = is_vbtable <- true

  method is_vbtable = is_vbtable

  method set_vftable = is_vftable <- true

  method is_vftable = is_vftable

  method set_operator name = 
    begin self#set_method_name (SimpleName name) ; is_operator <- true end

  method set_virtual = is_virtual <- true

  method set_accessibility s = accessibility <- s

  method set_returntype t = returntype <- Some t

  method set_const = is_const <- true

  method set_static = is_static <- true

  method set_storage_class s = storage_class <- s

  method get_parameter_type (index:int) =
    let len = List.length par_types in
    if index < len then
      List.nth (List.rev par_types) index
    else
      raise (BCH_failure
	       (LBLOCK [ STR "get_parameter_type: Index out of bounds: " ; INT index ;
			 STR " (number of types: " ; INT len ; STR ")" ]))
	      
	      
  method is_constructor = is_constructor 

  method is_destructor = is_destructor

  method is_operator = is_operator

  method toPretty =
    if self#is_vftable then STR "vftable" 
    else if self#is_vbtable then STR "vbtable"
    else
    LBLOCK [ 
      (if accessibility = "" then STR "" else LBLOCK [ STR accessibility ; STR ": " ]) ;
      (if is_virtual then STR "virtual " else STR "") ;
      (if is_static then STR "static " else STR "") ;
      (match returntype with 
	Some t -> LBLOCK [ STR (btype_to_string t) ; STR " " ] | _ -> STR "") ;
      STR calling_convention ; STR " " ;
      pretty_print_list name_space (fun s -> STR (tname_to_string s)) "" "::" "" ;
      (match name_space with [] -> STR "" | _ -> STR "::") ; 
      STR (tname_to_string method_name) ; 
      pretty_print_list (List.rev par_types )
	       (fun t -> STR (btype_to_string t)) "(" "," ")" ;
      (if is_const then STR "const" else STR "") ]

end

let t_bool = t_named "BOOL"
let t_char = t_named "char"
let t_double = t_named "double"
let t_ellipsis = t_named "..."
let t_float = t_named "float"
let t_int  = t_named "int"
let t_int64 = t_named "__int64"
let t_uint64 = t_named "unsigned __int64"
let t_long = t_named "long"
let t_schar = t_named "signed char"
let t_short = t_named "short"
let t_uchar = t_named "unsigned char"
let t_uint = t_named "unsigned int"
let t_ulong = t_named "unsigned long"
let t_ushort = t_named "unsigned short"
let t_wchar_t = t_named "wchar_t"

let t_pconstchar = t_ptrto (TInt (IChar, [Attr ("const", [])]))

let c_atsign       = 0x0040   (* @ *)
let c_dollarsign   = 0x0024   (* $ *)
let c_questionmark = 0x003F   (* ? *)
let c_underscore   = 0x005F   (* _ *)

let c_A            = 0x0041   (* A *)
let c_B            = 0x0042   (* B *)
let c_C            = 0x0043   (* C *)
let c_D            = 0x0044   (* D *)
let c_E            = 0x0045   (* E *)
let c_F            = 0x0046   (* F *)
let c_G            = 0x0047   (* G *)
let c_H            = 0x0048   (* H *)
let c_I            = 0x0049   (* I *)
let c_J            = 0x004A   (* J *)
let c_K            = 0x004B   (* K *)
let c_M            = 0x004D   (* M *)
let c_N            = 0x004E   (* N *)
let c_O            = 0x004F   (* O *)
let c_P            = 0x0050   (* P *)
let c_Q            = 0x0051   (* Q *)
let c_R            = 0x0052   (* R *)
let c_S            = 0x0053   (* S *)
let c_U            = 0x0055   (* U *)
let c_V            = 0x0056   (* V *)
let c_W            = 0x0057   (* W *)
let c_X            = 0x0058   (* X *)
let c_Y            = 0x0059   (* Y *)
let c_Z            = 0x005A   (* Z *)

let c_zero         = 0x0030   (* 0 *)
let c_one          = 0x0031   (* 1 *)
let c_two          = 0x0032   (* 2 *)
let c_three        = 0x0033   (* 3 *)
let c_four         = 0x0034   (* 4 *)
let c_five         = 0x0035   (* 5 *)
let c_six          = 0x0036   (* 6 *)
let c_seven        = 0x0037   (* 7 *)
let c_eight        = 0x0038   (* 8 *)
let c_nine         = 0x0039   (* 9 *)

let in_range c lower_bound upper_bound = c >= lower_bound && c <= upper_bound

let is_name_start_char c =
  (in_range c 0x0061 0x007A) ||    (* a-z *) 
  (in_range c 0x0041 0x005A) ||    (* A-Z *)
  (c = 0x005F)                     (*  _  *)


let is_name_char c =
  (is_name_start_char c)     ||    
  (c = 0x002D)               ||     (*  -  *)
  (c = 0x002E)               ||     (*  .  *)
  (c = 0x00B7)               ||
  (in_range c 0x0030 0x0039) ||     (* 0-9 *)
  (in_range c 0x0300 0x036F) ||
  (in_range c 0x203F 0x2040)

let basic_type_chars         = 
  [ c_underscore ; c_C ; c_D ; c_E ; c_F ; c_G ; c_H ; c_I ; c_J ; c_K ;
    c_M ; c_N ; c_X ]
let complex_type_chars = [ c_A ; c_P ; c_Q ; c_U ; c_V ; c_W ]

let x_access_qualifier_chars = [ c_A ; c_E ; c_I ; c_M ; c_Q ; c_U ]
let s_access_qualifier_chars = [ c_C ; c_K ; c_S ; c_Y ]
let const_qualifier_chars    = [ c_A ; c_B ]

let is_type_start_char c = 
  List.mem c (c_zero::c_one::c_two::(basic_type_chars @ complex_type_chars))
let is_basic_type_char c = List.mem c basic_type_chars
let is_complex_type_char c = List.mem c complex_type_chars

let is_x_access_qualifier_char c = List.mem c x_access_qualifier_chars
let is_s_access_qualifier_char c = List.mem c s_access_qualifier_chars
let is_const_qualifier_char c = List.mem c const_qualifier_chars

class demangler_t (s:string) =
object (self)

  val len = String.length s
  val mutable ch = IO.input_string s
  val mutable pos = 0
  val mutable char_la = 0
  val name_buffer = Buffer.create 17
  val cppname = new cppname_t
  val mutable names:tname_t list = []

  method get_cppname = cppname

  method get_name (index:int) = 
    try
      List.nth (List.rev names) index
    with
      Failure _ ->
	raise (BCH_failure 
		 (LBLOCK [ STR "get_name " ; INT index ; STR " on " ;
			   pretty_print_list (List.rev names) 
			     (fun s -> STR (tname_to_string s)) "[" ", " "]" ]))

  method private stop msg =
    let unparsed = String.sub s (pos-1) (((String.length s) - pos) + 1) in
    raise (BCH_failure (LBLOCK [
      STR "Current name: " ; cppname#toPretty ; NL ;
      STR "Stop at position " ; INT pos ; STR " while reading " ; STR msg ; NL ;
      STR "Unprocessed: " ; STR unparsed ]))

  method private read = begin pos <- pos + 1 ; Char.code (IO.read ch) end

  method private next_char = 
    if pos = len then 
      raise (BCH_failure (LBLOCK [ STR "End of string encountered. Current name: " ; 
				   cppname#toPretty ] ))
    else
      char_la <- self#read

  method private read_char expected_char =
    if char_la = expected_char then
      self#next_char
    else
      raise (BCH_failure (LBLOCK [ STR "Expected to see " ; INT expected_char ;
				   STR ", but found " ; INT char_la ]))

  method private check_char_la predicate msg =
    if predicate char_la then () else raise (BCH_failure msg)

  method private fill_name_buffer c = Buffer.add_char name_buffer (Char.chr c)

  method private check_end_of_string =
     if pos = len then () else 
       let unparsed = String.sub s pos ((String.length s) - pos) in
       self#stop ("leaving \"" ^ unparsed ^ "\" unparsed")

  method private read_name =
    begin
      Buffer.clear name_buffer ;
      self#check_char_la is_name_start_char
	(LBLOCK [ INT char_la ; STR " is not a valid starting character of a name "]) ;
      self#fill_name_buffer char_la ;
      self#next_char ;
      while is_name_char char_la do
	begin
	  self#fill_name_buffer char_la ;
	  self#next_char
	end
      done;
      Buffer.contents name_buffer
    end

  method private read_template_argument_list =
    let l = ref [] in
    begin
      while is_type_start_char char_la do
	l := self#read_type_code :: !l
      done ;
      List.rev !l
    end

  method private read_templated_name:tname_t =
    let tname =
      if is_name_start_char char_la then
	SimpleName self#read_name
      else if char_la = c_questionmark then
	begin
	  self#read_char c_questionmark ;
	  if char_la = c_dollarsign then
	    let _ = self#read_char c_dollarsign in
	    let base = self#read_templated_name in
	    let _ = self#read_char c_atsign in
	    let args = self#read_template_argument_list in
	    TemplatedName (base,args)
	  else
	    begin
	      self#stop ("reading templated-name (no dollar sign found)") ;
	      raise (BCH_failure
                       (STR "reading templated-name (no dollar sign found)"))
	    end
	end
      else
	begin
	  self#stop ("reading templated-name (not a name, not a questionmark)") ;
	  raise (BCH_failure
                   (STR "reading templated-name (not a name, not a questionmark)"))
	end in
    begin
      names <- tname :: names ;
      tname
    end
	  
  method demangle =
    begin
      self#next_char ;
      self#read_char c_questionmark ;
      self#read_base_name ;
      if cppname#is_vftable || cppname#is_vbtable then () else
	begin
	  self#read_function_type_code ;
	  (if char_la = c_atsign then self#read_char c_atsign) ;
	  self#read_storage_class ;
	  self#check_end_of_string
	end
    end

  method private read_storage_class =
    if char_la = c_A then
	cppname#set_storage_class "normal" 
    else if char_la = c_B then
	cppname#set_storage_class "volatile" 
    else if char_la = c_C then
	cppname#set_storage_class "const" 
    else if char_la = c_Z then
	cppname#set_storage_class "executable" 
    else
      self#stop "read storage-class"
      

  method private read_base_name =
    if char_la = c_questionmark then
      begin
	self#read_char c_questionmark ;
	self#read_encoded_basename
      end
    else if is_name_start_char char_la then
      self#read_string_name
    else
      self#stop "read base-name"

  method private read_operator code op =
    begin
      self#read_char code ;
      self#read_name_space_names ;
      cppname#set_operator ("operator" ^ op)
    end

  method private read_encoded_basename =
    if char_la = c_zero then
      begin
	self#read_char c_zero ;
	self#read_constructor_name
      end
    else if char_la = c_one then
      begin
	self#read_char c_one ;
	self#read_destructor_name
      end
    else if char_la = c_two then self#read_operator c_two "_new"
    else if char_la = c_three then self#read_operator c_three "_delete"
    else if char_la = c_four then self#read_operator c_four "="
    else if char_la = c_five then self#read_operator c_five ">>"
    else if char_la = c_six then  self#read_operator c_six  "<<"
    else if char_la = c_seven then self#read_operator c_seven "!"
    else if char_la = c_eight then self#read_operator c_eight "=="
    else if char_la = c_nine then self#read_operator c_nine "!="
    else if char_la = c_A then self#read_operator c_A "[]"
    else if char_la = c_B then self#read_operator c_B " int"
    else if char_la = c_D then self#read_operator c_D "*"
    else if char_la = c_E then self#read_operator c_E "++"
    else if char_la = c_F then self#read_operator c_F "--"
    else if char_la = c_G then self#read_operator c_G "-"
    else if char_la = c_H then self#read_operator c_H "+"
    else if char_la = c_I then self#read_operator c_I "&"
    else if char_la = c_M then self#read_operator c_M "<"
    else if char_la = c_N then self#read_operator c_N "<="
    else if char_la = c_O then self#read_operator c_O ">"
    else if char_la = c_P then self#read_operator c_P ">="
    else if char_la = c_R then self#read_operator c_R "()"
    else if char_la = c_S then self#read_operator c_S "~"
    else if char_la = c_U then self#read_operator c_U "|"
    else if char_la = c_X then self#read_operator c_X "*="
    else if char_la = c_Y then self#read_operator c_Y "+="
    else if char_la = c_Z then self#read_operator c_Z "-="
    else if char_la = c_underscore then
      begin
	self#read_char c_underscore ;
	if char_la = c_zero then self#read_operator c_zero "/="
	else if char_la = c_four then self#read_operator c_four "&="
	else if char_la = c_five then self#read_operator c_five "|="
	else if char_la = c_six then  self#read_operator c_six  "^-="
	else if char_la = c_seven then 
	  begin
	    self#read_char c_seven ;
	    cppname#set_vftable ;
	  end
	else if char_la = c_eight then 
	  begin
	    self#read_char c_eight ;
	    cppname#set_vbtable ;
	  end
	else if char_la = c_V then self#read_operator c_V " delete[]"
	else
	  self#stop "read encoded-base-name from underscore"
      end
    else
      self#stop "read encoded-base-name"

  method private read_constructor_name =
    let name = self#read_templated_name in
    begin
      cppname#add_name_space name ;
      cppname#set_method_name name ;
      cppname#set_constructor ;
      self#read_char c_atsign ;
      self#read_name_space_names
    end

  method private read_destructor_name =
    let name = self#read_templated_name in
    begin
      cppname#add_name_space name ;
      cppname#set_method_name name ;
      cppname#set_destructor ;
      self#read_char c_atsign ;
      self#read_name_space_names
    end

  method private read_name_space_names =
    begin
      while char_la != c_atsign do
	begin
	  cppname#add_name_space self#read_templated_name ;
	  self#read_char c_atsign
	end
      done ;
      self#read_char c_atsign
    end
      
  method private read_string_name =
    let name = self#read_templated_name in
    begin
      cppname#set_method_name name ;
      self#read_char c_atsign ;
      self#read_name_space_names
    end

  method private read_function_type_code =
    begin
      self#read_function_access ;
      (if cppname#is_constructor || cppname#is_destructor then
	  (if char_la = c_atsign then self#read_char c_atsign else ())
       else self#read_returntype) ;
      self#read_argument_list
    end

  method private read_function_access =
    begin
      self#read_access_qualifier ;
      self#read_calling_convention
    end

  method private read_access_qualifier =
    if is_x_access_qualifier_char char_la then
      self#read_xconst_access_qualifier
    else if is_s_access_qualifier_char char_la then
      self#read_s_access_qualifier
    else
      self#stop "read_function_access"    
	
  method private read_xconst_access_qualifier =
    begin
      self#read_x_access_qualifier ;
      self#read_const_qualifier
    end

  method private read_x_access_qualifier =
    if char_la = c_A then 
      begin
	cppname#set_accessibility "private" ;
	self#read_char c_A
      end
    else if char_la = c_E then
      begin
	cppname#set_accessibility "private" ;
	cppname#set_virtual ;
	self#read_char c_E
      end
    else if char_la = c_I then
      begin
	cppname#set_accessibility "protected" ;
	self#read_char c_I
      end
    else if char_la = c_M then
      begin
	cppname#set_accessibility "protected" ;
	cppname#set_virtual ;
	self#read_char c_M
      end
    else if char_la = c_Q then
      begin
	cppname#set_accessibility "public" ;
	self#read_char c_Q
      end
    else if char_la = c_U then
      begin
	cppname#set_accessibility "public" ;
	cppname#set_virtual ;
	self#read_char c_U
      end
    else
      self#stop "read x-access-qualifier"

  method private read_s_access_qualifier =
    if char_la = c_C then
      begin
	cppname#set_accessibility "private" ;
	cppname#set_static ;
	self#read_char c_C
      end
    else if char_la = c_K then
      begin
	cppname#set_accessibility "protected" ;
	cppname#set_static ;
	self#read_char c_K
      end
    else if char_la = c_S then
      begin
	cppname#set_accessibility "public" ;
	cppname#set_static ;
	self#read_char c_S
      end
    else if char_la = c_Y then
      self#read_char c_Y
    else
      self#stop "read s-access-qualifier"

  method private read_const_qualifier =
    if char_la = c_A then
      self#read_char c_A
    else if char_la = c_B then
      begin
	cppname#set_const ;
	self#read_char c_B
      end
    else
      self#stop "read const-qualifier"

  method private read_calling_convention =
    if char_la = c_A then
      begin
	cppname#set_calling_convention "__cdecl" ;
	self#read_char c_A
      end
    else if char_la = c_E then
      begin
	cppname#set_calling_convention "__thiscall" ;
	self#read_char c_E
      end
    else if char_la = c_G then
      begin
	cppname#set_calling_convention "__stdcall" ;
	self#read_char c_G
      end
    else if char_la = c_I then
      begin
	cppname#set_calling_convention "__fastcall" ;
	self#read_char c_I
      end
    else
      self#stop "read calling-convention"
    
  method private read_returntype = cppname#set_returntype self#read_type_code 

  method private read_argument_list = 
    while is_type_start_char char_la do
      cppname#add_par_type self#read_type_code
    done

  method private read_type_code =
    if char_la = c_zero then
      begin
	self#read_char c_zero ;
	cppname#get_parameter_type 0
      end
    else if char_la = c_one then
      begin
	self#read_char c_one ;
	cppname#get_parameter_type 1
      end
    else if char_la = c_two then
      begin
	self#read_char c_two ;
	cppname#get_parameter_type 2 ;
      end
    else if is_basic_type_char char_la then
      self#read_basic_type_code
    else if is_complex_type_char char_la then
      self#read_complex_type_code
    else if char_la = c_questionmark then
      begin
	self#read_char c_questionmark ;
	let modifier = self#read_type_modifier in
	let ty = self#read_complex_type_code in
	if modifier = "" then ty else t_add_attr ty modifier
      end
    else
      begin
	self#stop "read type-code" ;
	raise (BCH_failure (STR "read_type_code"))
      end

  method private read_basic_type_code =
    if char_la = c_C then
      begin self#read_char c_C ; t_schar end
    else if char_la = c_D then
      begin self#read_char c_D ; t_char end
    else if char_la = c_E then
      begin self#read_char c_E ; t_uchar end
    else if char_la = c_F then
      begin self#read_char c_F ; t_short end
    else if char_la = c_G then
      begin self#read_char c_G ; t_ushort end
    else if char_la = c_H then
      begin self#read_char c_H ; t_int end
    else if char_la = c_I then
      begin self#read_char c_I ; t_uint end
    else if char_la = c_J then
      begin self#read_char c_J ; t_long end
    else if char_la = c_K then
      begin self#read_char c_K ; t_ulong end
    else if char_la = c_M then
      begin self#read_char c_M ; t_float end
    else if char_la = c_N then
      begin self#read_char c_N ; t_double end
    else if char_la = c_X then
      begin self#read_char c_X ; t_void end
    else if char_la = c_underscore then
      begin
	self#read_char c_underscore ;
	if char_la = c_N then
	  begin self#read_char c_N ; t_bool end
	else if char_la = c_J then
	  begin self#read_char c_J ; t_int64 end
	else if char_la = c_K then
	  begin self#read_char c_K ; t_uint64 end
	else if char_la = c_W then
	  begin self#read_char c_W ; t_wchar_t end
	else
	  begin
	    self#stop "read basic_type-code underscore" ;
	    raise (BCH_failure (STR "read_basic_type_code"))
 	  end
      end
    else
      begin
	self#stop "read basic_type-code" ;
	raise (BCH_failure (STR "read_basic_type_code"))
      end

  method private read_name_sequence =
    if char_la = c_atsign then
      begin
	self#read_char c_atsign ;
	[]
      end
    else if char_la = c_zero then
      begin
	self#read_char c_zero ;
	(self#get_name 0) :: self#read_name_sequence
      end
    else if char_la = c_one then
      begin
	self#read_char c_one ;
	(self#get_name 1) :: self#read_name_sequence
      end
    else if char_la = c_two then
      begin
	self#read_char c_two ;
	(self#get_name 2) :: self#read_name_sequence
      end
    else if char_la = c_three then
      begin
	self#read_char c_three ;
	(self#get_name 3) :: self#read_name_sequence
      end
    else if char_la = c_four then
      begin
	self#read_char c_four ;
	(self#get_name 4) :: self#read_name_sequence
      end
    else if is_name_start_char char_la || char_la = c_questionmark then
      let name = self#read_templated_name in
      begin
	self#read_char c_atsign ;
	name :: self#read_name_sequence
      end
    else
      begin
	self#stop "read_name_sequence" ;
	raise (BCH_failure (STR "read_name_sequence"))
      end

  method read_complex_type_code =
    if char_la = c_P then
      let _ = self#read_char c_P in
      let modifier = self#read_type_modifier in
      let ty = self#read_complex_type_code in
      let ty = if modifier = "" then ty else t_add_attr ty modifier in
      t_ptrto ty
    else if char_la = c_A then
      let _ = self#read_char c_A in
      let modifier = self#read_type_modifier in
      let ty = self#read_complex_type_code in
      let ty = if modifier = "" then ty else t_add_attr ty modifier in
      t_refto ty
    else if char_la = c_V then
      let _ = self#read_char c_V in
      let names = self#read_name_sequence in
      match names with
      | name :: tl -> t_tclass ~name_space:tl name
      | _ -> raise (BCH_failure (LBLOCK [ STR "empty name sequence"]))
    else if char_la = c_U then
      let _ = self#read_char c_U in
      let names = self#read_name_sequence in
      match names with
      | name :: tl -> t_tcomp ~name_space:tl name
      | _ -> raise (BCH_failure (LBLOCK [ STR "empty name sequence"]))
    else if char_la = c_W then
      let _ = self#read_char c_W in
      if char_la = c_four then
	let _ = self#read_char c_four in
	let names = self#read_name_sequence in
	match names with
	| name :: tl -> t_tenum ~name_space:tl name
	| _ -> raise (BCH_failure (LBLOCK [ STR "empty name sequence"]))
      else
	begin
	  self#stop "read complex-type-code with W" ;
	  raise (BCH_failure (STR "read_complex_type_code with W"))
	end
    else if is_basic_type_char char_la then
      self#read_basic_type_code
    else
      begin
	self#stop "read complex-type-code" ;
	raise (BCH_failure (STR "read_complex_type_code"))
      end

  method read_type_modifier =
    if char_la = c_A then 
      begin self#read_char c_A ; "" end
    else if char_la = c_B then
      begin self#read_char c_B ; "const" end
    else
      begin
	self#stop "read type-modifier" ;
	raise (BCH_failure (STR "read_type_modifier"))
      end

  method toPretty = cppname#toPretty

end

let demangled_names = H.create 3
let demangling_failures = H.create 3

let demangle_name s =
  if String.length s = 0 || s.[0] != '?' then () else
    if H.mem demangled_names s then () else
      if H.mem demangling_failures s then () else
	let demangler = new demangler_t s in
	try
	  begin
	    demangler#demangle ;
	    H.add demangled_names s demangler#get_cppname#to_demangled_name
	  end
	with
	  BCH_failure p -> H.add demangling_failures s p

let get_demangled_name s =
  let _ = demangle_name s in
  if H.mem demangled_names s then H.find demangled_names s else 
    raise (BCH_failure (LBLOCK [ STR "No demangled name found for " ; STR s ]))

let has_demangled_name s = begin demangle_name s ; H.mem demangled_names s end

let report_demangling_failures () =
  H.iter (fun k v -> ch_error_log#add "demangling" (LBLOCK [ STR k ; STR ": " ; v ]))
    demangling_failures

let retrieve_demangling_failures () =
  let lst = ref [] in
  let _ = H.iter (fun k v -> lst := (k,v) :: !lst) demangling_failures in
  List.rev !lst


let demangle s =
  let _ = demangle_name s in
  if H.mem demangled_names s then demangled_name_to_string (H.find demangled_names s) else s
