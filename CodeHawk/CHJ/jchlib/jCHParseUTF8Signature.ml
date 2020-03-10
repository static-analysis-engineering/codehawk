(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHSignature

module H = Hashtbl

exception IllFormed
exception UTF8ParseError of pretty_t

(* ==============================================================================
   Grammar
   https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.3.2
   ==============================================================================

   Descriptors
   ------------------------------------------------------------------------------

   FieldDescriptor: 
     FieldType

   FieldType:
     BaseType 
     ObjectType 
     ArrayType

   BaseType:
     B : signed byte
     C : Unicode character code point in the Basic Multilingual Plane, encoded with UTF-16
     D : double-precision floating-point value
     F : single-precision floating-point value
     I : integer
     J : long integer
     S : signed short
     Z : boolean (true or false)

   ObjectType:
     L ClassName ;

   ArrayType:
     [ ComponentType

   ComponentType:
     FieldType

   MethodDescriptor:
     ( {ParameterDescriptor} ) ReturnDescriptor

   ParameterDescriptor:
     FieldType

   ReturnDescriptor:
     FieldType
     VoidDescriptor

   VoidDescriptor:
     V

   Signatures
   -----------------------------------------------------------------------------

   JavaTypeSignature
     ReferenceTypeSignature
     BaseType

   ReferenceTypeSignature:
     ClassTypeSignature
     TypeVariableSignature
     ArrayTypeSignature

   ClassTypeSignature:
     L [PackageSpecifier] SimpleClassTypeSignature {ClassTypeSignatureSuffix} ;

   PackageSpecifier:
     Identifier / {PackageSpecifier}

   SimpleClassTypeSignature:
     Identifier [TypeArguments]

   TypeArguments:
     < TypeArgument {TypeArgument} >

   TypeArgument:
     [WildcardIndicator] ReferenceTypeSignature
     *

   WildcardIndicator:
     +
     -

   ClassTypeSignatureSuffix:
     . SimpleClassTypeSignature

   TypeVariableSignature
     T Identifier ;

   ArrayTypeSignature:
     [ JavaTypeSignature


   ClassSignature:
     [TypeParameters] SuperclassSignature {SuperInterfaceSignature}

   TypeParameters:
     < TypeParameter {TypeParameter} >

   TypeParameter:
     Identifier ClassBound {InterfaceBound}

   ClassBound:
     : [ReferenceTypeSignature]

   InterfaceBound:
     : ReferenceTypeSignature

   SuperClassSignature:
     ClassTypeSignature

   SuperInterfaceSignature:
     ClassTypeSignature

   MethodSignature:
     [TypeParameters] ( {JavaTypeSignature} ) Result {ThrowSignature}

   Result:
     JavaTypeSignature
     VoidDescriptor

   ThrowSignature:
     ^ ClassTypeSignature
     ^ TypeVariableSignature

   FieldSignature:
     ReferenceTypeSignature

   ==============================================================================  

 *)

(* Char byte length according to first UTF-8 byte for the modified UTF-8
   used in the JVM. 

   The two differences with standard UTF-8 are:
   (ref: https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html#jvms-4.4.7)
   1) The null code point ('\u0000') is represented by two bytes;
      11000000 and 10000000
   2) Characters with code point above U+FFFF are represented by six bytes
      (the JVM does not have 4-byte sequences).
 *)
let utf8_length = [|        (* Char byte length according to first UTF-8 byte. *)
  0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 
  1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 
  0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 
  0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 
  0; 0; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 
  2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 3; 
  0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0 |]

let read_utf8 getchar =
  let b0 = getchar () in
  let check c = if c then () else raise IllFormed in
  match utf8_length.(b0) with
  | 0 -> raise IllFormed
  | 1 -> b0
  | 2 ->
     let b1 = getchar () in
     begin
       check ((b1 lsr 6) = 0b10) ;
       ((b0 land 0x1F) lsl 6) lor 
	 ((b1 land 0x3F))
     end
  | 3 ->
     let b1 = getchar () in
     let b2 = getchar () in
     begin
       check ((b2 lsr 6) = 0b10) ;
       (match b0 with
	| 0xE0 -> check (b1 >= 0xA0 && b1 <= 0xBF)
	| 0xED -> check (b1 >= 0x80 && b1 <= 0x9F)
	| _ -> check ((b1 lsr 6) = 0b10));
       ((b0 land 0x0F) lsl 12) lor 
	 ((b1 land 0x3F) lsl  6) lor 
	   ((b2 land 0x3F))
     end
  | _ -> assert false
       
let in_range c lower_bound upper_bound = c >= lower_bound && c <= upper_bound

let is_ascii c = in_range 0x01 0x7F


module XString = struct
  type t = string
  let empty = ""
  let length = String.length
  let append = ( ^ )
  let lowercase = String.lowercase_ascii
  let iter f s =
    let len = String.length s in
    let pos = ref ~-1 in
    let get () =
      incr pos ;
      if !pos = len then raise Exit else
	Char.code (String.get s !pos) in
    try 
      while true do f (read_utf8 get) done
    with
    | Exit -> ()
  let of_string s = s
  let to_utf8 f v x = f v x
  let compare = String.compare
end
               
let string_equal s1 s2 = (XString.compare s1 s2) = 0

module XBuffer = struct
  type string = XString.t
  type t = Buffer.t
  exception Full
  let create = Buffer.create
  let add_char = Buffer.add_char
  let add_uchar buffer uchar =
    try
      let store c = Buffer.add_char buffer (Char.chr c) in
      if uchar <= 0x007F then
	store uchar
      else if uchar <= 0x07FF then
	begin
	  store (0xC0 lor (uchar lsr 6));
	  store (0x80 lor (uchar land 0x3f)) 
	end
      else if uchar <= 0xFFFF then
	begin
	  store (0xE0 lor (uchar lsr 12));
	  store (0x80 lor ((uchar lsr 6) land 0x3F)) ;
	  store (0x80 lor (uchar land 0x3F))
	end
      else  (* code points larger than 0xFFFF not supported *)
        begin
          pr_debug [ STR "Encountered character larger than 0xFFFF: " ;
                     INT uchar ; NL ] ;
          assert false
        end
    with
    | Failure _ -> raise Full
                 
  let clear = Buffer.clear
  let contents = Buffer.contents
  let length = Buffer.length
end

let c_end_of_input = max_int

let raise_utf8_parse_error msg char_la s =
  if char_la = c_end_of_input then
    raise (UTF8ParseError (LBLOCK [ msg ; STR "end-of-input" ;
                                    STR " on string " ; STR s]))
  else
    raise (UTF8ParseError (LBLOCK [ msg ; STR (Char.escaped (Char.chr char_la)) ;
          STR " on string " ; STR s ]))

(* -------------------------------------------------------------------
   Delimiters
   ------------------------------------------------------------------- *)
let c_period            = 0x002E
let c_semicolon         = 0x003B
let c_leftsqbracket     = 0x005B
let c_fwdslash          = 0x002F
let c_leftanglebracket  = 0x003C
let c_rightanglebracket = 0x003E
let c_leftparen         = 0x0028
let c_rightparen        = 0x0029
let c_colon             = 0x003A    (* excluded from some names *)

let c_plus  = 0x002B
let c_minus = 0x002D
let c_star  = 0x002A
let c_caret = 0x005E

let c_L = 0x004C
let c_T = 0x0054
let c_V = 0x0056

let is_name_delimiter c =
  (c = c_period) || (c = c_semicolon) || (c = c_leftsqbracket)
  || (c = c_fwdslash) || (c = c_leftanglebracket) || (c = c_rightanglebracket)
  || (c = c_colon)

let is_name_char c =
  not ((is_name_delimiter c) || (c = c_end_of_input))
                   
(* -------------------------------------------------------------------
   literals
   ------------------------------------------------------------------- *)
let c_c = 0x0063
let c_i = 0x0069
let c_l = 0x006C
let c_n = 0x006E
let c_t = 0x0074
                        
(* -------------------------------------------------------------------
   Base types
   ------------------------------------------------------------------- *)
let c_B = 0x0042
let c_C = 0x0043
let c_D = 0x0044
let c_F = 0x0046
let c_I = 0x0049
let c_J = 0x004A
let c_S = 0x0053
let c_Z = 0x005A

let is_base_type_char c =
  (c = c_B) || (c = c_C) || (c = c_D) || (c = c_F) || (c = c_I)
  || (c = c_J) || (c = c_S) || (c = c_Z)

let get_base_type i =
  if is_base_type_char i then
    let c = Char.chr i in
    match c with
    | 'B' -> Byte
    | 'C' -> Char
    | 'D' -> Double
    | 'F' -> Float
    | 'I' -> Int
    | 'J' -> Long
    | 'S' -> Short
    | 'Z' -> Bool
    | _ ->
       raise_utf8_parse_error (STR "Invalid base type character: ") i "base-type"
  else
    raise_utf8_parse_error (STR "Invalid base type character: ") i "base-type"

class utf8_signature_reader_t (s:string) =
object (self)

  val mutable ch = IO.input_string s
  val mutable pos = (fun () -> 0)
  val mutable char_la = 0
  val name_buffer = XBuffer.create 17

  method input_unicode = read_utf8 (fun () -> IO.read_byte ch)

  method fill_name_buffer c = XBuffer.add_uchar name_buffer c

  method private read_char expected_char =
    if char_la = expected_char then
      self#next_char
    else
      raise_utf8_parse_error
        (LBLOCK [ STR "Expected to see " ; STR (Char.escaped (Char.chr expected_char)) ;
                  STR ", but found: " ])
        char_la s

  method private check_char_la predicate msg =
    if predicate char_la then
      ()
    else
      raise_utf8_parse_error msg char_la s

  method private next_char =
    try
      begin
        char_la <- self#input_unicode;
      end
    with
    | IO.No_more_input ->
       char_la <- c_end_of_input

  method private read_name =
    begin
      XBuffer.clear name_buffer ;
      if char_la = c_leftanglebracket then
        self#read_constructor_name
      else
        begin
          self#fill_name_buffer char_la ;
          self#next_char ;
          while is_name_char char_la do
            begin
              self#fill_name_buffer char_la ;
              self#next_char
            end
          done;
          XBuffer.contents name_buffer
        end
    end

  method private read_constructor_name =
    self#read_char c_leftanglebracket ;
    if char_la = c_i then
      begin
        self#read_char c_i ;
        self#read_char c_n ;
        self#read_char c_i ;
        self#read_char c_t ;
        self#read_char c_rightanglebracket ;
        "<init>"
      end
    else if char_la = c_c then
      begin
        self#read_char c_c ;
        self#read_char c_l ;
        self#read_char c_i ;
        self#read_char c_n ;
        self#read_char c_i ;
        self#read_char c_t ;
        self#read_char c_rightanglebracket ;
        "<clinit>"
      end
    else
      raise_utf8_parse_error (STR "Expected <init> or <clinit> but found: ") char_la s
      
    (* -------------------------------------------------------------------------
     * BaseType:
     *  B | C | D | F | I | J | S | Z
     * ------------------------------------------------------------------------- *)
  method private parse_BaseType =
    let _ =
      self#check_char_la
        is_base_type_char
        (STR "Expected base type character, but found: ") in
    let t = get_base_type char_la in
    let _ = self#next_char in
    t

    (* -------------------------------------------------------------------------
     *  ObjectType:
     *    L ClassName ;
     * ------------------------------------------------------------------------- *)
  method private parse_ObjectType:class_name_int =
    let names = ref [] in
    begin
      self#read_char c_L ;
      names := [ self#read_name ] ;
      while char_la = c_fwdslash do
        self#read_char c_fwdslash ;
        names := self#read_name :: !names
      done ;
      self#read_char c_semicolon ;
      common_dictionary#make_class_name (String.concat "." (List.rev !names))
    end

  method parse_class_name:class_name_int =
    let names = ref [] in
    begin
      names := self#read_name :: !names ;
      while char_la = c_fwdslash do
        self#read_char c_fwdslash ;
        names := self#read_name :: !names
      done ;
      common_dictionary#make_class_name (String.concat "." (List.rev !names))
    end

  method private parse_value_type:value_type_t =
    if is_base_type_char char_la then
      TBasic self#parse_BaseType
    else
      TObject self#parse_ot

  method private parse_array:value_type_t =
    begin
      self#read_char c_leftsqbracket ;
      self#parse_value_type
    end

  method private parse_ot:object_type_t =
    if char_la = c_leftsqbracket then
      TArray self#parse_array
    else if char_la = c_L then
      TClass self#parse_ObjectType
    else
      TClass self#parse_class_name

    (* -------------------------------------------------------------------------    
     * ArrayType:
     *  [ ComponentType
     * ------------------------------------------------------------------------- *)
  method private parse_ArrayType =
    begin
      self#read_char c_leftsqbracket ;
      self#parse_ComponentType
    end     

    (* -------------------------------------------------------------------------        
     * ComponentType:
     *   FieldType
     * ------------------------------------------------------------------------- *)
  method private parse_ComponentType =  self#parse_FieldType

    (* -------------------------------------------------------------------------        
     * FieldDescriptor: 
     *   FieldType
     * ------------------------------------------------------------------------- *)
  method private parse_FieldDescriptor = self#parse_FieldType

    (* -------------------------------------------------------------------------        
     * ParameterDescriptor:
     *   FieldType
     * ------------------------------------------------------------------------- *)
  method private parse_ParameterDescriptor = self#parse_FieldType

    (* -------------------------------------------------------------------------        
     * VoidDescriptor:
     *   V
     * ------------------------------------------------------------------------- *)
  method private parse_VoidDescriptor = self#read_char c_V
                                      
    (* -------------------------------------------------------------------------
     * FieldType:
     *   BaseType 
     *   ObjectType 
     *   ArrayType
     * ------------------------------------------------------------------------- *)
  method private parse_FieldType =
    if is_base_type_char char_la then
      TBasic self#parse_BaseType
    else if char_la = c_leftsqbracket then
      TObject (TArray self#parse_ArrayType)
    else if char_la = c_L then
      TObject (TClass self#parse_ObjectType)
    else
      raise_utf8_parse_error
        (STR "Expected basic type or L or [, but found: ") char_la s
    
    (* -------------------------------------------------------------------------
     * ReturnDescriptor:
     *   FieldType
     *   VoidDescriptor
     * ------------------------------------------------------------------------- *)
  method private parse_ReturnDescriptor =
    if char_la = c_V then
      begin
        self#parse_VoidDescriptor ;
        TBasic Void
      end
    else
      self#parse_FieldType

    (* -------------------------------------------------------------------------
     * MethodDescriptor:
     *   ( {ParameterDescriptor} ) ReturnDescriptor
     * ------------------------------------------------------------------------- *)
  method private parse_MethodDescriptor =
    let params =  ref [] in
    begin
      self#read_char c_leftparen ;
      while char_la <> c_rightparen do
        params := self#parse_ParameterDescriptor :: !params
      done ;
      self#read_char c_rightparen ;
      let returntype =
        match self#parse_ReturnDescriptor with
        | TBasic Void -> None
        | t -> Some t in
      make_method_descriptor ~arguments:(List.rev !params) ?return_value:returntype ()
    end


  method private parse_Descriptor =
    if char_la = c_leftparen then
      SMethod (self#parse_MethodDescriptor)
    else
      SValue (self#parse_FieldType)


    (* -------------------------------------------------------------------------
     * JavaTypeSignature
     *   ReferenceTypeSignature
     *   BaseType
     * ------------------------------------------------------------------------- *)
  method private parse_JavaTypeSignature:type_signature_int =
    if is_base_type_char char_la then
      let t = self#parse_BaseType in
      make_type_signature ~kind:BasicType ?basic_type:(Some t) ()
    else
      make_type_signature
        ~kind:ObjectType
        ?object_type:(Some self#parse_ReferenceTypeSignature) ()

    (* -------------------------------------------------------------------------
     * TypeArguments:
     *   < TypeArgument {TypeArgument} >
     * ------------------------------------------------------------------------- *)
  method private parse_TypeArguments:type_argument_int list =
    let args = ref [] in
    begin
      self#read_char c_leftanglebracket ;
      args := self#parse_TypeArgument :: !args ;
      while char_la <> c_rightanglebracket do
        args := self#parse_TypeArgument :: !args
      done ;
      self#read_char c_rightanglebracket ;
      List.rev !args
    end

    (* -------------------------------------------------------------------------
     * TypeArgument:
     *   [WildcardIndicator] ReferenceTypeSignature
     *   *
     * ------------------------------------------------------------------------- *)
  method private parse_TypeArgument:type_argument_int =
    if char_la = c_star then
      begin
        self#read_char c_star ;
        make_type_argument ~kind:ArgumentIsAny ()
      end
    else if char_la = c_plus then
      begin
        self#read_char c_plus ;
        make_type_argument
          ~kind:ArgumentExtends
          ~field_type_signature:self#parse_ReferenceTypeSignature ()
      end
    else if char_la = c_minus then
      begin
        self#read_char c_minus ;
        make_type_argument
          ~kind:ArgumentInherits
          ~field_type_signature:self#parse_ReferenceTypeSignature ()
      end
    else
      make_type_argument
        ~kind:ArgumentIs
        ~field_type_signature:self#parse_ReferenceTypeSignature ()
    

    (* -------------------------------------------------------------------------
     * WildcardIndicator:
     *   +
     *   -
     * ------------------------------------------------------------------------- *)

    (* -------------------------------------------------------------------------
     * PackageSpecifier:
     *   Identifier / {PackageSpecifier}
     * ------------------------------------------------------------------------- *)

    (* -------------------------------------------------------------------------
     * ClassTypeSignatureSuffix:
     *   . SimpleClassTypeSignature
     * ------------------------------------------------------------------------- *)
  method private parse_ClassTypeSignatureSuffix:simple_class_type_signature_int =
    begin
      self#read_char c_period ;
      self#parse_SimpleClassTypeSignature
    end

    (* -------------------------------------------------------------------------
     * SimpleClassTypeSignature:
     *   Identifier [TypeArguments]
     * ------------------------------------------------------------------------- *)
  method private parse_SimpleClassTypeSignature:simple_class_type_signature_int =
    let name = self#read_name in
    let type_arguments =
      if char_la = c_leftanglebracket then
        self#parse_TypeArguments
      else
        [] in
    make_simple_class_type_signature ~name ~type_arguments

    (* -------------------------------------------------------------------------
     * ArrayTypeSignature:
     *   [ JavaTypeSignature
     * ------------------------------------------------------------------------- *)
  method private parse_ArrayTypeSignature:type_signature_int =
    begin
      self#read_char c_leftsqbracket ;
      self#parse_JavaTypeSignature
    end
    
    (* -------------------------------------------------------------------------
     * TypeVariableSignature
     *   T Identifier ;
     * ------------------------------------------------------------------------- *)
  method private parse_TypeVariableSignature:type_variable_int =
    let _ = self#read_char c_T in
    let name = self#read_name in
    let _ = self#read_char c_semicolon in
    make_type_variable name

    (* -------------------------------------------------------------------------    
     * ClassTypeSignature:
     *  L [PackageSpecifier] SimpleClassTypeSignature {ClassTypeSignatureSuffix} ;
     * ------------------------------------------------------------------------- *)
  method private parse_ClassTypeSignature:class_type_signature_int =
    let _ = self#read_char c_L in
    let names = ref [] in
    let suffixes = ref [] in
    let _ = names := self#read_name :: !names in
    let _ =
      while char_la = c_fwdslash do
        begin
          self#read_char c_fwdslash ;
          names := self#read_name :: !names
        end
      done in
    let type_arguments =
      if char_la = c_leftanglebracket then
        self#parse_TypeArguments
      else
        [] in
    let _ =
      while char_la = c_period do
        suffixes := self#parse_ClassTypeSignatureSuffix :: !suffixes
      done in
    let _ = self#read_char c_semicolon in
    let suffixes = List.rev !suffixes in
    let cn = common_dictionary#make_class_name (String.concat "." (List.rev !names)) in
    let package = cn#package in
    let name = cn#simple_name in
    let firstct = make_simple_class_type_signature ~name ~type_arguments in
    let (simple_class_type_signature,enclosing_classes) =
      let revlist = List.rev (firstct :: suffixes) in
      (List.hd revlist, List.rev (List.tl revlist)) in
    make_class_type_signature
      ~package
      ~enclosing_classes
      ~simple_class_type_signature

    (* -------------------------------------------------------------------------
     * ReferenceTypeSignature:
     *   ClassTypeSignature
     *   TypeVariableSignature
     *   ArrayTypeSignature
     * ------------------------------------------------------------------------- *)
  method private parse_ReferenceTypeSignature:field_type_signature_int = 
    if char_la = c_T then
      let t = self#parse_TypeVariableSignature in
      make_field_type_signature ~kind:TypeVariable ~type_variable:t ()
    else if char_la = c_leftsqbracket then
      let t = self#parse_ArrayTypeSignature in
      make_field_type_signature ~kind:ArrayType ~array_type:t ()
    else if char_la = c_L then
      let t = self#parse_ClassTypeSignature in
      make_field_type_signature ~kind:ClassType ~class_type:t ()
    else
      raise_utf8_parse_error (STR "ReferenceTypeSignature: ") char_la s

    (* -------------------------------------------------------------------------
     * ClassBound:
     *   : [ReferenceTypeSignature]
     * ------------------------------------------------------------------------- *)
  method private parse_ClassBound:field_type_signature_int option =
    begin
      self#read_char c_colon ;
      if char_la = c_L || char_la = c_T || char_la = c_leftsqbracket then
        Some self#parse_ReferenceTypeSignature
      else
        None
    end

    (* -------------------------------------------------------------------------
     * InterfaceBound:
     *   : ReferenceTypeSignature
     * ------------------------------------------------------------------------- *)
  method private parse_InterfaceBound:field_type_signature_int =
    begin
      self#read_char c_colon ;
      self#parse_ReferenceTypeSignature
    end

    (* -------------------------------------------------------------------------
     * TypeParameter:
     *   Identifier ClassBound {InterfaceBound}
     * ------------------------------------------------------------------------- *)
  method private parse_TypeParameter:formal_type_parameter_int =
    let name = self#read_name in
    let class_bound = self#parse_ClassBound in
    let interface_bounds = ref [] in
    let _ =
      while char_la = c_colon do
        interface_bounds := self#parse_InterfaceBound :: !interface_bounds
      done in
    let interface_bounds = List.rev !interface_bounds in
    make_formal_type_parameter ~name ?class_bound ~interface_bounds ()

    (* -------------------------------------------------------------------------    
     * TypeParameters:
     *   < TypeParameter {TypeParameter} >
     * ------------------------------------------------------------------------- *)
  method private parse_TypeParameters:formal_type_parameter_int list =
    let params = ref [] in
    begin
      self#read_char c_leftanglebracket ;
      params := self#parse_TypeParameter :: !params ;
      while char_la <> c_rightanglebracket do
        params := self#parse_TypeParameter :: !params
      done ;
      self#read_char c_rightanglebracket ;
      List.rev !params
    end

  method private parse_opt_TypeParameters:formal_type_parameter_int list =
    if char_la = c_leftanglebracket then
      self#parse_TypeParameters
    else
      []

    (* -------------------------------------------------------------------------
     * SuperClassSignature:
     *   ClassTypeSignature
     * ------------------------------------------------------------------------- *)
  method private parse_SuperClassSignature:class_type_signature_int =
    self#parse_ClassTypeSignature

    (* -------------------------------------------------------------------------
     *  SuperInterfaceSignature:
     *    ClassTypeSignature
     * ------------------------------------------------------------------------- *)
  method private parse_SuperInterfaceSignature:class_type_signature_int =
    self#parse_ClassTypeSignature

    (* -------------------------------------------------------------------------
     * ClassSignature:
     *   [TypeParameters] SuperclassSignature {SuperInterfaceSignature}
     * ------------------------------------------------------------------------- *)
  method private parse_ClassSignature:class_signature_int =
    let formal_type_parameters = self#parse_opt_TypeParameters in
    let super_class = self#parse_SuperClassSignature in
    let interfaces = ref [] in
    let _ =
      while char_la <> c_end_of_input do
        interfaces := self#parse_SuperInterfaceSignature :: !interfaces
      done in
    let super_interfaces = List.rev !interfaces in
    make_class_signature ~formal_type_parameters ~super_class ~super_interfaces

    (* -------------------------------------------------------------------------
     * MethodSignature:
     *  [TypeParameters] ( {JavaTypeSignature} ) Result {ThrowSignature}
     * ------------------------------------------------------------------------- *)
  method private parse_MethodSignature:method_type_signature_int =
    let formal_type_parameters = self#parse_opt_TypeParameters in
    let _ = self#read_char c_leftparen in
    let ts = ref [] in
    let _ =
      while char_la <> c_rightparen do
        ts := self#parse_JavaTypeSignature :: !ts
      done in
    let type_signature = List.rev !ts in
    let _ = self#read_char c_rightparen in
    let return_type = self#parse_Result in
    let throws = ref [] in
    let _ =
      while char_la = c_caret do
        throws := self#parse_ThrowSignature :: !throws
      done  in
    let throws = List.rev !throws in
    make_method_type_signature
      ~formal_type_parameters
      ~type_signature
      ?return_type
      ~throws ()

    (* -------------------------------------------------------------------------
     * Result:
     *   JavaTypeSignature
     *   VoidDescriptor
     * ------------------------------------------------------------------------- *)
  method private parse_Result:type_signature_int option =
    if char_la = c_V then
      None
    else
      Some self#parse_JavaTypeSignature

    (* -------------------------------------------------------------------------
     * ThrowSignature:
     *   ^ ClassTypeSignature
     *   ^ TypeVariableSignature
     * ------------------------------------------------------------------------- *)
  method private parse_ThrowSignature:throws_signature_int =
    begin
      self#read_char c_caret ;
      if char_la = c_L then
        let class_type_signature = self#parse_ClassTypeSignature in
        make_throws_signature ~kind:ThrowsClass ~class_type_signature ()
      else if char_la = c_T then
        let type_variable = self#parse_TypeVariableSignature in
        make_throws_signature ~kind:ThrowsTypeVariable ~type_variable ()
      else
        raise_utf8_parse_error (STR "ThrowsSignature: ") char_la s
    end

    (* -------------------------------------------------------------------------
     * FieldSignature:
     *   ReferenceTypeSignature
     * ------------------------------------------------------------------------- *)
  method private parse_FieldSignature:field_type_signature_int =
    self#parse_ReferenceTypeSignature
                   

    
  (* ==================================================== public interface == *)

  method parse_base_type =
    begin
      self#next_char ;
      self#parse_BaseType
    end

  method parse_object_type =
    begin
      self#next_char ;
      self#parse_ot
    end

  method parse_field_type =
    begin
      self#next_char ;
      self#parse_FieldType
    end

  method parse_method_descriptor =
    begin
      self#next_char ;
      self#parse_MethodDescriptor
    end

  method parse_descriptor =
    begin
      self#next_char ;
      self#parse_Descriptor
    end

  method parse_class_signature =
    begin
      self#next_char  ;
      self#parse_ClassSignature
    end

  method parse_method_type_signature =
    begin
      self#next_char ;
      self#parse_MethodSignature
    end

  method parse_field_type_signature =
    begin
      self#next_char ;
      self#parse_FieldSignature
    end
    
end

(* -----------------------------------------------------------------------------
   Collection of parsed strings for validation
   ----------------------------------------------------------------------------- *)
let sigdb = H.create 5
let add (ty:string) (s:string) (p:pretty_t) =
  let t =
    if H.mem sigdb ty then
      H.find sigdb ty
    else
      let e = H.create 3 in
      begin H.add sigdb ty e ; e end in
  if H.mem t s then () else
    H.add t s p

let add_base_type s t = add "base type" s (java_basic_type_to_pretty t)

let add_class_name s t = add "classname" s t#toPretty

let add_object_type s t = add "object type" s (object_type_to_pretty t)

let add_value_type s t = add "value type" s (value_type_to_pretty t)

let add_method_descriptor s t = add "method descriptor" s t#toPretty

let add_descriptor s t = add "descriptor" s (descriptor_to_pretty t)         

let add_class_signature s t =
  add "class signature" s (LBLOCK [ NL ; INDENT (6, t#toPretty) ])

let add_method_type_signature s t =
  add "method type signature" s (LBLOCK [ NL ; INDENT (6, t#toPretty) ])

let add_field_type_signature s t = add "field type signature" s t#toPretty
                                 

let get_utf8_parsed_strings () =
  H.fold (fun ty table acc ->
      (ty, H.fold (fun s p acct -> (s,p)::acct) table []) :: acc) sigdb []
  
let trace = ref false
let activate_tracing () = trace := true

let parse_base_type (s:string):java_basic_type_t =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_base_type in
  begin
    (if !trace then add_base_type s result) ;
    result
  end
  
let parse_class_name (s:string):class_name_int =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_class_name in
  begin
    (if !trace then add_class_name s result) ;
    result
  end

let parse_object_type (s:string):object_type_t =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_object_type in
  begin
    (if !trace then add_object_type s result) ;
    result
  end

let parse_field_type (s:string):value_type_t =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_field_type in
  begin
    (if !trace then add_value_type s result) ;
    result
  end

let parse_field_descriptor = parse_field_type

let parse_method_descriptor (s:string):method_descriptor_int =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_method_descriptor in
  begin
    (if !trace then add_method_descriptor s result) ;
    result
  end

let parse_descriptor (s:string):descriptor_t =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_descriptor in
  begin
    (if !trace then add_descriptor s result) ;
    result
  end

let parse_class_signature (s:string):class_signature_int =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_class_signature in
  begin
    (if !trace then add_class_signature s result) ;
    result
  end

let parse_method_type_signature (s:string):method_type_signature_int =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_method_type_signature in
  begin
    (if !trace then add_method_type_signature s result) ;
    result
  end

let parse_field_type_signature (s:string):field_type_signature_int =
  let reader = new utf8_signature_reader_t s in
  let result = reader#parse_field_type_signature in
  begin
    (if !trace then add_field_type_signature s result) ;
    result
  end
