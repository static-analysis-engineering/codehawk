(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2024 Aarno Labs LLC

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

(** Utility to parse C-style format strings *)

(* chlib *)
open CHCommon
open CHPretty

module H = Hashtbl

(* =============================================================================
   Based on the C99 standard, section 7.19.6

   Undefined behavior:
   - Insufficient arguments
   - presence of precision with conversion specifiers c, s, p, n
   - presence of # flag with conversion specifiers d, i, u, c, s, p, n
   - presence of 0 flag with conversion specifiers c, s, p, n
   - presence of hh length modifier with conversion specifiers ...
   - ....

*)

(* =============================================================================
   Grammar (fprintf family)
   =============================================================================

   format-string:
       (ch)* (% (flag)* (fieldwidth)? ('.' (precision)?)? (lengthmod)? conversion)*

   flag:
     '-' | '+' | ' ' | '#' | '0'

   fieldwidth:
     '*' | non-negative number

   precision:
     '*' | number

   lengthmod:
     'hh' | 'h' | 'l' | 'll' | 'j' | 'z' | 't' | 'L'

   conversion:
     'd' | 'i' | 'o' | 'u' | 'x' | 'X' | 'f' | 'F' | 'e' | 'E' | 'g' | 'G' |
     'a' | 'A' | 'c' | 's' | 'P' | 'n' | '%'

   =============================================================================
   Grammar (fscanf family)
   =============================================================================

   format-string:
       (ch)* (% ('*')? (fieldwidth)? (lengthmod)? conversion)*

   fieldwidth:
     positive number

   lengthmod:
     'hh' | 'h' | 'l' | 'll' | 'j' | 'z' | 't' | 'L'

   conversion:
     'd' | 'i' | 'o' | 'u' | 'x' | 'X' | 'f' | 'F' | 'e' | 'E' | 'g' | 'G' |
     'a' | 'A' | 'c' | 's' | 'P' | 'n' | '%' | '[' (ch)* ']'

   ============================================================================= *)

let c_space    = 0x0020  (*   *)
let c_hash     = 0x0023  (* # *)
let c_percent  = 0x0025  (* % *)
let c_asterisk = 0x002A  (* * *)
let c_plus     = 0x002B  (* + *)
let c_minus    = 0x002D  (* - *)
let c_period   = 0x002E  (* . *)
let c_lbracket = 0x005B  (* [ *)
let c_rbracket = 0x005D  (* ] *)
let c_caret    = 0x005E  (* ^ *)

let c_A        = 0x0041   (* A *)
let _c_B       = 0x0042   (* B *)
let _c_C       = 0x0043   (* C *)
let _c_D       = 0x0044   (* D *)
let c_E        = 0x0045   (* E *)
let c_F        = 0x0046   (* F *)
let c_G        = 0x0047   (* G *)
let _c_H       = 0x0048   (* H *)
let _c_I       = 0x0049   (* I *)
let _c_J       = 0x004A   (* J *)
let _c_K       = 0x004B   (* K *)
let c_L        = 0x004C   (* L *)
let _c_M       = 0x004D   (* M *)
let _c_N       = 0x004E   (* N *)
let _c_O       = 0x004F   (* O *)
let c_P        = 0x0050   (* P *)
let _c_Q       = 0x0051   (* Q *)
let _c_R       = 0x0052   (* R *)
let _c_S       = 0x0053   (* S *)
let _c_U       = 0x0055   (* U *)
let _c_V       = 0x0056   (* V *)
let _c_W       = 0x0057   (* W *)
let c_X        = 0x0058   (* X *)
let _c_Y       = 0x0059   (* Y *)
let _c_Z       = 0x005A   (* Z *)

let c_a        = 0x0061   (* a *)
let _c_b       = 0x0062   (* b *)
let c_c        = 0x0063   (* c *)
let c_d        = 0x0064   (* d *)
let c_e        = 0x0065   (* e *)
let c_f        = 0x0066   (* f *)
let c_g        = 0x0067   (* g *)
let c_h        = 0x0068   (* h *)
let c_i        = 0x0069   (* i *)
let c_j        = 0x006A   (* j *)
let _c_k       = 0x006B   (* k *)
let c_l        = 0x006C   (* l *)
let _c_m       = 0x006D   (* m *)
let c_n        = 0x006E   (* n *)
let c_o        = 0x006F   (* o *)
let c_p        = 0x0070   (* p *)
let _c_q       = 0x0071   (* q *)
let _c_r       = 0x0072   (* r *)
let c_s        = 0x0073   (* s *)
let c_t        = 0x0074   (* t *)
let c_u        = 0x0075   (* u *)
let _c_v       = 0x0076   (* v *)
let _c_w       = 0x0077   (* w *)
let c_x        = 0x0078   (* x *)
let _c_y       = 0x0079   (* y *)
let c_z        = 0x007A   (* z *)

let c_zero     = 0x0030   (* 0 *)
let _c_one     = 0x0031   (* 1 *)
let _c_two     = 0x0032   (* 2 *)
let _c_three   = 0x0033   (* 3 *)
let _c_four    = 0x0034   (* 4 *)
let _c_five    = 0x0035   (* 5 *)
let _c_six     = 0x0036   (* 6 *)
let _c_seven   = 0x0037   (* 7 *)
let _c_eight   = 0x0038   (* 8 *)
let c_nine     = 0x0039   (* 9 *)

let in_range c lb ub = c >= lb && c <= ub

let is_percent_sign c = c = c_percent

let is_star c = c = c_asterisk

let is_period c = c = c_period

let is_left_bracket c = c = c_lbracket

let is_right_bracket c = c = c_rbracket

let is_caret c = c = c_caret

let _is_precision_start c = c = c_period

let is_number c = in_range c c_zero c_nine

let is_flag c =
  c = c_minus || c = c_plus || c = c_space || c = c_hash || c = c_zero

let is_fieldwidth_start c =  (is_star c) || (is_number c)

let is_lengthmodifier_start c =
  c = c_h || c = c_l || c = c_j || c = c_z || c = c_t || c = c_L

let _is_conversion c =
  c = c_d || c = c_i || c = c_o || c = c_u || c = c_x || c = c_X || c = c_f ||
    c = c_F || c = c_e || c = c_E || c = c_g || c = c_G || c = c_a || c = c_A ||
      c = c_c || c = c_s || c = c_P || c = c_n

type fieldwidth_t =
  | NoFieldwidth
  | FieldwidthArgument
  | FieldwidthConstant of int

type precision_t =
  | NoPrecision
  | PrecisionArgument
  | PrecisionConstant of int

type lengthmodifier_t =
  | NoModifier
  | CharModifier
  | ShortModifier
  | LongModifier
  | LongLongModifier
  | IntMaxModifier
  | SizeModifier
  | PtrDiffModifier
  | LongDoubleModifier

type conversion_t =
  | IntConverter
  | DecimalConverter
  | UnsignedOctalConverter
  | UnsignedDecimalConverter
  | UnsignedHexConverter of bool                  (* true is caps *)
  | FixedDoubleConverter of bool                  (* true is caps *)
  | ExpDoubleConverter of bool                    (* true is caps *)
  | FlexDoubleConverter of bool                   (* true is caps *)
  | HexDoubleConverter of bool                    (* true is caps *)
  | UnsignedCharConverter
  | StringConverter
  | PointerConverter
  | OutputArgument


let lengthmodifier_table = H.create 23

let invlengthmodifier_table = H.create 23

let _ =
  List.iter (fun (m,lm) ->
      begin
        H.add lengthmodifier_table m lm;
        H.add invlengthmodifier_table lm m
      end)
    [ ("hh", CharModifier);
      ("h" , ShortModifier);
      ("l" , LongModifier);
      ("ll", LongLongModifier);
      ("j" , IntMaxModifier);
      ("z" , SizeModifier);
      ("t" , PtrDiffModifier);
      ("L" , LongDoubleModifier)]


let conversion_table = H.create 23

let invconversion_table = H.create 23

let _ =
  List.iter (fun (ch, cv) ->
      begin
        H.add conversion_table ch cv;
        H.add invconversion_table cv ch
      end)
    [ (c_d, DecimalConverter);
      (c_i, IntConverter);
      (c_o, UnsignedOctalConverter);
      (c_u, UnsignedDecimalConverter);
      (c_x, UnsignedHexConverter false);
      (c_X, UnsignedHexConverter true);
      (c_f, FixedDoubleConverter false);
      (c_F, FixedDoubleConverter true);
      (c_e, ExpDoubleConverter false);
      (c_E, ExpDoubleConverter true);
      (c_g, FlexDoubleConverter false);
      (c_G, FlexDoubleConverter true);
      (c_a, HexDoubleConverter false);
      (c_A, HexDoubleConverter true);
      (c_c, UnsignedCharConverter);
      (c_s, StringConverter);
      (c_p, PointerConverter);
      (c_n, OutputArgument)]


class type argspec_int =
  object
    method add_flag: int -> unit
    method set_fieldwidth_arg: unit
    method set_precision_arg: unit
    method set_fieldwidth: int -> unit
    method set_precision: int -> unit
    method set_lengthmodifier: string -> unit
    method set_conversion: int -> unit
    method set_scanset: unit

    method get_flags: int list
    method get_fieldwidth: fieldwidth_t
    method get_precision: precision_t
    method get_conversion: conversion_t
    method get_lengthmodifier: lengthmodifier_t

    method has_fieldwidth: bool
    method has_precision : bool
    method has_lengthmodifier: bool
    method is_well_defined: bool
    method is_scanset: bool

    method toPretty: pretty_t
  end


class type formatstring_spec_int =
  object
    method start_argspec: unit
    method add_flag: int -> unit
    method set_fieldwidth_arg: unit
    method set_precision_arg: unit
    method set_precision: int -> unit
    method set_fieldwidth: int -> unit
    method set_lengthmodifier: string -> unit
    method set_conversion: int -> unit
    method set_literal_length: int -> unit
    method set_scanset: unit

    method get_arguments: argspec_int list
    method get_literal_length: int

    method has_arguments: bool
    method is_well_defined: bool

    method toPretty: pretty_t
  end


class type formatstring_parser_int =
  object
    method get_result: formatstring_spec_int
    method get_literal_length: int
    method parse: unit
  end


class argspec_t:argspec_int =
object (self)

  val mutable flags = []
  val mutable fieldwidth = NoFieldwidth
  val mutable precision  = NoPrecision
  val mutable cconversion = c_i
  val mutable conversion = IntConverter
  val mutable slengthmodifier = ""
  val mutable lengthmodifier = NoModifier
  val mutable isscanset = false

  method add_flag f =
    flags <- f :: flags

  method set_fieldwidth_arg =
    fieldwidth <- FieldwidthArgument

  method set_precision_arg =
    precision <- PrecisionArgument

  method set_fieldwidth w =
    fieldwidth <- FieldwidthConstant w

  method set_precision p =
    precision <- PrecisionConstant p

  method set_scanset = isscanset <- true

  method set_lengthmodifier m =
    if H.mem lengthmodifier_table m then
      begin
        lengthmodifier <- H.find lengthmodifier_table m;
        slengthmodifier <- m
      end
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "String ";
                STR m;
                STR " is not a valid length modifier"]))

  method set_conversion c =
    if H.mem conversion_table c then
      begin
        conversion <- H.find conversion_table c;
        cconversion <- c
      end
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "Character "; INT c;
                STR " is not a valid conversion specifier"]))

  method get_flags = List.rev flags

  method get_fieldwidth =
    if self#has_fieldwidth then
      fieldwidth
    else
      raise
        (CHFailure
           (LBLOCK [STR "Format argument spec does not have a field width"]))

  method get_precision =
    if self#has_precision then
      precision
    else
      raise
        (CHFailure
           (LBLOCK [STR "Format argument spec does not have a precision"]))

  method get_lengthmodifier =
    if self#has_lengthmodifier then
      lengthmodifier
    else
      raise
        (CHFailure
           (LBLOCK [STR "Argument spec does not have a length modifier"]))

  method get_conversion = conversion

  method has_fieldwidth =
    match fieldwidth with NoFieldwidth -> false | _ -> true

  method has_precision =
    match precision with NoPrecision -> false | _ -> true

  method has_lengthmodifier =
    match lengthmodifier with NoModifier -> false | _ -> true

  method is_scanset = isscanset

  method private has_flag c = List.mem c flags

  method is_well_defined =
    let has_simple_lengthmodifier =
        if self#has_lengthmodifier then
            match self#get_lengthmodifier with
            | CharModifier
            | ShortModifier
            | LongLongModifier
            | IntMaxModifier
            | SizeModifier
            | PtrDiffModifier -> true
            | _ -> false
        else false in
    let has_longdouble_lengthmodifier =
      self#has_lengthmodifier && self#get_lengthmodifier = LongDoubleModifier in
    match self#get_conversion with
    | IntConverter ->
       not (self#has_flag c_hash || has_longdouble_lengthmodifier)
    | DecimalConverter ->
       not (self#has_flag c_hash || has_longdouble_lengthmodifier)
    | UnsignedOctalConverter ->
       not has_longdouble_lengthmodifier
    | UnsignedDecimalConverter ->
       not (self#has_flag c_hash || has_longdouble_lengthmodifier)
    | UnsignedHexConverter _ ->
       not has_longdouble_lengthmodifier
    | FixedDoubleConverter _ ->
       not has_simple_lengthmodifier
    | ExpDoubleConverter _ ->
       not has_simple_lengthmodifier
    | FlexDoubleConverter _ ->
       not has_simple_lengthmodifier
    | HexDoubleConverter _ ->
       not has_simple_lengthmodifier
    | UnsignedCharConverter ->
       not (self#has_flag c_hash
            || self#has_flag c_zero
            || self#has_precision
            || has_longdouble_lengthmodifier
            || has_simple_lengthmodifier)
    | StringConverter ->
       not (self#has_flag c_hash
            || self#has_flag c_zero
            || self#has_precision
            || has_longdouble_lengthmodifier
            || has_simple_lengthmodifier)
    | PointerConverter ->
       not (self#has_flag c_hash
            || self#has_flag c_zero
            || self#has_precision
            || self#has_lengthmodifier)
    | OutputArgument ->
       let cur_flags = self#get_flags in
       not (List.length cur_flags <> 0
            || self#has_precision
            || self#has_fieldwidth
            || has_longdouble_lengthmodifier)


  method toPretty =
    let pflags =
      match self#get_flags with
      | [] -> STR ""
      | l ->
         LBLOCK [
             STR "flags: ";
             pretty_print_list
               l
               (fun f -> STR (Char.escaped (Char.chr f)))
               "'" " " "'"; NL] in
    let pfieldwidth = match fieldwidth with
      | FieldwidthConstant 0 | NoFieldwidth -> STR ""
      | FieldwidthArgument -> LBLOCK [STR "fieldwidth: argument"; NL]
      | FieldwidthConstant n -> LBLOCK [STR "fieldwidth: "; INT n; NL] in
    let pprecision = match precision with
      | PrecisionConstant 1 | NoPrecision -> STR ""
      | PrecisionArgument -> LBLOCK [STR "precision: argument"; NL]
      | PrecisionConstant n -> LBLOCK [STR "precision: "; INT n; NL] in
    let plengthmodifier = match lengthmodifier with
      | NoModifier -> STR ""
      | _ -> LBLOCK [STR "length modifier: "; STR slengthmodifier; NL] in
    let pconversion =
      LBLOCK [
          STR "conversion: ";
          STR (Char.escaped (Char.chr cconversion));
          NL] in
    LBLOCK [pconversion; plengthmodifier; pflags; pfieldwidth; pprecision]

end


class formatstring_spec_t:formatstring_spec_int =
object (self)

  val mutable argspecs = []
  val mutable literallength = 0
  val mutable currentspec = None

  method get_arguments =
    List.rev argspecs

  method get_literal_length =
    literallength

  method has_arguments =
    match argspecs with [] -> false | _ -> true

  method is_well_defined =
    List.fold_left (fun result a ->
        result && a#is_well_defined) true self#get_arguments

  method start_argspec =
    currentspec <- Some (new argspec_t)

  method set_literal_length n =
    literallength <- n

  method private stop msg =
    raise
      (CHFailure
         (LBLOCK [STR "No current spec active when adding "; STR msg]))

  method add_flag f =
    match currentspec with
    | Some s -> s#add_flag f
    | _ -> self#stop "flag"

  method set_precision p =
    match currentspec with
    | Some s -> s#set_precision p
    | _ -> self#stop "precision"

  method set_fieldwidth w =
    match currentspec with
    | Some s -> s#set_fieldwidth w
    | _ -> self#stop "field width"

  method set_precision_arg =
    begin
      (match currentspec with
       | Some s -> s#set_precision_arg
       | _ -> self#stop "precision argument");
      argspecs <- (new argspec_t) :: argspecs;
    end

  method set_fieldwidth_arg =
    begin
      (match currentspec  with
       | Some s -> s#set_fieldwidth_arg
       | _ -> self#stop "field width argument");
      argspecs <- (new argspec_t) :: argspecs;
    end

  method set_lengthmodifier m =
    match currentspec with
    | Some s -> s#set_lengthmodifier m
    | _ -> self#stop "length modifier"

  method set_conversion c =
    match currentspec with
    | Some s ->
       begin
         s#set_conversion c;
         argspecs <- s :: argspecs;
         currentspec <- None
       end
    | _ -> self#stop "conversion"

  method set_scanset =
    match currentspec with
    | Some s ->
       begin
         s#set_scanset;
         argspecs <- s :: argspecs;
         currentspec <- None
       end
    | _ -> self#stop "scanset"

  method toPretty =
    LBLOCK
      (List.mapi (fun i a ->
           LBLOCK [
               STR "Argument ";
               INT i;
               NL;
               INDENT (3,a#toPretty);
               NL]) self#get_arguments)

end


class virtual formatstring_parser_t (s:string) =
object (self)

  val len = String.length s
  val mutable literallen = 0
  val mutable ch = IO.input_string s
  val mutable pos = 0
  val mutable char_la = 0
  val result = new formatstring_spec_t

  method get_result = result

  method get_literal_length = literallen

  method private read =
    begin pos <- pos + 1; Char.code (IO.read ch) end

  method private next_char =
    if pos = len then
      raise
        (CHFailure
           (LBLOCK [
                STR "End of string encountered. Current format: ";
                result#toPretty]))
    else
      char_la <- self#read

  method private read_char expected_char =
    if char_la = expected_char then
      self#next_char
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "Expected to see ";
                INT expected_char;
                STR ", but found ";
                INT char_la]))

  method private check_char_la predicate msg =
    if predicate char_la then () else raise (CHFailure msg)

  method virtual parse: unit

  method private read_fieldwidth =
    if is_star char_la then
      begin
        result#set_fieldwidth_arg;
        self#read_char c_asterisk
      end
    else
      result#set_fieldwidth self#read_number

  method private read_precision =
    begin
      self#read_char c_period;
      if is_star char_la then
        begin
          result#set_precision_arg;
          self#read_char c_asterisk
        end
      else
        result#set_precision self#read_number
    end

  method private read_lengthmodifier =
    if char_la = c_h then
      begin
        self#read_char c_h;
        if char_la = c_h then
          begin
            result#set_lengthmodifier "hh";
            self#read_char c_h
          end
        else
          result#set_lengthmodifier "h"
      end
    else if char_la = c_l then
      begin
        self#read_char c_l;
        if char_la = c_l then
          begin
            result#set_lengthmodifier "ll";
            self#read_char c_l
          end
        else
          result#set_lengthmodifier "l"
      end
    else if char_la = c_j then
      begin
        result#set_lengthmodifier "j";
        self#read_char c_j
      end
    else if char_la = c_z then
      begin
        result#set_lengthmodifier "z";
        self#read_char c_z
      end
    else if char_la = c_t then
      begin
        result#set_lengthmodifier "t";
        self#read_char c_t
      end
    else if char_la = c_L then
      begin
        result#set_lengthmodifier "L";
        self#read_char c_L
      end
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "Expected to see length modifier but encountered ";
                STR (Char.escaped (Char.chr char_la))]))

  method private read_number =
    let numval = ref 0 in
    let _ =
      while (is_number char_la) do
        begin
          numval := (10 * !numval) + (char_la - 0x0030);
          self#next_char
        end
      done in
    !numval

  method private read_conversion =
    begin
      result#set_conversion char_la;
    end

end


class output_formatstring_parser_t (s:string):formatstring_parser_int =
object (self)

  inherit formatstring_parser_t s

  method parse =
    try
      while (pos < len) do
        begin
          self#next_char;
          while (not (is_percent_sign char_la)) && (pos < len) do
            begin
              literallen <- literallen + 1;
              self#next_char
            end
          done;
          if pos < len then
            begin
              self#read_char c_percent;
              if (is_percent_sign char_la) then
                let _ = (if pos = len then () else self#read_char c_percent) in
                literallen <- literallen + 1
              else
                begin
                  result#start_argspec;
                  (while (is_flag char_la && pos < len) do
                     begin
                       result#add_flag char_la;
                       self#next_char
                     end
                   done);
                  (if (is_fieldwidth_start char_la) then
                     self#read_fieldwidth);
                  (if (is_period char_la) then self#read_precision);
                  (if (is_lengthmodifier_start char_la) then
                    self#read_lengthmodifier);
                  self#read_conversion
                end
            end
        end
      done
    with
    | CHFailure p ->
       let unparsed = String.sub s (pos-1) (((String.length s) - pos) + 1) in
       raise
         (CHFailure
            (LBLOCK [
                 STR "Format string parse error: "; p; NL;
                 STR "Format string: "; STR s; NL;
                 STR "Error at position: "; INT pos; NL;
                 STR "Remaining string: "; STR unparsed; NL]))


end


class input_formatstring_parser_t (s:string):formatstring_parser_int =
object (self)

  inherit formatstring_parser_t s

  method private read_scanset =
    begin
      self#read_char c_lbracket;
      (if is_right_bracket char_la then self#read_char c_rbracket);
      (if is_caret char_la then
         begin
           self#read_char c_caret;
           (if is_right_bracket char_la then self#read_char c_rbracket)
         end);
      (while (not (is_right_bracket char_la)) && (pos < len) do
        self#next_char
      done);
      self#read_char c_rbracket;
      result#set_scanset
    end

  method parse =
    try
      while (pos < len) do
        begin
          self#next_char;
          (while (not (is_percent_sign char_la)) && (pos < len) do
            self#next_char
          done);
          if pos < len then
            begin
              self#read_char c_percent;
              if (is_percent_sign char_la) then
                (if pos = len then () else self#read_char c_percent)
              else
                begin
                  result#start_argspec;
                  (if (is_fieldwidth_start char_la) then
                     self#read_fieldwidth);
                  (if (is_lengthmodifier_start char_la) then
                     self#read_lengthmodifier);
                  (if (is_left_bracket char_la) then
                    self#read_scanset);
                  self#read_conversion
                end
            end
        end
      done
    with
    | CHFailure p ->
       let unparsed = String.sub s (pos-1) (((String.length s) - pos) + 1) in
       raise
         (CHFailure
            (LBLOCK [
                 STR "Format string parse error: "; p; NL;
                 STR "Format string: "; STR s; NL;
                 STR "Error at position: "; INT pos; NL;
                 STR "Remaining string: "; STR unparsed; NL]))

end


let get_output_formatstring_parser = new output_formatstring_parser_t

let get_input_formatstring_parser = new input_formatstring_parser_t

let parse_formatstring (s:string) (isinput:bool) =
  let parser =
    if isinput then
      get_input_formatstring_parser s
    else
      get_output_formatstring_parser s in
  let _ = parser#parse in
  let result = parser#get_result in
  let _ = result#set_literal_length parser#get_literal_length in
  result
