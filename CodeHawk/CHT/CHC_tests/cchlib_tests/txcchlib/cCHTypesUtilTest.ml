(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2026      Aarno Labs LLC

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


(* Tests for CCHTypesUtil: machine model selection from the word size, integer
   constants, and offset operations.

   Machine model: selection of the target machine model from the word size.

   Type ranges are used both as facts and as safety bounds, so they must come
   from the machine model the source was parsed for; there is no default.
   system_settings is global and the word size cannot be unset, so the test
   for the missing word size must run first. *)

(* cchlib *)
open CCHBasicTypes
open CCHMachineSizes
open CCHSettings
open CCHTypesUtil

module A = TCHAssertion
module TS = TCHTestSuite


let testname = "cCHTypesUtilTest"
let lastupdated = "2026-11-15"


let ub (k: ikind) = (get_safe_upperbound k)#toString
let lb (k: ikind) = (get_safe_lowerbound k)#toString
let width (k: ikind) = string_of_int (get_safe_bit_width k)

let p2 (n: int) = CHNumerical.mkNumericalPowerOf2 n

(* expected values written out, independent of the implementation *)
let umax (n: int) =
  match n with
  | 32 -> "4294967295"
  | 64 -> "18446744073709551615"
  | _ -> A.fail_msg ("umax " ^ string_of_int n)

let smin (n: int) =
  match n with
  | 32 -> "-2147483648"
  | 64 -> "-9223372036854775808"
  | _ -> A.fail_msg ("smin " ^ string_of_int n)


let test_machine_model () =
  begin
    TS.new_testsuite testname lastupdated;

    TS.add_simple_test
      ~title:"no-wordsize-raises"
      (fun () -> A.raises (fun () -> get_safe_upperbound IULong));

    TS.add_simple_test
      ~title:"invalid-wordsize-rejected"
      (fun () -> A.raises (fun () -> system_settings#set_wordsize 8));

    TS.add_simple_test
      ~title:"no-model-for-24"
      (fun () ->
        A.equal_string
          "none"
          (match machine_sizes_of_wordsize 24 with
           | Some _ -> "some" | None -> "none"));

    TS.add_simple_test
      ~title:"ilp32-ranges"
      (fun () ->
        begin
          system_settings#set_wordsize 32;
          A.equal_string ~msg:"ulong ub" (umax 32) (ub IULong);
          A.equal_string ~msg:"long lb" (smin 32) (lb ILong);
          A.equal_string ~msg:"ulonglong ub" (umax 64) (ub IULongLong);
          A.equal_string ~msg:"uint ub" (umax 32) (ub IUInt);
          A.equal_string ~msg:"long width" "32" (width ILong)
        end);

    TS.add_simple_test
      ~title:"lp64-ranges"
      (fun () ->
        begin
          system_settings#set_wordsize 64;
          A.equal_string ~msg:"ulong ub" (umax 64) (ub IULong);
          A.equal_string ~msg:"long lb" (smin 64) (lb ILong);
          A.equal_string ~msg:"ulonglong ub" (umax 64) (ub IULongLong);
          A.equal_string ~msg:"uint ub" (umax 32) (ub IUInt);
          A.equal_string ~msg:"long width" "64" (width ILong);
          (* 2^32 fits unsigned long on LP64, not unsigned int *)
          A.equal_string ~msg:"2^32 fits ulong" "true"
            (string_of_bool (int_fits_kind (p2 32) IULong));
          A.equal_string ~msg:"2^32 fits uint" "false"
            (string_of_bool (int_fits_kind (p2 32) IUInt))
        end);

    TS.launch_tests ()
  end


(* Integer constants: CInt (int64, ikind); unsigned values >= 2^63 are stored
   in two's-complement form (issue 23). *)
let test_integer_constants () =
  let num (s: string) = CHNumerical.mkNumericalFromString s in
  let read (i64: int64) (ik: ikind) =
    (CHNumerical.mkNumerical_big (CCHBasicUtil.cint_to_big i64 ik))#toString in
  let roundtrip (s: string) =
    match make_constant (num s) with
    | CInt (i64, ik, _) -> read i64 ik
    | _ -> "not an integer constant" in
  begin
    TS.new_testsuite (testname ^ "-constants") lastupdated;

    TS.add_simple_test
      ~title:"read-unsigned-wrapped"
      (fun () ->
        begin
          A.equal_string ~msg:"-1 as ulong" (umax 64) (read Int64.minus_one IULong);
          A.equal_string ~msg:"min_int as ulonglong" "9223372036854775808"
            (read Int64.min_int IULongLong);
          A.equal_string ~msg:"-1 as long" "-1" (read Int64.minus_one ILong);
          A.equal_string ~msg:"-1 as int" "-1" (read Int64.minus_one IInt)
        end);

    TS.add_simple_test
      ~title:"make-constant-roundtrip"
      (fun () ->
        begin
          A.equal_string ~msg:"0" "0" (roundtrip "0");
          A.equal_string ~msg:"int64 min" (smin 64) (roundtrip (smin 64));
          A.equal_string ~msg:"int64 max" "9223372036854775807"
            (roundtrip "9223372036854775807");
          A.equal_string ~msg:"2^63" "9223372036854775808"
            (roundtrip "9223372036854775808");
          A.equal_string ~msg:"2^64-1" (umax 64) (roundtrip (umax 64))
        end);

    TS.add_simple_test
      ~title:"make-constant-out-of-range"
      (fun () ->
        begin
          A.raises (fun () -> make_constant (num "18446744073709551616"));
          A.raises (fun () -> make_constant (num "-9223372036854775809"))
        end);

    TS.launch_tests ()
  end


(* Offsets in memory variables and pointer arithmetic: a
   trailing NoOffset counts as index 0; pointer arithmetic shifts the last
   integer index; the region reachable from a pointer to an array element is
   the enclosing array; overlap is decided conservatively. *)
let test_offsets () =
  let n (i: int) = CHNumerical.mkNumerical i in
  let idx (i: int) (o: offset) =
    match mk_constant_index_offset (n i) with
    | Index (e, _) -> Index (e, o)
    | _ -> A.fail_msg "mk_constant_index_offset" in
  let fld (f: string) (o: offset) = Field ((f, 1), o) in
  let varidx (o: offset) = Index (Lval (Var ("i", 7), NoOffset), o) in
  let sizeofidx (o: offset) = Index (SizeOf (TInt (IChar, [])), o) in
  let chridx (o: offset) = Index (Const (CChr 'a'), o) in
  (* printer independent of the implementation *)
  let rec pr (o: offset) =
    match o with
    | NoOffset -> ""
    | Field ((f, _), r) -> "." ^ f ^ pr r
    | Index (Const (CInt (i64, _, _)), r) -> "[" ^ Int64.to_string i64 ^ "]" ^ pr r
    | Index (_, r) -> "[?]" ^ pr r in
  let shift (o: offset) (k: int) =
    match shift_last_index o (n k) with
    | Some o' -> pr o'
    | None -> "none" in
  let region (o: offset) = pr (reachable_region_offset o) in
  let overlap (o1: offset) (o2: offset) = string_of_bool (offsets_overlap o1 o2) in
  begin
    TS.new_testsuite (testname ^ "-offsets") lastupdated;

    TS.add_simple_test
      ~title:"shift-last-index"
      (fun () ->
        begin
          (* *(p + 1) with p = &a[0] is a[1], not a[0][1] *)
          A.equal_string ~msg:"[0] + 1" "[1]" (shift (idx 0 NoOffset) 1);
          A.equal_string ~msg:"[2] - 2" "[0]" (shift (idx 2 NoOffset) (-2));
          (* trailing NoOffset is index 0 *)
          A.equal_string ~msg:"NoOffset + 3" "[3]" (shift NoOffset 3);
          A.equal_string ~msg:"NoOffset + 0" "" (shift NoOffset 0);
          (* the innermost array is shifted *)
          A.equal_string ~msg:".f[2] + 1" ".f[3]" (shift (fld "f" (idx 2 NoOffset)) 1);
          A.equal_string ~msg:"[1].f[0] + 4" "[1].f[4]"
            (shift (idx 1 (fld "f" (idx 0 NoOffset))) 4);
          (* pointer to a field: trailing NoOffset counts as index 0 *)
          A.equal_string ~msg:".f + 1" ".f[1]" (shift (fld "f" NoOffset) 1);
          (* non-integer last index: unknown *)
          A.equal_string ~msg:"[i] + 1" "none" (shift (varidx NoOffset) 1);
          A.equal_string ~msg:"[sizeof] + 1" "none" (shift (sizeofidx NoOffset) 1);
          A.equal_string ~msg:".f[i] + 1" "none" (shift (fld "f" (varidx NoOffset)) 1)
        end);

    TS.add_simple_test
      ~title:"reachable-region"
      (fun () ->
        begin
          (* &a[1]: the whole array a (ptr[-1] is legal) *)
          A.equal_string ~msg:"[1]" "" (region (idx 1 NoOffset));
          (* &s.f[2]: the array s.f, not s.g *)
          A.equal_string ~msg:".f[2]" ".f" (region (fld "f" (idx 2 NoOffset)));
          (* &s.f: the field itself *)
          A.equal_string ~msg:".f" ".f" (region (fld "f" NoOffset));
          (* &a[1].f[2]: the array a[1].f *)
          A.equal_string ~msg:"[1].f[2]" "[1].f" (region (idx 1 (fld "f" (idx 2 NoOffset))));
          A.equal_string ~msg:"NoOffset" "" (region NoOffset)
        end);

    TS.add_simple_test
      ~title:"offsets-overlap"
      (fun () ->
        begin
          A.equal_string ~msg:"whole object" "true" (overlap NoOffset (fld "f" NoOffset));
          A.equal_string ~msg:"prefix" "true" (overlap (fld "f" NoOffset) (fld "f" (idx 3 NoOffset)));
          A.equal_string ~msg:"sibling fields" "false" (overlap (fld "f" NoOffset) (fld "g" NoOffset));
          A.equal_string ~msg:"distinct indices" "false" (overlap (idx 1 NoOffset) (idx 2 NoOffset));
          A.equal_string ~msg:"same index" "true" (overlap (idx 2 NoOffset) (idx 2 NoOffset));
          A.equal_string ~msg:"variable index" "true" (overlap (varidx NoOffset) (idx 2 NoOffset));
          (* only integer constants are compared by value: sizeof(char) and
             'a' may equal another index, so they must overlap *)
          A.equal_string ~msg:"sizeof index" "true" (overlap (sizeofidx NoOffset) (idx 1 NoOffset));
          A.equal_string ~msg:"char index" "true" (overlap (chridx NoOffset) (idx 97 NoOffset));
          (* different shapes: conservatively overlapping *)
          A.equal_string ~msg:"index vs field" "true" (overlap (idx 0 NoOffset) (fld "f" NoOffset));
          A.equal_string ~msg:"nested distinct" "false"
            (overlap (fld "f" (idx 1 NoOffset)) (fld "f" (idx 2 NoOffset)));
          A.equal_string ~msg:"nested same field different subfield" "false"
            (overlap (fld "f" (fld "a" NoOffset)) (fld "f" (fld "b" NoOffset)))
        end);

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    test_machine_model ();
    test_integer_constants ();
    test_offsets ();
    TS.exit_file ()
  end
