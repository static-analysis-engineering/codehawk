(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* cchlib *)
open CCHUtilities

(* cchpre *)
open CCHPreTypes

module H = Hashtbl

let crefs = H.create 15

let _ =
  List.iter
    (fun (section,item,p) -> H.add crefs (section,item) p)
    [("6.5.2.1. Array subscripting","2",
       LBLOCK [
           STR "A postfix expression followed by an expression in ";
           STR "square brackets [] is a"; NL;
           STR "subscripted designation of an element of an array object. ";
           STR "The definition "; NL;
           STR "of the subscript operator [] is that E1[E2] is identical to ";
           STR "(*((E1)+(E2))). "; NL;
           STR "Because of the conversion rules that apply to the binary + ";
           STR "operator, if E1 is"; NL;
           STR "an array object (equivalently, a pointer to the initial ";
           STR "element of an array"; NL;
           STR "object) and E2 is an integer, E1[E2] designates the E2-th ";
           STR "element of E1"; NL;
           STR "(counting from zero)."]);
      ("6.5.6. Additive operators","8",
       LBLOCK [
           STR "When an expression that has integer type is added to or ";
           STR "subtracted from a pointer,"; NL;
           STR "the result has the type of the pointer operand. If the ";
           STR "pointer operand points to"; NL;
           STR "an element of an array object, and the array is large enough, ";
           STR "the result points to"; NL;
           STR "an element offset from the original element such that the ";
           STR "difference of the subscripts"; NL;
           STR "of the resulting and original array elements equals the ";
           STR "integer expression. In other"; NL;
           STR "words, if the expression P points to the i-th element of an ";
           STR "array object, the"; NL;
           STR "expressions (P)+N (equivalently, N+(P)) and (P)-N (where N ";
           STR "has the value n) point to,"; NL;
           STR "respectively, the i+n-th and i?n-th elements of the array ";
           STR "object, provided they exist."; NL;
           STR "Moreover, if the expression P points to the last element of ";
           STR "an array object, the "; NL;
           STR "expression (P)+1 points one past the last element of the ";
           STR "array object, and if the "; NL;
           STR "expression Q points one past the last element of an array ";
           STR "object, the expression (Q)-1"; NL;
           STR "points to the last element of the array object. If both the ";
           STR "pointer operand and the"; NL;
           STR "result point to elements of the same array object, or one ";
           STR "past the last element of the"; NL;
           STR "array object, the evaluation shall not produce an overflow; ";
           STR "otherwise, the behavior is"; NL;
           STR "undefined. If the result points one past the last element of ";
           STR "the array object, it shall"; NL;
           STR "not be used as the operand of a unary * operator that is ";
           STR "evaluated."])
   ]

let po_explanations = H.create 15


let _ =
  List.iter
    (fun x -> H.add po_explanations x.pox_tag x)
    [{
        pox_tag = "index-lower-bound";
        pox_desc = "value i is used to index an array; its value must be non-negative";
        pox_arguments = [(1,"i","exp","value used as an array index")];
        pox_cstandard_refs = [
            { por_section = "6.5.2.1. Array subscripting";
              por_item = "2" };
            { por_section = "6.5.6. Additive operators";
              por_item = "8" }
         ];
        pox_notes = [];
        pox_severity = UndefinedBehavior
      };
      {
        pox_tag = "index-upper-bound";
        pox_desc =
          "value i is used to index an array with size n; its value "
          ^ "must be less than n";
        pox_arguments = [
            (1,"i","exp","value used as an array index");
            (2,"n","exp","size of the array indexed")];
        pox_cstandard_refs = [
            { por_section = "6.5.2.1. Array subscripting";
              por_item = "2" };
            { por_section = "6.5.6. Additive operators";
              por_item = "8" }
         ];
        pox_notes = [];
        pox_severity = UndefinedBehavior
      };
      {
        pox_tag = "pointer-lower-bound";
        pox_desc =
          "Scalar value i is added to or subtracted from pointer p of type"
          ^ "\n(t *). As per the C standard definition the value of p plus/minus"
          ^ "\nthe value of i times the size of t shall not point more than"
          ^ "\none past the last element of the array object. In this case"
          ^ "\nthe size of the array object must be obtained separately, as"
          ^ "\nthe pointer p does not have a declared size. Violation leads"
          ^ "\nto undefined behavior.";
        pox_arguments = [
            (1,"t","type","type of the pointer target");
            (2,"op","+/-","operation performed (addition or subtraction)");
            (3,"p","exp","pointer expression");
            (4,"i","exp","scalar expression to be added/subtracted")];
        pox_cstandard_refs = [
            { por_section = "6.5.6. Additive operators";
              por_item = "8" }
          ];
        pox_notes = [];
        pox_severity = UndefinedBehavior
      }
    ]


let prototype_to_pretty (x:po_explanation_t) =
  LBLOCK [
      STR x.pox_tag;
      pretty_print_list
        x.pox_arguments
        (fun (_,name,vtype,_) ->
          LBLOCK [STR name; STR ":";  STR vtype]) "(" "," ")"]


let get_cref_section (section:string) (item:string) =
  if H.mem crefs (section,item) then
    H.find crefs (section,item)
  else
    raise
      (CCHFailure
         (LBLOCK [
              STR "No cref section found for ";
              STR section;
              STR " and item ";
              STR item]))


let get_po_explanation (tag:string) =
  if H.mem po_explanations tag then
    H.find po_explanations tag
  else
    raise
      (CCHFailure (LBLOCK [STR "No explanation found for: "; STR tag]))


let has_po_explanation (tag:string) = H.mem po_explanations tag
