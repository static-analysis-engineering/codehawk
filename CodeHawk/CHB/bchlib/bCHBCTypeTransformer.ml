(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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

(* bchlib *)
open BCHBCTypes


let rec modify_type (f: type_transformer_t) (t: btype_t) =
  let rec tf tname =
    match tname with
    | SimpleName name -> SimpleName (f name)
    | TemplatedName (base,args) ->
      TemplatedName (tf base,List.map (fun a -> modify_type f a) args) in
  match t with
  | TPtr (tt,attrs) -> TPtr (modify_type f tt,attrs)
  | TRef (tt,attrs) -> TRef (modify_type f tt,attrs)
  | TArray (tt,e,attrs) -> TArray (modify_type f tt, e, attrs)
  | TFun (tt,optArgs,b,attrs) ->
    TFun (modify_type f tt, modify_type_optargs f optArgs, b, attrs)
  | TNamed (s,attrs) -> TNamed (f s,attrs)
  | TComp (ckey, attrs) -> TComp (ckey, attrs)
  | TCppComp (tname, ns, attrs) ->
     TCppComp (tf tname, List.map tf ns, attrs)
  | _ -> t


and modify_type_optargs (f: type_transformer_t) (args: bfunarg_t list option) =
  match args with
  | Some l -> Some (List.map (fun (s, t, a) -> (s, modify_type f t, a)) l)
  | _ -> None


let t_add_attr (t:btype_t) (a:string) =
  let add l = (Attr (a, [])) :: l in
  match t with
  | TVoid attrs -> TVoid (add attrs)
  | TInt (ik, attrs) -> TInt (ik, add attrs)
  | TFloat (fk, rep, attrs) -> TFloat (fk, rep, add attrs)
  | TPtr (tt, attrs) -> TPtr (tt, add attrs)
  | TRef (tt, attrs) -> TRef (tt, add attrs)
  | THandle (s, attrs) -> THandle (s, add attrs)
  | TArray (tt, e, attrs) -> TArray (tt, e, add attrs)
  | TFun (tt, args, v, attrs) -> TFun (tt, args, v, add attrs)
  | TNamed (s, attrs) -> TNamed (s, add attrs)
  | TComp (ckey, attrs) -> TComp (ckey, add attrs)
  | TCppComp (tn, tns, attrs) -> TCppComp (tn, tns, add attrs)
  | TEnum (ename, attrs) -> TEnum (ename, add attrs)
  | TCppEnum (tn, tns, attrs) -> TCppEnum (tn, tns, add attrs)
  | TVarArg attrs -> TVarArg (add attrs)
  | TBuiltin_va_list attrs -> TBuiltin_va_list (add attrs)
  | TClass (s, ns, attrs) -> TClass (s, ns, add attrs)
  | TUnknown attrs -> TUnknown (add attrs)

           
let add_attributes (t: btype_t) (a: b_attributes_t) =
  match t with
  | TVoid aa -> TVoid (aa @ a)
  | TInt (ik, aa) -> TInt (ik, aa @ a)
  | TFloat (fk, fr, aa) -> TFloat (fk, fr, aa @ a)
  | TPtr (tt, aa) -> TPtr (tt, aa @ a)
  | TRef (tt, aa) -> TRef (tt, aa @ a)
  | THandle (s, aa) -> THandle (s, aa @ a)
  | TArray (tt, e, aa) -> TArray (tt, e, aa @ a)
  | TFun (tt, l, b, aa) -> TFun (tt, l, b, aa @ a)
  | TNamed (s, aa) -> TNamed (s, aa @ a)
  | TComp (k, aa) -> TComp (k, aa @ a)
  | TEnum (s, aa) -> TEnum (s, aa @ a)
  | TCppComp (s, sl, aa) -> TCppComp (s, sl, aa @ a)
  | TCppEnum (s, sl, aa) -> TCppEnum (s, sl, aa @ a)
  | TClass (s, sl, aa) -> TClass (s, sl, aa @ a)
  | TBuiltin_va_list aa -> TBuiltin_va_list (aa @ a)
  | TVarArg aa -> TVarArg (aa @ a)
  | TUnknown aa -> TUnknown (aa @ a)
