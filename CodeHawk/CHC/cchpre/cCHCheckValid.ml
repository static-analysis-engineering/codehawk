(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023-2025 Aarno Labs LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* xprlib *)
open XprToPretty

(* cchlib *)
open CCHBasicTypes
open CCHDictionary
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHPreFileIO
open CCHPreTypes
open CCHProofScaffolding

let pd = CCHPredicateDictionary.predicate_dictionary
let fenv = CCHFileEnvironment.file_environment

let p2s = pretty_to_string
let e2s e = pretty_to_string (exp_to_pretty e)
let stri = string_of_int

let int64_non_negative i = (Int64.compare Int64.zero i) <= 0

let int64_positive i = (Int64.compare Int64.zero i) < 0


let get_nibbles v n =
  let rec aux v pos nibbles =
    if pos = n then nibbles
    else aux (v lsr 4) (pos+1) ((v mod 16) :: nibbles) in
  aux v 0 []


let to_hex_string (num:numerical_t):string =
  try
    let nibbles = get_nibbles num#toInt 8 in
    match nibbles with
      [n8; n7; n6; n5; n4; n3; n2; n1] ->
      Printf.sprintf "0x%x%x%x%x%x%x%x%x" n8 n7 n6 n5 n4 n3 n2 n1
    | _ ->
       num#toString
  with
  | _ -> num#toString


let i64_to_hex_string (i64:int64) =
  to_hex_string (mkNumericalFromInt64 i64)


let rec is_zero e = match e with
  | Const (CInt (i64, _, _)) -> (Int64.compare i64 Int64.zero) = 0
  | CastE (_, e) -> is_zero e
  | _ -> false


let rec is_constant_string e = match e with
  | Const (CStr _) -> true
  | CastE (_,e) -> is_constant_string e
  | _ -> false


let rec is_constant_wide_string e = match e with
  | Const (CWStr _) -> true
  | CastE (_, e) -> is_constant_wide_string e
  | _ -> false


let rec get_num_value env e =
  match e with
  | CastE (_, x) -> get_num_value env x
  | Const (CInt (i64, _, _)) -> Some (mkNumericalFromInt64 i64)
  | Const (CChr c) -> Some (mkNumerical (Char.code c))
  | SizeOf (TArray (TInt (IChar, []),Some (Const (CInt (i64, _, _))), [])) ->
     Some (mkNumericalFromInt64 i64)
  | SizeOf t ->
     (match size_of_type env t with
      | XConst (IntConst n) -> Some n
      | x ->
         begin
           chlog#add
             "type size"
             (LBLOCK [typ_to_pretty t; STR ": "; xpr_formatter#pr_expr x]);
           None
         end)
  | SizeOfE e -> get_num_value env (SizeOf (type_of_exp env e))
  | BinOp (binop, e1, e2, _) ->
    begin
      match (binop, get_num_value env e1, get_num_value env e2) with
      | (PlusA, Some v1, Some v2) -> Some (v1#add v2)
      | (MinusA, Some v1, Some v2) -> Some (v1#sub v2)
      | (Mult, Some v1, Some v2) -> Some (v1#mult v2)
      | (Div, Some v1, Some v2) when not (v2#equal numerical_zero) ->
         Some (v1#div v2)
      | (Mod, Some _, Some _) -> None
      (* TODO: add some code for mod Some (v1 mod v2) *)
      | _ -> None
    end
  | _ -> None


let rec get_scalar_value ?(positive=false) env e =
  let i64_to_string i64 =
    let num = mkNumericalFromInt64 i64 in
    if num#gt  (mkNumerical 100) then
      to_hex_string num
    else
      num#toString in
  match e with

  | Const (CInt (i64,_,_)) when positive ->
     if int64_positive i64 then Some (i64_to_string i64) else None

  | Const (CInt (i64,_,_)) -> Some (i64_to_string i64)

  | CastE (_, x) -> get_scalar_value ~positive env x

  | BinOp (PlusA, e1, e2, _) ->
     begin
       match (get_scalar_value env e1, get_scalar_value env e2) with
       | (Some s1, Some s2) -> Some ("(" ^ s1 ^ " + " ^ s2 ^ ")")
       | _ -> None
     end

  | BinOp (Mult, e1, e2, _) ->
     begin
       match (get_scalar_value env e1, get_scalar_value env e2) with
       | (Some s1, Some s2) -> Some ("(" ^ s1 ^ " * " ^ s2 ^ ")")
       | _ -> None
     end

  | BinOp (BAnd, e1, e2, _) ->
     begin
       match (get_scalar_value env e1, get_scalar_value env e2) with
       | (Some s1, Some s2) -> Some ("(" ^ s1 ^ " & " ^ s2 ^ ")")
       | _ -> None
     end

  | UnOp (Neg, e1, _) ->
     begin
       match (get_scalar_value env e1) with
       | Some s -> Some ("(-" ^ s ^ ")")
       | _ -> None
     end

  | Lval (Mem (CastE (ty,Const (CInt (i64,_,_)))),NoOffset) ->
     Some ("*(("  ^ (p2s (typ_to_pretty ty)) ^ ") " ^ (i64_to_string i64) ^ ")")

  | Lval _ -> Some (e2s e)

  | _ -> None


let get_absolute_memory_address env e =
  match e with
  | CastE (ty, e) when
         is_pointer_type ty && is_integral_type (type_of_exp env e) ->
     get_scalar_value ~positive:true env e
  | _ -> None


let is_absolute_memory_address env e =
  match get_absolute_memory_address env e with
  | Some _ -> true | _ -> false


let rec get_num_range ?(apply_cast=true) env e =
  try
    match get_num_value env e with
    | Some v -> (Some v, Some v)
    | _ ->
       match e with

       | CastE (ty, x) when apply_cast ->
          begin
            match fenv#get_type_unrolled ty with
            | TInt (k,_) ->
               let ubk = get_safe_upperbound k in
               let lbk = get_safe_lowerbound k in
               let (optlbr,optubr) = get_num_range env x in
               let lb = match optlbr with
                 | Some lbr -> if lbr#gt lbk then Some lbr else Some lbk
                 | _ -> Some lbk in
               let ub = match optubr with
                 | Some ubr -> if ubr#lt ubk then Some ubr else Some ubk
                 | _ -> Some ubk in
               (lb,ub)
            | _ -> get_num_range env x
          end

       | CastE (_,x) -> get_num_range env x

       | Const (CInt (i64, _, _)) ->
          let v = mkNumericalFromInt64 i64 in
          (Some v, Some v)

       | Const (CChr c) ->
          let v = mkNumerical (Char.code c) in
          (Some v, Some v)

       | SizeOf (TArray
                   (TInt (IChar, []),
                    Some (Const (CInt (i64, _, _))), [])) ->
          (Some numerical_zero,Some (mkNumericalFromInt64 i64))

       | SizeOfE e -> get_num_range env (SizeOf (type_of_exp env e))

       | BinOp (binop, e1, e2, TInt (k, _)) ->
          let lbk = get_safe_lowerbound k in
          let ubk = get_safe_upperbound k in
          let (optlbr1, optubr1) = get_num_range env e1 in
          let (optlbr2, optubr2) = get_num_range env e2 in
          let get_lb optlbr =
            match optlbr with
            | Some lbr -> if lbr#gt lbk then Some lbr else Some lbk
            | _ -> Some lbk in
          let get_ub optubr =
            match optubr with
            | Some ubr -> if ubr#lt ubk then Some ubr else Some ubk
            | _ -> Some ubk in
          begin
            match binop with

            | PlusA ->
               let optlbr =
                 match (optlbr1,optlbr2) with
                 | (Some v1, Some v2) -> Some (v1#add v2)
                 | _ -> None in
               let optubr =
                 match (optubr1,optubr2) with
                 | (Some v1, Some v2) -> Some (v1#add v2)
                 | _ -> None in
               (get_lb optlbr, get_ub optubr)

            | MinusA ->
               let optlbr =
                 match (optlbr1, optubr2) with
                 | (Some v1, Some v2) -> Some (v1#sub v2)
                 | _ -> None in
               let optubr =
                 match (optubr1, optlbr2) with
                 | (Some v1, Some v2) -> Some (v1#sub v2)
                 |  _ -> None  in
               (get_lb optlbr, get_ub optubr)

            | Mult ->
               let optlbr =
                 match (optlbr1,optlbr2) with
                 | (Some v1, Some v2)
                      when v1#geq numerical_zero && v2#geq numerical_zero ->
                    Some (v1#mult v2)
                 | _ -> None in
               let optubr =
                 match (optlbr1, optlbr2, optubr1, optubr2) with
                 | (Some lb1, Some lb2, Some ub1, Some ub2)
                      when lb1#geq numerical_zero && lb2#geq numerical_zero  ->
                    Some (ub1#mult ub2)
                 | _ -> None in
               (get_lb optlbr, get_ub optubr)

            | Mod ->
               let optlbr =
                 match (optlbr1, optubr2) with
                 | (Some lb1, _) when lb1#geq numerical_zero ->
                    Some numerical_zero
                 | (Some _lb1, Some lb2) when lb2#gt numerical_zero ->
                    Some (lb2#neg#add numerical_one)
                 | (Some _lb1, Some lb2) when lb2#lt numerical_zero ->
                    Some (lb2#add numerical_one)
                 | _ -> None in
               let optubr =
                 match optubr2 with
                 | Some ub2 -> Some (ub2#sub numerical_one)
                 | _ -> None in
               (get_lb optlbr, get_ub optubr)
            | Div ->
               let optlbr =
                 match (optlbr1, optlbr2) with
                 | (Some lb1, Some lb2)
                      when lb1#geq numerical_zero && lb2#gt numerical_zero ->
                    Some numerical_zero
                 | (Some lb1, Some lb2)
                      when lb1#lt numerical_zero && lb2#gt numerical_zero ->
                    Some lb1
                 | _ -> None in
               let optubr =
                 match (optlbr1,optlbr2,optubr1) with
                 | (Some lb1, Some lb2, Some ub1)
                      when lb1#geq numerical_zero  && lb2#gt numerical_zero ->
                    Some ub1
                 | (Some lb1, Some ub2,_)
                      when lb1#geq numerical_zero && ub2#lt numerical_zero ->
                    Some numerical_zero
                 | (Some ub1, Some lb2,_)
                      when ub1#leq numerical_zero && lb2#gt numerical_zero ->
                    Some numerical_zero
                 | _ -> None in
               (get_lb optlbr, get_ub optubr)

            | Shiftrt ->
               let optlbr =
                 match optlbr1 with
                 | Some lb1 when lb1#geq numerical_zero -> Some numerical_zero
                 | _ -> None in
               let optubr =
                 match (optlbr1,optubr1) with
                 | (Some lb1, Some ub1) when lb1#geq numerical_zero -> Some ub1
                 | _ -> None in
               (get_lb optlbr, get_ub optubr)

            | Shiftlt ->
               let optlbr =
                 match optlbr1 with
                 | Some lb1 when lb1#geq numerical_zero -> Some numerical_zero
                 | _ -> None in
               (get_lb optlbr, get_ub None)

            | BAnd ->
               let optlbr =
                 match (optlbr1, optlbr2) with
                 | (Some lb1, _) when lb1#geq numerical_zero ->
                    Some numerical_zero
                 | (_, Some lb2) when lb2#geq numerical_zero ->
                    Some numerical_zero
                 | _ -> None in
               let optubr =
                 match (optlbr1, optlbr2, optubr1, optubr2) with
                 | (Some lb1, Some lb2, Some ub1, Some ub2)
                      when lb1#geq numerical_zero && lb2#geq numerical_zero ->
                    Some (if ub1#lt ub2 then ub1 else ub2)
                 | (Some lb1, _, Some ub1, _)
                      when lb1#geq numerical_zero -> Some ub1
                 | (_, Some lb2, _, Some ub2)
                      when lb2#geq numerical_zero -> Some ub2
                 | (_,_,Some ub1, Some ub2)
                      when ub1#lt numerical_zero && ub2#lt numerical_zero->
                    Some numerical_zero
                 | _ -> None in
               (get_lb optlbr, get_ub optubr)
            | _ -> (None, None)
          end

       | UnOp (op, e1, TInt (k, _)) ->
          let lbk = get_safe_lowerbound k in
          let ubk = get_safe_upperbound k in
          let (optlbr1,optubr1) = get_num_range env e1 in
          let get_lb optlbr =
            match optlbr with
            | Some lbr -> if lbr#gt lbk then Some lbr else Some lbk
            | _ -> Some lbk in
          let get_ub optubr =
            match optubr with
            | Some ubr -> if ubr#lt ubk then Some ubr else Some ubk
            | _ -> Some ubk  in
          begin
            match op with
            | Neg ->
               let lb = match get_lb optubr1 with
                 | Some ub -> Some ub#neg | _ -> None in
               let ub = match get_ub optlbr1 with
                 | Some lb -> Some lb#neg | _ -> None in
               (lb ,ub)
            | BNot -> (get_lb None,  get_ub None)
            | LNot -> (get_lb (Some numerical_zero), get_ub (Some numerical_one))
          end

       | _ ->
          match type_of_exp env e with
          | TInt (k, _) ->
             (Some (get_safe_lowerbound  k), Some (get_safe_upperbound k))
          | _ -> (None, None)
  with
  | _ -> (None,None)


let rec get_stack_address e =
  match e with
  | AddrOf (Var (vname, vid), _)
  | StartOf (Var (vname, vid), _) -> Some (vname, vid)
  | CastE (_, ee) -> get_stack_address ee
  | _ -> None


let is_stack_address e =
  match get_stack_address e with
  | Some _ -> true | _ -> false


let rec get_string_literal e =
  match e with
  | Const (CStr s) -> Some s
  | CastE (_, ee) -> get_string_literal ee
  | _ -> None


let is_string_literal e =
  match get_string_literal e with
  | Some _ -> true | _ -> false


let is_bitwise_ops_on_constants env e =
  let rec aux x bitwise =
    match get_num_value env x with
    | Some _v -> bitwise
    | _ ->
      match x with
      | BinOp (binop, x1, x2, _) ->
	 let bitwise =
           bitwise
           || (match binop with
               | Shiftlt | Shiftrt | BAnd | BXor | BOr -> true
               | _ -> false) in
	(aux x1 bitwise) || (aux x2 bitwise)
      | _ -> false in
  aux e false


let rec is_null_pointer e = match e with
  | CastE (TPtr _, e) when is_zero e -> true
  | CastE (_, e) when is_null_pointer e -> true
  | _ -> false


let rec is_embedded_null_dereference e =
  let check l = List.exists (fun x ->
    match x with Some e -> is_embedded_null_dereference e | _ -> false) l in
  (is_null_pointer e) ||
    (match e with
    | Lval lval -> lval_is_embedded_null_dereference lval
    | CastE (_, e) -> is_embedded_null_dereference e
    | UnOp (_, e, _) -> is_embedded_null_dereference e
    | BinOp (_, e1, e2, _) ->
       is_embedded_null_dereference e1 || is_embedded_null_dereference e2
    | FnApp (_, _, l) -> check l
    | CnApp (_, l, _) -> check l
    | _ -> false)


and lval_is_embedded_null_dereference lval =
  match lval with
  | (Mem e,_) -> is_embedded_null_dereference e
  | _ -> false


let rec has_embedded_null_dereference e =
  let check l =
    List.exists (fun x ->
        match x with
        | Some e -> has_embedded_null_dereference e
        | _ -> false) l in
  match e with
  | Lval lval -> lval_is_embedded_null_dereference lval
  | CastE (_, e) -> has_embedded_null_dereference e
  | BinOp (_, e1, e2, _) ->
     has_embedded_null_dereference e1 || has_embedded_null_dereference e2
  | CnApp ("ntp", [Some e], _) -> is_embedded_null_dereference e
  | FnApp (_, _, l) -> check l
  | CnApp (_, l, _) -> check l
  | _ -> false


let rec exp_fits_kind e k =
  let lb = get_safe_lowerbound k in
  let ub = get_safe_upperbound k in
  match e with
  | Const (CInt (i64, _, _)) ->
     let i = mkNumericalFromInt64 i64 in
     i#geq lb && i#leq ub
  | BinOp (BAnd,_,c,_) -> exp_fits_kind c k
  | _ -> false


let rec exp_size_kind e k =
  let lb = get_safe_lowerbound k in
  let ub = get_safe_upperbound k in
  match e with
  | Const (CInt (i64,_,_)) when exp_fits_kind e k ->
     (Int64.to_string i64
      ^ " in range ["
      ^ lb#toString
      ^ "; "
      ^ ub#toString
      ^ "]")
  | BinOp (BAnd, _, c, _) when exp_fits_kind e k ->
     " and expr with constant " ^ (exp_size_kind c k)
  | _ ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Unexpected expression in exp_size_kind: ";
	       exp_to_pretty e]))


let rec get_not_zero_evidence (env:cfundeclarations_int) (x:exp) =
  match x with
  | Const (CInt (i64, _, _)) when (not ((Int64.compare i64 Int64.zero) = 0)) ->
     Some ("value is " ^ (Int64.to_string i64))

  | Const  (CReal (f, _, _)) when f > 0.0  || f < 0.0 ->
     Some ("value is " ^ (string_of_float f))

  | SizeOf (TInt _) | SizeOf (TPtr _) | SizeOf (TFloat _) ->
     Some ("value is size of type")

  | SizeOf ((TNamed _) as tt) ->
     get_not_zero_evidence env (SizeOf (fenv#get_type_unrolled tt))

  | SizeOfE e ->
     get_not_zero_evidence env (SizeOf (type_of_exp env e))

  | CastE (_, e) -> get_not_zero_evidence env e

  | BinOp (Mult, e1, e2, _) ->
    begin
      match (get_not_zero_evidence env e1, get_not_zero_evidence env e2) with
      | (Some ev1, Some ev2) ->
	Some ("product of two non-zero numbers: " ^ ev1 ^ " and " ^ ev2)
      | _ -> None
    end
  | _ -> None


let rec is_global_address (e:exp) =
  match e with
  | CastE (TPtr _, Const (CInt (i64,_,_)))
       when (Int64.compare i64 Int64.zero) = 1 -> true
  | BinOp (PlusPI, e1, _, _) -> is_global_address e1
  | _ -> false


let check_ppo_validity
      (fname:string) (env:cfundeclarations_int) (ppo:proof_obligation_int) =

  let get_varinfo = env#get_varinfo_by_vid in

  let set_diagnostic =  ppo#add_diagnostic_msg in

  let is_argv (vid:int) =
    vid > 0
    && fname = "main"
    && env#is_formal vid
    && (get_varinfo vid).vparam = 2 in

  let rec is_program_name (e:exp) =
    fname = "main" &&
      (match e with
       | CastE (_, ee) -> is_program_name ee
       | Lval (Mem (BinOp
                      ((PlusPI | IndexPI),
                       Lval (Var (_, vid), NoOffset),
                       Const (CInt (i64, _, _)), _)),
               NoOffset) ->
          is_argv vid && (get_varinfo vid).vparam = 2 && (Int64.to_int i64) = 0
       | _ -> false) in

  let make_record status mth explanation =
    begin
      ppo#set_status status;
      ppo#set_dependencies mth;
      ppo#set_explanation explanation
    end in

  let make = make_record Green DStmt in
  let make_violation = make_record Red DStmt in
  let make_warning _s = make_record Green DStmt in   (* TBD *)
  let _ = pd#index_po_predicate ppo#get_predicate in
  try
    match ppo#get_predicate with

    | PAllocationBase e when has_embedded_null_dereference e ->
    make "embedded null dereference; null dereference is checked separately"

  | PNotZero e ->
    begin
      match get_not_zero_evidence env e with
      | Some ev -> make ev
      | _ -> if is_zero e then make_violation "divisor is zero" else ()
    end

  | PNonNegative e ->
     begin
       match get_num_range env e with
       | (Some lb, _) when lb#geq numerical_zero ->
          make
            ("lower-bound on " ^ (e2s e) ^ " is non-negative: " ^ lb#toString)
       | (_, Some ub) when ub#lt numerical_zero ->
          make_violation
            ("upper-bound on " ^ (e2s e) ^ " is negative: " ^ ub#toString)
       | _ -> ()
     end

  | PNotNull e when is_program_name e ->
     make
       ("pointer to program name is guaranteed not null by operating system")

  | PNotNull (Lval (Var (_vname, vid), NoOffset)) when is_argv vid ->
     make
       ("second argument to main is guaranteed not-null by the operating system")

  | PNotNull (AddrOf (Var v,_))
  | PNotNull (StartOf (Var v,_))
  | PNotNull (CastE (_,AddrOf (Var v,_)))
  | PNotNull (CastE (_,CastE (_,AddrOf (Var v,_)))) ->
     make ("address of variable " ^ (fst v))

  | PNotNull (AddrOf (Mem _,_))
    | PNotNull (CastE (_, (AddrOf (Mem _,_)))) ->
     make ("address of dereferenced memory region")

  | PNotNull (StartOf _)
    | PNotNull (CastE (_, StartOf _)) ->
     make ("address of a location cannot be null")

  | PNotNull e when is_absolute_memory_address env e ->
     (match get_absolute_memory_address env e with
      | Some s -> make ("absolute address in memory: " ^ s)
      | _ -> ())

  | PNotNull (CastE (_, Const (CInt (i64, _, _)))) ->
     let _ =
       chlog#add
         "absolute address pointer"
         (LBLOCK [STR "Not null: "; STR (i64_to_hex_string i64)]) in
     make ("absolute address in memory: " ^ (i64_to_hex_string i64))

  | PNotNull (CastE(_,CastE (_,Const (CInt (i64,_,_))))) ->
     let _ =
       chlog#add
         "absolute address pointer"
         (LBLOCK [STR "Not null: "; STR (i64_to_hex_string i64)]) in
     make ("absolute address in memory: " ^ (i64_to_hex_string i64))

  | PNotNull (Const (CStr _))
    | PNotNull (CastE (_, Const (CStr _))) -> make "string literal"

  | PNotNull (Const (CWStr _))
    | PNotNull (CastE (_, Const (CWStr _))) -> make "wide string literal"

  | PNotNull (BinOp (IndexPI, _, _, _))
  | PNotNull (BinOp (PlusPI, _ , _, _))
  | PNotNull (BinOp (MinusPI, _, _, _))
  | PNotNull (CastE (_, BinOp (IndexPI, _, _, _)))
  | PNotNull (CastE (_, BinOp (PlusPI, _, _, _)))
  | PNotNull (CastE (_, BinOp (MinusPI, _, _, _))) ->
     make "arguments of pointer arithmetic are checked for null"

  | PNotNull (Lval (Var ((("stdin" | "stdout" | "stderr") as vname),_),NoOffset))
    | PNotNull
        (CastE (_, Lval
                     (Var ((("stdin"|"stdout"|"stderr") as vname),_),
                      NoOffset))) ->
     make ("library variable " ^ vname ^ " is not null")

  | PNotNull e when is_null_pointer e ->
     make_violation "expression is a null pointer"

  | PNotNull e when has_embedded_null_dereference e ->
     make (
         "null pointer cannot be dereferenced; acceptability of null pointer "
         ^ "is checked separately")

  | PNull e when is_null_pointer e ->
    make "constant null pointer"

  | PValidMem (Lval (Var ((("stdin" | "stdout" | "stderr") as vname),_),NoOffset))
    | PValidMem
        (CastE (_, Lval
                     (Var ((("stdin"|"stdout"|"stderr") as vname), _),
                      NoOffset))) ->
     make ("library variable " ^ vname ^ " is valid")

  | PValidMem e when is_program_name e ->
     make
       ("validity of pointer to program name is guaranteed by the "
        ^ "operating system")

  | PValidMem e when is_null_pointer e ->
     make "null pointer"

  | PValidMem e when is_absolute_memory_address env e ->
     (match get_absolute_memory_address env e with
      | Some s -> make ("absolute address in memory: " ^ s)
      | _ -> ())

  | PValidMem e when has_embedded_null_dereference e ->
     make "embedded null dereference: null dereference is checked separately"

  | PValidMem e ->
     begin
       match e with
       | Const (CStr _)
         | CastE (_, Const (CStr _)) ->
	  make "constant string is allocated by compiler"

       | Const (CWStr _)
         | CastE (_, Const (CWStr _)) ->
          make "constant wide string is allocated by compiler"

       | BinOp (PlusPI, _, _, _)
         | BinOp (MinusPI, _, _, _)
         | BinOp (IndexPI, _, _, _)
         | CastE (_, BinOp (PlusPI, _, _, _))
         | CastE (_, BinOp (MinusPI, _, _, _))
         | CastE (_, BinOp (IndexPI, _, _, _)) ->
	  make "pointer arithmetic stays within memory region"

       | AddrOf (Var _, _)
         | StartOf (Var _, _)
         | CastE (_, AddrOf (Var _, _))
         | CastE (_, StartOf (Var _, _)) ->
	  make "address of a variable is a valid memory region"
       | _ -> ()
     end

  | POutputParameterArgument e when is_null_pointer e ->
     make "null pointer"

  | POutputParameterArgument e when is_absolute_memory_address env e ->
     (match get_absolute_memory_address env e with
      | Some s -> make_violation ("absolute address in memory: " ^ s)
      | _ -> ())

  | POutputParameterArgument e ->
     (match e with
      | AddrOf (Var (vname, vid), _)
        | CastE (_, AddrOf (Var (vname, vid), _)) when env#is_local vid ->
         make ("address of local variable: " ^ vname)
      | AddrOf (Var (vname, _), _)
        | CastE (_, AddrOf (Var (vname, _), _)) ->
         make_violation ("address of non-local variable: " ^ vname)
      | StartOf (Var (vname, _), _)
        | CastE (_, StartOf (Var (vname, _), _)) ->
         make_violation ("address of array: " ^ vname)
      | _ -> ())

  | PStackAddressEscape (_,e) when is_null_pointer e ->
     make "null pointer can leave the local scope"

  | PStackAddressEscape (_,e) when has_embedded_null_dereference e ->
     make "embedded null dereference; null dereference is checked separately"

  | PStackAddressEscape (Some (Var (vname,vid),offset),_)
       when env#is_local vid ->
     make
       ("assignment to a local variable: "
        ^ vname
        ^ (match offset with
           | NoOffset -> ""
           | _ -> "." ^ (p2s (offset_to_pretty offset))))

  | PStackAddressEscape (_, AddrOf (Var (vname, vid), offset))
    | PStackAddressEscape (_, StartOf (Var (vname, vid), offset))
    | PStackAddressEscape (_, CastE (_, AddrOf (Var (vname, vid), offset)))
    | PStackAddressEscape (_, CastE (_, StartOf (Var (vname, vid), offset)))
       when vid > 0 ->
     let vinfo = get_varinfo vid in
     let poffset = match offset with
       | NoOffset -> ""
       | _ -> "."  ^ (p2s (offset_to_pretty offset)) in
    if vinfo.vglob then
      make
        ("address of global variable "
         ^ vname
         ^ poffset
	 ^ (match vinfo.vstorage with Static -> " (static)" | _ -> ""))
    else
      make_violation
        ("address of local variable "
         ^ vname
         ^ poffset
         ^ " cannot leave local scope")

  | PInScope e when is_null_pointer e ->
     make "null pointer is always in scope"

  | PInScope e when is_function_type (type_of_tgt_exp env e) ->
     make "function pointer is global"

  | PInScope e when has_embedded_null_dereference e ->
     make "embedded null dereference; null dereference is checked separately"

  | PInScope e when is_absolute_memory_address env e ->
     (match get_absolute_memory_address env e with
      | Some s -> make ("absolute address in memory: " ^ s)
      | _ -> ())

  |  PInScope (CastE (_, Const (CInt (i64,_,_))))
     | PInScope (CastE (_, (CastE (_, Const (CInt (i64,_,_))))))
       when int64_non_negative i64 ->
      make ("memory mapped i/o at address " ^ (i64_to_hex_string i64))

  | PInScope (Lval (Var ((("stdin" | "stdout" | "stderr") as vname),_),NoOffset))
    | PInScope
        (CastE (_, Lval
                     (Var ((("stdin" | "stdout" | "stderr") as vname), _),
                      NoOffset))) ->
     make ("library variable " ^ vname ^ " is in scope")

  | PInScope (Lval (Var (vname, vid), _))
       when vid > 0 && (get_varinfo vid).vglob ->
     make ("variable " ^ vname ^ " is global")

  | PInScope (AddrOf (Mem (CastE (TPtr _, (Const (CInt (i64, _, _))))), _))
       when int64_non_negative i64 ->
     make ("memory mapped i/o at address " ^  (i64_to_hex_string i64))

  | PInScope (AddrOf (Var (vname, vid),_))
    | PInScope (StartOf (Var (vname,vid),_)) when vid > 0 ->
     let vinfo = get_varinfo vid in
     if vinfo.vglob then
       make
         ("address of global variable "
          ^  vname
          ^ (match vinfo.vstorage with Static -> "(static)" | _ -> ""))
     else
       make ("address of local variable " ^ vname)

  | PInScope (CastE (_, AddrOf (Var (vname,vid), _)))
    | PInScope (CastE (_, StartOf (Var (vname,vid),_))) when vid > 0 ->
     let vinfo = get_varinfo vid in
     if vinfo.vglob then
       make
         ("address of global variable "
          ^ vname
	  ^ (match vinfo.vstorage with Static -> " (static)" | _ -> ""))
     else
       make ("address of local variable " ^ vname)

  | PInScope e when is_constant_string e ->
     make ("address of constant string")

  | PInScope (BinOp ((IndexPI | PlusPI | MinusPI), _, _, _))
    | PInScope (CastE (_, BinOp ((IndexPI | PlusPI | MinusPI),_,_,_))) ->
     make "arguments of pointer arithmetic are checked for being in scope"

  | PCast (tfrom,tto,_) when (typ_compare tfrom tto) = 0 ->
     make "source and target type are the same"

  | PFormatCast (tfrom,tto,_) when (typ_compare tfrom tto) = 0 ->
     make "source and target type are the same"

  | PPointerCast (tfrom,tto,_) when (typ_compare tfrom tto) = 0 ->
     make "source and target type are the same"

  | PFormatCast (tfrom,((TPtr _) as tto),_)
       when not (is_pointer_type (fenv#get_type_unrolled tfrom)) ->
     make_violation
       ("argument type: "
        ^  (p2s (typ_to_pretty tfrom))
        ^ " must be a pointer type: "
        ^ (p2s (typ_to_pretty tto)))

  | PCast (tfrom,
           tto, Lval (Mem (CastE (_, Const (CInt (i64, _, _)))), NoOffset))
       when (is_volatile_type tfrom && is_volatile_type tto) ->
     let _ =
       chlog#add
         "absolute address memory region"
         (LBLOCK [
              STR "cast from ";
              typ_to_pretty tfrom; STR " to ";
              typ_to_pretty tto;
              STR " for memory address ";
              STR (i64_to_hex_string i64)]) in
     make ("cast of volatile region in memory: " ^ (i64_to_hex_string i64) )

  | PPointerCast (tfrom,tto,_) when (typ_compare tfrom tto) = 0 ->
     make "source and target type are the same"

  | PCast (TInt (IInt,_), TPtr _, e) when is_zero e ->
     make "null-pointer cast"

  | PCast (TInt (_ik, _), TPtr _, (Const (CInt (i64, _, _))))
       when int64_non_negative i64 ->
     make ("casting memory address to pointer: " ^ (i64_to_hex_string i64))

  | PCast (TInt (_ik, _), TPtr _, (CastE(_, Const (CInt (i64, _, _)))))
       when int64_non_negative i64 ->
     make ("casting memory address to pointer: " ^ (i64_to_hex_string i64))

  | PCast (TInt (IInt, _), TInt (IBool, _), BinOp (b, _, _, _))
       when (match b with
             | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr -> true
             | _ -> false) ->
     make "cast result from boolean expression to bool"

  | PCast (TPtr (TVoid _, _), TInt (IULong, _), e) when is_zero e ->
     make "null-pointer cast"

  | PCast (TFloat (FFloat, _), TFloat (FDouble, _), _) ->
     make "cast from float to double is safe (value is unchanged)"

  | PCast (TFloat (FFloat, _), TFloat (FLongDouble, _), _) ->
     make "cast from float to long double is safe (value is unchanged)"

  | PCast (TFloat (FDouble, _), TFloat (FLongDouble, _), _) ->
     make "cast from double to long double is safe (value is unchanged)"

  | PCast (TFloat (FDouble, _), TFloat (FFloat, _), Const (CReal (f, _, _)))
       when float_fits_kind f FFloat ->
     make
       ("cast from double to float is safe for value: "
        ^ (string_of_float f))

  | PCast (TInt (IChar,_), TFloat _, _)
    | PCast (TInt (ISChar,_), TFloat _, _)
    | PCast (TInt (IUChar,_), TFloat _, _)
    | PCast (TInt (IBool,_), TFloat _, _)
    | PCast (TInt (IInt,_), TFloat _, _)
    | PCast (TInt (IUInt,_), TFloat _, _)
    | PCast (TInt (IShort,_), TFloat _, _)
    | PCast (TInt (IUShort,_), TFloat _, _) ->
     make "cast from regular integer type to float is safe"

  | PCast (TPtr _, (TInt _ as tto), _) ->
    make_warning "word-size"
      ("casting a pointer to integer type " ^ (p2s (typ_to_pretty tto)))

  | PPointerCast (TVoid _, TInt (IChar,_), e) when is_zero e ->
    make "null-terminator cast"

  | PPointerCast (_, TVoid _, _) -> make "cast to void pointer"

  | PPointerCast (_, TInt (ik,_), _) when is_character_type ik ->
     make "cast to character type"

  | PPointerCast (TFun _, TFun _, _) ->
     make "cast from function pointer to function pointer"

  | PPointerCast (_,_,e) when is_null_pointer e ->
     make "cast of null-pointer"

  | PPointerCast (_,_,e) when has_embedded_null_dereference e ->
     make ("embedded null dereference: null dereference is checked separately")

  | PPointerCast (TVoid _, TInt _,
                  CastE (TPtr ((TVoid _),_), AddrOf (Var (vname,vid),NoOffset)))
       when  vid > 0
             && (let vinfo = get_varinfo vid in
                 match vinfo.vtype with TInt _ -> true | _ -> false) ->
     make ("original type of " ^ vname ^ " is integer")

  | PCast (TInt _, TEnum (ename,_), (Const _ as e))
       when is_enum_constant ename e ->
     make
       ("value "
        ^ (p2s (exp_to_pretty e))
        ^ " belongs to enumeration "
        ^ ename)

  | PCast (TEnum (ename,_), TInt (ik, _), _) when enum_fits_kind ename ik ->
     let its = int_type_to_string in
     make ("all enum values in " ^ ename ^ " fit into " ^ (its ik))

  | PCast (_, TEnum (ename,_), (UnOp (LNot, _, _)))
       when (is_enum_constant ename zero) && (is_enum_constant ename one) ->
     make ("zero and one belong to enumeration " ^ ename)

  | PCast (_, TEnum (ename,_), (BinOp ((Lt|Gt|Le|Ge|Eq|Ne), _, _, _)))
       when (is_enum_constant ename zero) && (is_enum_constant ename one) ->
     make ("zero and one belong to enumeration " ^ ename)

  | PCast (_,_,e) when has_embedded_null_dereference e ->
     make ("embedded null dereference: null dereference is checked separately")

  | PUnsignedToUnsignedCast (_,ik2,BinOp (op,_,_,_))
       when is_bool_type ik2  && is_relational_operator op ->
     make ("casting result of assertion to bool")

  | PSignedToSignedCastLB (ik1, ik2, _)
    | PSignedToSignedCastUB (ik1, ik2, _)
    | PSignedToUnsignedCastLB (ik1, ik2, _)
    | PSignedToUnsignedCastUB (ik1, ik2, _)
    | PUnsignedToSignedCast (ik1, ik2, _)
    | PUnsignedToUnsignedCast (ik1, ik2, _)
       when is_safe_int_cast ik1 ik2 ->
     let its = int_type_to_string in
     make ("casting from " ^ (its ik1) ^ " to " ^ (its ik2) ^ " is safe")

  | PSignedToSignedCastLB (_, ik2, e)
    | PSignedToSignedCastUB (_, ik2, e)
    | PSignedToUnsignedCastLB (_, ik2, e)
    | PSignedToUnsignedCastUB (_, ik2, e)
    | PUnsignedToSignedCast (_, ik2, e)
    | PUnsignedToUnsignedCast (_, ik2,e)
       when exp_fits_kind e ik2 ->
     let its = int_type_to_string in
     make ("casting expression " ^ (exp_size_kind e ik2) ^ " to " ^ (its ik2))

  | PSignedToSignedCastLB (_, ik2, Lval (Var (_, vid), Index (_, NoOffset)))
    | PSignedToSignedCastUB (_, ik2, Lval (Var (_, vid), Index (_, NoOffset)))
    | PSignedToUnsignedCastLB (_, ik2, Lval (Var (_, vid), Index (_, NoOffset)))
    | PSignedToUnsignedCastUB (_, ik2, Lval (Var (_, vid), Index (_, NoOffset)))
    | PUnsignedToSignedCast (_, ik2, Lval (Var (_, vid), Index (_, NoOffset)))
    | PUnsignedToUnsignedCast (_, ik2, Lval (Var (_, vid), Index (_, NoOffset)))
       when vid > 0 ->
     let vinfo = get_varinfo vid in
     let its = int_type_to_string in
     begin
       match vinfo.vtype with
       | TArray (TInt (ikt, _), _, _) when is_safe_int_cast ikt ik2 ->
          make
            ("casting expression of original type "
             ^ (its ikt)
             ^ " to "
             ^ (its ik2)
             ^ " is safe")
       | _ -> ()
     end

  | PSignedToUnsignedCastLB (_,_,e)
    | PSignedToUnsignedCastUB (_,_,e)
       when is_bitwise_ops_on_constants env e ->
     make ("casting the result of a bitwise manipulation to an unsigned")

  | PSignedToSignedCastLB (_, _, e)
    | PSignedToSignedCastUB (_, _, e)
    | PSignedToUnsignedCastLB (_, _, e)
    | PSignedToUnsignedCastUB (_, _, e)
    | PUnsignedToSignedCast (_,_, e)
    | PUnsignedToUnsignedCast (_, _, e)
       when has_embedded_null_dereference e ->
     make ("embedded null dereference: null dereference is checked separately")

  | PSignedToUnsignedCastLB (_, ik2, UnOp (BNot, Const (CInt (i64, _, _)), _))
    | PSignedToUnsignedCastUB (_, ik2, UnOp (BNot, Const (CInt (i64, _, _)), _))
       when int_fits_kind (mkNumericalFromInt64 i64) ik2 ->
     make
       ("bit complement of "
        ^ (i64_to_hex_string i64)
        ^ " fits into "
        ^ (int_type_to_string ik2))

  | PSignedToUnsignedCastLB (_, ik, BinOp (op, _, _, _))
    | PSignedToUnsignedCastUB (_, ik, BinOp (op, _, _, _))
       when (match op with
             | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr -> true
             | _ -> false) ->
     make ("cast from boolean result to " ^ (int_type_to_string ik))

  | PSignedToUnsignedCastLB (_ik1, _ik2, e) ->
    begin
      match get_num_value env e with
      | Some i when i#geq numerical_zero ->
	 make ("constant value " ^ i#toString ^ " is non-negative")
      | Some i when i#lt numerical_zero ->
	 make_violation
           ("casting a negative number to an unsigned: " ^ i#toString)
      | _ ->
         match get_num_range env e with
	 | (Some lb, _) when lb#geq numerical_zero ->
	    make ("LB: " ^ lb#toString ^ " is non-negative")
         | (_, Some ub) when ub#lt numerical_zero ->
            make_violation
              ("UB: "
               ^ ub#toString
               ^ " is negative; "
               ^ "casting a negative number to an unsigned")
         | _ -> ()
    end

  | PSignedToUnsignedCastUB (_ik1, ik2, e)
    | PSignedToSignedCastUB (_ik1, ik2, e)
    | PUnsignedToSignedCast (_ik1, ik2, e) ->
     begin
       match get_num_value env e with
       | Some i when int_fits_kind i ik2 ->
	  make
            ("constant value "
             ^ i#toString
             ^ " fits in type "
             ^ (int_type_to_string ik2))
       | _ ->
          match get_num_range ~apply_cast:false env e with
	  | (_, Some ub) when int_fits_kind ub ik2 ->
	     make
               ("UB: " ^ ub#toString
                ^ " fits in type "
                ^ (int_type_to_string ik2))
	  | (Some lb,_) when lb#gt (get_safe_upperbound ik2) ->
	     make_violation
               ("LB: "
                ^ lb#toString
                ^ " violates safe UB: "
                ^ (get_safe_upperbound ik2)#toString)
	  | _ -> ()
     end

  | PSignedToSignedCastLB  (_ik1, ik2, e) ->
     begin
       match get_num_value env e with
       | Some i when int_fits_kind i ik2 ->
          make
            ("constant value "
             ^ i#toString
             ^ " fits in type "
             ^ (int_type_to_string ik2))
       | _ ->
          match get_num_range ~apply_cast:false env e with
          | (Some lb, _) when int_fits_kind lb ik2 ->
             make
               ("LB: "
                ^ lb#toString
                ^ " fits in type "
                ^ (int_type_to_string ik2))
          | (_, Some ub) when ub#lt (get_safe_lowerbound ik2) ->
             make_violation
               ("UB: "
                ^ ub#toString
                ^ " violates safe LB: "
                ^ (get_safe_lowerbound ik2)#toString)
          | _ -> ()
     end

  | PIntUnderflow (PlusA,CnApp("ntp", _, _),CnApp("ntp", _, _), _) ->
     make "addition of null-terminator-positions is non-negative"

  | PIntUnderflow (_, x1, x2, _)
  | PIntOverflow (_, x1, x2, _)
       when has_embedded_null_dereference x1
            || has_embedded_null_dereference x2 ->
     make "embedded null dereference; null dereference is checked separately"

  | PIntOverflow (PlusA,Const (CInt (i64, _, _)),Const (CInt (j64, _, _)), k)
    | PUIntOverflow (PlusA,Const (CInt (i64, _, _)),Const (CInt (j64, _, _)), k) ->
     let upperbound = get_safe_upperbound k in
     let sum = (mkNumericalFromInt64 i64)#add (mkNumericalFromInt64 j64) in
     if sum#leq upperbound then
       make
         ("sum of constants ("
          ^ sum#toString
          ^ ") is less than safe upperbound ("
          ^ upperbound#toString
          ^ ")")
     else
       begin
	 ch_error_log#add
           "int-overflow"
	   (LBLOCK [
                STR "Potential integer overflow in ";
                INT ppo#index;
                STR ". ";
		STR " sum: ";
                sum#toPretty;
                STR ", safe upperbound: ";
		upperbound#toPretty])
       end

  | PIntOverflow (MinusA,Const (CInt (i64, _, _)),Const (CInt (j64, _, _)), k)
    | PUIntOverflow (MinusA,Const (CInt (i64,_,_)),Const (CInt (j64,_,_)),k) ->
     let upperbound = get_safe_upperbound k in
     let difference =
       (mkNumericalFromInt64 i64)#sub (mkNumericalFromInt64 j64) in
     if difference#leq upperbound then
       make
         ("difference of constants ("
          ^ difference#toString
          ^ ") is less than safe upperbound ("
          ^ upperbound#toString
          ^ ")")
     else
       begin
	 ch_error_log#add
           "int-overflow"
	   (LBLOCK [
                STR "Potential integer overflow in ";
                INT ppo#index;
                STR ". ";
		STR " difference: ";
                difference#toPretty;
		STR ", safe upperbound: ";
                upperbound#toPretty])
       end

  | PIntOverflow (Mult, Const (CInt (i64, _, _)),Const (CInt (j64, _, _)), k)
    | PUIntOverflow
        (Mult, Const (CInt (i64, _, _)),Const (CInt (j64, _, _)), k) ->
     let upperbound = get_safe_upperbound k in
     let product =
       (mkNumericalFromInt64 i64)#mult (mkNumericalFromInt64 j64) in
     if product#leq upperbound then
       make
         ("product of constants ("
          ^ product#toString
          ^ ") is less than safe upperbound ("
          ^ upperbound#toString
          ^ ")")
     else
       begin
	 ch_error_log#add
           "int-overflow"
	   (LBLOCK [
                STR "Potential integer overflow in ";
                INT ppo#index;
                STR ". ";
		STR " product: ";
                product#toPretty;
                STR ", safe upperbound: ";
		upperbound#toPretty])
       end

  | PIntOverflow (MinusA, _, e, _)
    | PUIntOverflow (MinusA, _, e, _) ->
     begin
       match get_num_range env e with
       | (Some lb, _) when lb#geq numerical_zero ->
          make
            ("subtracting a non-negative number (lower bound on "
             ^ (e2s e)
             ^ ": " ^ lb#toString
             ^ ")")
       | _ -> ()
     end

  | PIntOverflow (PlusA, e1, e2, ik)
    | PUIntOverflow (PlusA, e1, e2, ik) ->
     let upperbound = get_safe_upperbound ik in
     begin
       match (get_num_range env e1, get_num_range env e2) with
       | ((_, Some ub1), (_, Some ub2)) when (ub1#add ub2)#leq upperbound ->
	  make
            ("maximum value of sum: "
             ^ (ub1#add ub2)#toString
             ^ " is less than safe upperbound "
             ^ upperbound#toString)
       | ((_, Some ub1), _) when ub1#leq numerical_zero ->
          make
            ("adding a non-positive number (upper bound on "
             ^ (e2s e1)
             ^ ": "
             ^ ub1#toString)
       |  (_, (_, Some ub2)) when ub2#leq numerical_zero ->
           make
             ("adding a non-positive number (upper bound on "
              ^ (e2s e2)
              ^ ": "
              ^ ub2#toString)
       | _ -> ()
     end

  | PIntOverflow (Mult, (Const _ as e), _, _)
    | PUIntOverflow (Mult,(Const _ as e), _, _) when is_zero e ->
     make "multiplication by zero"

  | PIntOverflow (Mult, _, (Const _ as e), _)
    | PUIntOverflow (Mult, _,(Const _ as e), _) when is_zero e ->
     make "multiplication by zero"

  | PIntOverflow (Mult, e1, e2, ik)
    | PUIntOverflow (Mult, e1, e2, ik) ->
     let upperbound = get_safe_upperbound ik in
     begin
       match (get_num_range env e1, get_num_range env e2) with
       | ((Some lb1, Some ub1), (Some lb2, Some ub2))
            when lb1#geq numerical_zero && lb2#geq numerical_zero ->
          if (ub1#mult ub2)#leq upperbound then
            make
              ("maximum value of product "
               ^ (ub1#mult ub2)#toString
               ^ " is less than or equal to safe upperbound "
               ^ upperbound#toString)
          else
            ()
       | ((Some lb1, _), (_, Some ub2))
            when lb1#geq numerical_zero && ub2#lt numerical_zero ->
          make
            ("result of multiplication is negative: "
             ^ "(lower-bound on first operand:  "
             ^ lb1#toString
             ^ "; upper-bound on second operand: "
             ^ ub2#toString)
       | ((_, Some ub1), (Some lb2, _))
            when lb2#geq numerical_zero && ub1#lt numerical_zero ->
          make
            ("result of multiplication is negative: (lower-bound "
             ^ "on second operand: "
             ^ lb2#toString
             ^ "; upper-bound on first operand: "
             ^ ub1#toString)
       | _ -> ()
     end

  | PIntOverflow (Div, e1, e2, _)
    | PUIntOverflow (Div, e1, e2, _) ->
     begin
       match get_num_range env e2 with
       | (Some lb, _) when lb#gt numerical_zero ->
          make
            ("division by positive number (lower bound on "
             ^ (e2s e2)
             ^ ": "
             ^ lb#toString
             ^ ") cannot lead to integer overflow")
       | _ ->
          match get_num_range env e1 with
          | (Some lb, _) when lb#gt numerical_zero ->
             make
               ("division of positive number (lower bound on "
                ^ (e2s e1)
                ^ ": "
                ^ lb#toString
                ^ ") cannot lead to integer overflow")
          | _ -> ()
     end

  | POutputParameterScalar (_, e) when not (is_pointer_type (type_of_exp env e)) ->
     make ("expression " ^ (e2s e) ^ " is not a pointer type")

  | POutputParameterScalar (_, e) when is_null_pointer e ->
     make ("expression " ^ (e2s e) ^ " is a null pointer")

  | POutputParameterScalar (_, e)
       when (match e with
             | Lval _ | CastE (_, Lval _) -> true | _ -> false) ->
     make ("expression " ^ (e2s e) ^ " is an lval expression")

  | POutputParameterScalar (_, e) when is_string_literal e ->
     make ("expression " ^ (e2s e) ^ " is a string literal")

  | PWidthOverflow (e, ik) ->
     let safeBitWidth = mkNumerical (get_safe_bit_width ik) in
     begin
       match get_num_range env e with
       | (_, Some v) when v#lt safeBitWidth ->
	  make
            ("upper bound on "
             ^ (e2s e)
             ^ ": " ^ v#toString
             ^ " is less than minimum word size ("
             ^ safeBitWidth#toString
             ^ ")")
       | (Some lb, Some ub) when lb#equal ub && ub#geq safeBitWidth ->
          make_violation
            ("value: "
             ^ lb#toString
             ^ " is larger than or equal to bit width: "
             ^ safeBitWidth#toString)
       | (_, Some v) when v#lt (mkNumerical 256) ->
	  let minWidth = get_required_minimum_bit_width v#toInt in
	  begin
	    ch_info_log#add
              "minimum word size"
	      (LBLOCK [
                   STR fname;
		   STR " requires a minimum word size of ";
                   INT minWidth;
		   STR " for shift of ";
                   v#toPretty;
                   STR " to be defined"]);
	    make
              ("value "
               ^ v#toString
               ^ " requires a minimum word size of "
               ^ (stri minWidth))
	  end
       | _ -> ()
     end

  | PIntUnderflow (PlusA,Const (CInt (i64, _, _)),Const (CInt (j64, _, _)), k) ->
     let lowerbound = get_safe_lowerbound k in
     let sum = (mkNumericalFromInt64 i64)#add (mkNumericalFromInt64 j64) in
     if sum#geq lowerbound then
       make
         ("sum of constants ("
          ^ sum#toString
          ^ ") is greater than or equal to safe lowerbound ("
          ^ lowerbound#toString
          ^ ")" )
    else
      begin
	ch_error_log#add
          "int-underflow"
	  (LBLOCK [
               STR "Potential integer underflow in ";
               INT ppo#index;
               STR ". ";
	       STR " sum: ";
               sum#toPretty;
               STR ", safe lowerbound: ";
	       lowerbound#toPretty])
      end

  | PIntUnderflow (MinusA, Const (CInt (i64, _, _)),Const (CInt (j64, _, _)), k) ->
     let lowerbound = get_safe_lowerbound k in
     let difference = (mkNumericalFromInt64 i64)#sub (mkNumericalFromInt64 j64) in
     if difference#geq lowerbound then
       make
         ("difference of constants ("
          ^ difference#toString
          ^ ") is greater than or equal to safe lowerbound (" ^
	    lowerbound#toString
            ^ ")" )
    else
      begin
	ch_error_log#add
          "int-underflow"
	  (LBLOCK [
               STR "Potential integer underflow in ";
               INT ppo#index;
               STR ". ";
	       STR " difference: ";
               difference#toPretty;
               STR ", safe lowerbound: ";
	       lowerbound#toPretty])
      end

  | PIntUnderflow (Mult, Const (CInt (i64, _, _)), Const (CInt (j64, _, _)), k) ->
     let lowerbound = get_safe_lowerbound k in
     let product = (mkNumericalFromInt64 i64)#mult (mkNumericalFromInt64 j64) in
     if product#geq lowerbound then
       make
         ("product of constants ("
          ^ product#toString
          ^ ") is greater than or equal to safe lowerbound (" ^
	    lowerbound#toString ^ ")" )
    else
      begin
	ch_error_log#add
          "int-underflow"
	  (LBLOCK [
               STR "Potential integer underflow in ";
               INT ppo#index;
               STR ". ";
	       STR " product: ";
               product#toPretty;
               STR ", safe lowerbound: ";
	       lowerbound#toPretty])
      end

  | PIntUnderflow (Mult, e1, e2, _) ->
     begin
       match (get_num_range env e1, get_num_range env e2) with
       | ((Some lb1, _), (Some lb2, _))
            when lb1#geq numerical_zero && lb2#geq numerical_zero ->
          make  "multiplication of two non-negative integers"
       | _ -> ()
     end

  | PIntUnderflow (PlusA, _, e2, _) ->
     begin
       match get_num_range env e2 with
       | (Some lb, _) when lb#geq numerical_zero ->
          make ("add non-negative number (lower-bound: " ^ lb#toString ^ ")")
       | _ -> ()
     end

  | PIntUnderflow (MinusA, _, e, _) ->
     begin
       match get_num_range env e with
       | (_, Some ub) when ub#leq numerical_zero ->
          make
            ("subtracting non-positive number (upper bound on "
             ^ (e2s e)
             ^ ": "
             ^ ub#toString
             ^ ")")
      | _ -> ()
    end

  | PIntUnderflow (Div, _, _, _) ->
     make "division cannot lead to integer underflow"

  | PUIntUnderflow (PlusA, _, _, _) ->
     make
       ("unsigned addition cannot cause an underflow: both operands"
        ^ "are non-negative")

  | PUIntUnderflow (Mult, _, _, _) ->
     make
       ("unsigned multiplication cannot cause an underflow: both operands "
        ^ "are non-negative")

  | PUIntUnderflow (Div, _, _, _) ->
     make
       ("unsigned division cannot cause an underflow: both operands "
        ^ " are non-negative")

  | PPtrLowerBound (_, _, x1, x2)
       when has_embedded_null_dereference x1
            || has_embedded_null_dereference x2 ->
     make "embedded null dereference; null dereference is checked separately"

  | PPtrLowerBound (_, PlusPI, _, e)
    | PPtrLowerBound (_, IndexPI, _, e) ->
     begin
       match get_num_range env e with
       | (Some lb, _) when lb#geq numerical_zero ->
          make
            ("adding non-negative number (lower bound on "
             ^ (e2s e)
             ^ ": "
             ^ lb#toString
             ^ ")")
       | _ -> ()
     end

  | PPtrLowerBound (_, MinusPI, _, e) ->
     begin
       match get_num_range env e with
       | (_, Some ub) when ub#leq numerical_zero ->
          make
            ("subtracting non-positive number (upper bound on "
             ^ (e2s e)
             ^ ": "
             ^ ub#toString
             ^ ")")
       | _ -> ()
     end

  | PPtrUpperBound (_, _, e, _) when is_program_name e ->
     make
       ("validity of pointer to program name is guaranteed by the "
        ^ "operating system")

  | PPtrUpperBound (_, _, e, _) when is_null_pointer e ->
     make ("not-null of first argument is checked separately")

  | PPtrUpperBound (_, _, x1, x2)
    | PPtrUpperBoundDeref (_, _, x1, x2)
       when has_embedded_null_dereference x1
            || has_embedded_null_dereference x2 ->
     make "embedded null dereference; null dereference is checked separately"

  | PPtrUpperBound (_, MinusPI, _, e)
    | PPtrUpperBoundDeref (_, MinusPI, _, e) ->
     begin
       match get_num_range env e with
       | (Some lb, _) when lb#geq numerical_zero ->
          make
            ("subtracting non-negative number (lower bound on "
             ^ (e2s e)
             ^ ": "
             ^ lb#toString
             ^ ")")
       | _ -> ()
     end

  | PPtrUpperBound (_, PlusPI, _, e)
  | PPtrUpperBound (_, IndexPI, _, e)
  | PPtrUpperBoundDeref (_, PlusPI, _, e)
  | PPtrUpperBoundDeref (_, IndexPI, _, e) when is_zero e ->
     make "add zero"

  | PPtrUpperBound (_, PlusPI, StartOf (Var (_, vid),NoOffset), (Const _ as e))
    | PPtrUpperBound
        (_, PlusPI, CastE(_, StartOf (Var (_, vid), NoOffset)), (Const _ as e))
    | PPtrUpperBound
        (_, PlusPI,CastE(_,StartOf (Var (_, vid),NoOffset)),
	 CastE (_, (Const _ as e))) when vid > 0 ->
     begin
      match (get_num_value env e, (get_varinfo vid).vtype) with
      | (Some v, TArray (_, Some (Const _ as clen), _)) when
	     (match get_num_value env clen with
              | Some _len -> true
              | _ -> false) ->
	let len = Option.get (get_num_value env clen) in
	if v#leq len then
	  make
            ("adding "
             ^ v#toString
             ^ " to the start of an array of length "
             ^ len#toString)
	else
	  make_violation
            ("adding "
             ^ v#toString
             ^ " to the start of an array of length "
             ^ len#toString
             ^ " violates the one-beyond-upperbound")
      | _ -> ()
    end

  | PPtrUpperBound (_, PlusPI, StartOf (Var (vname,vid), NoOffset),
		    CnApp ("ntp", [Some (CastE(_, Const (CStr s)))], _))
  | PPtrUpperBound (_, PlusPI, CastE(_, StartOf (Var (vname, vid), NoOffset)),
		    CnApp ("ntp", [Some (CastE(_,Const (CStr s)))], _) )
  | PPtrUpperBound (_, PlusPI, StartOf (Var (vname, vid), NoOffset),
		    CnApp ("ntp", [Some (Const (CStr s))], _) )
  | PPtrUpperBound (_, PlusPI,CastE(_, StartOf (Var (vname, vid), NoOffset)),
		    CnApp ("ntp", [Some (Const (CStr s))], _) ) when vid > 0 ->
     begin
       match (get_varinfo vid).vtype with
       | TArray (_,Some (Const _ as clen), _) ->
	  begin
	    match (get_num_value env clen) with
	    | Some length ->
               let (_, _, strlen) = mk_constantstring s in
	       if length#gt (mkNumerical strlen) then
	         make
                   ("constant string with length "
                    ^ (stri strlen)
                    ^ " fits in "
                    ^ vname
                    ^ " of size "
                    ^ length#toString)
	       else
	         make_violation
                   ("constant string with length "
                    ^ (stri strlen)
                    ^ " does not fit in "
                    ^ vname
                    ^ " of size "
                    ^ length#toString)
	  | _ -> ()
	end
      | _ -> ()
    end

  | PPtrUpperBound (_, PlusPI,AddrOf (Var (vname, vid), NoOffset),
		    SizeOfE (Lval (Var (wname, wid), NoOffset)))
  | PPtrUpperBound (_, PlusPI,AddrOf (Var (vname, vid), NoOffset),
		    SizeOfE
                      (Lval (Mem (AddrOf (Var (wname, wid), NoOffset)), NoOffset)))
       when vname = wname && vid = wid ->
     make
       ("result of addition points to one beyond the end of the variable "
        ^ vname)

  | PPtrUpperBound (_, PlusPI, CastE(_, StartOf (Var (vname, vid), NoOffset)),
		    BinOp
                      (MinusA, SizeOfE (Lval (Var (wname, wid), NoOffset)), e, _))
      when vname = wname && vid = wid ->
    begin
      match get_num_range env e with
      | (Some lb, _) when lb#geq numerical_zero ->
         make
           ("result of addition is less than or equal to size of the variable "
            ^ vname
            ^ " (difference with size: "
            ^ lb#toString
            ^ ")")
      | _ -> ()
    end

  | PPtrUpperBound (_, PlusPI,CastE(_, StartOf lval1), SizeOfE (Lval lval2))
       when (lval_compare lval1 lval2) = 0 ->
     make
       ("adding the size of a variable to the start of the same variable "
        ^ (p2s (lval_to_pretty lval1)))

  | PPtrUpperBound (_, PlusPI,CastE(_, AddrOf lval1), ub)
    | PPtrUpperBound (_, PlusPI, CastE(_, StartOf lval1), ub) ->
     (match (get_num_value env (SizeOf (type_of_lval env lval1)),
             get_num_value env ub) with
        (Some s1, Some s2) ->
        if s1#geq s2 then
          make
            ("adding "
             ^ s2#toString
             ^ " to start of variable of size "
             ^ s1#toString)
        else
          make_violation
            ("adding "
             ^ s2#toString
             ^ " to start of variable of size "
             ^ s1#toString
             ^ " violates the upper bound")
      | _ -> ())

  | PPtrUpperBound (_, PlusPI,Const (CStr s1),
		    CnApp ("ntp", [Some (Const (CStr s2))], _))
  | PPtrUpperBound (_, PlusPI,CastE(_, Const (CStr s1)),
		    CnApp ("ntp", [Some (CastE(_, Const (CStr s2)))], _))
       when s1 = s2->
     let (s,ishex,len) = mk_constantstring s1 in
     let ps =
       if ishex || len > 20 then
         (string_of_int len) ^ "-character string"
       else
         s in
     make ("upperbound of constant string argument: " ^ ps)

  | PPtrUpperBound (_, PlusPI,Const (CWStr s1),
		    CnApp ("ntp", [Some (Const (CWStr s2))], _) )
  | PPtrUpperBound (_, PlusPI,CastE(_, Const (CWStr s1)),
		    CnApp ("ntp", [Some (CastE(_, Const (CWStr s2)))], _) )
       when (List.length s1) = (List.length s2) ->
     make ("upperbound of constant wide string argument")

  | PPtrUpperBound(_, PlusPI, CastE(_,Const (CStr s)), e)
       when (match get_num_value env e with
             | Some _ -> true | _ -> false) ->
     (match get_num_value env e with
      | Some num ->
         let (_, _, strlen) = mk_constantstring s in
         if num#leq (mkNumerical strlen) then
           make
             ("pointer upper bound offset of "
              ^ num#toString
              ^ " is within constant string of length "
              ^ (stri strlen))
         else
           make_violation
             ("pointer upper bound offset of "
              ^ num#toString
              ^ " lies outside constant string of length "
              ^ (stri strlen))
      | _ -> ())

  | PPtrUpperBound(_, PlusPI, (CastE(_, Lval (Var (vname1, _), NoOffset))),
                   CnApp
                     ("ntp",
                      [Some (CastE (_, Lval (Var (vname2, _), NoOffset)))], _))
       when vname1 = vname2 ->
     make ("null-termination within bounds is checked separately")

  | PPtrUpperBoundDeref (_,
                         PlusPI,
                         StartOf (Var (_, vid), NoOffset), (Const _ as e))
       when vid > 0 ->
    begin
      match (get_num_value env e, (get_varinfo vid).vtype) with
      | (Some v, TArray (_, Some (Const _ as clen), _)) when
	     (match get_num_value env clen with
              | Some _ -> true | _ -> false) ->
	let len = Option.get (get_num_value env clen) in
	if v#lt len then
	  make
            ("adding "
             ^ v#toString
             ^ " to the start of an array of length "
             ^ len#toString)
	else
	  make_violation
            ("adding "
             ^ v#toString
             ^ " to the start of an array of length "
             ^ len#toString
             ^ " violates the upperbound")
      | _ -> ()
    end

  | PLowerBound (_, e) when is_program_name e ->
     make
       ("validity of pointer to program name is guaranteed by the "
        ^ "operating system")

  | PLowerBound (_, Const (CStr _))
  | PLowerBound (_, CastE (_, Const (CStr _))) ->
     make "constant string is allocated by compiler"

  | PLowerBound (_, Const (CWStr _))
    | PLowerBound (_, CastE (_, Const (CWStr _))) ->
     make "constant wide string is allocated by compiler"

  | PLowerBound (_, e) when is_absolute_memory_address env e ->
     (match get_absolute_memory_address env e with
      | Some s -> make ("absolute address in memory: " ^ s)
      | _ -> ())

  | PLowerBound (_,
                 Lval (Var ((("stdin" | "stdout" | "stderr") as vname), _),
                       NoOffset))
    | PLowerBound (_,
                   CastE
                     (_, Lval (Var ((("stdin"|"stdout"|"stderr") as vname), _),
                               NoOffset))) ->
     make ("library variable " ^ vname ^ " satisfies lower bound")

  | PLowerBound (_, CastE(_, Const (CInt (i64, _, _)))) ->
     let addr = i64_to_hex_string i64 in
     let _ =
       chlog#add
         "absolute address pointer"
         (LBLOCK [STR "Lower bound of "; STR addr]) in
     make ("absolute address in memory: " ^ addr)

  | PLowerBound (_, CastE(_, CastE(_, Const (CInt (i64, _, _))))) ->
     let addr = i64_to_hex_string i64 in
     let _ =
       chlog#add
         "absolute address pointer"
         (LBLOCK [STR "Lower bound of "; STR addr]) in
     make ("absolute address in memory: " ^ addr)

  | PLowerBound (_,
                 (AddrOf (Mem (CastE (TPtr _, (Const (CInt (i64, _, _))))), _)) )
       when int64_non_negative i64 ->
     make ("memory mapped i/o at address " ^  (i64_to_hex_string i64))

  | PLowerBound (_, AddrOf (Var _, _))
    | PLowerBound (_, CastE (_,AddrOf (Var _, _)))
    | PLowerBound (_, StartOf (Var _, _))
    | PLowerBound (_, CastE (_, StartOf (Var _, _))) ->
     make "address of a variable"

  | PLowerBound (_, BinOp _)
  | PLowerBound (_, CastE (_, BinOp _))
  | PLowerBound (_, CastE (_, CastE (_, BinOp _))) ->
     make
       ("result of pointer arithmetic is guaranteed to satisfy lowerbound "
        ^ "by inductive hypothesis")

  | PLowerBound (_, e) when is_null_pointer e ->
     make "null pointer does not violate bounds"

  | PLowerBound (_, e) when has_embedded_null_dereference e ->
     make
       ("null pointer cannot be dereferenced; acceptability of null "
        ^ "pointer is checked separately")

  | PUpperBound (_, Lval (Var ((("stdin" | "stdout" | "stderr") as vname), _),
                          NoOffset))
    | PUpperBound (_, CastE (_, Lval
                                  (Var ((("stdin"|"stdout"|"stderr") as vname), _),
                                   NoOffset))) ->
     make ("library variable " ^ vname ^ " satisfies upper bound")

  | PUpperBound (_,e) when is_program_name e ->
     make
       ("validity of pointer to program name is guaranteed by the "
        ^ "operating system")

  | PUpperBound (_, Const (CStr _))
    | PUpperBound (_, CastE (_, Const (CStr _))) ->
     make "constant string is allocated by compiler"

  | PUpperBound (_, BinOp (PlusPI, e1, CnApp ("ntp", [Some e2], _), _))
       when (exp_compare e1 e2) = 0 && is_constant_string e1 ->
     make "constant string is allocated by compiler"

  | PUpperBound (_, Const (CWStr _))
    | PUpperBound (_, CastE (_, Const (CWStr _))) ->
     make "constant wide string is allocated by compiler"

  | PUpperBound (_, e) when is_absolute_memory_address env e ->
     (match get_absolute_memory_address env e with
      | Some s -> make ("absolute address in memory: " ^ s)
      | _ -> ())

  | PUpperBound (_, CastE(_, Const (CInt (i64, _, _)))) ->
     let addr = i64_to_hex_string i64 in
     let _ =
       chlog#add
         "absolute address pointer"
         (LBLOCK [STR "Upper bound of "; STR addr]) in
     make ("absolute address in memory: " ^ addr)

  | PUpperBound (_, CastE(_, CastE(_, Const (CInt (i64, _, _))))) ->
     let addr = i64_to_hex_string i64 in
     let _ =
       chlog#add
         "absolute address pointer"
         (LBLOCK [STR "Upper bound of "; STR addr]) in
     make ("absolute address in memory: " ^ addr)

  | PUpperBound (_,
                 (AddrOf (Mem (CastE (TPtr _, (Const (CInt (i64, _, _))))), _)))
       when int64_non_negative i64 ->
     make ("memory mapped i/o at address " ^ (i64_to_hex_string i64))

  | PUpperBound (_, AddrOf (Var _, _))
    | PUpperBound (_, CastE (_, AddrOf (Var _, _)))
    | PUpperBound (_, StartOf (Var _, _))
    | PUpperBound (_, CastE (_, StartOf (Var _, _))) ->
     make "address of a variable"

  | PUpperBound (_, e) when has_embedded_null_dereference e ->
     make
       ("null pointer cannot be dereferenced; acceptability of null "
        ^ "pointer is checked separately")

  | PUpperBound (_, BinOp (IndexPI,StartOf (Var (_, vid),NoOffset), c, _))
  | PUpperBound (_,BinOp (PlusPI,StartOf (Var (_, vid), NoOffset), c, _)) when
         vid > 0
         && (match get_num_value env c with
             | Some _ -> true | _ -> false) ->
     let vty = fenv#get_type_unrolled (get_varinfo vid).vtype in
     begin
       match vty with
       | TArray (_, Some e, _) ->
	  begin
	    match get_num_value env e with
	    | Some k ->
	       let inc = Option.get (get_num_value env c) in
	       if inc#lt k then
	         make
                   ("offset ("
                    ^ inc#toString
                    ^ ") is less than array size ("
                    ^ k#toString
                    ^ ")")
	       else
	         make_violation
                   ("offset ("
                    ^ inc#toString
                    ^ ") is greater than or equal to array size ("
                    ^ k#toString
                    ^ ")")
	    | _ -> ()
	  end
       | _ -> ()
     end

  | PUpperBound (_, BinOp _) ->
     make
       ("result of pointer arithmetic is guaranteed to satisfy upperbound "
        ^ "by inductive hypothesis")

  | PUpperBound (_, e) when is_null_pointer e ->
     make "null pointer does not violate bounds"

  | PIndexLowerBound e when is_unsigned_integral_type (type_of_exp env e) ->
     make ("unsigned value is always non-negative")

  | PIndexLowerBound (BinOp (BAnd, _, Const (CInt (j64, _, _)), _)) ->
     let mask = mkNumericalFromInt64 j64 in
     if mask#geq numerical_zero then
       make
         ("index value is masked with a non-negative number: "
          ^ mask#toString)
     else
       ()

  | PIndexLowerBound e ->
     begin
       match get_num_value env e with
       | Some i when i#geq numerical_zero ->
	  make ("index value " ^ i#toString ^ " is non-negative")
       | Some i when i#lt numerical_zero ->
	  make_violation ("index value " ^ i#toString ^ " is negative")
       | _ -> ()
     end

  | PIndexUpperBound (BinOp (BAnd, _, Const (CInt (i64, _, _)), _),
                      Const (CInt (j64, _, _))) ->
     let mask = mkNumericalFromInt64 i64 in
     let ub = mkNumericalFromInt64 j64 in
     if mask#lt ub then
       make
         ("index value is masked with "
          ^ mask#toString
          ^ " which is less than the size of the array: "
          ^ ub#toString)
     else
       (* add diagnostic *) ()

  | PIndexUpperBound (e, Const (CInt (j64, _, _))) ->
     let ub = mkNumericalFromInt64 j64 in
     begin
       match get_num_value env e with
       | Some i when i#lt ub ->
	  make
            ("index value "
             ^ i#toString
             ^ " is less than bound "
             ^ ub#toString)
       | Some i when i#geq ub ->
	  make_violation
            ("index value "
             ^ i#toString
             ^ " violates upper bound "
             ^ ub#toString)
       | _ -> ()
    end

  (* CStandard: 6.7.8/10:
     If an object that has static storage duration is not initialized
     explicitly, then:
     - if it has pointer type, it is initialized to a null pointer;
     - if it has arithmetic type, it is initialized to (positive or
         unsigned) zero;
     - if it is an aggregate, every member is initialized (recursively)
         according to these rules;
     - if it is a union, the first named member is initialized
         (recursively) according to these rules.
   *)
  | PInitialized (Var (vname, vid), _)
       when vid > 0 && (env#has_varinfo vid) && (get_varinfo vid).vglob ->
     make (vname ^ " is global")

  | PInitialized (Mem e, NoOffset) when is_absolute_memory_address env e ->
     (match get_absolute_memory_address env e with
      | Some s -> make ("reading global location: " ^ s)
      | _ -> ())

  | PInitialized (Mem (CastE (_, Const (CInt (i64, _, _)))),
                  Field ((fname,_), NoOffset)) ->
     let _ =
       chlog#add
         "reading global memory"
         (LBLOCK [STR "memory region: "; STR (i64_to_hex_string i64)]) in
     make
       ("field "
        ^ fname
        ^ " in global address struct: "
        ^ (i64_to_hex_string i64))

  | PInitialized (Mem (CastE (_, Const (CInt (i64, _, _)))), offset) ->
     let _ =
       chlog#add
         "reading global memory"
         (LBLOCK [STR "memory region: "; STR (i64_to_hex_string i64)]) in
     begin
       match offset with
       | NoOffset ->
          make ("global address region: " ^ (i64_to_hex_string i64))
       | _ ->
          make
            ("global address region: "
             ^ (i64_to_hex_string i64)
             ^ " with offset "
             ^ (p2s (offset_to_pretty offset)))
     end

  | PInitialized (Mem (CastE (_, BinOp (_, Const (CInt (i64, _, _)),e,_))),
                  offset) ->
     let _ =
       chlog#add
         "reading global memory"
         (LBLOCK [
              STR "memory region: ";
              STR (i64_to_hex_string i64);
              STR " with offset ";
              exp_to_pretty e]) in
     begin
       match offset with
       | NoOffset ->
          make
            ("global address region: "
             ^ (i64_to_hex_string i64)
             ^ " with offset "
             ^ (e2s e))
       | _ ->
          make
            ("global address region: "
             ^ (i64_to_hex_string i64)
             ^ " with offset "
             ^ (e2s e)
             ^ " and offset "
             ^ (p2s (offset_to_pretty offset)))
     end

  | PInitialized (Mem
                    (Lval (Var ((("stdin"|"stdout"|"stderr") as vname), _),
                           NoOffset)),
                  NoOffset)
    | PInitialized (Mem
                      (CastE (_,
                              Lval (Var ((("stdin"|"stdout"|"stderr") as vname),_ ),
                                    NoOffset))),
                    NoOffset) ->
     make ("library variable " ^ vname ^ " is guaranteed to be initialized")

  | PInitialized (Mem (AddrOf (Var (vname,vid), _)), _)
    | PInitialized (Mem (CastE (_, AddrOf (Var (vname, vid), _))), _)
       when vid > 0 && (env#has_varinfo vid) && (get_varinfo vid).vglob ->
     make (vname ^ " is global")

  | PInitialized (Mem e, _offset) when is_global_address e ->
     make ("location " ^ (e2s e) ^ " is a global address")

  | PInitialized (Var (vname, vid),_) when env#is_formal vid ->
     make (vname ^ " is a function parameter")

  | PInitialized (Mem e, _)
       when is_null_pointer e || has_embedded_null_dereference e ->
     make
       ("null pointer cannot be dereferenced, and hence target cannot "
        ^ "be initialized "
        ^ "(acceptability of null is checked separately)")

  | PInitialized (Mem e, NoOffset) when is_constant_string e ->
     make ("constant string is guaranteed to have at least one character")

  | PInitializedRange (e, _) when is_program_name e ->
     make
       ("validity of pointer to program name is guaranteed by the "
        ^ "operating system")

  | PInitializedRange (e, _) when is_null_pointer e ->
     make "null pointer does have any range, so this is trivially valid"

  | PInitializedRange (e,_) when has_embedded_null_dereference e ->
    make "embedded null dereference; null dereference is checked separately"

  | PInitializedRange (e1, CnApp ("ntp", [Some e2], _))
      when (exp_compare e1 e2) = 0 && is_constant_string e1 ->
     make ("constant string")

  | PInitializedRange (e1, CnApp ("ntp", [Some e2], _))
       when (exp_compare e1 e2) = 0 && is_constant_wide_string e1 ->
     make ("constant wide string")

  | PInitializedRange (CastE (_, Const (CStr s)), len)
       when (match get_num_value env len with
             | Some _ -> true | _ -> false) ->
     (match get_num_value env len with
      | Some num ->
         let (_, _, strlen) = mk_constantstring s in
         if num#leq (mkNumerical strlen) then
           make
             ("constant string with length "
              ^ (stri strlen)
              ^ " has "
              ^ num#toString
              ^ " initialized bytes")
         else
           make_violation
             ("constant string with length "
              ^ (stri strlen)
              ^ " does not have "
              ^ num#toString
              ^ " initialized bytes")
      | _ -> ())

  | PFormatString (Const (CStr s))
    | PFormatString (CastE (_, Const (CStr s))) ->
     let (s, ishex, len) = mk_constantstring s in
     let ps =
       if ishex || len > 20 then
         (string_of_int len) ^ "-character string"
       else
         s in
     make (ps ^ " is a string literal")

  | PFormatString (Const (CWStr _))
    | PFormatString (CastE (_, Const (CWStr _))) ->
     make "constant wide string"

  | PVarArgs (a,(-1),_) ->
     set_diagnostic ("format string not interpreted: " ^ (e2s a))

  | PVarArgs (a, req_argcount, args) when List.length args = req_argcount ->
     make
       ("actual number of arguments: "
        ^ (stri (List.length args))
        ^ " is equal to expected number of arguments: "
        ^ (stri req_argcount)
        ^ " in formatstring: "
        ^ (e2s a))

  | PVarArgs (a, req_argcount, args)
       when List.length args > req_argcount && req_argcount >= 0 ->
     make
       ("actual number of arguments: "
        ^ (stri (List.length args))
        ^ " is greater than expected number of arguments: "
        ^ (stri req_argcount)
        ^ " in formatstring: "
        ^ (e2s a)
        ^ " (excess arguments are ignored)")

  | PVarArgs (a, req_argcount, args) when List.length args < req_argcount ->
     make_violation
       ("actual number of arguments: "
        ^ (stri (List.length args))
        ^ " is less than expected number of arguments: "
        ^ (stri req_argcount)
        ^ " in formatstring: "
        ^ (e2s a))

  | PNullTerminated (Const (CStr _))
    | PNullTerminated (CastE (_, Const (CStr _))) -> make "string literal"

  | PNullTerminated (Const (CWStr _))
    | PNullTerminated (CastE (_, Const (CWStr _))) -> make "wide string literal"

  | PNullTerminated e when is_program_name e ->
     make
       ("validity of pointer to program name is guaranteed by the "
        ^ "operating system")

  | PNullTerminated e when is_null_pointer e ->
    make "null pointer is not subject to null-termination"

  | PNullTerminated e when has_embedded_null_dereference e ->
     make
       ("null pointer cannot be dereferenced; acceptability of null "
        ^ "pointer is checked separately")

  | PNoOverlap (_, e2) when is_string_literal e2 ->
     make ("one of the addresses is a string literal")

  | PNoOverlap (e1, e2) when is_null_pointer e1 || is_null_pointer e2 ->
     make ("one of the arguments is a null pointer ")

  | PNoOverlap (e1, e2) when (is_stack_address e1) && (is_stack_address e2) ->
     (match (get_stack_address e1, get_stack_address e2) with
      | (Some (vname1, vid1), Some (_, vid2)) when vid1 = vid2 ->
         make_violation ("addresses are of the same stack variable: " ^ vname1)
      | (Some (vname1, _), Some (vname2, _)) ->
         make
           ("addresses of two distinct stack variables: "
            ^ vname1
            ^ " and "
            ^ vname2)
      | _ -> ())

  | PValueConstraint e when has_embedded_null_dereference e ->
     make
       ("embedded null dereference; null dereference is checked separately")

  | PValueConstraint (BinOp (Eq, e1, e2, _)) when (exp_compare e1 e2) = 0 ->
     make ("expressions are equal")

  | PValueConstraint (BinOp (Gt, e1, e2, _)) ->
     begin
       match (get_num_value env e1, get_num_value env e2) with
       | (Some n1, Some n2) when  n1#gt n2 ->
          make
            ("value of "
             ^ (e2s e1)
             ^ ": "
             ^ n1#toString
             ^ " is greater than value of "
             ^ (e2s e2)
             ^ ": "
             ^ n2#toString)
       | _ -> ()
     end

  | PValueConstraint (BinOp (Ge, e1, e2, _)) ->
     begin
       match (get_num_value env e1, get_num_value env e2) with
       | (Some n1, Some n2) when n1#geq n2 ->
          make
            ("value of "
             ^ (e2s e1)
             ^ ": "
             ^ n1#toString
             ^ " is greater than or equal to value of "
             ^ (e2s e2)
             ^ ": "
             ^ n2#toString)
       | _ -> ()
     end

  | PValueConstraint (BinOp (Lt, e1, e2, _)) ->
     begin
       match (get_num_value env e1, get_num_value env e2) with
       | (Some n1, Some n2) when n1#lt n2 ->
          make
            ("value of "
             ^ (e2s e1)
             ^ ": "
             ^ n1#toString
             ^ " is less than value of "
             ^ (e2s e2) ^ ": "
             ^ n2#toString)
       | (Some n1, Some n2) ->
          make_violation
            ("value of "
             ^ (e2s e1)
             ^ ": "
             ^ n1#toString
             ^ " is greater than or equal to the value of "
             ^ (e2s e2)
             ^ ": "
             ^ n2#toString)
       | _ -> ()
     end

  | PValueConstraint (BinOp (Le, e1, e2, _)) ->
     begin
       match (get_num_value env e1, get_num_value env e2) with
       | (Some n1, Some n2) when n1#leq n2 ->
          make
            ("value of "
             ^ (e2s e1)
             ^ ": "
             ^ n1#toString
             ^ " is less than or equal to value of "
             ^ (e2s e2)
             ^ ": "
             ^ n2#toString)
       | _ -> ()
     end

  | PValueConstraint (BinOp (Ne, e1, e2, _)) ->
     begin
       match (get_num_value env e1, get_num_value env e2) with
       | (Some n1, Some n2) when not (n1#equal n2) ->
          make
            ("value of "
             ^ (e2s e1)
             ^ ": "
             ^ n1#toString
             ^ " is not equal to value of "
             ^ (e2s e2)
             ^ ": "
             ^ n2#toString)
       | _ -> ()
     end

  | PControlledResource (_, e)
       when (match get_num_value env e with
             | Some _ -> true | _ -> false) ->
     begin
       match get_num_value env e with
       | Some n -> make ("constant value: " ^ n#toString)
       | _ -> ()
     end

  | _ -> ()
  with CCHFailure pp ->
    begin
      pr_debug [
          STR "Failure in checkvalid of proof obligation ";
          INT ppo#index;
          STR ": ";
          (* po_predicate_to_pretty ppo#get_predicate; *) STR ": ";
          pp;
          NL]
    end


let process_function fname =
  let fundec = read_function_semantics fname in
  List.iter
    (fun p -> check_ppo_validity fname fundec.sdecls p)
    (proof_scaffolding#get_proof_obligations fname)
