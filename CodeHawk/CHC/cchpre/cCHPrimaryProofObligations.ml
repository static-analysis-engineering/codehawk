(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHCommon
open CHPretty

(* chutil *)
open CHLogger
open CHFormatStringParser
open CHUtil

(* xprlib *)
open Xprt

(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHDictionary
open CCHExternalPredicate
open CCHFileContract
open CCHFileEnvironment
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesCompare
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities


(* cchpre *)
open CCHAssignDictionary
open CCHCallsite
open CCHPOPredicate
open CCHPPO
open CCHProofScaffolding
open CCHPreTypes

let cd = CCHDictionary.cdictionary
let fenv = CCHFileEnvironment.file_environment
   
module H = Hashtbl

let createppos = ref true
let set_create_ppos v = createppos := v
                      
let current_function = ref None
let set_current_function f = current_function := Some f
let get_current_function () = match !current_function with Some f -> f | _ ->
  raise (CCHFailure (LBLOCK [ STR "Current function not set" ] ))
let current_loc_to_pretty loc = 
  let fname = (get_current_function ()).svar.vname in
  LBLOCK [ STR " (" ; STR fname ; STR "@" ; INT loc.line ; STR ")" ]
  
  
let add_to_table t name =
  if H.mem t name then
    H.replace t name ((H.find t name) + 1)
  else
    H.add t name 1
  
let missing_summaries = Hashtbl.create 53
let add_missing_summary s = add_to_table missing_summaries s
let reset_missing_summaries () = H.clear missing_summaries
  
let get_missing_summaries () =
  let result = ref [] in
  let _ = H.iter (fun k v -> result := (k,v) :: !result) missing_summaries in
  !result
  
let add_proof_obligation pred loc (ctxt:program_context_int) =
  if !createppos then
    let fname = (get_current_function ()).svar.vname in
    (proof_scaffolding#get_ppo_manager fname)#add_ppo loc ctxt pred

let add_lib_proof_obligation pred loc (ctxt:program_context_int) (libfname:string) (xpred:xpredicate_t) =
  if !createppos then
    let fname = (get_current_function ()).svar.vname in
    (proof_scaffolding#get_ppo_manager fname)#add_lib_ppo loc ctxt pred libfname xpred

let loc_to_pretty (loc:location) = LBLOCK [ STR "line: " ; INT loc.line ]
  
let create_po_dereference add env (context:program_context_int) (e:exp) loc =
  let tgttyp = 
    let t = type_of_exp env e in
    match t with
    | TPtr (tt,_) -> tt
    | _ -> 
      let f = get_current_function () in
      begin
	ch_error_log#add "pointer dereference"
	  (LBLOCK [ STR "Target type of Mem is not a pointer (assigning void*): " ; 
		    typ_to_pretty t ; STR " (" ; exp_to_pretty e ; STR ")" ; 
		    current_loc_to_pretty loc ; STR " in " ; STR f.svar.vname ]) ;
	TVoid []
      end in
  begin
    add (PNotNull e) context;
    add (PValidMem e) context;
    add (PInScope e) context;
    (* add (PTypeAtOffset (tgttyp,e)) ; *)
    add (PLowerBound (tgttyp,e)) context;
    add (PUpperBound (tgttyp,e)) context
  end
    
let rec create_po_lval env (context:program_context_int) ((host,offset):lval) (loc:location) = 
  let add p = add_proof_obligation p loc in
  match host with
  | Var (vname,vid) -> 
     create_po_offset env context#add_var offset (env#get_varinfo_by_vid vid).vtype loc 
  | Mem e ->
     let tgttyp = 
       let t = type_of_exp env e in
       match t with
       | TPtr (tt,_) -> tt
       | _ -> 
          let f = get_current_function () in
          begin
	    ch_error_log#add
              "pointer dereference"
	      (LBLOCK [ STR "Target type of Mem is not a pointer (assigning void*): " ; 
		        exp_to_pretty e ; current_loc_to_pretty loc ; STR " in " ;
		        STR f.svar.vname ]);
	    TVoid []
          end in
     begin
       create_po_exp ~deref:true env context#add_mem e loc ;
       create_po_dereference add env context#add_mem e loc ;
       create_po_offset env context#add_mem offset tgttyp loc
     end
      
and create_po_binop
?(deref=false) env (context:program_context_int) binop e1 e2 t loc  =
  let add p = add_proof_obligation p loc context in
  let addxop p n = add_proof_obligation p loc (context#add_binop n) in
  let are_cast_pointer_types e1 e2 =
    match (e1,e2) with
    | (CastE (_,ee1), CastE (_,ee2)) ->
       (is_pointer_type (type_of_exp env ee1))
       && (is_pointer_type (type_of_exp env ee2))
    | _ -> false in
  match binop with
  | PlusA | MinusA | Mult ->
    begin
      match fenv#get_type_unrolled t with
      | TInt (ik,_) when is_signed_type ik -> 
	begin
	  add (PIntUnderflow (binop,e1,e2,ik))   ;
	  add (PIntOverflow (binop,e1,e2,ik))
	end
      | TInt (ik,_) -> 
	begin
	  add (PUIntUnderflow (binop,e1,e2,ik))   ;
	  add (PUIntOverflow (binop,e1,e2,ik))
	end
      | TFloat _ -> ()
      | _ -> 
	 ch_error_log#add
           "unknown arithmetic type"
	   (LBLOCK [
                exp_to_pretty e1 ; STR (binop_to_print_string binop) ; 
		exp_to_pretty e2 ; STR " : " ; typ_to_pretty t ; STR " " ;
		current_loc_to_pretty loc ])
    end
  | Shiftlt | Shiftrt ->
  (* result is undefined if second operand is negative or if second operand is greater
     than or equal to the width of the first operand, ref. C99:6.5.7(3) *)
    begin 
      match fenv#get_type_unrolled t with
      | TInt (ik,_) ->
         let ty = get_integer_promotion (TInt (ik,[])) (TInt (IInt,[])) in
	 begin
           match ty with
           | TInt (ikp,_) ->
	      addxop (PNonNegative e2) 2 ;
	      addxop (PWidthOverflow (e2, ikp)) 2
           | _ ->
              raise (CCHFailure
                       (LBLOCK [ STR "Unexpected type returned by integer promotions: " ;
                                 typ_to_pretty ty ]))
	 end
      | _ ->
	ch_error_log#add "unknown shift type"
	(LBLOCK [ exp_to_pretty e1 ; STR (binop_to_print_string binop) ; 
		  exp_to_pretty e2 ; STR " : " ; typ_to_pretty t ; STR " " ;
		  current_loc_to_pretty loc ])
    end
  | Div -> 
    begin
      match fenv#get_type_unrolled t with
      | TInt (ik,_) when is_signed_type ik -> 
	begin
	  add (PIntUnderflow (binop,e1,e2,ik)) ;
	  add (PIntOverflow (binop,e1,e2,ik)) ;
	  addxop (PNotZero e2) 2
	end
      | TInt (ik,_) -> 
	begin
	  add (PUIntUnderflow (binop,e1,e2,ik)) ;
	  add (PUIntOverflow (binop,e1,e2,ik)) ;
	  addxop (PNotZero e2) 2
	end
      | TFloat _ -> add (PNotZero e2)
      | _ -> 
	ch_error_log#add "unknown arithmetic type"
	(LBLOCK [ exp_to_pretty e1 ; STR (binop_to_print_string binop) ; 
		  exp_to_pretty e2 ; STR " : " ; typ_to_pretty t ; STR " " ;
		  current_loc_to_pretty loc ])
    end
  | Mod -> addxop (PNotZero e2) 2
  | PlusPI | IndexPI | MinusPI ->
    let exptyp = fenv#get_type_unrolled t in
    let tgttyp = match exptyp with
      | TPtr (tt,_) -> tt
      | _ -> 
	begin 
	  ch_error_log#add "unknown target type in pointer arithmetic"
	  (LBLOCK [ exp_to_pretty e1 ; STR (binop_to_print_string binop) ; 
		    exp_to_pretty e2 ; STR " : " ;
		    typ_to_pretty exptyp ; current_loc_to_pretty loc ]);
	  TVoid [] 
	end in
    begin
      addxop (PNotNull e1) 1 ;
      addxop (PValidMem e1) 1;
      addxop (PInScope e1) 1 ;
      add (PPtrLowerBound (tgttyp, binop, e1, e2)) ;
      add (if deref then 
	  PPtrUpperBoundDeref (tgttyp, binop, e1, e2) 
	else 
	  PPtrUpperBound (tgttyp, binop, e1, e2)) ;
    end
  | MinusPP ->
    let e1typ = fenv#get_type_unrolled (type_of_exp env e1) in
    let e2typ = fenv#get_type_unrolled (type_of_exp env e2) in
    let tgttyp1 = match e1typ with
      | TPtr (tt,_) -> tt
      | _ -> 
	begin 
	  ch_error_log#add "unknown target type in pointer arithmetic"
	  (LBLOCK [ exp_to_pretty e1 ; STR (binop_to_print_string binop) ; 
		    exp_to_pretty e2 ; STR " : " ;
		    typ_to_pretty e1typ ; current_loc_to_pretty loc ]);
	  TVoid [] 
	end in
    let tgttyp2 = match e2typ with
      | TPtr (tt,_) -> tt
      | _ -> 
	begin 
	  ch_error_log#add "unknown target type in pointer arithmetic"
	  (LBLOCK [ exp_to_pretty e1 ; STR (binop_to_print_string binop) ; 
		    exp_to_pretty e2 ; STR " : " ;
		    typ_to_pretty e1typ ; current_loc_to_pretty loc ]);
	  TVoid [] 
	end in
    let _ = if (typ_compare tgttyp1 tgttyp2) = 0 then () else
	ch_error_log#add "different pointer target types in subtraction"
	  (LBLOCK [ exp_to_pretty e1 ; STR ": " ; typ_to_pretty tgttyp1 ; STR "; " ;
		    exp_to_pretty e2 ; STR ": " ; typ_to_pretty tgttyp2 ; 
		    current_loc_to_pretty loc ]) in
    begin
      addxop (PNotNull e1) 1 ;
      addxop (PNotNull e2) 2 ;
      addxop (PValidMem e1) 1 ;
      addxop (PValidMem e2) 2 ;
      addxop (PInScope e1) 1 ;
      addxop (PInScope e2) 2 ;
      add (PCommonBase (e1,e2)) ;
      add (PCommonBaseType (e1,e2)) ;
    end
  | Lt | Gt | Le | Ge when is_pointer_type t ->
    begin
      addxop (PNotNull e1) 1 ;
      addxop (PNotNull e2) 2 ;
      addxop (PValidMem e1) 1 ;
      addxop (PValidMem e2) 2 ;
      addxop (PInScope e1) 1 ;
      addxop (PInScope e2) 2 ;
      add (PCommonBase (e1,e2))
    end
  | Lt | Gt | Le | Ge when are_cast_pointer_types e1 e2 ->
     begin
       match (e1,e2) with
       | (CastE (_,ee1), CastE (_,ee2)) ->
          begin
            addxop (PNotNull ee1) 1 ;
            addxop (PNotNull ee2) 2 ;
            addxop (PValidMem ee1) 1 ;
            addxop (PValidMem ee2) 2 ;
            addxop (PInScope ee1) 1 ;
            addxop (PInScope ee2) 2 ;
            add (PCommonBase (ee1,ee2))
          end
       | _ ->
          raise (CCHFailure
                   (LBLOCK [ STR "Internal error in creating primary proof obligations" ]))
     end
  | _ -> ()
    
and create_po_exp ?(deref=false) env (context:program_context_int) (x:exp) (loc:location) =
  let has_struct_type vid =
    let vinfo = env#get_varinfo_by_vid vid in
    match fenv#get_type_unrolled vinfo.vtype with
    | TComp _ -> true | _ -> false in
  let add p = add_proof_obligation p loc context in
  let add_int_cast (ikfrom:ikind) (ikto:ikind) (e:exp) =
    if ikfrom = ikto then
      ()
    else if is_signed_type ikfrom && is_signed_type ikto then
      begin
        add (PSignedToSignedCastLB (ikfrom,ikto, e)) ;
        add (PSignedToSignedCastUB (ikfrom,ikto, e))
      end
    else if is_signed_type ikfrom && is_unsigned_type ikto then
      begin
        add (PSignedToUnsignedCastLB (ikfrom,ikto, e)) ;
        add (PSignedToUnsignedCastUB (ikfrom,ikto, e))
      end
    else if is_unsigned_type ikfrom && is_signed_type ikto then
      add (PUnsignedToSignedCast (ikfrom, ikto, e))
    else
      add (PUnsignedToUnsignedCast (ikfrom, ikto, e)) in
   match x with
   | Const c -> ()
   | Lval (Var (vname,vid),NoOffset) when has_struct_type vid ->
      let vinfo = env#get_varinfo_by_vid vid in
      begin
        match fenv#get_type_unrolled vinfo.vtype with
        | TComp (tckey,_) ->
           let cinfo = fenv#get_comp tckey in
           begin
             List.iter (fun f ->
                 add (PInitialized (Var (vname,vid),Field ((f.fname,f.fckey),NoOffset))))
                       cinfo.cfields ;
             create_po_lval env context#add_lval (Var (vname,vid),NoOffset) loc
           end
        | _ -> ()
      end
  | Lval lval -> 
    begin
      add (PInitialized lval) ;
      create_po_lval env context#add_lval lval loc
    end
  | SizeOf _ -> ()
  | SizeOfE _ -> ()   (* expression is not evaluated ; only its type is determined *) 
  | SizeOfStr _ -> ()
  | AlignOf _ -> ()
  | AlignOfE _ -> ()
  | UnOp (unop,e,t) -> create_po_exp env context#add_unop e loc
  | BinOp (binop,e1,e2,t) -> 
    begin 
      create_po_exp ~deref env (context#add_binop 1) e1 loc ; 
      create_po_exp ~deref env (context#add_binop 2) e2 loc ;
      create_po_binop ~deref env context binop e1 e2 t loc
    end
  | Question (e1,e2,e3,t) -> 
    begin 
      create_po_exp env (context#add_question 1) e1 loc; 
      create_po_exp env (context#add_question 2) e2 loc ; 
      create_po_exp env (context#add_question 3) e3 loc 
    end
  | CastE (t,e) -> 
    let exptyp = fenv#get_type_unrolled (type_of_exp env e) in
    let tgttyp = fenv#get_type_unrolled t in
    let _ =
      match (exptyp,tgttyp)  with
      | (TInt (ik1,_), TInt (ik2,_)) -> add_int_cast ik1 ik2 e
      | (TPtr (tt1,_), TPtr (tt2,_)) -> add (PPointerCast (tt1,tt2,e))  (* may need additional int cast *)
      | _ -> add (PCast (exptyp, tgttyp, e)) in
    create_po_exp ~deref env context#add_cast e loc
  | AddrOf l -> create_po_lval env context#add_addrof l loc
  | AddrOfLabel _ -> ()
  | StartOf l -> create_po_lval env context#add_startof l loc
  | FnApp _ | CnApp _ -> ()
    
and create_po_offset env (context:program_context_int) (o:offset) (hosttyp:typ) (loc:location) = 
  let add p = add_proof_obligation p loc context in
  match o with
  | NoOffset -> ()
  | Field ((fname,ckey),oo) ->
    begin
      match fenv#get_type_unrolled hosttyp with
      | TComp (tckey,_) -> 
	if tckey = ckey then
	  let ftype = fenv#get_field_type ckey fname in
	  create_po_offset env (context#add_field_offset fname) oo ftype loc
	else
	  ch_error_log#add "field offset: mismatch in host type key and field key"
	    (LBLOCK [ STR "Field key: " ; INT ckey ; STR "; host key: " ; INT tckey ;
		      current_loc_to_pretty loc ])
      | _ -> 
	ch_error_log#add "field offset: host type is not a struct"
	  (LBLOCK [ STR "Field: " ; STR fname ; STR "; host type: " ; 
		    typ_to_pretty hosttyp ; current_loc_to_pretty loc ])
    end
  | Index (exp,oo) ->
    begin
      match fenv#get_type_unrolled hosttyp with
      | TArray (tt,Some len,_) ->
	begin
	  add (PIndexLowerBound exp) ;
	  add (PIndexUpperBound (exp,len)) ;
	  create_po_exp env context#add_index exp loc ;
	  create_po_offset env context#add_index_offset oo tt loc
	end
      | TArray (tt,_,_) -> 
	ch_error_log#add "array without length"
	  (LBLOCK [ offset_to_pretty o ; STR " on " ; typ_to_pretty hosttyp ; 
		    current_loc_to_pretty loc ])
      | _ -> 
	ch_error_log#add "index of non-array type" 
	  (LBLOCK  [ offset_to_pretty o ; STR " on " ; typ_to_pretty hosttyp ; 
		    current_loc_to_pretty loc ])
    end
      
and create_po_dereference_range add env (context:program_context_int) (base:exp) (len:exp)
(loc:location) =
  let add p = add p context in
  let tgttyp = 
    let t = type_of_exp env base in
    match t with
    | TPtr (tt,_) -> tt
    | _ -> 
      begin 
	ch_error_log#add "pointer dereference"
	  (LBLOCK [ STR "Target type of Mem is not a pointer: " ; 
		    typ_to_pretty t ; current_loc_to_pretty loc ]) ; 
	   TVoid [] 
      end in
  begin
    add (PNotNull base) ;
    add (PValidMem base) ;
    add (PInScope base) ;
		(* add (PTypeAtOffset (tgttyp,base)) ; *)
    add (PLowerBound (tgttyp,base)) ;
    add (PPtrUpperBoundDeref (tgttyp,PlusPI,base,len)) 
  end
    
and create_po_dereference_range_read add env
  (context:program_context_int)
  (base:exp) (len:exp) (loc:location) =
  begin
    create_po_dereference_range add env context#add_deref_read base len loc ;
    add (PInitializedRange (base,len)) context
  end

(* get_arg retrieves the argument that corresponds to the term given in the
   function summary spec. In the process of retrieving the argument it may
   generate proof obligations for sub-expressions; these predicates are returned
   with the argument.
   Returns:
      (list of predicates, argument expr, argument indices)
 *)
and get_arg env (s:s_term_t) (args:exp list) =
  match s with
  | ArgValue (ParFormal i,ArgNoOffset) ->
     if List.length args >= i then
       ([],List.nth  args (i-1),[i])
     else
       raise (CCHFailure (LBLOCK [ STR "Expected at least " ; INT i ;
                                   STR " arguments, but found " ;
                                   INT (List.length args) ]))
  | NumConstant i -> ([],Const (CInt64 (Int64.of_string i#toString,IInt,None)),[])
  | NamedConstant s -> ([],CnApp (s,[],TInt (IInt,[])),[])
  | ArgAddressedValue (ptr,ArgNoOffset) -> 
    let (p,a,i) = get_arg env ptr args in 
    let t = type_of_exp env a in
    let expp = [ PLowerBound (t, a) ; PUpperBound (t, a) ] in
    (p @ expp,Lval (Mem a,NoOffset),i)
  | ArgNullTerminatorPos arg -> 
    let (p,a,i) = get_arg env arg args in
    (p,CnApp ("ntp", [ Some a ], TInt (IInt,[])),i)
  | ArithmeticExpr (op,arg1,arg2) -> 
    let get_kind e = match type_of_exp env e with TInt (ik,_) -> ik | _ ->
      raise (CCHFailure (LBLOCK [ STR "Unexpected type in get_kind " ; 
				  typ_to_pretty (type_of_exp env e) ])) in
    let (p1,a1,i) = get_arg env arg1 args in
    let (p2,a2,j) = get_arg env arg2 args in
    let t = type_of_exp env a1 in
    let expp = if is_pointer_type t then
	let destType = type_of_tgt_exp env a1 in
	[ PPtrLowerBound (destType,op,a1,a2) ;
	  PPtrUpperBoundDeref (destType,op,a1,a2) ]
      else
	let k = get_kind a1 in
        if is_signed_type k then
	  [ PIntUnderflow (op,a1,a2,k) ; PIntOverflow (op,a1,a2,k) ]
        else
	  [ PUIntUnderflow (op,a1,a2,k) ; PUIntOverflow (op,a1,a2,k) ] in            
    (p1 @ p2 @ expp, BinOp (op,a1,a2,type_of_exp env a1),i@j)
  | RuntimeValue -> ([],CnApp ("runtime-value",[],TInt (IInt,[])),[])
  | _ -> 
    raise (CCHFailure (LBLOCK [ STR "Argument " ; 
				s_term_to_pretty s ; STR " not recognized"]))

and get_input_format_proofobligations env argspec arg =
  let argtype = type_of_exp env arg in
  let get_po (argtype:typ) (tgttype:typ) =
    match argtype with
    | TPtr (ty,_) ->  PPointerCast (ty,tgttype,arg)
    | _ -> PFormatCast (argtype,TPtr (tgttype,[]) ,arg) in
  if argspec#is_scanset then  (* TBD: add user bound *)
    [ get_po argtype (TInt (IChar,[])) ; PNotNull arg ]
  else
    let conversion = argspec#get_conversion in
    match conversion with
    | IntConverter | DecimalConverter ->
       if argspec#has_lengthmodifier then
         match argspec#get_lengthmodifier with
         | CharModifier ->
            [ get_po argtype (TInt (ISChar,[])) ; PNotNull arg  ]
         | ShortModifier ->
            [ get_po argtype (TInt (IShort, [])) ; PNotNull arg ]
         | LongModifier ->
            [ get_po argtype  (TInt (ILong, [])) ; PNotNull arg  ]
         | LongLongModifier ->
            [ get_po argtype (TInt (ILongLong, [])) ; PNotNull arg ]
         | IntMaxModifier | SizeModifier | PtrDiffModifier ->
            [ get_po argtype (TInt (ILong, [])) ; PNotNull arg ]    (* check; may not be correct *)
         | _ ->
            begin
              ch_error_log#add "format arguments"
                               (LBLOCK [ STR "Length modifier does not apply" ]) ;
              []
            end
       else
           [ get_po argtype (TInt (IInt,[])) ; PNotNull arg ]
    | UnsignedOctalConverter
      | UnsignedDecimalConverter
      | UnsignedHexConverter _ ->
       [ get_po argtype (TInt (IUInt,[])) ; PNotNull arg ]
    | FixedDoubleConverter _
      | ExpDoubleConverter _
      | FlexDoubleConverter _
      | HexDoubleConverter _ ->
       [ get_po argtype (TFloat (FFloat,[])) ; PNotNull arg ]
    | UnsignedCharConverter ->
       if argspec#has_lengthmodifier then
         match argspec#get_lengthmodifier with
         | LongModifier | LongLongModifier ->
            begin
              match argspec#get_fieldwidth with
              | FieldwidthConstant i ->
                 let len = Const (CInt64 (Int64.of_int i,IInt,None)) in
                 [ get_po argtype (TInt (IUShort,[])) ; PNotNull arg ;
                   PPtrUpperBound (TInt (IUShort,[]), PlusPI,arg,len) ]
              | _ ->  (* TBD: add user bound *)
                 [ get_po argtype (TInt (IUShort,[])) ; PNotNull arg ]
            end
         | _ ->
            if argspec#has_fieldwidth then
              match argspec#get_fieldwidth with
              | FieldwidthConstant i ->
                 let len = Const (CInt64 (Int64.of_int i,IInt,None)) in
                 [ get_po argtype (TInt (IChar,[])) ; PNotNull arg ;
                   PPtrUpperBound (TInt (IChar,[]), PlusPI,arg,len) ]
              | _ -> (* TBD: add user bound *)
                 [ get_po argtype (TInt (IChar,[])) ; PNotNull arg ]
            else
              []    (* TBD: check *)
       else
         if  argspec#has_fieldwidth then
           match argspec#get_fieldwidth with
           | FieldwidthConstant i ->
              let len = Const (CInt64 (Int64.of_int i,IInt,None)) in
              [ get_po argtype (TInt (IChar,[])) ; PNotNull arg ;
                PPtrUpperBound (TInt (IChar,[]), PlusPI,arg,len) ]
           | _ -> (* TBD: add user bound *)
              [ get_po argtype (TInt (IChar,[])) ; PNotNull arg ]
         else
           []   (*  TBD: check *)
    | StringConverter ->
       begin (* TBD: add user bound *)
         if argspec#has_lengthmodifier then
           match argspec#get_lengthmodifier with
           | LongModifier | LongLongModifier ->
              [ get_po argtype (TInt (IUShort,[])) ; PNotNull arg ]
           | _ ->
              [ get_po argtype (TInt (IChar,[])) ; PNotNull arg ]
         else
           [ get_po argtype (TInt (IChar,[])) ; PNotNull arg ]
       end
    | PointerConverter ->  (* TBD: add user bound *)
       [ get_po argtype (TPtr (TVoid [],[])) ; PNotNull arg ]
    | OutputArgument ->
       [ get_po argtype (TInt (IInt,[])) ; PNotNull arg ]
      
and get_output_format_proofobligations env argspec arg =
  let conversion = argspec#get_conversion in
  let argtype = type_of_exp env arg in
  let get_int_cast (ikfrom:ikind) (ikto:ikind) (e:exp) =
    if ikfrom = ikto then
      []
    else if is_signed_type ikfrom && is_signed_type ikto then
      [ PSignedToSignedCastLB (ikfrom,ikto, e) ;
        PSignedToSignedCastUB (ikfrom,ikto, e) ]
    else if is_signed_type ikfrom && is_unsigned_type ikto then
       [ PSignedToUnsignedCastLB (ikfrom,ikto, e) ;
         PSignedToUnsignedCastUB (ikfrom,ikto, e) ]
    else if is_unsigned_type ikfrom && is_signed_type ikto then
      [ PUnsignedToSignedCast (ikfrom, ikto, e) ]
    else
      [ PUnsignedToUnsignedCast (ikfrom, ikto, e) ] in
  let get_po ty2 =
    match (argtype, ty2) with
    | (TInt (ik1,_), TInt (ik2,_)) -> get_int_cast ik1 ik2 arg
    | _ -> [ PFormatCast (argtype, ty2, arg) ] in
  match conversion with
  | IntConverter | DecimalConverter ->
     if argspec#has_lengthmodifier then
       match argspec#get_lengthmodifier with
       | CharModifier -> get_po (TInt (ISChar,[]))
       | ShortModifier -> get_po (TInt (IShort, []))
       | LongModifier -> get_po (TInt (ILong, []))
       | LongLongModifier -> get_po (TInt (ILongLong, []))
       | IntMaxModifier | SizeModifier | PtrDiffModifier ->
          get_po (TInt (ILong, []))     (* check; may not be correct *)
       | _ ->
          begin
            ch_error_log#add "format arguments"
                             (LBLOCK [ STR "Length modifier does not apply" ]) ;
            []
          end
     else
       [ PFormatCast (argtype, TInt (IInt, []), arg) ]
  | UnsignedOctalConverter
    | UnsignedDecimalConverter
    | UnsignedHexConverter  _ ->
     if argspec#has_lengthmodifier then
       match argspec#get_lengthmodifier with
       | CharModifier -> get_po (TInt (IUChar,[]))
       | ShortModifier -> get_po (TInt (IUShort, []))
       | LongModifier -> get_po (TInt (IULong, []))
       | LongLongModifier -> get_po (TInt (IULongLong, []))
       | IntMaxModifier | SizeModifier | PtrDiffModifier ->
          get_po (TInt (IULong, []))    (* check; may not be correct *)
       | _ ->
          begin
            ch_error_log#add "format arguments"
                             (LBLOCK [ STR "Length modifier does not apply" ]) ;
            []
          end
     else
       [ PFormatCast (argtype, TInt (IUInt, []), arg) ]
  | FixedDoubleConverter _
    | ExpDoubleConverter _
    | FlexDoubleConverter _
    | HexDoubleConverter _ ->
     if argspec#has_lengthmodifier then
       match argspec#get_lengthmodifier with
       | LongDoubleModifier -> get_po ( TFloat (FLongDouble, []))
       | _ ->
          begin
            ch_error_log#add "format arguments"
                             (LBLOCK [ STR "length modifier does not apply" ]) ;
            []
          end
     else
       [ PFormatCast(argtype, TFloat (FDouble, []), arg) ]
  | UnsignedCharConverter -> get_po ( TInt (IUChar, []))
  | StringConverter ->
     if is_pointer_type argtype then
       let argptrtotype = get_pointer_expr_target_type env arg in
       let lenarg = CnApp ("ntp", [ Some arg ], TInt (IInt,[])) in  (* TBD: may have precision *)
       let dsttype = TInt (IChar, []) in
       let ptrcast = PPointerCast(argptrtotype, dsttype, arg) in
       let notnull = PNotNull arg in
       let nullterminated = PNullTerminated arg in
       let ptrupperbound = PPtrUpperBound(dsttype, PlusPI, arg, lenarg) in
       let initializedrange = PInitializedRange (arg, lenarg) in
       [ ptrcast ; notnull ; nullterminated ; ptrupperbound ; initializedrange ]
     else
       let dsttype = TPtr (TInt (IChar, []),[]) in
       let cast = PFormatCast(argtype,dsttype,arg) in
       begin
         ch_error_log#add "format arguments"
                          (LBLOCK [ STR "string argument is not a pointer type" ]) ;
         [ cast ]
       end
  | PointerConverter ->
     if is_pointer_type argtype then
       let argptrtotype = get_pointer_expr_target_type env arg in
       [ PPointerCast (argptrtotype, TVoid [], arg) ]
     else
       begin
         ch_error_log#add "format arguments"
                          (LBLOCK [ STR "pointer argument is not a pointer type" ]) ;
         []
       end
  | OutputArgument ->
     if is_pointer_type argtype then
       let argptrtotype = get_pointer_expr_target_type env arg in
       let ptrcast = PPointerCast (argptrtotype, TInt (IInt, []), arg) in
       let notnull = PNotNull arg in
       [ ptrcast ; notnull ]
     else
       begin
         ch_error_log#add "format arguments"
                          (LBLOCK [ STR "output argument is not a pointer type" ]) ;
         []
       end

and get_format_spec (args:exp list) (index:int) (isinput:bool) =
  if List.length args >= index then
    let fmtstring = List.nth args (index - 1) in
    match fmtstring with
    | Const (CStr s)
      | CastE (_,Const (CStr s)) ->
       let (str,ishex,len) = mk_constantstring s in
       if ishex then
         begin
           ch_error_log#add
             "format string"
             (LBLOCK [ STR "Encountered format string with " ;
                       STR "control characters (length: " ;
                       INT len ; STR ")" ]) ;
           None
         end
       else
         begin
           try
             Some (parse_formatstring str isinput)
           with
             CHFailure p ->
             begin
               ch_error_log#add
                 "format string"
                 (LBLOCK [ STR "Unable to parse format string: " ;
                           STR str ; STR ": " ; p ]) ;
               None
             end
         end
    | _ ->
       begin
         ch_error_log#add
           "format string"
           (LBLOCK [ STR "Format string is not a constant string: " ;
                     exp_to_pretty fmtstring ]) ;
         None
       end
  else
    begin
      ch_error_log#add
        "format arguments"
        (LBLOCK [ STR "Format argument not found in arguments" ]) ;
      None
    end

and get_formatargs_po env (args:exp list) (index:int) (isinput:bool) =
  match get_format_spec args index isinput with
  | Some fmtspec ->
     let argspecs = fmtspec#get_arguments in
     begin
       match get_slice args index (List.length argspecs) with
       | Some fmtargs ->
          let pv = (List.length argspecs, fmtargs) in
          let argspecs = List.mapi (fun i a -> (i+index,a)) argspecs in
          let args_pos =
            List.map2 (fun (i,argspec) arg ->
                let pfmt =
                  if isinput then
                    get_input_format_proofobligations env argspec arg
                  else
                    get_output_format_proofobligations env argspec arg in
                (i,pfmt)) argspecs fmtargs in
          (pv, args_pos)
       | _ ->
          let fmtargs = list_suffix index args in
          begin
            ch_error_log#add
              "format arguments"
              (LBLOCK [ STR "Expected number of arguments: " ;
                        INT (List.length argspecs) ;
                        STR "; actual number of arguments: " ;
                        INT ((List.length args) - index) ;
                        STR " for format string " ;
                        fmtspec#toPretty ; STR " at index " ; INT index ]) ;
            ((List.length argspecs,fmtargs),[])
          end
     end
  | _ ->
     ((-1,[]),[])
              

(* ---------------------------------------------------------------------
 * The preconditions PreDerefRead and PreDerefWrite denote minimum
 * required buffer sizes. These are converted into proof obligations
 * of type PLowerBound and PPtrUpperBound. Although the intention
 * is to dereference the buffer, we can use PPtrUpperBound instead of
 * PPtrUpperBoundDeref, because indicating a buffer size of n indicates
 * to the receiver that it can access the buffer up to element n-1 and
 * iterate to element n, which is represented by PPtrUpperBound.
 * --------------------------------------------------------------------- *)
and get_precondition_po_predicates env pre args (context:program_context_int) loc =
  let get_tgttyp e = 
    try
     type_of_tgt_exp env e
    with
      CCHFailure p ->
      begin 
	ch_error_log#add "precondition pointer dereference"
	  (LBLOCK [ STR "Target type is not a pointer: " ; p  ;
		    current_loc_to_pretty loc ]);
	TVoid [] 
      end  in
  let geta t = get_arg env t args in
  let addx argslist predicatelist =
    let x = match argslist with
      | [] -> context
      | [ i ] -> context#add_arg i
      | l -> context#add_args l in
    List.map (fun p -> (x,p)) predicatelist in
  let rec get_suffix l i = if i <= 0 then l else get_suffix (List.tl l) (i-1) in
  try
    match pre with
    | XNotNull s -> let (p,a,i) = geta s in addx i (p @ [ PNotNull a ])
    | XNull s -> let (p,a,i) = geta s in addx i (p @ [ PNull a ])
    | XControlledResource (r,s) ->
       let (p,a,i) = geta s in addx i (p  @ [ PControlledResource (r,a) ])
    | XBuffer (dest,IndexSize (NumConstant numerical_one)) ->
      let (p,destArg,i) = geta dest in
      addx i p
    | XBuffer (dest,FormattedOutputSize arg) ->
       let (p1,destArg,i1) = geta dest in
       let (p2,fmtArg,i2) = geta arg in
       let destType = get_tgttyp destArg in
       let fmtargs =
         match i2 with
         | [index] -> List.map (fun a -> Some a) (get_suffix args (index-1))
         | _ -> [] in
       let lenArg = CnApp ("formatted-output-size", fmtargs , TInt (IInt,[])) in
       (addx i1 p1) @ (addx i2 p2) @
          (addx i1 [ PPtrUpperBound (destType, PlusPI,destArg,lenArg)])
    | XBuffer (dest,IndexSize (ArgNullTerminatorPos arg)) ->
      let (p1,destArg,i1) = geta dest in
      let (p2,strArg,i2) = geta arg in
      let destType = get_tgttyp destArg in
      let lenArg = CnApp ("ntp", [ Some strArg ], TInt (IInt,[])) in
      (addx i1 p1) @ (addx i2 p2) @
        (addx i1[ PPtrUpperBound (destType,PlusPI,destArg,lenArg)])
    | XBuffer (dest,IndexSize len) -> 
      let (p1,destArg,i1) = geta dest in
      let (p2,len,i2) = geta len in
      let destType = get_tgttyp destArg in
      (addx i1 p1) @ (addx i2 p2) @
        (addx i1 [ PPtrUpperBound (destType,PlusPI,destArg,len) ])
    | XBuffer (dest,ByteSize len) 
    | XBuffer (dest,len) ->
      let (p1,destArg,i1) = geta dest in
      let (p2,len,i2) = geta len in
      let destType = get_tgttyp destArg in
      (addx i1 p1) @ (addx i2 p2) @
        (addx i1 [ PPtrUpperBound (destType,PlusPI,destArg,len) ])
    | XRevBuffer (dest,xlen) ->
       let (p1,destArg,i1) = geta dest in
       let (p2,len,i2) = geta xlen in
       let destType = get_tgttyp destArg in
       (addx i1 p1)  @  (addx i2 p2)  @
           (addx i1 [ PPtrLowerBound (destType,MinusPI,destArg,len) ])
    | XInitializedRange (dest,IndexSize (ArgNullTerminatorPos s)) ->
      let (p,destArg,i) = geta dest in
      let lenArg = CnApp ("ntp", [ Some destArg ],TInt (IInt,[])) in
      let destType = get_tgttyp destArg in
      addx i (p @ [ PNullTerminated destArg ;
	              PPtrUpperBound (destType,PlusPI,destArg,lenArg) ;
	              PInitializedRange (destArg,lenArg) ])
    | XInitializedRange (dest,IndexSize (NumConstant numerical_one)) ->
      let (p,destArg,i) = geta dest in
      addx i (p @ [ PInitialized ((Mem destArg,NoOffset)) ])
    | XInitializedRange (dest,IndexSize len) ->
      let (p1,destArg,i1) = geta dest in
      let (p2,len,i2) = geta len in
      let destType = get_tgttyp destArg in
      (addx i1 p1) @ (addx i2 p2) @
        (addx i1 [ PPtrUpperBound (destType,PlusPI,destArg,len) ;
		   PInitializedRange (destArg,len) ])
    | XInitializedRange (dest,ByteSize len)
    | XInitializedRange (dest,len) ->
      let (p1,destArg,i1) = geta dest in
      let (p2,len,i2) = geta len in
      let destType = get_tgttyp destArg in
      let typesize = size_of_type env destType in
      begin
        match typesize with
        | XConst (IntConst n) ->
           let tlen =
             BinOp (Div, len, Const (CInt64 (Int64.of_string n#toString, IUInt,None)),
                    TInt (IUInt,[])) in
           (addx i1 p1) @ (addx i2 p2) @
             (addx i1 [ PPtrUpperBound (destType,PlusPI,destArg,tlen) ;
		        PInitializedRange (destArg,len) ])
        |  _  ->
           (addx i1 p1) @ (addx i2 p2) @
             (addx i1 [ PPtrUpperBound (destType,PlusPI,destArg,len) ;
		        PInitializedRange (destArg,len) ])
      end
    | XAllocationBase s -> 
      let (p,a,i) = geta s in (addx i (p @ [ PAllocationBase a ]))
    | XNoOverlap (s1,s2) -> 
      let (p1,a1,i1) = geta s1 in
      let (p2,a2,i2) = geta s2 in
      ((addx i1 p1) @ (addx i2 p2) @ (addx (i1 @ i2) [ PNoOverlap (a1,a2) ]))
    | XInputFormatString s ->
       let (p,a,i) = geta s in
       begin
         match i with
         | [ index ] ->
            let ((argc,fmtargs),pf) = get_formatargs_po env args index true in
            let pv = PVarArgs (a,argc,fmtargs) in
            (addx i (p @ [ pv ; PFormatString a ])) @
              (List.concat (List.map (fun (i,pl) -> addx [i] pl) pf))
         | _ ->
            let pf = PFormatString a in
            let pv = PVarArgs (a,-1,[]) in
            (addx i [ pv ; pf ])
       end
    | XOutputFormatString s ->
       let (p,a,i) = geta s in
       begin
         match i with
         | [ index ] ->
            let ((argc,fmtargs),pf) = get_formatargs_po env args index false in
            let pv = PVarArgs (a,argc,fmtargs) in
            (addx i (p @ [ pv ; PFormatString a ])) @
              (List.concat (List.map (fun (i,pl) -> addx [i] pl) pf))
         | _ ->
            let pf = PFormatString a in
            let pv = PVarArgs (a,-1,[]) in
            (addx i [ pv ; pf ])
       end
    | XRelationalExpr (op,s1,s2) -> 
      let (p1,a1,i1) = geta s1 in
      let (p2,a2,i2) = geta s2 in
      ((addx i1 p1) @ (addx i2 p2) @
         (addx (i1 @ i2) [ PValueConstraint (BinOp (op,a1,a2,TInt (IBool,[]))) ]))
    | _ -> []
  with
  | CCHFailure p -> 
    begin 
      ch_error_log#add "f-pre" (LBLOCK [ p ; current_loc_to_pretty loc ]); 
      [] 
    end
    
and create_po_precondition env
  (context:program_context_int)
  (fs:function_summary_t)
  (el:exp list)
  (loc:location) = 
  let add pred pre ctxt = add_lib_proof_obligation pred loc ctxt fs.fs_fname pre in
  let get_name par = let (n,_) = (List.find (fun (_,i) -> i = par) fs.fs_params) in n in
  List.iter (fun (pre,_) ->              (* TBD: make use of precondition annotation *)
    let parameters = get_xpredicate_parameters pre in
    let (_,args) = List.fold_left (fun (c,acc) e -> 
      if List.mem c parameters then 
	(c+1,(e,c,get_name c) :: acc) 
      else 
	(c+1,acc)) (1,[]) el in
    let predicates = get_precondition_po_predicates env pre el context loc in
    match predicates with
    | [] ->
    (* add (PPre (pre,args)) context *)
       ch_error_log#add
         "precondition"
         (LBLOCK [ STR "No representation for precondition " ;
                   xpredicate_to_pretty pre ;
                   pretty_print_list
                     args
                     (fun (e,_,s) -> LBLOCK [ STR s ; STR ":" ; exp_to_pretty e ])
                     "(" "," ")" ])
    | _ -> List.iter
             (fun (ctxt,p) ->
               add p pre ctxt) predicates) 
    fs.fs_preconditions

let rec create_po_stmtkind env (context:program_context_int) (k:stmtkind) =
  match k with
  | Instr l -> List.iteri (fun i instr -> create_po_instr env (context#add_instr i) instr) l
  | Return (e,loc) -> create_po_return env context e loc
  | ComputedGoto (e,loc) -> create_po_computed_goto env context e loc
  | If (e,thenblock,elseblock,loc) -> create_po_if env context e thenblock elseblock loc
  | Switch (e,b,_,loc) -> create_po_switch env context e b loc
  | Loop (b,loc,_,_) -> create_po_loop env context#add_loop b loc
  | Block b -> create_po_block env context b
  | Goto _ | Break _ | Continue _ -> ()
  | TryFinally _ -> 
    pr_debug [ STR "Proof obligations for TryFinally currently not supported" ; NL ]
  | TryExcept _ -> 
    pr_debug [ STR "Proof obligations for TryExcept currently not supported" ; NL ]
    
and create_po_instr env (context:program_context_int) (i:instr) = 
  match i with
  | Set (lval,e,loc) -> create_po_assignment env context lval e loc
  | Call (optLval,e,el,loc) -> create_po_call env context optLval e el loc
  | Asm (_,templates,asmoutputs,asminputs,_,loc) ->
     let noutputs = List.length asmoutputs in
     let ninputs = List.length asminputs in
     begin
       chlog#add "assembly code"
                 (LBLOCK [ STR (String.concat "; " (List.map cd#get_string templates)) ;
                           STR " (outputs: " ;  INT noutputs ; STR "; inputs: " ;
                           INT ninputs ; STR ")" ]) ;
       List.iter (fun (_,_,lval) ->
           create_po_lval env context#add_lhs lval loc) asmoutputs ;
       List.iter (fun (_,_,exp) ->
           create_po_exp ~deref:true env context#add_rhs exp loc) asminputs ;
     end
    
(* require valid lower and upper bound for global variables that are pointers, 
   so these properties can be assumed when these variables are used; idem for
   field assignments.
   require validmem for all pointer values being assigned (similar to requiring
   validmem for function arguments. 
   require null-termination for all pointer-to-char values being assigned.

   Require global memory (not stack-allocated) addresses for all pointers that are
   assigned to global variables or field expressions, as part of the inductive
   hypothesis that stack addresses do not escape their scope. Note that this requirement
   is too strong in general, since it may be okay to assign these values as long
   as they don't escape, but it seems good coding practice to enforce this anyway
   and is probably satisfied in the majority of cases.

   Note that it is not sound to assume that these values are still valid mem or
   null-terminated when they are used, because these are properties of the 
   pointed-to object, which may be changed independently later by aliases.
*)
and create_po_assignment env (context:program_context_int) (lval:lval) (e:exp) (loc:location) = 
  let add p context = add_proof_obligation p loc context in
  let is_field_assignment = is_field_offset (snd lval) in
  let fname = (get_current_function ()).svar.vname in
  let _ = 
    match mk_assignment fname env loc context lval e with
    | Some a -> ignore (assigndictionary#index_assignment a)
    | _ -> () in
  
  let add_global_proof_obligations () =
    match fenv#get_type_unrolled (type_of_exp env e) with
    | (TPtr (tgtTyp,_)) ->
      begin
	add (PLowerBound (tgtTyp,e)) context ;
	add (PUpperBound (tgtTyp,e)) context ;
	add (PValidMem e) context ;
	(match tgtTyp with
	| TInt (IChar, _)
	| TInt (ISChar, _)
	| TInt (IUChar, _) -> add (PNullTerminated e) context
	| _ -> ())
      end
    | _ -> () in
  begin
    create_po_lval env context#add_lhs lval loc ;
    create_po_exp ~deref:true env context#add_rhs e loc ;
    (match fenv#get_type_unrolled (type_of_exp env e) with
     | TPtr _ ->  add  (PStackAddressEscape (Some lval,e)) context
     | _ -> ()) ;

    if has_global_vars_in_exp env (Lval lval) || is_field_assignment then
      add_global_proof_obligations () ;
  end

  (* Note: we cannot require global-mem for pointer arguments passed to
     function calls in general, because of the common practice of having
     local variables initialized by another function, e.g.
     int a
     initvar(&a)
   *)
 
and create_po_call env
  (context:program_context_int)
  (optLval:lval option)
  (e:exp)
  (el:exp list)
  (loc:location) =
  let fname = (get_current_function ()).svar.vname in
  let spomanager = proof_scaffolding#get_spo_manager fname in
  let fApi = proof_scaffolding#get_function_api fname in
  let add p context = add_proof_obligation p loc context in
  let add_library_call header vname vid =
    let _ = fApi#add_library_call header vname in
    let _ = if vname = "free" &&  global_contract#is_nofree then
              fApi#add_contract_condition_failure
                "nofree" ("@line " ^ (string_of_int loc.line)) in
    if function_summary_library#has_summary header vname then
      begin
        create_po_precondition
          env context (function_summary_library#get_summary vname) el loc ;
        spomanager#add_direct_call
          loc context ~header:("lib:"^header) (env#get_varinfo_by_vid vid) el
      end
    else
      begin
	fApi#add_missing_summary (header ^ "/" ^ vname) ;
        spomanager#add_direct_call loc context ~header (env#get_varinfo_by_vid vid) el
      end in    
  begin
    (match optLval with 
    | Some lval -> create_po_lval env context#add_lhs lval loc
    | _ -> () ) ;
    (match e with 
      Lval (Var (vname,vid),NoOffset) ->
	if fenv#has_external_header vname then 
	  let header = fenv#get_external_header vname in
          add_library_call header vname vid
	else if function_summary_library#has_builtin_summary vname then
          add_library_call "builtins" vname vid
        else
	  begin
            spomanager#add_direct_call loc context (env#get_varinfo_by_vid vid) el ;
	  end
    | _ -> 
      begin
	create_po_exp ~deref:true env context#add_ftarget e loc ;
        spomanager#add_indirect_call loc context e el ;
      end) ;
    (List.iteri (fun i x ->
         let newcontext = context#add_arg (i+1) in
         begin
	   create_po_exp ~deref:true env newcontext x loc;
	   (match fenv#get_type_unrolled (type_of_exp env x) with
	    | (TPtr (tgtTyp,_)) ->
	       begin
	         add (PValidMem x) newcontext ;
                 add (PInScope x) newcontext ;
	         add (PLowerBound (tgtTyp,x)) newcontext ;
	         add (PUpperBound (tgtTyp,x)) newcontext
	  end
	| _ -> ())
      end ) el)
  end
    
(* Note: may have to create an additional upper-bound proof obligation for pointer return
   types, as the result of pointer arithmetic is allowed to be one beyond the upper-bound
   of a buffer, but we assume within bounds for the receiving function
*)
and create_po_return env (context:program_context_int) (e:exp option) (loc:location) = 
  let add p = add_proof_obligation p loc context#add_return in
  let fname = (get_current_function ()).svar.vname in
  let spomanager = proof_scaffolding#get_spo_manager fname in
  let _ = spomanager#add_return loc context#add_return e in
  match e with
  | Some x ->
     begin
       create_po_exp ~deref:true env context#add_return x loc ;
       (match type_of_exp env x with
        | TPtr (tt,_) ->               (* require return of valid (if non-null) pointer *)
	   begin
	     add (PValidMem x)  ;
	     add (PInScope x) ;
             add (PStackAddressEscape (None, x)) ;     (* cannot return local stack address *)
	     add (PLowerBound (tt,x)) ;
	     add (PUpperBound (tt,x)) 
	   end
        | _ -> ()) ;
     end
  | _ -> ()
    
and create_po_computed_goto env (context:program_context_int) (e:exp) (loc:location) =
  create_po_exp env context#add_goto e loc
  
and create_po_if env
  (context:program_context_int)
  (e:exp)
  (tb:block)
  (eb:block)
  (loc:location) = 
  begin
    create_po_exp env context#add_if_expr e loc ;
    create_po_block env context#add_if_then tb ;
    create_po_block env context#add_if_else eb
  end
    
and create_po_switch env (context:program_context_int) (e:exp) (b:block) (loc:location) = 
  begin 
    create_po_exp env context#add_switch_expr e loc ; 
    create_po_block env context b 
  end
    
and create_po_loop env (context:program_context_int) (b:block) (loc:location) =
  create_po_block env context b 
  
and create_po_stmt env (context:program_context_int) (s:stmt) =
  create_po_stmtkind env context s.skind
  
and create_po_block env (context:program_context_int) (b:block) =
  List.iter (fun s -> create_po_stmt env (context#add_stmt s.sid) s) b.bstmts

let create_contract_proof_obligations () =
  let fname = (get_current_function ()).svar.vname in
  let spomanager = proof_scaffolding#get_spo_manager fname in
  spomanager#create_contract_proof_obligations
  
let create_proof_obligations ?(createppos=true) (f:fundec) =
  begin
    set_create_ppos createppos ;
    (if not createppos then chlog#add "no ppos created" (STR f.svar.vname)) ;
    set_current_function f ;
    reset_missing_summaries () ;
    create_po_block f.sdecls (mk_program_context ()) f.sbody ;
    create_contract_proof_obligations () 
  end
   
