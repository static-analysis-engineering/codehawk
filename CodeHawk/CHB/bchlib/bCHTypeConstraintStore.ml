(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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
open CHUtils

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBCTypePretty
open BCHTypeConstraintGraph
open BCHTypeConstraintUtil
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHLibTypes

module H = Hashtbl

let bcd = BCHBCDictionary.bcdictionary
let bd = BCHDictionary.bdictionary
let tcd = BCHTypeConstraintDictionary.type_constraint_dictionary


class type_constraint_store_t: type_constraint_store_int =
object (self)

  val store = H.create 5

  (* constraints that involve function type, indexed by faddr *)
  val functiontypes = H.create 5

  (* constraints that involve a particular reglhs:
     faddr -> reg-index -> iaddr -> constraint list *)
  val reglhss = H.create 5

  (* constraints that involve a particular stacklhs:
     faddr -> stack-offset -> iaddr -> constraint list *)
  val stacklhss = H.create 5

  (* constraints that involve a global address *)
  val data_address_types = H.create 5

  (* constraints that involve a global variable *)
  val gvartypes = H.create 5

  method add_constraint (c: type_constraint_t) =
    let index = tcd#index_type_constraint c in
    (* index the constraint *)
    if H.mem store index then
      ()
    else
      begin
        H.add store index c;

        (* index the base variables *)
        (match c with
         | TySub (t1, t2)
           | TyGround (t1, t2) ->
            begin
              self#add_term_constraint_xref t1 index;
              self#add_term_constraint_xref t2 index;
            end
         | TyZeroCheck t ->
            self#add_term_constraint_xref t index
         | _ -> ())
      end

  method private add_term_constraint_xref (t: type_term_t) (c: int) =
    match t with
    | TyConstant _ -> ()
    | TyVariable tv ->
       (match tv.tv_basevar with
        | FunctionType faddr -> self#add_function_type_xref faddr c
        | DataAddressType gaddr -> self#add_data_address_type_xref gaddr c
        | GlobalVariableType gaddr -> self#add_gvar_type_xref gaddr c
        | RegisterLhsType (reg, faddr, iaddr) ->
           self#add_reglhs_xref reg faddr iaddr c
        | LocalStackLhsType (offset, faddr, iaddr) ->
           self#add_stacklhs_xref offset faddr iaddr c)

  method private add_function_type_xref (faddr: string) (c: int) =
    let entry =
      if H.mem functiontypes faddr then H.find functiontypes faddr else [] in
    H.replace functiontypes faddr (c :: entry)

  method private add_data_address_type_xref (gaddr: string) (c: int) =
    let entry =
      if H.mem data_address_types gaddr then
        H.find data_address_types gaddr
      else
        [] in
    H.replace data_address_types gaddr (c :: entry)

  method private add_gvar_type_xref (gaddr: string) (c: int) =
    let entry = if H.mem gvartypes gaddr then H.find gvartypes gaddr else [] in
    H.replace gvartypes gaddr (c :: entry)

  method private add_reglhs_xref
                   (reg: register_t)
                   (faddr: string)
                   (iaddr: string)
                   (c: int) =
    let rindex = bd#index_register reg in
    let regentry =
      if H.mem reglhss faddr then
        H.find reglhss faddr
      else
        let newentry = H.create 5 in
        begin
          H.add reglhss faddr newentry;
          newentry
        end in
    let iaddrentry =
      if H.mem regentry rindex then
        H.find regentry rindex
      else
        let newentry = H.create 5 in
        begin
          H.add regentry rindex newentry;
          newentry
        end in
    let entry =
      if H.mem iaddrentry iaddr then H.find iaddrentry iaddr else [] in
    H.replace iaddrentry iaddr (c :: entry)

  method private add_stacklhs_xref
                   (offset: int)
                   (faddr: string)
                   (iaddr: string)
                   (c: int) =
    let offsetentry =
      if H.mem stacklhss faddr then
        H.find stacklhss faddr
      else
        let newentry = H.create 5 in
        begin
          H.add stacklhss faddr newentry;
          newentry
        end in
    let iaddrentry =
      if H.mem offsetentry offset then
        H.find offsetentry offset
      else
        let newentry = H.create 5 in
        begin
          H.add offsetentry offset newentry;
          newentry
        end in
    let entry =
      if H.mem iaddrentry iaddr then H.find iaddrentry iaddr else [] in
    H.replace iaddrentry iaddr (c :: entry)

  method add_var_constraint (tyvar: type_variable_t) =
    self#add_constraint (TyVar (TyVariable tyvar))

  method add_term_constraint (t: type_term_t) =
    match t with
    | TyVariable tv -> self#add_var_constraint tv
    | _ -> ()

  method add_zerocheck_constraint (tyvar: type_variable_t) =
    begin
      self#add_var_constraint tyvar;
      self#add_constraint (TyZeroCheck (TyVariable tyvar))
    end

  method add_subtype_constraint (t1: type_term_t) (t2: type_term_t) =
    begin
      self#add_term_constraint t1;
      self#add_term_constraint t2;
      self#add_constraint (TySub (t1, t2))
    end

  method add_ground_constraint (t1: type_term_t) (t2: type_term_t) =
    begin
      self#add_term_constraint t1;
      self#add_term_constraint t2;
      self#add_constraint (TyGround (t1, t2))
    end

  method get_function_type_constraints (faddr: string): type_constraint_t list =
    if H.mem functiontypes faddr then
      List.map tcd#get_type_constraint (H.find functiontypes faddr)
    else
      []

  method get_reglhs_constraints
           (reg: register_t)
           (faddr: string)
           (iaddr: string): type_constraint_t list =
    if H.mem reglhss faddr then
      let regentry = H.find reglhss faddr in
      let rindex = bd#index_register reg in
      if H.mem regentry rindex then
        let iaddrentry = H.find regentry rindex in
        if H.mem iaddrentry iaddr then
          List.map tcd#get_type_constraint (H.find iaddrentry iaddr)
        else
          []
      else
        []
    else
      []

  method get_stack_lhs_constraints
           (offset: int) (faddr: string): type_constraint_t list =
    if H.mem stacklhss faddr then
      let offsetentry = H.find stacklhss faddr in
      if H.mem offsetentry offset then
        let result = ref [] in
        let iaddrentry = H.find offsetentry offset in
        let _ =
          H.iter (fun _ tcs ->
              result := !result @ (List.map tcd#get_type_constraint tcs))
            iaddrentry in
        let _ =
          chlog#add
            "stack lhs constraints"
            (LBLOCK [
                 INT offset;
                 STR ": ";
                 pretty_print_list !result
                   (fun tc -> STR (type_constraint_to_string tc))
                   "[" "; " "]"]) in
        !result
      else
        []
    else
      []

  method evaluate_reglhs_type
           (reg: register_t) (faddr: string) (iaddr: string)
         :(type_variable_t list * type_constant_t list) list =
    let konstraints = self#get_reglhs_constraints reg faddr iaddr in
    let termset = new IntCollections.set_t in
    let constraintset = new IntCollections.set_t in
    let _ =
      List.iter (fun c ->
          begin
            termset#addList
              (List.map tcd#index_type_term (type_constraint_terms c));
            constraintset#add (tcd#index_type_constraint c)
          end) konstraints in
    let changed = ref true in
    while !changed do
      begin
        changed := false;
        H.iter (fun ixc c ->
            if constraintset#has ixc then
              ()
            else
              let cterms = type_constraint_terms c in
              let prefixterms =
                List.concat (List.map type_term_prefix_closure cterms) in
              let cterms = List.map tcd#index_type_term prefixterms in
              match cterms with
              | [] -> ()
              | [_] -> ()
              | _ ->
                 if List.for_all termset#has cterms then
                   ()
                 else if List.exists termset#has cterms then
                   begin
                     List.iter termset#add cterms;
                     constraintset#add ixc;
                     changed := true
                   end
                 else
                   ()) store
      end
    done;
    let tygraph = mk_type_constraint_graph () in
    begin
      tygraph#initialize (List.map tcd#get_type_term termset#toList);
      constraintset#iter (fun ixc ->
          let c = tcd#get_type_constraint ixc in
          tygraph#add_constraint c);
      let newgraph = tygraph#saturate in
      let newgraph = newgraph#saturate in
      let partition = newgraph#partition in
      List.fold_left (fun acc s ->
          let terms = List.map tcd#get_type_term s#toList in
          let reglhsvars =
            List.fold_left (fun acc t ->
                match t with
                | TyVariable tv when has_reg_lhs_basevar reg faddr iaddr t ->
                   tv :: acc
                | _ -> acc) [] terms in
          let tyconsts =
            List.fold_left (fun acc t ->
                match t with
                | TyConstant c -> c :: acc
                | _ -> acc) [] terms in
          match (reglhsvars, tyconsts) with
          | ([], _) -> acc
          | (_, []) -> acc
          | _ -> (reglhsvars, tyconsts) :: acc) [] partition
    end

  method evaluate_stack_lhs_type (offset: int) (faddr: string)
         :(type_variable_t list * type_constant_t list) list =
    let konstraints = self#get_stack_lhs_constraints offset faddr in
    let termset = new IntCollections.set_t in
    let constraintset = new IntCollections.set_t in
    let _ =
      List.iter (fun c ->
          begin
            termset#addList
              (List.map tcd#index_type_term (type_constraint_terms c));
            constraintset#add (tcd#index_type_constraint c)
          end) konstraints in
    let changed = ref true in
    while !changed do
      begin
        changed := false;
        H.iter (fun ixc c ->
            if constraintset#has ixc then
              ()
            else
              let cterms = type_constraint_terms c in
              let prefixterms =
                List.concat (List.map type_term_prefix_closure cterms) in
              let cterms = List.map tcd#index_type_term prefixterms in
              match cterms with
              | [] -> ()
              | [_] -> ()
              | _ ->
                 if List.for_all termset#has cterms then
                   ()
                 else if List.exists termset#has cterms then
                   begin
                     List.iter termset#add cterms;
                     constraintset#add ixc;
                     changed := true
                   end
                 else
                   ()) store
      end
    done;
    let tygraph = mk_type_constraint_graph () in
    begin
      tygraph#initialize (List.map tcd#get_type_term termset#toList);
      constraintset#iter (fun ixc ->
          let c = tcd#get_type_constraint ixc in
          tygraph#add_constraint c);
      let newgraph = tygraph#saturate in
      let newgraph = newgraph#saturate in
      let partition = newgraph#partition in
      List.fold_left (fun acc s ->
          let terms = List.map tcd#get_type_term s#toList in
          let stacklhsvars =
            List.fold_left (fun acc t ->
                match t with
                | TyVariable tv when has_stack_lhs_basevar offset faddr t ->
                   tv :: acc
                | _ -> acc) [] terms in
          let tyconsts =
            List.fold_left (fun acc t ->
                match t with
                | TyConstant c -> c :: acc
                | _ -> acc) [] terms in
          match (stacklhsvars, tyconsts) with
          | ([], _) -> acc
          | (_, []) -> acc
          | _ -> (stacklhsvars, tyconsts) :: acc) [] partition
    end

  method resolve_reglhs_type
           (reg: register_t) (faddr: string) (iaddr: string): btype_t option =
    let evaluation = self#evaluate_reglhs_type reg faddr iaddr in
    let log_evaluation () =
      chlog#add
        ("reglhs resolution was not successfull:" ^ faddr)
        (LBLOCK [
             STR iaddr;
             STR " - ";
             STR (register_to_string reg);
             STR ": ";
             pretty_print_list
               evaluation
               (fun (vars, consts) ->
                 LBLOCK [
                     STR "vars: ";
                     pretty_print_list
                       vars
                       (fun v -> STR (type_variable_to_string v))
                       "[" "; " "]";
                     STR "; consts: ";
                     pretty_print_list
                       consts
                       (fun c -> STR (type_constant_to_string c))
                       "[" "; " "]";
                     NL]) "[[" " -- " "]]"]) in
    let result = new IntCollections.set_t in
    begin
      List.iter (fun (vars, consts) ->
          let jointy = type_constant_join consts in
          List.iter (fun v ->
              let optty =
                match jointy with
                | TyTUnknown -> None
                | _ ->
                   match v.tv_capabilities with
                   | [] -> Some (type_constant_to_btype jointy)
                   | [Deref | Load | Store] ->
                      Some (t_ptrto (type_constant_to_btype jointy))
                   | [OffsetAccessA (size, _)] ->
                      Some (t_array (type_constant_to_btype jointy) size)
                   | _ -> None in
              match optty with
              | Some ty -> result#add (bcd#index_typ ty)
              | _ -> ()) vars) evaluation;
      if result#isEmpty then
        begin
          log_evaluation ();
          None
        end
      else
        match result#singleton with
        | Some ixty -> Some (bcd#get_typ ixty)
        | _ ->
           begin
             log_evaluation ();
             chlog#add
               "top type constant in join"
               (LBLOCK [
                    STR iaddr;
                    STR " --- ";
                    STR (register_to_string reg);
                    STR ": ";
                    pretty_print_list
                      (List.map bcd#get_typ result#toList)
                      (fun ty -> STR (btype_to_string ty)) "[" "; " "]"]);
             None
           end
    end

  method resolve_stack_lhs_type
           (offset: int) (faddr: string): btype_t option =
    let evaluation = self#evaluate_stack_lhs_type offset faddr in
    let log_evaluation () =
      chlog#add
        ("stacklhs resolution was not successfull:" ^ faddr)
        (LBLOCK [
             INT offset;
             STR ": ";
             pretty_print_list
               evaluation
               (fun (vars, consts) ->
                 LBLOCK [
                     STR "vars: ";
                     pretty_print_list
                       vars
                       (fun v -> STR (type_variable_to_string v))
                       "[" "; " "]";
                     STR "; consts: ";
                     pretty_print_list
                       consts
                       (fun c -> STR (type_constant_to_string c))
                       "[" "; " "]";
                     NL]) "[[" " -- " "]]"]) in
    let first_field_struct (s: IntCollections.set_t): btype_t option =
      (* The type of a data item at a particular stack offset can legally
         be both a struct and the type of the first field of the struct.
         If the set contains both a struct array type and the type of the
         first field of that struct and nothing else, return the struct
         array type. *)
      let optstructty =
        s#fold (fun acc ixty ->
            match acc with
            | Some _ -> acc
            | _ ->
               let ty = bcd#get_typ ixty in
               match ty with
               | TArray (TComp _, _, _) -> Some ty
               | _ -> None) None in
      match optstructty with
      | None -> None
      | Some (TArray (TComp _ as ty, _, _) as tstructarray) ->
         let cinfo = get_struct_type_compinfo ty in
         let finfo0 = List.hd cinfo.bcfields in
         let ftype = resolve_type finfo0.bftype in
         let ixftype = bcd#index_typ ftype in
         let ixctype = bcd#index_typ tstructarray in
         let _ =
           chlog#add
             "first field struct check"
             (LBLOCK [
                  INT offset;
                  STR ": ";
                  pretty_print_list
                    s#toList
                    (fun i -> STR (btype_to_string (bcd#get_typ i)))
                    "{" "; " "}";
                  STR ": compinfo: ";
                  STR cinfo.bcname;
                  STR ": first field type: ";
                  STR (btype_to_string ftype)]) in
         if s#fold (fun acc i -> acc && (i = ixftype || i = ixctype)) true then
           Some tstructarray
         else
           None
      | _ -> None in
    let get_promotion (s: IntCollections.set_t): IntCollections.set_t =
      let prom = new IntCollections.set_t in
      begin
        s#iter (fun ix ->
            let ty = bcd#get_typ ix in
            if is_int ty then
              prom#add (bcd#index_typ (promote_int ty))
            else
              prom#add ix);
        prom
      end in
    let result = new IntCollections.set_t in
    begin
      List.iter (fun (vars, consts) ->
          List.iter (fun v ->
              List.iter (fun c ->
                  let optty =
                    match v.tv_capabilities with
                    | [] -> Some (type_constant_to_btype c)
                    | [Deref | Load | Store] ->
                       Some (t_ptrto (type_constant_to_btype c))
                    | [OffsetAccessA (size, _)] ->
                       Some (t_array (type_constant_to_btype c) size)
                    | _ -> None in
                  match optty with
                  | Some ty -> result#add (bcd#index_typ ty)
                  | _ -> ()) consts) vars) evaluation;
      if result#isEmpty then
        begin
          log_evaluation ();
          None
        end
      else
        match result#singleton with
        | Some ixty -> Some (bcd#get_typ ixty)
        | _ ->
           match (get_promotion result)#singleton with
           | Some ixty -> Some (bcd#get_typ ixty)
           | _ ->
              match first_field_struct result with
              | Some ty -> Some ty
              | _ ->
                 begin
                   log_evaluation ();
                   chlog#add
                     "multiple distinct types"
                     (LBLOCK [
                          INT offset;
                          STR "; ";
                          pretty_print_list
                            (List.map bcd#get_typ result#toList)
                            (fun ty -> STR (btype_to_string ty)) "[" "; " "]"]);
                   None
                 end
    end

  method resolve_reglhs_types (faddr: string):
           (register_t * string * btype_t option) list =
    let result = ref [] in
    let _ =
      if H.mem reglhss faddr then
        let regs = H.find reglhss faddr in
        H.iter (fun ixreg iaddrs ->
            let reg = bd#get_register ixreg in
            H.iter (fun iaddr _ ->
                let optty = self#resolve_reglhs_type reg faddr iaddr in
                result := (reg, iaddr, optty) :: !result) iaddrs) regs
      else
        () in
    !result

  method resolve_local_stack_lhs_types (faddr: string):
           (int * btype_t option) list =
    let result = ref [] in
    let _ =
      if H.mem stacklhss faddr then
         let offsets = H.find stacklhss faddr in
         H.iter (fun offset iaddrs ->
             H.iter (fun _ _ ->
                 let optty = self#resolve_stack_lhs_type offset faddr in
                 result := (offset, optty) :: !result) iaddrs) offsets
      else
        () in
    !result

  method toPretty =
    let constraints = ref [] in
    let _ =
      H.iter
        (fun _ v ->
          constraints :=
            (type_constraint_to_string v) :: !constraints) store in
    let constraints = List.sort Stdlib.compare !constraints in
    STR (String.concat "\n" constraints)

end


let mk_type_constraint_store () = new type_constraint_store_t
