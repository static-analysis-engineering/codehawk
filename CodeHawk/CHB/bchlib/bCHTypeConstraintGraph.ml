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
open CHTraceResult

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHTypeConstraintUtil

module H = Hashtbl


let tcd = BCHTypeConstraintDictionary.type_constraint_dictionary


class type_constraint_graph_t: type_constraint_graph_int =
object (self: 'a)

  (* Let V be the set of type variables, and C be the set of type constants

     Initially:
       - tvars = {(v, {v}) | v in V}
       - tvreps = {(v, v) | v in V}

     Update for constraint of type (v, c) or (c, w), v in V, c in C:

     tvars'(w) = tvars(w) u {c}, tvreps' = tvreps           if w = tvreps(v)
     tvars'(w) = tvars(w), tvreps' = tvreps                 otherwise

     Update for constraint of type (v1, v2), v1, v2 in V:

     tvars' = tvars, tvreps' = tvreps        if tvreps(v1) = tvreps(v2)

     otherwise:
       tvars'(z) = tvars(tvreps(v1)) u tvars(tvreps(v2))
       tvreps'(v) = z   for all v in tvars(tvreps(v1)) u tvars(tvreps(v2)
       tvreps'(v) = tvreps(v)   for all other v in V
              with z = min(tvars(tvreps(v1)) u tvars(tvreps(v2)))

     Invariants maintained:

     - { w | (v, w) in tvars } forms a partition of V
     - tvreps is a total function on V, with range { v | v in domain(tvars) }

     Saturation

   *)

  val tvars: (int, IntCollections.set_t) H.t = H.create 5
  val tvreps: (int, int) H.t = H.create 5
  val edges: (int, (int, IntCollections.set_t) H.t) H.t = H.create 5

  method private mkNew =
    {< tvars = H.create 5;
       tvreps = H.create 5;
       edges = H.create 5
    >}

  method partition_size = H.length tvars

  method typevarcount = H.length tvreps

  method initialize (tl: type_term_t list) =
    let s = new IntCollections.set_t in
    begin
      List.iter (fun t ->
          match t with
          | TyConstant _ -> ()
          | TyVariable _ ->
             let ts = type_term_prefix_closure t in
             begin
               s#addList (List.map tcd#index_type_term ts);

               (* add edges *)
               List.iter (fun t ->
                   match pop_capability t with
                   | None -> ()
                   | Some (tp, cap) ->
                      self#add_edge
                        (tcd#index_type_term tp) (tcd#index_type_term t) cap) ts
             end) tl;

      s#iter self#add_typevar;
    end

  method add_typevar (v: int) =
    let vs = new IntCollections.set_t in
    begin
      vs#add v;
      H.replace tvars v vs;
      H.replace tvreps v v
    end

  method private add_edge (src: int) (tgt: int) (cap: type_cap_label_t) =
    let tentry =
      if H.mem edges src then
        H.find edges src
      else
        let tgts = H.create 5 in
        begin
          H.add edges src tgts;
          tgts
        end in
    let capentry =
      if H.mem tentry tgt then
        H.find tentry tgt
      else
        let caps = new IntCollections.set_t in
        begin
          H.add tentry tgt caps;
          caps
        end in
    capentry#add (tcd#index_type_caplabel cap)

  method partition: IntCollections.set_t list =
    H.fold (fun _ v acc -> v :: acc) tvars []

  method add_constraint (tc: type_constraint_t) =
    match tc with
    | TyVar _ -> ()
    | TyZeroCheck t -> self#add_zero_check t
    | TySub (t1, t2)
      | TyGround (t1, t2) ->
       match t1, t2 with
       | TyVariable _, TyVariable _ -> self#add_tvar_constraint t1 t2
       | TyVariable _, TyConstant _ -> self#add_tconst_constraint t1 t2
       | TyConstant _, TyVariable _ -> self#add_tconst_constraint t2 t1
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "Unexpected type constraint of two constants: ";
                    STR (type_term_to_string t1);
                    STR " and ";
                    STR (type_term_to_string t2)]))

  method private tvrep (ixtr: int traceresult): int traceresult =
    match ixtr with
    | Ok ixt ->
       if H.mem tvreps ixt then
         Ok (H.find tvreps ixt)
       else
         Error ["no typevar representative found for " ^ (string_of_int ixt)]
    | _ -> ixtr

  method private tvset (ixtr: int traceresult): IntCollections.set_t traceresult =
    match ixtr with
    | Ok ixt ->
       if H.mem tvars ixt then
         Ok (H.find tvars ixt)
       else
         Error ["no type-term set found for typevar " ^ (string_of_int ixt)]
    | Error e -> Error ("tv set could not be obtained" :: e)

  method private add_zero_check (t: type_term_t) =
    self#add_tconst_constraint t (TyConstant TyZero)

  method private add_tconst_constraint (tv: type_term_t) (tc: type_term_t) =
    let ixtv = tcd#index_type_term tv in
    let ixtc = tcd#index_type_term tc in
    let tvrepr = self#tvrep (Ok ixtv) in
    let tvset = self#tvset tvrepr in
    log_tfold_default
      (mk_tracelog_spec
         ~tag:"add constant constraint"
         (type_term_to_string tv))
      (fun tvset ->
        let newset = tvset#clone in
        let _ = newset#add ixtc in
        H.replace tvars (tget_ok tvrepr) newset)
      ()
      tvset

  method private add_tvar_constraint (t1: type_term_t) (t2: type_term_t) =
    let log_error msg = mk_tracelog_spec ~tag:"add_tvar_constraint" msg in
    let ixtv1 = tcd#index_type_term t1 in
    let ixtv2 = tcd#index_type_term t2 in
    let tvrepr1 = self#tvrep (Ok ixtv1) in
    let tvrepr2 = self#tvrep (Ok ixtv2) in
    let needsmerge =
      log_tfold_default
        (log_error ("rep for " ^ (type_term_to_string t1) ^ " not found"))
        (fun tvrep1 ->
          log_tfold_default
            (log_error ("rep for " ^ (type_term_to_string t2) ^ " not found"))
            (fun tvrep2 -> tvrep1 != tvrep2)
            false
            tvrepr2)
        false
        tvrepr1 in
    if needsmerge then
      let tvsetr1 = self#tvset tvrepr1 in
      let tvsetr2 = self#tvset tvrepr2 in
      log_tfold_default
        (log_error ("set for " ^ (type_term_to_string t1) ^ " not found"))
        (fun tvset1 ->
          log_tfold_default
            (log_error ("set for " ^ (type_term_to_string t2) ^ " not found"))
            (fun tvset2 ->
              (* known to be ok at this point *)
              let tvrep1 = tget_ok tvrepr1 in
              let tvrep2 = tget_ok tvrepr2 in
              let newset = tvset1#clone in
              let _ = newset#addSet tvset2 in
              let (newrep, remrep) =
                if tvrep1 < tvrep2 then (tvrep1, tvrep2) else (tvrep2, tvrep1) in
              begin
                H.replace tvars newrep newset;
                H.remove tvars remrep;
                newset#iter (fun ixt -> H.replace tvreps ixt newrep);
                self#merge_edges newrep remrep
              end)
            ()
            tvsetr2)
        ()
        tvsetr1

  method private merge_edges (newrep: int) (remrep: int) =
    let newreptgts =
      if H.mem edges newrep then
        H.find edges newrep
      else
        let newrepedges = H.create 5 in
        begin
          H.add edges newrep newrepedges;
          newrepedges
        end in

    H.iter (fun src tgts ->
        if src = remrep then
          begin
            H.iter (fun remtgt remcapset ->
                if H.mem newreptgts remtgt then
                  let repcapset = H.find newreptgts remtgt in
                  let newcapset = repcapset#clone in
                  let _ = newcapset#addSet remcapset in
                  H.replace newreptgts remtgt newcapset
                else
                  H.add newreptgts remtgt remcapset) tgts;
            H.remove edges remrep
          end
        else
          if H.mem tgts remrep then
            let remcapset = H.find tgts remrep in
            if H.mem tgts newrep then
              let repcapset = H.find tgts newrep in
              let newcapset = repcapset#clone in
              let _ = newcapset#addSet remcapset in
              begin
                H.replace tgts newrep newcapset;
                H.remove tgts remrep
              end
            else
              H.add tgts newrep remcapset
          else
            ()) edges

  method saturate: 'a =
    let newconstraints = new IntCollections.set_t in
    let newterms = new IntCollections.set_t in
    begin
      H.iter (fun tvar tset ->
          if H.mem edges tvar then
            if H.mem edges tvar then
              let tgts = H.find edges tvar in
              tset#iter (fun tv ->
                  H.iter (fun tgt caps ->
                      if H.mem tvars tgt then
                        let tgtset = H.find tvars tgt in
                        caps#iter (fun ixcap ->
                            match (tcd#get_type_term tv) with
                            | TyConstant _ -> ()
                            | TyVariable tyvar ->
                               let cap = tcd#get_type_caplabel ixcap in
                               let tyvar' = add_capability [cap] tyvar in
                               let newterm = TyVariable tyvar' in
                               let ixnewterm = tcd#index_type_term newterm in
                               if tgtset#has ixnewterm then
                                 ()
                               else
                                 let newc = TySub (tcd#get_type_term tgt, newterm) in
                                 begin
                                   newconstraints#add (tcd#index_type_constraint newc);
                                   if not (H.mem tvreps ixnewterm) then
                                     newterms#add ixnewterm
                                 end)) tgts)) tvars;
      (if newconstraints#isEmpty then
         self
       else
         let clone = {<>} in
         begin
           newterms#iter clone#add_typevar;
           newconstraints#iter (fun c ->
               let newtc = tcd#get_type_constraint c in
               clone#add_constraint newtc);
           clone
         end)
    end

  method toPretty =
    let vlist = ref [] in
    let slist = ref [] in
    let edgelist = ref [] in
    begin
      H.iter (fun k v ->
          vlist :=
            (LBLOCK [
                 INT k;
                 STR ": {";
                 LBLOCK (List.map (fun vm ->
                        (LBLOCK [
                             INT vm;
                             STR ":";
                             STR (type_term_to_string (tcd#get_type_term vm));
                             STR "; -- "])) v#toList);
                 STR "}";
                 NL]) :: !vlist) tvars;
      H.iter (fun k v ->
          slist :=
            (LBLOCK [
                 INT k;
                 STR ": ";
                 INT v;
                 STR ": ";
                 STR (type_term_to_string (tcd#get_type_term v));
                 NL]) :: !slist) tvreps;
      H.iter (fun src tgts ->
          H.iter (fun tgt caps ->
              edgelist :=
                (LBLOCK [
                     STR "(";
                     INT src;
                     STR ", ";
                     INT tgt;
                     STR "): ";
                     pretty_print_list
                       (List.map tcd#get_type_caplabel caps#toList)
                       (fun c -> STR (type_cap_label_to_string c))
                       "[" ", " "]";
                     NL])
                :: !edgelist) tgts) edges;
      LBLOCK (
          [STR "Type variables: "; NL]
          @ !vlist
          @ [STR "Representatives: "; NL]
          @ !slist
          @ [STR "Edges: "; NL]
          @ !edgelist)
    end

end


let mk_type_constraint_graph () = new type_constraint_graph_t
