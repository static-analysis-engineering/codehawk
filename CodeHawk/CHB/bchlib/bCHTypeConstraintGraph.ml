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

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHTypeConstraintUtil

module H = Hashtbl


let tcd = BCHTypeConstraintDictionary.type_constraint_dictionary


class type_constraint_graph_t: type_constraint_graph_int =
object (self: 'a)

  val vertices: (int, IntCollections.set_t) H.t = H.create 5
  val subsumed: (int, IntCollections.set_t) H.t = H.create 5
  val edges: (int, (int, IntCollections.set_t) H.t) H.t = H.create 5

  method private mkNew =
    {< vertices = H.create 5;
       subsumed = H.create 5;
       edges = H.create 5
    >}

  method partition_size = H.length vertices

  method term_size = (H.length vertices) + (H.length subsumed)

  method initialize (tl: type_term_t list) =
    let s = new IntCollections.set_t in
    begin
      List.iter (fun t ->
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

      s#iter self#add_new_vertex;
    end

  method add_new_vertex (v: int) =
    let vs = new IntCollections.set_t in
    begin
      vs#add v;
      H.add vertices v vs
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
    H.fold (fun _ v acc -> v :: acc) vertices []

  method private get_set (ixt: int): IntCollections.set_t =
    if H.mem vertices ixt then
      H.find vertices ixt
    else if H.mem subsumed ixt then
      H.find subsumed ixt
    else
      raise
        (BCH_failure
           (LBLOCK [
                STR "Term ";
                INT ixt;
                STR ": ";
                STR (type_term_to_string (tcd#get_type_term ixt));
                STR " not found in graph";
                NL;
                self#toPretty]))

  method saturate: 'a =
    let newconstraints = new IntCollections.set_t in
    let newterms = new IntCollections.set_t in
    begin
      H.iter (fun vertex vs ->
          if H.mem edges vertex then
            let tgts = H.find edges vertex in
            vs#iter (fun v ->
                H.iter (fun tgt caps ->
                    let tgtset = H.find vertices tgt in
                    caps#iter (fun ixcap ->
                        match (tcd#get_type_term v) with
                        | TyConstant _ -> ()
                        | TyVariable tvar ->
                           let newcap =
                             match tcd#get_type_caplabel ixcap with
                             | Load | Store | Deref -> Deref
                             | cap -> cap in
                           let tvar' = add_capability [newcap] tvar in
                           let newterm = TyVariable tvar' in
                           let ixnewterm = tcd#index_type_term newterm in
                           if tgtset#has ixnewterm then
                             ()
                           else if H.mem vertices ixnewterm then
                             let newc = TySub (tcd#get_type_term tgt, newterm) in
                             newconstraints#add (tcd#index_type_constraint newc)
                           else if H.mem subsumed ixnewterm then
                             let subsumset = H.find subsumed ixnewterm in
                             let minsub =
                               List.hd
                                 (List.sort Stdlib.compare subsumset#toList) in
                             let newc =
                               TySub (
                                   tcd#get_type_term tgt,
                                   tcd#get_type_term minsub) in
                             newconstraints#add (tcd#index_type_constraint newc)
                           else
                             let newc = TySub (tcd#get_type_term tgt, newterm) in
                             begin
                               newterms#add ixnewterm;
                               newconstraints#add (tcd#index_type_constraint newc)
                             end)
                  ) tgts)) vertices;
      (if newconstraints#isEmpty then
         self
       else
         let clone = {< >} in
         let _ = newterms#iter clone#add_new_vertex in
         newconstraints#fold (fun g i ->
             let newtc = tcd#get_type_constraint i in
             g#add_constraint newtc) clone)
    end

  method add_constraint (tc: type_constraint_t): 'a =
    match tc with
    | TyVar _ -> self
    | TyZeroCheck _ -> self
    | TySub (t1, t2)
      | TyGround (t1, t2) ->
       let ixt1 = tcd#index_type_term t1 in
       let ixt2 = tcd#index_type_term t2 in
       let s1 = self#get_set ixt1 in
       let s2 = self#get_set ixt2 in
       if not (s1#equal s2) then
         let s12 = s1#union s2 in
         let newvertices: (int, IntCollections.set_t) H.t = H.create 5 in
         let newsubsumed = H.create 5 in
         let newedges = H.create 5 in
         let mins12 = List.hd (List.sort Stdlib.compare s12#toList) in
         begin
           H.iter (fun v s ->
               if s12#has v then
                 if v = mins12 then
                   H.add newvertices v s12
                 else
                   H.add newsubsumed v s12
               else
                 H.add newvertices v s) vertices;
           H.iter (fun v s ->
               if s12#has v then
                 H.add newsubsumed v s12
               else
                 H.add newsubsumed v s) subsumed;
           H.iter (fun src tgts ->
               H.iter (fun tgt capset ->
                   if s12#has src then
                     if s12#has tgt then
                       raise
                         (BCH_failure
                            (LBLOCK [STR "Src and tgt both in union set"]))
                     else
                       let tentry =
                         if H.mem newedges mins12 then
                           H.find newedges mins12
                         else
                           H.create 5 in
                       let ctentry =
                         if H.mem tentry tgt then
                           H.find tentry tgt
                         else
                           new IntCollections.set_t in
                       begin
                         ctentry#addSet capset;
                         H.replace tentry tgt ctentry;
                         H.replace newedges mins12 tentry
                       end
                   else if s12#has tgt then
                     let tentry =
                       if H.mem newedges src then
                         H.find newedges src
                       else
                         H.create 5 in
                     let ctentry =
                       if H.mem tentry mins12 then
                         H.find tentry mins12
                       else
                         new IntCollections.set_t in
                     begin
                       ctentry#addSet capset;
                       H.replace tentry mins12 ctentry;
                       H.replace newedges src tentry
                     end
                   else
                     let tentry =
                       if H.mem newedges src then
                         H.find newedges src
                       else
                         H.create 5 in
                     let ctentry =
                       if H.mem tentry tgt then
                         H.find tentry tgt
                       else
                         new IntCollections.set_t in
                     begin
                       ctentry#addSet capset;
                       H.replace tentry tgt ctentry;
                       H.replace newedges src tentry
                     end) tgts) edges;
           {< vertices = newvertices;
              subsumed = newsubsumed;
              edges = newedges >}
         end
       else
         self

  method toPretty =
    let vlist = ref [] in
    let slist = ref [] in
    let edgelist = ref [] in
    begin
      H.iter (fun k v ->
          vlist := (LBLOCK [INT k; STR ": "; v#toPretty; NL]) :: !vlist) vertices;
      H.iter (fun k v ->
          slist := (LBLOCK [INT k; STR ": "; v#toPretty; NL]) :: !slist) subsumed;
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
          [STR "Vertices: "; NL]
          @ !vlist
          @ [STR "Subsumed: "; NL]
          @ !slist
          @ [STR "Edges: "; NL]
          @ !edgelist)
    end

end


let mk_type_constraint_graph () = new type_constraint_graph_t
