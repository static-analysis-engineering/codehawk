(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet and Henny Sipma
   -----------------------------------------------------------------------------
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
  ============================================================================== *)

(* chlib *)
open CHCommon
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues   
open CHPretty
open CHSymbolicSets
open CHUtils


module H = Hashtbl

(* policy: policy-name, transitions
   transition: transition       -name, (pre,post) list
 *)

[@@@warning "-27"]
         
class state_sets_domain_no_arrays_t
        (policies:(string * (string * (symbol_t * symbol_t) list) list) list) = 
object (self: 'a)
     
  inherit non_relational_domain_t
        
  val policytable =
    let pt = H.create 3 in
    let _ =
      List.iter (fun (pname,transitions) ->
          let tt = H.create 3 in
          begin
            H.add pt pname tt  ;
            List.iter (fun (tname,preposts) ->
                let ptt = H.create 3 in
                begin
                  H.add tt tname ptt ;
                  List.iter (fun (pre,post) ->
                      H.add ptt pre#getBaseName post) preposts
                end) transitions
          end) policies in
    pt
    
  method private getValue' v =
    let v_value = self#getValue v in
    match v_value#getValue with
    | SYM_SET_VAL i -> i
    | TOP_VAL -> topSymbolicSet
    | _ -> raise (CHFailure (LBLOCK [ STR "Symbolic set expected. " ; v#toPretty ;
				      STR ": " ; v_value#toPretty]))
	 
  method private setValue' t v x =
    self#setValue t v (new non_relational_domain_value_t (SYM_SET_VAL x))
    
  method special _cmd _args = {< >}
                          
  method private importValue v =
    new non_relational_domain_value_t (SYM_SET_VAL (v#toSymbolicSet))
    
  method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
	{< table = table' >}
      in
      match cmd with
      | ABSTRACT_VARS l ->
	 begin
	   self#abstractVariables table' l;
	   default ()
	 end
      | ASSIGN_SYM (x, SYM s) ->
	 self#setValue' table' x (new symbolic_set_t [s]);
	 default ()
      | ASSIGN_SYM (x, SYM_VAR y) ->
	 self#setValue' table' x (self#getValue' y);
	 default ()
      | READ_SYM_ELT (x, _, _) ->
	 table'#remove x;
	 default ()
      | ASSERT TRUE ->
	 default ()
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (SUBSET (x, syms)) ->
	 let symbols = self#getValue' x in
	 let result = symbols#meet (new symbolic_set_t syms) in
	 if result#isBottom then
           let _ =
             pr_trace
               1
               [ STR "Bottom from SUBSET: " ; x#toPretty ; NL ;
                 INDENT (3, LBLOCK [ STR "syms: " ;
                                     pretty_print_list syms (fun s -> s#toPretty) "[" "," "]" ; NL ]) ;
                 INDENT (3, LBLOCK [ STR "symbols: " ; symbols#toPretty ; NL ]) ] in
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' x result;
	     default ()
	   end
      | ASSERT (DISJOINT (x, syms)) ->
	 let symbols = self#getValue' x in
	 let result = symbols#delta syms in
	 if result#isBottom then
           let _ =
             pr_trace
               1
               [ STR "Bottom from DISJOINT: " ; x#toPretty ; NL ;
                 INDENT (3, LBLOCK [ STR "syms: " ;
                                     pretty_print_list syms (fun s -> s#toPretty) "[" "," "]"; NL ]) ;
                 INDENT (3, LBLOCK [ STR "symbols: " ; symbols#toPretty ; NL ]) ] in
	   self#mkBottom
	 else
	   begin
	     self#setValue' table' x result;
	     default ()
	   end
      | _ ->
	 default ()
        
  method private analyzeBwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      let table' = table#clone in
      let default () =
	{< table = table' >}
      in
      match cmd with
      | ABSTRACT_VARS l ->
	 begin
	   self#abstractVariables table' l;
	   default ()
	 end
      | ASSIGN_SYM (x, SYM s) ->
	 let x_s = self#getValue' x in
	 let x_s' = x_s#meet (new symbolic_set_t [s]) in
	 if x_s'#isBottom then
           let _ =
             pr_trace
               1
               [ STR "Bottom from ASSIGN_SYM-BW: " ; x#toPretty ; NL ;
                 INDENT (3, LBLOCK [ STR "s: " ; s#toPretty ]) ; NL ; NL ] in
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     default ()
	   end
      | ASSIGN_SYM (x, SYM_VAR y) ->
	 let x_s = self#getValue' x in
	 let y_s = self#getValue' y in
	 let y_s' = y_s#meet x_s in
	 if y_s'#isBottom then
           let _ =
             pr_trace
               1
               [ STR "Bottom from ASSIGN_SYM_VAR-BW: " ; x#toPretty ;
                 STR ", " ; y#toPretty ; NL ] in
	   self#mkBottom
	 else
	   begin
	     table'#remove x;
	     self#setValue' table' y y_s';
	     default ()
	   end
      | READ_SYM_ELT (x, _, _) ->
	 table'#remove x;
	 default ()
      | ASSERT _ ->
	 self#analyzeFwd' cmd
      | _ ->
	 default ()
        
  method private get_transition_table (name:string) =
    if H.mem policytable name then
      H.find policytable name
    else
      raise (CHFailure (LBLOCK [ STR "Policy " ; STR name ; STR " not found" ]))
    
  method! analyzeOperation ~(domain_name:string) ~(fwd_direction:bool)
                           ~(operation:operation_t):'a =
    let name = operation.op_name#getBaseName in
    let policyname = List.hd operation.op_name#getAttributes in
    let transitiontable = self#get_transition_table policyname in
    let table' = table#clone in
    let default () = {<table = table' >} in
    match name with
      "initialize" ->
      begin
        List.iter (fun (_,v,_) ->
            self#setValue' table' v (new symbolic_set_t [new symbol_t "start"])) operation.op_args ;
        default ()
      end
    | _ ->
       if H.mem transitiontable name then
         let preposts = H.find transitiontable name in
         begin
           List.iter (fun (_sym,v,_) ->
               if fwd_direction then
                 let states = self#getValue' v in
                 if states#isTop || states#isBottom then
                   self#setValue' table' v states
                 else
                   let states' = new SymbolCollections.set_t in
                   begin
                     states#iter (fun s ->
                         if H.mem preposts s#getBaseName then
                           states'#add (H.find preposts s#getBaseName)
                         else
                           states'#add (new symbol_t "error")) ;
                     self#setValue' table' v (new symbolic_set_t states'#toList)
                   end
               else
		 table'#remove v) operation.op_args ;
           default ()
         end
       else
         raise (CHFailure (LBLOCK [ STR "State transition " ; STR name ;
                                    STR " not recognized" ]))
      
end
  
