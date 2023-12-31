(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
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
open CHDomainObserver
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues
open CHNumerical
open CHNumericalConstraints
open CHPEPRange
open CHPEPRTypes
open CHPretty

module H = Hashtbl

let pr_trace = pr_trace 2

class type pepr_domain_no_arrays_int =
  object ('a)

    (* operations *)
    method analyzeBwd: (code_int, cfg_int) command_t -> 'a
    method analyzeBwdInTransaction: (code_int,cfg_int) command_t -> 'a
    method analyzeFwd: (code_int, cfg_int) command_t -> 'a
    method analyzeFwdInTransaction: (code_int,cfg_int) command_t -> 'a
    method analyzeOperation:
             domain_name:string -> fwd_direction:bool -> operation:operation_t -> 'a

    method importNonRelationalValues:
             ?refine:bool -> (variable_t * non_relational_domain_value_t) list -> 'a
    method importNumericalConstraints: numerical_constraint_t list -> 'a

    method clone: 'a
    method setDownlink: (string -> 'a) -> unit
    method join: ?variables:variable_t list -> 'a -> 'a
    method meet: ?variables:variable_t list -> 'a -> 'a
    method widening: ?kind:string -> ?variables:variable_t list -> 'a -> 'a
    method narrowing: ?variables:variable_t list -> 'a -> 'a

    method projectOut: variable_t list -> 'a
    method special: string -> domain_cmd_arg_t list -> 'a

    method mkBottom: 'a
    method mkEmpty: 'a

    (* accessors *)
    method getNonRelationalValue: variable_t -> non_relational_domain_value_t

    method observer: domain_observer_t

    (* predicates *)
    method isBottom: bool
    method isRelational: bool
    method equal: 'a -> bool
    method leq: ?variables:variable_t list -> 'a -> bool

    (* printing *)
    method toPretty: pretty_t

  end


class pepr_domain_no_arrays_t
        (params:pepr_params_int)
        (timeout:float):pepr_domain_no_arrays_int =
object (self:'a)

  inherit non_relational_domain_t

  val params = params
  val starttime = Unix.gettimeofday ()

  (* env: auxiliary variable that keeps track of local parameter relationships
     depvalues: cache of parameter relationships to transfer values from ASSERT
                to ASSIGN instructions *)
  val env = new variable_t (new symbol_t "$env$") NUM_VAR_TYPE
  val depvalues = H.create 1

  method private getValue' v =
    if self#is_parameter v then
      mk_parameter_pepr_value (params#variable_index v) params#size
    else
      match (self#getValue v)#getValue with
      | PEPR_VAL v -> v
      | TOP_VAL -> top_pepr_value
      | _ ->
         raise (CHFailure (LBLOCK [ STR "Parametric range value expected for " ;
                                    v#toPretty ; STR "; found value: " ;
                                    (self#getValue v)#toPretty ]))

  method private setValue' t v x =
    if self#is_parameter v then
      self#abstractVariables t [v]
    else
      self#setValue t v (new non_relational_domain_value_t (PEPR_VAL x))

  method private showVariables =
    let vars = self#observer#getObservedVariables in
    List.iter (fun v ->
        let r = self#getValue' v in
        pr_trace [ v#toPretty ; STR ": " ; r#toPretty ; NL ]) vars

  method special _cmd _args = {< >}

  method private is_parameter (v:variable_t) = params#has_variable v

  method private importValue v =
    new non_relational_domain_value_t (PEPR_VAL v#toPEPRValue)

  method private analyzeFwd' (cmd:(code_int, cfg_int) command_t) =
    let _ =
      if ((Unix.gettimeofday ()) -. starttime) > timeout then
           raise (CHTimeOut "pepr") in
    if bottom then
      self#mkBottom
    else
      try
        let table' = table#clone in
        let default () =
          {< table = table' >} in
        let _ = self#showVariables in
        match cmd with
        | ABSTRACT_VARS l ->
           begin
             self#abstractVariables table' l;
             default ()
           end
        | ASSIGN_NUM (v, NUM n) ->
           let dv =
             if v#equal env then
               H.find depvalues n#toInt
             else
               mk_singleton_pepr_value n in
           let _ = pr_trace [ NL ; STR "ASSIGN " ; v#toPretty ; STR " := " ; dv#toPretty ; NL ] in
           begin
             self#setValue' table' v dv;
             default ()
           end
        | ASSIGN_NUM (v, NUM_VAR w) ->
           let _ = pr_trace [ NL ; STR "ASSIGN " ; v#toPretty ; STR " := " ; w#toPretty ;
                              STR " (" ; (self#getValue' w)#toPretty ; STR ")" ; NL ] in
           begin
             self#setValue' table' v (self#getValue' w);
             default ()
           end
        | ASSIGN_NUM (v, PLUS (x,y)) ->
           let _ = pr_trace
                     [ NL ; STR "ASSIGN " ; v#toPretty ; STR " := " ; 
                       x#toPretty ; STR " + " ; y#toPretty ; NL ;
                       INDENT(3, LBLOCK [ STR " (" ; (self#getValue' x)#toPretty ; STR ")"]) ; NL ;
                       INDENT(3, LBLOCK [ STR " (" ; (self#getValue' y)#toPretty ; STR ")"]) ; NL ] in
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           begin
             self#setValue' table' v (x_i#add y_i) ;
             default ()
           end
        | ASSIGN_NUM (v, MINUS (x,y)) ->
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           begin
             self#setValue' table' v (x_i#sub y_i);
             default ()
           end
        | ASSIGN_NUM (v, MULT (x,y)) ->
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           begin
             self#setValue' table' v (x_i#mult y_i) ;
             default ()
           end
        | ASSIGN_NUM (v, DIV (x,y)) ->
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           begin
             self#setValue' table' v (x_i#div y_i) ;
             default ()
           end
        | INCREMENT (x,n) ->
           let _ = pr_trace [ NL ; STR "INCREMENT " ; x#toPretty ; STR " by " ; n#toPretty ; NL ] in
           let x_i = self#getValue' x in
           begin
             self#setValue' table' x (x_i#add (mk_singleton_pepr_value n)) ;
             default ()
           end
        | READ_NUM_ELT (x,_,_) ->
           begin
             table'#remove x ;
             default ()
           end
        | ASSERT TRUE -> default ()
        | ASSERT FALSE -> self#mkBottom
        | ASSERT (LEQ (x,y)) ->
           let _ = pr_trace
                     [ NL ; STR "ASSERT " ; x#toPretty ; STR " <= " ; y#toPretty ; NL ;
                       INDENT (3, LBLOCK [STR " (" ; (self#getValue' x)#toPretty ; STR ")"]) ; NL ;
                       INDENT (3, LBLOCK [STR " (" ; (self#getValue' y)#toPretty ; STR ")"]) ; NL ] in
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           let envalue = self#getValue' env in
           let _ = pr_trace [ STR "Env value: " ; envalue#toPretty ; NL ] in
           let (x_i',xdeps) = x_i#upper_bound y_i#get_max in
           let (y_i',ydeps) = y_i#lower_bound x_i#get_min in
           let _ = pr_trace [ STR "xdeps: " ; xdeps#toPretty ; NL ] in
           let _ = pr_trace [ STR "ydeps: " ; ydeps#toPretty ; NL ] in
           let envalue' = (envalue#meet xdeps)#meet ydeps in
           let envindex = envalue'#index in
           let _ = H.replace depvalues envindex envalue' in
           let _ = pr_trace [ STR "Set dependencies: " ; envalue'#toPretty ; NL ] in
           if x_i'#is_bottom || y_i'#is_bottom then
             let _ = pr_trace [ STR "ASSERT LEQ leads to bottom" ; NL ] in
             self#mkBottom
           else
             begin
               self#setValue' table' x x_i';
               self#setValue' table' y y_i';
               (default ())#analyzeFwd (ASSIGN_NUM (env, NUM (mkNumerical envindex))) 
             end
        | ASSERT(GEQ (x, y)) ->
           self#analyzeFwd' (ASSERT (LEQ (y,x)))
        | ASSERT (LT (x, y)) ->
           let _ = pr_trace
                     [ NL ; STR "ASSERT " ; x#toPretty ; STR " < " ; y#toPretty ; NL ;
                       INDENT (3, LBLOCK [STR " (" ; (self#getValue' x)#toPretty ; STR ")"]) ; NL ;
                       INDENT (3, LBLOCK [STR " (" ; (self#getValue' y)#toPretty ; STR ")"]) ; NL ] in
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           let envalue = self#getValue' env in
           let _ = pr_trace [ STR "Env value: " ; envalue#toPretty ; NL ] in
           let (x_i',xdeps) = x_i#strict_upper_bound y_i#get_max in
           let (y_i',ydeps) = y_i#strict_lower_bound x_i#get_min in
           let _ = pr_trace [ STR "xdeps: " ; xdeps#toPretty ; NL ] in
           let _ = pr_trace [ STR "ydeps: " ; ydeps#toPretty ; NL ] in
           let envalue' = (envalue#meet xdeps)#meet ydeps in
           let envindex = envalue'#index in
           let _ = H.replace depvalues envindex envalue' in
           let _ = pr_trace [ STR "Set dependencies: " ; envalue'#toPretty ; NL ] in
           if x_i'#is_bottom || y_i'#is_bottom then
             let _ = pr_trace [ STR "ASSERT LT leads to bottom" ; NL ] in
             self#mkBottom
           else
             begin
               self#setValue' table' x x_i' ;
               self#setValue' table' y y_i' ;
               (default ())#analyzeFwd (ASSIGN_NUM (env, NUM (mkNumerical envindex)))
             end
        | ASSERT (GT (x, y)) -> self#analyzeFwd' (ASSERT (LT (y, x)))
        | ASSERT (EQ (x, y)) ->     (* TBD: emit parameter relationship *)
           let _ = pr_trace
                     [ NL ; STR "ASSERT " ; x#toPretty ; STR " == " ; y#toPretty ; NL ;
                       INDENT (3, LBLOCK [STR " (" ; (self#getValue' x)#toPretty ; STR ")"]) ; NL ;
                       INDENT (3, LBLOCK [STR " (" ; (self#getValue' y)#toPretty ; STR ")"]) ; NL ] in
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           let new_i = x_i#meet y_i in
           if new_i#is_bottom then
             self#mkBottom
           else
             begin
               self#setValue' table' x new_i ;
               self#setValue' table' y new_i ;
               default ()
             end
        | ASSERT (NEQ (x,y)) ->
           let _ = pr_trace
                     [ NL ; STR "ASSERT " ; x#toPretty ; STR " != " ; y#toPretty ; NL ;
                       INDENT (3, LBLOCK [ STR " (" ; (self#getValue' x)#toPretty ; STR ")"]) ; NL ;
                       INDENT (3, LBLOCK [ STR " (" ; (self#getValue' y)#toPretty ; STR ")"]) ; NL ] in
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           begin
             match (x_i#singleton, y_i#singleton) with
             | (Some x_c, Some y_c) ->
                if x_c#equal y_c then
                  let _ = pr_trace  [ STR "constant value " ; x_c#toPretty ;
                                      STR " leads to bottom" ; NL ] in
                  self#mkBottom
                else
                  default ()
             | (Some x_c, _) ->
                if y_i#is_top then
                  default ()
                else if y_i#get_max#is_number && y_i#get_max#get_number#equal x_c then
                  self#analyzeFwd' (ASSERT (LT (y,x)))
                else if y_i#get_min#is_number && y_i#get_min#get_number#equal x_c then
                  self#analyzeFwd' (ASSERT (LT (x,y)))
                else
                  default ()
             | (_, Some y_c) ->
                if x_i#is_top then
                  default ()
                else if x_i#get_max#is_number && x_i#get_max#get_number#equal y_c then
                  self#analyzeFwd' (ASSERT (LT (x,y)))
                else if x_i#get_min#is_number && x_i#get_min#get_number#equal y_c then
                  self#analyzeFwd' (ASSERT (LT (y,x)))
                else
                  default ()
             | _ ->
                match (x_i#parameters, y_i#parameters) with
                | ( [ xp ], [ yp ]) ->
                   if xp = yp then
                     let _ = pr_trace  [ STR "parameter value " ; INT xp  ;
                                         STR " leads to bottom" ; NL ] in
                     self#mkBottom
                   else
                     default ()
                | ( [ xp ], _ ) ->
                   if y_i#is_top then
                     default ()
                   else
                     let maxpars = y_i#get_max#get_parameter_indices in
                     let minpars = y_i#get_min#get_parameter_indices in
                     if List.mem xp maxpars then
                       self#analyzeFwd' (ASSERT (LT (x,y)))
                     else if List.mem xp minpars then
                       self#analyzeFwd' (ASSERT (LT (y,x)))
                     else
                       default ()
                | ( _, [ yp ]) ->
                   if x_i#is_top then
                     default ()
                   else
                     let maxpars = x_i#get_max#get_parameter_indices in
                     let minpars = y_i#get_min#get_parameter_indices in
                     if List.mem yp maxpars then
                       self#analyzeFwd' (ASSERT (LT (x,y)))
                     else if List.mem yp minpars then
                       self#analyzeFwd' (ASSERT (LT (y,x)))
                     else
                       default ()
                | _ -> default ()
           end
        | _ -> default ()
      with
      | CHDomainFailure (d,p) ->
         let _ = pr_trace [ STR "Failure: " ; NL ]  in
         let _ = self#showVariables in
         raise (CHDomainFailure (d,p))
      | CHFailure p ->
         let _ = pr_debug [ STR "Failure in PEPR: " ; p ; NL ] in
         raise (CHDomainFailure("pepr",p))

  method private analyzeBwd' (cmd:(code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      try
        let table' = table#clone in
        let default () =
          {< table = table' >} in
        match cmd with
        | ABSTRACT_VARS l ->
           begin
             self#abstractVariables table' l ;
             default ()
           end
        | ASSIGN_NUM (x, NUM n) ->
           let _ = pr_trace [ NL ; STR "ASSIGN-BW: " ; x#toPretty ;
                              STR " := " ; n#toPretty ; NL ] in
           let x_i = self#getValue' x in
           let x_i' = x_i#meet (mk_singleton_pepr_value n) in
           if x_i'#is_bottom then
             self#mkBottom
           else
             begin
               table'#remove x;
               default ()
             end
        | ASSIGN_NUM (x, NUM_VAR y) ->
           let _ = pr_trace [ NL ; STR "ASSIGN-BW: " ; x#toPretty ;
                              STR " := " ; y#toPretty ; NL ] in
           let x_i = self#getValue' x in
           let y_i = self#getValue' y in
           let y_i' = y_i#meet x_i in
           if y_i'#is_bottom then
             self#mkBottom
           else
             begin
               table'#remove x;
               self#setValue' table' y y_i';
               default ()
             end
        | ASSIGN_NUM (x, PLUS (y,z)) ->
           let _ = pr_trace [ NL ; STR "ASSIGN-BW: " ; x#toPretty ; STR " := " ;
                              y#toPretty ; STR " + " ; z#toPretty ; NL ] in
           let x_i' = self#getValue' x in
           let y_i' = self#getValue' y in
           let z_i' = self#getValue' z in
           let y_i = if x#equal y then top_pepr_value else y_i' in
           let z_i = if x#equal z then top_pepr_value else z_i' in
           let y_i'' = y_i#meet (x_i'#sub z_i) in
           let z_i'' = z_i#meet (x_i'#sub y_i) in
           if y_i''#is_bottom || z_i''#is_bottom then
             self#mkBottom
           else
             begin
               table'#remove x;
               self#setValue' table' y y_i'' ;
               self#setValue' table' z z_i'' ;
               default ()
             end
        | ASSIGN_NUM (x, MINUS (y,z)) ->
           let _ = pr_trace [ NL ; STR "ASSIGN-BW: " ; x#toPretty ; STR " := " ;
                              y#toPretty ; STR " - " ; z#toPretty ; NL ] in
           let x_i' = self#getValue' x in
           let y_i' = self#getValue' y in
           let z_i' = self#getValue' z in
           let y_i = if x#equal y then top_pepr_value else y_i' in
           let z_i = if x#equal z then top_pepr_value else z_i' in
           let y_i'' = y_i#meet (x_i'#add z_i) in
           let z_i'' = z_i#meet (y_i#sub x_i') in
           if y_i''#is_bottom || z_i''#is_bottom then
             self#mkBottom
           else
             begin
               table'#remove x;
               self#setValue' table' y y_i'';
               self#setValue' table' z z_i'';
               default ()
             end
        | ASSIGN_NUM (v, MULT (_x, _y)) ->
           begin
             table'#remove v ;
             default ()
           end
        | ASSIGN_NUM (v, DIV (_x, _y)) ->
           begin
             table'#remove v ;
             default ()
           end
        | INCREMENT (x, n) ->
           let _ = pr_trace [ NL ; STR "INCREMENT-BW " ;
                              x#toPretty ; STR " by " ; n#toPretty ; NL ] in
           let x_i = self#getValue' x in
           begin
             self#setValue' table' x (x_i#sub (mk_singleton_pepr_value n)) ;
             default ()
           end
        | READ_NUM_ELT (x, _, _) ->
           begin
             table'#remove x;
             default ()
           end
        | ASSERT _ -> self#analyzeFwd' cmd
        | _ -> default ()
      with
      | CHDomainFailure (d,p) ->
         let _ = pr_trace [ STR "Failure: " ; NL ]  in
         let _ = self#showVariables in
         raise (CHDomainFailure (d,p))


end
   
let mk_pepr_domain_no_arrays = new pepr_domain_no_arrays_t
