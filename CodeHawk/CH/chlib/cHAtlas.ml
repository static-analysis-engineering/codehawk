(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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
open CHDomain   
open CHLanguage
open CHNonRelationalDatabase   
open CHPretty
open CHSigmaCombinator   
open CHUtils


class atlas_t
        ?(db_num = "<?>")
        ?(db_sym = "<?>")
        ?(sigmas = [])
        (doms: (string * domain_int) list) =
object (self: 'a)

 (** The initial domain values are used whenever a domain is activated
     or reactivated. *)
  val initials: domain_int StringCollections.table_t =  new StringCollections.table_t
  
  val domains: domain_int StringCollections.table_t = new StringCollections.table_t

  val database: non_relational_database_t = new non_relational_database_t

  val reductions: ('a sigma_combinator_int) list = sigmas

  val db_num_domain = db_num

  val db_sym_domain = db_sym

  initializer
    List.iter (fun (s, d) -> initials#set s d; d#setDownlink self#getDomain) doms

  method getDatabase = database

  method getDomains = domains#listOfKeys

  method hasRelationalDomain =
    domains#fold (fun a _ d -> a || d#isRelational) false
      
  method getDomain (s: string) =
    match domains#get s with
      | None -> raise (CHFailure (LBLOCK [STR "Domain "; STR s; STR " not found"]))
      | Some d -> d

  method private hasDomain (s: string) =
    match domains#get s with
    | None -> false
    | _ -> true
	  
  method setDomains (l : (string * domain_int) list) =
    let domains' = new StringCollections.table_t in
    let _ =
      domains#iter (fun n d -> 
	  let d' = try
	      List.assoc n l
	    with Not_found -> d
	  in
	  domains'#set n d')
    in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method updateDownlinks =
    domains#iter (fun _ d -> d#setDownlink self#getDomain)
    
  method private checkCompatibility (a: 'a) =
    let names = new StringCollections.set_t in
    let names' = new StringCollections.set_t in
    let _ = names#addList domains#listOfKeys in
    let _ = names'#addList a#getDomains in
    if names#equal names' then
      ()
    else
      raise (CHFailure (LBLOCK [STR "Incompatible atlas structures: ";
                                names#toPretty; STR " and "; names'#toPretty]))
    
  method mkBottom =
    let domains' = new StringCollections.table_t in
    let _ = domains#iter (fun n d -> domains'#set n d#mkBottom) in
    {< domains = domains' >}
    
  method mkEmpty =
    let domains' = new StringCollections.table_t in
    let _ = domains#iter (fun n d -> domains'#set n d#mkEmpty) in
    {< domains = domains' >}
    
  method isBottom = 
    try
      let _ = domains#iter (fun _ d -> if d#isBottom then raise Found else ()) in
      false
    with Found -> true
                
  method leq ?variables (a: 'a) =
    let _ = self#checkCompatibility a in
    let names = domains#listOfKeys in
    List.fold_left (fun acc s ->
        acc && (self#getDomain s)#leq ?variables (a#getDomain s)) true names
    && database#leq a#getDatabase
    
  method equal (a: 'a) =
    let _ = self#checkCompatibility a in
    let names = domains#listOfKeys in
    List.fold_left (fun acc s -> acc && (self#getDomain s)#equal (a#getDomain s)) true names
    && database#equal a#getDatabase
    
  method meet ?variables (a: 'a) =
    let _ = self#checkCompatibility a in
    let names = domains#listOfKeys in
    let domains' = new StringCollections.table_t in
    let _ =
      List.iter (fun s ->
          domains'#set s ((self#getDomain s)#meet ?variables (a#getDomain s))) names in
    let atlas = {< domains = domains'; database = database#meet a#getDatabase >} in
    let _ = atlas#updateDownlinks in
    atlas#reduce
    
  method join ?variables (a: 'a) =
    let _ = self#checkCompatibility a in
    let names = domains#listOfKeys in
    let domains' = new StringCollections.table_t in
    let _ =
      List.iter (fun s ->
          domains'#set s ((self#getDomain s)#join ?variables (a#getDomain s))) names in
    let atlas = {< domains = domains'; database = database#join a#getDatabase >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method widening ?kind ?variables (a: 'a) =
    let _ = self#checkCompatibility a in
    let names = domains#listOfKeys in
    let domains' = new StringCollections.table_t in
    let _ =
      List.iter (fun s ->
          domains'#set s ((self#getDomain s)#widening ?kind ?variables (a#getDomain s))) names in
    let atlas = {< domains = domains'; database = database#widening a#getDatabase >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method narrowing ?variables (a: 'a) =
    let _ = self#checkCompatibility a in
    let names = domains#listOfKeys in
    let domains' = new StringCollections.table_t in
    let _ =
      List.iter (fun s ->
          domains'#set s ((self#getDomain s)#narrowing ?variables (a#getDomain s))) names in
    let atlas = {< domains = domains'; database = database#narrowing a#getDatabase >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method reduce =
    List.fold_left (fun a sigma -> sigma#reduce a) self reductions
    
  method toPretty = 
    if self#isBottom then
      STR "_|_"
    else
      LBLOCK [domains#toPretty; NL; database#toPretty]
    
  method sendCmd dom cmd args =
    let domain = self#getDomain dom in
    let domains' = domains#clone in
    let _ = domains'#set dom (domain#special cmd args) in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method private analyzeFwd' ~in_transaction (cmd: (code_int, cfg_int) command_t) =
    let domains' = new StringCollections.table_t in
    let _ =
      domains#iter (fun s d ->
          domains'#set
            s
            (if in_transaction then d#analyzeFwdInTransaction cmd else d#analyzeFwd cmd)) in      
    let database' = match cmd with
      | ABSTRACT_VARS vars ->
	 let tables = List.filter (fun v -> v#isTable) vars in
	 begin
	   match tables with
	   | [] -> database
	   | _ -> database#removeTables tables
	 end
      | _ -> database 
    in
    let atlas = {< domains = domains'; database = database' >} in
    let _ = atlas#updateDownlinks in
    match cmd with
    | ASSERT _ -> atlas#reduce
    | _ -> atlas
	 
  method private analyzeBwd' ~in_transaction (cmd: (code_int, cfg_int) command_t) =
    let domains' = new StringCollections.table_t in
    let _ =
      domains#iter (fun s d ->
          domains'#set
            s
            (if in_transaction then d#analyzeBwdInTransaction cmd else d#analyzeBwd cmd)) in
    let database' = match cmd with
      | ABSTRACT_VARS vars ->
	 let tables = List.filter (fun v -> v#isTable) vars in
	 begin
	   match tables with
	   | [] -> database
	   | _ -> database#removeTables tables
	 end
      | _ -> database 
    in
    let atlas = {< domains = domains'; database = database' >} in
    let _ = atlas#updateDownlinks in
    match cmd with
    | ASSERT _ -> atlas#reduce
    | _ -> atlas
         
  method analyzeFwd (cmd: (code_int, cfg_int) command_t) =
    self#analyzeFwd' ~in_transaction:false cmd
                                                         
  method analyzeBwd (cmd: (code_int, cfg_int) command_t) =
    self#analyzeBwd' ~in_transaction:false cmd
    
  method analyzeFwdInTransaction (cmd: (code_int, cfg_int) command_t) =
    self#analyzeFwd' ~in_transaction:true cmd
    
  method analyzeBwdInTransaction (cmd: (code_int, cfg_int) command_t) =
    self#analyzeBwd' ~in_transaction:true cmd
    
  method domainOperation fwd_direction doms operation =
    let domains' = domains#clone in
    let _ =
      List.iter (fun dom ->
          if self#hasDomain dom then
	    let domain = self#getDomain dom in
	    domains'#set
              dom
              (domain#analyzeOperation
                 ~domain_name:dom ~fwd_direction:fwd_direction ~operation:operation)
          else
	    ()
        ) doms
    in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas    
    
  method clone =
    let domains' = new StringCollections.table_t in
    let _ = domains#iter (fun s d -> domains'#set s d#clone) in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method activateDomains doms =
    let domains' = domains#clone in
    let activate dom =
      if domains'#has dom then
	()
      else
	match initials#get dom with
	| None -> raise (CHFailure (LBLOCK [STR "Unknown domain: "; STR dom]))
	| Some i -> domains'#set dom i
    in
    let _ = List.iter activate doms in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method deactivateDomains doms =
    let domains' = domains#clone in
    let _ = List.iter (fun dom -> domains'#remove dom) doms in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method move ~relational ~vars ~src ~tgt =
    let domains' = domains#clone in
    let src_dom = self#getDomain src in
    let tgt_dom = self#getDomain tgt in
    let tgt_dom' =
      if not(relational) then
        let var_obs = src_dom#observer#getNonRelationalVariableObserver in
        let env = List.map (fun v -> (v, var_obs v)) vars in
	tgt_dom#importNonRelationalValues ~refine:true env
      else
        let csts = src_dom#observer#getNumericalConstraints ~variables:(Some vars) () in
	tgt_dom#importNumericalConstraints csts
    in
    if tgt_dom'#isBottom then
      self#mkBottom
    else
      let _ = domains'#set tgt tgt_dom' in
      let atlas = {< domains = domains' >} in
      let _ = atlas#updateDownlinks in
      atlas
      
  method analyzeDBQuery (cmd: (code_int, cfg_int) command_t) =
    let domains' = new StringCollections.table_t in
    let env = database#analyzeQuery
                ~db_num:(self#getDomain db_num_domain)
                ~db_sym:(self#getDomain db_sym_domain)
                ~cmd:cmd in
    let _ =
      domains#iter (fun s d ->
          domains'#set s (d#importNonRelationalValues ~refine:false env)) in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method analyzeDBQueryNoDB (cmd: (code_int, cfg_int) command_t) =
    let domains' = new StringCollections.table_t in
    let env = database#analyzeQueryNoDB cmd in
    let _ =
      domains#iter (fun s d ->
          domains'#set s (d#importNonRelationalValues ~refine:false env)) in
    let atlas = {< domains = domains' >} in
    let _ = atlas#updateDownlinks in
    atlas
    
  method analyzeDBUpdate (cmd: (code_int, cfg_int) command_t) =
    {< database = database#analyzeUpdate
                    ~db_num:(self#getDomain db_num_domain)
                    ~db_sym:(self#getDomain db_sym_domain)
                    ~cmd:cmd >}
	
end
