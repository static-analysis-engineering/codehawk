(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHAtlas
open CHCommon
open CHDomain   
open CHLanguage   
open CHNumerical
open CHPretty
open CHStack   
open CHUtils

exception Found_breakout_fwd
exception Found_breakout_bwd of atlas_t
exception Not_stable

type op_semantics_t =
  invariant: atlas_t
  -> stable: bool
  -> fwd_direction: bool
  -> context: symbol_t stack_t
  -> operation: operation_t -> atlas_t

type cmd_processor_t =
  invariant: atlas_t
  -> context: symbol_t stack_t
  -> cmd: (code_int, cfg_int) command_t
  -> (code_int, cfg_int) command_t

type proc_semantics_t =
  invariant: atlas_t
  -> stable: bool
  -> context: symbol_t stack_t
  -> procedure: symbol_t
  -> args: (symbol_t * variable_t) list
  -> atlas_t

type iteration_strategy_t = {
    widening: int -> bool * string;
    narrowing: int -> bool;
  }

type iteration_mode_t =
  | WIDENING_MODE
  | NARROWING_MODE
  | STABLE_MODE
  | BREAKOUT_POINT of symbol_t * (atlas_t ref)
                    
class boxed_mode_t mode =
object
  
  val mode = mode
           
  method getMode = mode
                 
  method toPretty =
    match mode with
    | WIDENING_MODE -> STR "WIDENING_MODE"
    | NARROWING_MODE -> STR "NARROWING_MODE"
    | STABLE_MODE -> STR "STABLE_MODE"
    | BREAKOUT_POINT (s, breakout_inv) ->
       LBLOCK [STR "BREAKOUT_POINT: "; s#toPretty; STR " => "; (!breakout_inv)#toPretty]
      
end
  
open CHSCC
   
module CFGAtlasTable =
  CHAtlasTable.Make
    (struct
      type t = symbol_t
      let compare s1 s2 = s1#compare s2
      let toPretty s = s#toPretty
    end)
  
  
module FwdBwdTable = 
  CHCollections.Make
    (struct
      type t = int * int
      let compare = Stdlib.compare
      let toPretty (id1, id2) = LBLOCK [INT id1; STR "@"; INT id2]
    end)
  
class fwd_graph_t (g: cfg_int) =
object
  
  val graph = g
            
  method getRootNode = graph#getEntry#getLabel
                     
  method getNextNodes s = (graph#getState s)#getOutgoingEdges
                        
end
  
class bwd_graph_t (g: cfg_int) =
object
  
  val graph = g
            
  method getRootNode = graph#getExit#getLabel
                     
  method getNextNodes s = (graph#getState s)#getIncomingEdges
                        
end
  
class loop_counter_factory_t =
object (self: _)
     
  val mutable count = 1
                    
  method reset = count <- 1
               
  method mkSCCCounterName (head: symbol_t) =
    new symbol_t ~atts:(head#getSymbol) "SCC_COUNTER"
    
  method mkSCCCounter (head: symbol_t) =
    new variable_t (self#mkSCCCounterName head) NUM_LOOP_COUNTER_TYPE
    
  method mkCounter = 
    let v = new variable_t
                (new symbol_t "LOOP_COUNTER")
                ~suffix:count NUM_LOOP_COUNTER_TYPE in
    let _ = count <- count + 1 in
    v
    
end
  
class iterator_t
        ?(db_enabled = true)
        ?strategy ?(do_narrowing = true)
        ?(do_loop_counters = false)
        ?op_semantics ?cmd_processor
        ?proc_semantics system =
object (self: _)
     
  val system: system_int = system
                         
  val strategy: iteration_strategy_t = 
    match strategy with
    | Some s -> s
    | None -> {widening = (fun i -> (i >= 2, "")); narrowing = (fun i -> i >= 2)}
            
  val do_narrowing = do_narrowing
                   
  val do_loop_counters = do_loop_counters
                       
  val op_semantics: op_semantics_t option = op_semantics
                                          
  val cmd_processor: cmd_processor_t option = cmd_processor
                                            
  val proc_semantics: proc_semantics_t option = proc_semantics
                                              
  val iteration_stack = new stack_t
                      
  val goto_table_stack = new stack_t
                       
  val loop_counter_factory = new loop_counter_factory_t
                           
  method private activeDomains domains =
    let ds = domains#listFromTop in
    let active = new StringCollections.set_t in
    let _ = List.iter (fun d -> active#addList d) ds in
    active
    
  method private stable =
    let l = iteration_stack#listFromTop in
    List.fold_left (fun a m ->
        a && (match m with STABLE_MODE | BREAKOUT_POINT _ -> true | _ -> false)) true l
    
  method private getInv table s =
    match table#get s with
    | None -> raise (CHFailure (LBLOCK [STR "State "; s#toPretty;
                                        STR " not found in invariant table"]))
    | Some inv -> inv
	        
  method private propagateInv
                   fwd_bwd
                   iterate_on_transactions
                   iterate_on_relations
                   modified
                   context
                   domains
                   loop_stack_table
                   loop_mode_table
                   inv_table
                   loop_counter_table
                   src
                   tgt
                   inv =
    let mods = modified#clone in
    let get_loop_counter head = loop_counter_factory#mkSCCCounter head in
    let add_loop_counter head pre =
      if do_loop_counters then
	let loop_counter = get_loop_counter head in
	self#analyzeFwd
          ~in_transaction:false
          ~iterate_on_transactions:iterate_on_transactions
          ~iterate_on_relations:iterate_on_relations 
	  ~fwd_bwd:fwd_bwd
          ~modified:mods
          ~context:context
          ~domains:domains
          ~pre:pre
          ~cmd:(ASSIGN_NUM (loop_counter, NUM numerical_one))
      else
	pre
    in
    let add_loop_counters pre suffix =
      List.fold_left (fun inv head -> add_loop_counter head inv) pre suffix
    in
    let remove_loop_counter head pre =
      if do_loop_counters then
	let loop_counter = get_loop_counter head in
	self#analyzeFwd
          ~in_transaction:false
          ~iterate_on_transactions:iterate_on_transactions
          ~iterate_on_relations:iterate_on_relations 
	  ~fwd_bwd:fwd_bwd
          ~modified:mods
          ~context:context
          ~domains:domains
          ~pre:pre
          ~cmd:(ABSTRACT_VARS [loop_counter])
      else
	pre
    in    
    let remove_loop_counters pre suffix =
      List.fold_left (fun inv head -> remove_loop_counter head inv) pre suffix
    in
    let propagate invariant =
      match inv_table#get tgt with
      | None -> inv_table#set tgt invariant
      | Some inv' -> inv_table#set tgt (inv'#join ?variables:(Some mods#toList) invariant)
    in
    match (loop_stack_table#get src, loop_stack_table#get tgt) with
    | (Some src_stack, Some tgt_stack) ->
       let (src_suffix, tgt_suffix) = src_stack#delta tgt_stack in
       let src_suffix_is_stable =
         List.fold_left 
	   (fun a s ->
             a && 
	       (match loop_mode_table#get s with 
	        | None -> raise (CHFailure (STR "Internal error in loop table"))
	        | Some mode when mode#getMode = STABLE_MODE -> true 
	        | _ -> false)
	   ) true src_suffix#getStack 
       in
       if src_suffix_is_stable then
	 propagate (add_loop_counters
                      (remove_loop_counters inv src_suffix#getStack) tgt_suffix#getStack)
       else
	 ()
    | (_, _) -> raise (CHFailure (LBLOCK [STR "Internal error in loop stack"]))
	      
  method private analyzeCFG
                   ~must_terminate
                   ~iterate_on_transactions
                   ~iterate_on_relations
                   ~fwd_bwd
                   ~modified
                   ~context 
                   ~domains
                   ~inv_table
                   ~loop_counter_table
                   ~cfg
                   ~wto
                   ~fwd
                   ~graph
                   ~loop_stack_table
                   ~loop_mode_table =
    List.iter
      (fun comp ->
	match comp with
	| SCC (((VERTEX head) :: _) as wto) ->
	   let mods = new VariableCollections.set_t in
	   let loop_counter = loop_counter_factory#mkSCCCounter head in
	   let _ = loop_counter_table#set head loop_counter in
	   let _ =
             if do_loop_counters then
	       let head_inv = self#getInv inv_table head in
	       inv_table#set
                 head
                 (self#analyzeFwd
                    ~in_transaction:false
                    ~iterate_on_transactions:iterate_on_transactions
                    ~iterate_on_relations:iterate_on_relations 
		    ~fwd_bwd:fwd_bwd
                    ~modified:mods
                    ~context:context
                    ~domains:domains
                    ~pre:head_inv
                    ~cmd:(ASSIGN_NUM (loop_counter, NUM numerical_zero)))
	     else
	       ()
	   in
	   let initial = self#getInv inv_table head in
	   let stride mod_vars =
	     let _ =
               if do_loop_counters then
		 let head_inv = self#getInv inv_table head in
		 inv_table#set
                   head
                   (self#analyzeFwd
                      ~in_transaction:false
                      ~iterate_on_transactions:iterate_on_transactions
                      ~iterate_on_relations:iterate_on_relations 
		      ~fwd_bwd:fwd_bwd
                      ~modified:mod_vars
                      ~context:context
                      ~domains:domains
                      ~pre:head_inv
                      ~cmd:(INCREMENT (loop_counter, numerical_one)))
	       else
		 ()
	     in
	     self#analyzeCFG
               ~must_terminate:must_terminate
               ~iterate_on_transactions:iterate_on_transactions
               ~iterate_on_relations:iterate_on_relations 
	       ~fwd_bwd:fwd_bwd
               ~modified:mod_vars
               ~context:context
               ~domains:domains
               ~inv_table:inv_table 
	       ~loop_counter_table:loop_counter_table
               ~cfg:cfg
               ~wto:wto
               ~fwd:fwd 
	       ~graph:graph
               ~loop_stack_table:loop_stack_table
               ~loop_mode_table:loop_mode_table
	   in
	   let finish () =
	     let _ = iteration_stack#push STABLE_MODE in
	     let _ = loop_mode_table#set head (new boxed_mode_t STABLE_MODE) in
	     let _ = modified#addList mods#toList in
	     let _ = stride modified in
	     let _ = if do_loop_counters then modified#remove loop_counter else () in
	     let _ = iteration_stack#pop in
	     let _ = loop_mode_table#remove head in
	     let _ = inv_table#remove head in
	     ()
	   in
	   let rec down_iteration pre i =
	     let _ = iteration_stack#push NARROWING_MODE in
	     let _ = loop_mode_table#set head (new boxed_mode_t NARROWING_MODE) in
	     let _ = stride mods in
	     let _ = iteration_stack#pop in
	     let _ = loop_mode_table#remove head in
	     let mods_l = mods#toList in
	     let post = initial#join ?variables:(Some mods_l) (self#getInv inv_table head) in
	     let narrowed =
               if strategy.narrowing i then
                 pre#narrowing ?variables:(Some mods_l) post
               else pre#meet ?variables:(Some mods_l) post in
	     if pre#leq ?variables:(Some mods_l) narrowed then
	       let _ = inv_table#set head pre in
	       finish ()
	     else
	       down_iteration narrowed (i + 1)
	   in
	   let rec up_iteration pre i =
	     let _ = iteration_stack#push WIDENING_MODE in
	     let _ = loop_mode_table#set head (new boxed_mode_t WIDENING_MODE) in
	     let _ = stride mods in
	     let _ = iteration_stack#pop in
	     let _ = loop_mode_table#remove head in
	     let mods_l = mods#toList in
	     let post = initial#join ?variables:(Some mods_l) (self#getInv inv_table head) in
	     if post#leq ?variables:(Some mods_l) pre then
	       let _ = inv_table#set head post in
	       if do_narrowing then
		 down_iteration post 1
	       else
		 finish ()
	     else
	       let widening = strategy.widening i in
	       let widened =
                 if fst widening then
		   let kind = snd widening in
		   if kind = "" then
		     pre#widening ?kind:None ?variables:(Some mods_l) post
		   else
		     pre#widening ?kind:(Some kind) ?variables:(Some mods_l) post
		 else
		   pre#join ?variables:(Some mods_l) post
	       in
	       let _ = inv_table#set head widened in
	       up_iteration widened (i + 1)
	   in
	   up_iteration initial 1
	| VERTEX s ->
	   let cmd = (cfg#getState s)#getCode in
	   let inv = self#getInv inv_table s in
	   let sym = new symbol_t "vertex" in
	   let inv' =
             if fwd then
	       if cfg#getExit#getLabel#equal s then
		 inv
	       else
		 let _ = inv_table#remove s in
		 self#analyzeFwd
                   ~in_transaction:false
                   ~iterate_on_transactions:iterate_on_transactions
                   ~iterate_on_relations:iterate_on_relations
		   ~fwd_bwd:fwd_bwd
                   ~modified:modified
                   ~context:context
                   ~domains:domains
                   ~pre:inv
                   ~cmd:(CODE (sym, cmd))
	     else
	       if cfg#getEntry#getLabel#equal s then
		 inv
	       else
		 let _ = inv_table#remove s in
		 self#analyzeBwd
                   ~in_transaction:false
                   ~must_terminate:must_terminate
                   ~iterate_on_transactions:iterate_on_transactions 
		   ~iterate_on_relations:iterate_on_relations
                   ~fwd_bwd:fwd_bwd
                   ~modified:modified
                   ~context:context 
		   ~domains:domains
                   ~post:inv
                   ~cmd:(CODE (sym, cmd))
	   in
	   let nexts = graph#getNextNodes s in
	   List.iter (fun next ->
               self#propagateInv
                 fwd_bwd
                 iterate_on_transactions
                 iterate_on_relations
                 modified
                 context 
		 domains
                 loop_stack_table
                 loop_mode_table
                 inv_table
                 loop_counter_table
                 s
                 next
                 inv') nexts
	| _ ->
	   raise (CHFailure (STR "Internal error in wto"))
      ) wto
    
  method private analyzeCFGBwd
                   ~must_terminate
                   ~iterate_on_transactions
                   ~iterate_on_relations
                   ~fwd_bwd
                   ~modified
                   ~context
                   ~domains
                   ~post
                   ~cfg =
    let graph = new bwd_graph_t cfg in
    let engine = new wto_engine_t graph in
    let wto = engine#computeWTO in
    let inv_table = new SymbolCollections.table_t in
    let loop_counter_table = new SymbolCollections.table_t in
    let _ = inv_table#set cfg#getExit#getLabel post in
    let entry = cfg#getEntry in
    let _ =
      self#analyzeCFG
        ~must_terminate:must_terminate
        ~iterate_on_transactions:iterate_on_transactions
        ~iterate_on_relations:iterate_on_relations 
        ~fwd_bwd:fwd_bwd
        ~modified:modified
        ~context:context
        ~domains:domains
        ~inv_table:inv_table
        ~loop_counter_table:loop_counter_table 
        ~cfg:cfg
        ~wto:wto
        ~fwd:false
        ~graph:graph
        ~loop_stack_table:engine#getLoopStackTable
        ~loop_mode_table:(new SymbolCollections.table_t)
    in
    let reachable = new SymbolCollections.set_t in
    let states = new SymbolCollections.set_t in
    let _ = reachable#addList (cfg#getStatesFrom cfg#getExit#getLabel) in
    let _ = states#addList cfg#getStates in
    let unreachable = states#diff reachable in
    let sym = new symbol_t "state" in
    let _ =
      unreachable#iter (fun s ->
	  let state = cfg#getState s in
	  let _ = self#analyzeBwd
                    ~in_transaction:false
                    ~must_terminate:must_terminate
                    ~iterate_on_transactions:iterate_on_transactions 
		    ~iterate_on_relations:iterate_on_relations
                    ~fwd_bwd:fwd_bwd
                    ~modified:(new VariableCollections.set_t)
                    ~context:context 
		    ~domains:domains
                    ~post:post#mkBottom
                    ~cmd:(CODE (sym, state#getCode)) in
	  ())
    in
    let inv_at_entry = match inv_table#get entry#getLabel with
      | None -> 
	 (* The entry node is unreachable *)
	 post#mkBottom
      | Some inv -> inv
    in
    self#analyzeBwd
      ~in_transaction:false
      ~must_terminate:must_terminate
      ~iterate_on_transactions:iterate_on_transactions
      ~iterate_on_relations:iterate_on_relations 
      ~fwd_bwd:fwd_bwd
      ~modified:modified
      ~context:context
      ~domains:domains 
      ~post:inv_at_entry
      ~cmd:(CODE (sym, entry#getCode))
    
  method private analyzeCFGFwd
                   ~iterate_on_transactions
                   ~iterate_on_relations
                   ~fwd_bwd
                   ~modified
                   ~context
                   ~domains
                   ~pre
                   ~cfg =
    let graph = new fwd_graph_t cfg in
    let engine = new wto_engine_t graph in
    let wto = engine#computeWTO in
    let inv_table = new SymbolCollections.table_t in
    let loop_counter_table = new SymbolCollections.table_t in
    let _ = inv_table#set cfg#getEntry#getLabel pre in
    let exit = cfg#getExit in
    let _ = self#analyzeCFG
              ~must_terminate:false
              ~iterate_on_transactions:iterate_on_transactions
              ~iterate_on_relations:iterate_on_relations 
              ~fwd_bwd:fwd_bwd
              ~modified:modified
              ~context:context
              ~domains:domains 
              ~inv_table:inv_table
              ~loop_counter_table:loop_counter_table 
              ~cfg:cfg
              ~wto:wto
              ~fwd:true
              ~graph:graph
              ~loop_stack_table:engine#getLoopStackTable
              ~loop_mode_table:(new SymbolCollections.table_t)
    in
    let reachable = new SymbolCollections.set_t in
    let states = new SymbolCollections.set_t in
    let _ = reachable#addList (cfg#getStatesFrom cfg#getEntry#getLabel) in
    let _ = states#addList cfg#getStates in
    let unreachable = states#diff reachable in
    let sym = new symbol_t "state" in
    let _ =
      unreachable#iter (fun s ->
	  let state = cfg#getState s in
	  let _ = self#analyzeFwd
                    ~in_transaction:false
                    ~iterate_on_transactions:iterate_on_transactions
                    ~iterate_on_relations:iterate_on_relations 
		    ~fwd_bwd:fwd_bwd
                    ~modified:(new VariableCollections.set_t) 
		    ~context:context
                    ~domains:domains
                    ~pre:pre#mkBottom
                    ~cmd:(CODE (sym, state#getCode)) in
	  ())
    in
    let inv_at_exit = match inv_table#get exit#getLabel with
      | None -> 
	 (* The exit node is unreachable *)
	 pre#mkBottom
      | Some inv -> inv
    in
    self#analyzeFwd
      ~in_transaction:false
      ~iterate_on_transactions:iterate_on_transactions
      ~iterate_on_relations:iterate_on_relations 
      ~fwd_bwd:fwd_bwd
      ~modified:modified
      ~context:context
      ~domains:domains 
      ~pre:inv_at_exit
      ~cmd:(CODE (sym, exit#getCode))
	
  method private analyzeBwd_FwdBwd
                   ~in_transaction
                   ~iterate_on_transactions
                   ~iterate_on_relations
                   ~modified
                   ~context
                   ~domains
                   ~post
                   ~code =
    let sym = new symbol_t "code" in
    let cmd = CODE (sym, code) in
    let _ = iteration_stack#push NARROWING_MODE in
    let post' = 
      let rec loop i post =
	let mods = new VariableCollections.set_t in
	let pre = self#analyzeBwd
                    ~in_transaction:in_transaction
                    ~must_terminate:true
                    ~iterate_on_transactions:iterate_on_transactions 
	            ~iterate_on_relations:iterate_on_relations
                    ~fwd_bwd:None
                    ~modified:mods
                    ~context:context
                    ~domains:domains
                    ~post:post#clone
                    ~cmd:cmd in
	let post' = self#analyzeFwd
                      ~in_transaction:in_transaction
                      ~iterate_on_transactions:iterate_on_transactions
                      ~iterate_on_relations:iterate_on_relations
	              ~fwd_bwd:None
                      ~modified:mods
                      ~context:context
                      ~domains:domains
                      ~pre:pre
                      ~cmd:cmd in
	let mods_l = mods#toList in
	let narrowed =
          if strategy.narrowing i then
            post#narrowing ?variables:(Some mods_l) post'
          else
            post#meet ?variables:(Some mods_l) post' in
	if post#leq ?variables:(Some mods_l) narrowed then
	  post
	else
	  loop (i + 1) narrowed
      in
      loop 1 post
    in
    let _ = iteration_stack#pop in
    let _ = iteration_stack#push STABLE_MODE in
    let pre = self#analyzeBwd
                ~in_transaction:in_transaction
                ~must_terminate:true
                ~iterate_on_transactions:iterate_on_transactions
                ~iterate_on_relations:iterate_on_relations
                ~fwd_bwd:None
                ~modified:modified
                ~context:context
                ~domains:domains
                ~post:post'
                ~cmd:cmd in
    let _ = iteration_stack#pop in
    pre
	
  method private analyzeBwd
                   ~in_transaction
                   ~must_terminate
                   ~iterate_on_transactions
                   ~iterate_on_relations
                   ~fwd_bwd
                   ~modified
                   ~context
                   ~domains
                   ~post
                   ~cmd =
    match cmd with
    | CODE (_, code) ->       
       let l = code#length in
       let code_id = code#getId in
       let acc = ref post in
       let _ =
         for i = l - 1 downto 0 do
	   let safe_acc =
             if self#stable && in_transaction then
               (!acc)#clone
             else
               !acc in
	   let acc' = ref (self#analyzeBwd
                             ~in_transaction:in_transaction
                             ~must_terminate:must_terminate
                             ~iterate_on_transactions:iterate_on_transactions
			     ~iterate_on_relations:iterate_on_relations
                             ~fwd_bwd:fwd_bwd
                             ~modified:modified
                             ~context:context
                             ~domains:domains
                             ~post:(!acc) 
			     ~cmd:(code#getCmdAt i))
	   in
	   let _ =
	     match fwd_bwd with
	     | None -> ()
	     | Some pre_table ->
		begin
		  match pre_table#get (code_id, i) with
		  | None -> ()
		  | Some pre -> acc' := (!acc')#meet ?variables:(Some modified#toList) pre
		end
	   in
	   begin
	     if self#stable then
	       let _ = match cmd_processor with
		 | None -> ()
		 | Some f ->
                    code#setCmdAt
                      i (f ~invariant:safe_acc ~context:context ~cmd:(code#getCmdAt i))
	       in
	       let _ = match fwd_bwd with
		 | None -> ()
		 | Some table -> table#set (code_id, i) safe_acc
	       in
	       ()
	     else
	       ();
	     acc := !acc'
	   end
	 done
       in
       !acc
    | CFG (_, cfg) ->
       self#analyzeCFGBwd
         ~must_terminate:must_terminate
         ~iterate_on_transactions:iterate_on_transactions
         ~iterate_on_relations:iterate_on_relations 
	 ~fwd_bwd:fwd_bwd
         ~modified:modified
         ~context:context
         ~domains:domains
         ~post:post
         ~cfg:cfg
    | RELATION code ->
       if iterate_on_relations then 
	 self#analyzeBwd_FwdBwd
           ~in_transaction:false
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~modified:modified
           ~context:context
           ~domains:domains
           ~post:post
           ~code:code
       else
	 let sym = new symbol_t "relation" in
	 self#analyzeBwd
           ~in_transaction:false
           ~must_terminate:true
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~post:post
           ~cmd:(CODE (sym, code))
    | BREAKOUT_BLOCK (s, code) ->
       let _ = iteration_stack#push (BREAKOUT_POINT (s, ref post)) in
       let sym = new symbol_t "breakout" in
       let cmd' = CODE (sym, code) in
       let pre =
         self#analyzeBwd
           ~in_transaction:false
           ~must_terminate:must_terminate
           ~iterate_on_transactions:iterate_on_transactions
	   ~iterate_on_relations:iterate_on_relations
           ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~post:post
           ~cmd:cmd' in
       let _ = iteration_stack#pop in
       pre
    | BREAK s ->
       begin
	 try
	   List.iter (fun mode ->
               match mode with
	       | BREAKOUT_POINT (s', breakout_inv) when s#equal s' -> 
		  raise (Found_breakout_bwd (!breakout_inv))
	       | _ -> 
		  ())
		     iteration_stack#listFromTop;
	   raise (CHFailure (STR "Break statement encountered outside of a matching breakout block"))
	 with
         | Found_breakout_bwd pre -> pre
       end  
    | GOTO_BLOCK code ->
       let sym = new symbol_t "goto_block" in
       let _ = goto_table_stack#push (new CFGAtlasTable.atlas_table_t) in
       let pre =
         self#analyzeBwd
           ~in_transaction:false
           ~must_terminate:must_terminate
           ~iterate_on_transactions:iterate_on_transactions
	   ~iterate_on_relations:iterate_on_relations
           ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~post:post
           ~cmd:(CODE (sym, code)) in
       let _ = goto_table_stack#pop in
       pre
    | LABEL label ->
       let goto_table = goto_table_stack#top in
       let _ = goto_table#add label post in
       post
    | GOTO label ->
       let goto_table = goto_table_stack#top in
       let pre = match goto_table#get label with
	 | None ->
            raise (CHFailure (LBLOCK [STR "Command GOTO "; label#toPretty;
                                      STR " has no matching label"]))
	 | Some pre' -> pre'
       in
       pre
    | SKIP ->
       post
    | TRANSACTION (s, code, post_code) ->
       let tmps = (tmp_vars_in_code code) in
       let tmps = match post_code with
	 | None -> tmps
	 | Some post_code -> tmps @ (tmp_vars_in_code post_code)
       in
       let mods = new VariableCollections.set_t in
       let pre_post_code = match post_code with
	 | None -> post
	 | Some post_code ->
            self#analyzeBwd
              ~in_transaction:false
              ~must_terminate:must_terminate
              ~iterate_on_transactions:iterate_on_transactions
	      ~iterate_on_relations:iterate_on_relations
              ~fwd_bwd:fwd_bwd
              ~modified:mods
              ~context:context
              ~domains:domains
              ~post:post
              ~cmd:(CODE (s, post_code))
       in
       let pre =
         if post#hasRelationalDomain || not(iterate_on_transactions) then
	   self#analyzeBwd
             ~in_transaction:true ~must_terminate:true
             ~iterate_on_transactions:iterate_on_transactions
             ~iterate_on_relations:iterate_on_relations 
	     ~fwd_bwd:fwd_bwd
             ~modified:mods
             ~context:context
             ~domains:domains
             ~post:pre_post_code#clone
             ~cmd:(CODE (s, code))
	 else
	   self#analyzeBwd_FwdBwd
             ~in_transaction:true
             ~iterate_on_transactions:iterate_on_transactions
             ~iterate_on_relations:iterate_on_relations 
	     ~modified:mods
             ~context:context
             ~domains:domains
             ~post:pre_post_code#clone
             ~code:code
       in
       let pre' =
         self#analyzeBwd
           ~in_transaction:true
           ~must_terminate:true
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:mods
           ~context:context
           ~domains:domains
           ~post:pre
           ~cmd:(ABSTRACT_VARS tmps) in
       let mods' = mods#filter (fun v -> not(v#isTmp)) in
       let _ = modified#addSet mods' in
       pre'
    | ASSERT RANDOM ->
       if must_terminate then
	 post
       else
	 post#mkEmpty
    | ASSIGN_STRUCT (s1, s2) ->
       let assignments = expand_structure_assignment s1 s2 in
       List.fold_left (fun post' cmd -> 
	   let mods = modified_vars_in_cmd_bwd cmd in
	   let _ = modified#addList mods in
	   (if in_transaction then
              post'#analyzeBwdInTransaction
            else
              post'#analyzeBwd) cmd) post assignments
    | ABSTRACT_VARS l ->
       let l' = expand_struct_vars_in_list l in
       let _ = modified#addList l' in
       (if in_transaction then
          post#analyzeBwdInTransaction
        else
          post#analyzeBwd) (ABSTRACT_VARS l')
    | ABSTRACT_ELTS _
      | ASSIGN_NUM _
      | ASSIGN_ARRAY _
      | INCREMENT _
      | ASSIGN_SYM _
      | ASSIGN_NUM_ELT _
      | ASSIGN_SYM_ELT _
      | READ_NUM_ELT _
      | READ_SYM_ELT _
      | SHIFT_ARRAY _
      | BLIT_ARRAYS _
      | SET_ARRAY_ELTS _
      | ASSERT _ ->
       let mods = modified_vars_in_cmd_bwd cmd in
       let _ = modified#addList mods in
       (if in_transaction then post#analyzeBwdInTransaction else post#analyzeBwd) cmd
    | SELECT _
      | INSERT _
      | DELETE _
      | ASSIGN_TABLE _ ->
       raise (CHFailure (STR "Database command encountered during backward iteration"))
    | BRANCH cl ->
       let sym = new symbol_t "branch" in
       let mods = new VariableCollections.set_t in
       let pre_l =
         List.map (fun code ->
             self#analyzeBwd
               ~in_transaction:false
               ~must_terminate:must_terminate
               ~iterate_on_transactions:iterate_on_transactions
	       ~iterate_on_relations:iterate_on_relations
               ~fwd_bwd:fwd_bwd
               ~modified:mods
               ~context:context
               ~domains:domains
               ~post:post
               ~cmd:(CODE (sym, code))) cl in
       let mod_list = mods#toList in
       let _ = modified#addList mod_list in
       List.fold_left (fun acc pre ->
           acc#join ?variables:(Some mod_list) pre) post#mkBottom pre_l
    | LOOP (loop_true, loop_false, body) ->
       let sym = new symbol_t "loop" in
       let loop_counter = loop_counter_factory#mkCounter in
       let post =
         if do_loop_counters then
	   self#analyzeFwd
             ~in_transaction:false
             ~iterate_on_transactions:iterate_on_transactions
             ~iterate_on_relations:iterate_on_relations 
	     ~fwd_bwd:fwd_bwd
             ~modified:modified
             ~context:context
             ~domains:domains
             ~pre:post
             ~cmd:(ASSIGN_NUM (loop_counter, NUM numerical_zero))
	 else
	   post
       in
       let post_loop =
         self#analyzeBwd
           ~in_transaction:false
           ~must_terminate:must_terminate
           ~iterate_on_transactions:iterate_on_transactions
	   ~iterate_on_relations:iterate_on_relations
           ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~post:post
           ~cmd:(CODE (sym, loop_false)) in
       let mods = new VariableCollections.set_t in
       let stride post =
	 let post =
           if do_loop_counters then
	     self#analyzeFwd
               ~in_transaction:false
               ~iterate_on_transactions:iterate_on_transactions
               ~iterate_on_relations:iterate_on_relations 
	       ~fwd_bwd:fwd_bwd
               ~modified:mods
               ~context:context
               ~domains:domains
               ~pre:post
               ~cmd:(INCREMENT (loop_counter, numerical_one))
	   else
	     post
	 in
	 let b = self#analyzeBwd
                   ~in_transaction:false
                   ~must_terminate:must_terminate
                   ~iterate_on_transactions:iterate_on_transactions
	           ~iterate_on_relations:iterate_on_relations
                   ~fwd_bwd:fwd_bwd
                   ~modified:mods
                   ~context:context
                   ~domains:domains
                   ~post:post
                   ~cmd:(CODE (sym, body)) in
	 let t = self#analyzeBwd
                   ~in_transaction:false
                   ~must_terminate:must_terminate
                   ~iterate_on_transactions:iterate_on_transactions
	           ~iterate_on_relations:iterate_on_relations
                   ~fwd_bwd:fwd_bwd
                   ~modified:mods
                   ~context:context
                   ~domains:domains
                   ~post:b
                   ~cmd:(CODE (sym, loop_true)) in
	 post_loop#join ?variables:(Some mods#toList) t
       in
       let finish post =
	 let _ = iteration_stack#push STABLE_MODE in
	 let _ = stride post in
	 let _ = iteration_stack#pop in
	 let _ = modified#addList mods#toList in
	 if do_loop_counters then
	   let post' =
             self#analyzeBwd
               ~in_transaction:false
               ~must_terminate:must_terminate
               ~iterate_on_transactions:iterate_on_transactions
	       ~iterate_on_relations:iterate_on_relations
               ~fwd_bwd:fwd_bwd
               ~modified:modified
               ~context:context
               ~domains:domains
               ~post:post
               ~cmd:(ABSTRACT_VARS [loop_counter]) in
	   let _ = modified#remove loop_counter in
	   post'
	 else
	   post
       in
       let rec down_iteration post i =
	 let _ = iteration_stack#push NARROWING_MODE in
	 let pre = stride post in
	 let _ = iteration_stack#pop in
	 let mods_l = mods#toList in
	 let narrowed =
           if strategy.narrowing i then
             post#narrowing ?variables:(Some mods_l) pre
           else
             post#meet ?variables:(Some mods_l) pre in
	 if post#leq ?variables:(Some mods_l) narrowed then
	   finish post
	 else
	   down_iteration narrowed (i + 1)
       in
       let rec up_iteration post i =		      
	 let _ = iteration_stack#push WIDENING_MODE in
	 let pre = stride post in
	 let _ = iteration_stack#pop in
	 let mods_l = mods#toList in
	 if pre#leq ?variables:(Some mods_l) post then
	   if do_narrowing then
	     down_iteration pre 1
	   else
	     finish pre
	 else
	   let widening = strategy.widening i in
	   let widened =
             if fst widening then 
	       let kind = snd widening in
	       if kind = "" then
		 post#widening ?kind:None ?variables:(Some mods_l) pre 
	       else
		 post#widening ?kind:(Some kind) ?variables:(Some mods_l) pre 
	     else 
	       post#join ?variables:(Some mods_l) pre
	   in
	   up_iteration widened (i + 1)
       in
       up_iteration post_loop 1
    | OPERATION operation ->
       let mods =
         List.filter (fun (_, v, mode) ->
             match mode with READ -> false | _ -> true) operation.op_args in
       let mods_l = List.map (fun (_, v, _) -> v) mods in
       begin
	 match op_semantics with
	 | Some semantics -> 
	    let _ = modified#addList mods_l in
	    semantics
              ~invariant:post
              ~fwd_direction:false
              ~context:context
              ~stable:self#stable
              ~operation:operation
	 | None ->
	    self#analyzeBwd
              ~in_transaction:in_transaction
              ~must_terminate:must_terminate
              ~iterate_on_transactions:iterate_on_transactions
	      ~iterate_on_relations:iterate_on_relations
              ~fwd_bwd:fwd_bwd
              ~modified:modified
              ~context:context
              ~domains:domains
              ~post:post
              ~cmd:(ABSTRACT_VARS mods_l)
       end
    | DOMAIN_OPERATION (domains, operation) ->
       post#domainOperation false domains operation
    | CALL (proc, args) ->
       let signature = (system#getProcedure proc)#getSignature in
       let arg_set = new SymbolCollections.set_t in
       let _ =
         List.iter (fun (arg, _, mode) ->
             match mode with READ -> () | _ -> arg_set#add arg) signature in
       let mods =
         List.fold_left (fun l (arg, v) ->
             if arg_set#has arg then v :: l else l) [] args in
       begin
	 match proc_semantics with
	 | Some semantics ->
	    let _ = modified#addList mods in
	    semantics
              ~stable:self#stable
              ~context:context
              ~invariant:post
              ~procedure:proc
              ~args:args
	 | None ->
	    self#analyzeBwd
              ~in_transaction:false
              ~must_terminate:must_terminate
              ~iterate_on_transactions:iterate_on_transactions
	      ~iterate_on_relations:iterate_on_relations
              ~fwd_bwd:fwd_bwd
              ~modified:modified
              ~context:context
              ~domains:domains
              ~post:post
              ~cmd:(ABSTRACT_VARS mods)
       end
    | DOMAINS (doms, code) ->
       let sym = new symbol_t "domains" in
       let active = self#activeDomains domains in
       let activated = List.filter (fun dom -> not (active#has dom)) doms in
       let _ = domains#push doms in
       let post' = post#activateDomains activated in
       let pre =
         self#analyzeBwd
           ~in_transaction:in_transaction
           ~must_terminate:must_terminate
           ~iterate_on_transactions:iterate_on_transactions
	   ~iterate_on_relations:iterate_on_relations
           ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~post:post'
           ~cmd:(CODE (sym, code)) in	    
       let _ = domains#pop in
       pre#deactivateDomains activated
    | CONTEXT (symbol, code) ->
       let sym = new symbol_t "context" in
       let _ = context#push symbol in
       let pre =
         self#analyzeBwd
           ~in_transaction:in_transaction
           ~must_terminate:must_terminate
           ~iterate_on_transactions:iterate_on_transactions
	   ~iterate_on_relations:iterate_on_relations
           ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~post:post
           ~cmd:(CODE (sym, code)) in
       let _ = context#pop in
       pre
    | DOMAIN_CMD (dom, cmd, args) ->
       post#sendCmd dom cmd args
    | MOVE_VALUES (vars, src, tgt) ->
       post#move ~relational:false ~vars:vars ~src:tgt ~tgt:src
    | MOVE_RELATIONS (vars, src, tgt) ->
       post#move ~relational:true ~vars:vars ~src:tgt ~tgt:src
      
  method private analyzeFwd_FwdBwd
                   ~in_transaction
                   ~iterate_on_transactions
                   ~iterate_on_relations
                   ~modified
                   ~context
                   ~domains
                   ~pre
                   ~code =
    let sym = new symbol_t "code" in
    let cmd = CODE (sym, code) in
    let _ = iteration_stack#push NARROWING_MODE in
    let pre' = 
      let rec loop i pre =	
	let mods = new VariableCollections.set_t in
	let post =
          self#analyzeFwd
            ~in_transaction:in_transaction
            ~iterate_on_transactions:iterate_on_transactions
            ~iterate_on_relations:iterate_on_relations 
	    ~fwd_bwd:None
            ~modified:mods
            ~context:context
            ~domains:domains
            ~pre:pre#clone
            ~cmd:cmd in
	let pre' =
          self#analyzeBwd
            ~in_transaction:in_transaction
            ~must_terminate:true
            ~iterate_on_transactions:iterate_on_transactions
            ~iterate_on_relations:iterate_on_relations 
	    ~fwd_bwd:None
            ~modified:mods
            ~context:context
            ~domains:domains
            ~post:post
            ~cmd:cmd in
	let mods_l = mods#toList in
	let narrowed =
          if strategy.narrowing i then
            pre#narrowing ?variables:(Some mods_l) pre'
          else
            pre#meet ?variables:(Some mods_l) pre' in
	if pre#leq ?variables:(Some mods_l) narrowed then
	  pre
	else
	  loop (i + 1) narrowed
      in
      loop 1 pre
    in
    let _ = iteration_stack#pop in
    let _ = iteration_stack#push STABLE_MODE in
    let post =
      self#analyzeFwd
        ~in_transaction:in_transaction
        ~iterate_on_transactions:iterate_on_transactions
        ~iterate_on_relations:iterate_on_relations 
        ~fwd_bwd:None
        ~modified:modified
        ~context:context
        ~domains:domains
        ~pre:pre'
        ~cmd:cmd in
    let _ = iteration_stack#pop in
    post
	
  method private analyzeFwd
                   ~in_transaction
                   ~iterate_on_transactions
                   ~iterate_on_relations
                   ~fwd_bwd ~modified
                   ~context
                   ~domains
                   ~pre
                   ~cmd =
    match cmd with
    | CODE (_, code) ->
       let l = code#length in
       let code_id = code#getId in
       let acc = ref pre in
       let _ =
         for i = 0 to l - 1 do
	   let safe_acc =
             if self#stable && in_transaction then
               (!acc)#clone
             else
               !acc in
	   let acc' =
             ref (self#analyzeFwd
                    ~in_transaction:in_transaction
                    ~iterate_on_transactions:iterate_on_transactions
                    ~iterate_on_relations:iterate_on_relations
		    ~fwd_bwd:fwd_bwd
                    ~modified:modified
                    ~context:context
                    ~domains:domains
                    ~pre:(!acc)
                    ~cmd:(code#getCmdAt i))
	   in
	   let _ =
	     match fwd_bwd with
	     | None -> ()
	     | Some post_table ->
		begin
		  match post_table#get (code_id, i) with
		  | None -> ()
		  | Some post -> acc' := (!acc')#meet ?variables:(Some modified#toList) post
		end
	   in
	   begin
	     if self#stable then
	       let _ = match cmd_processor with
		 | None -> ()
		 | Some f ->
                    code#setCmdAt i (f ~invariant:safe_acc ~context:context ~cmd:(code#getCmdAt i))
	       in
	       let _ =
		 match fwd_bwd with
		 | None -> ()
		 | Some table -> table#set (code_id, i) safe_acc
	       in
	       ()
	     else
	       ();
	     acc := !acc'
	   end
	 done
       in
       !acc
    | CFG (_, cfg) ->
       self#analyzeCFGFwd
         ~iterate_on_transactions:iterate_on_transactions
         ~iterate_on_relations:iterate_on_relations 
	 ~fwd_bwd:fwd_bwd
         ~modified:modified
         ~context:context
         ~domains:domains
         ~pre:pre
         ~cfg:cfg
    | RELATION code ->
       if iterate_on_relations then 
	 self#analyzeFwd_FwdBwd
           ~in_transaction:false
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~modified:modified
           ~context:context
           ~domains:domains
           ~pre:pre
           ~code:code
       else
	 let sym = new symbol_t "relation" in
	 self#analyzeFwd
           ~in_transaction:false
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~pre:pre
           ~cmd:(CODE (sym, code))
    | BREAKOUT_BLOCK (s, code) ->
       let _ = iteration_stack#push (BREAKOUT_POINT (s, ref pre#mkBottom)) in
       let sym = new symbol_t "break_out" in
       let cmd' = CODE (sym, code) in
       let post =
         self#analyzeFwd
           ~in_transaction:false
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~pre:pre
           ~cmd:cmd' in
       begin
	 match iteration_stack#pop with
	 | BREAKOUT_POINT (s', breakout_inv) when s#equal s'-> post#join (!breakout_inv)
	 | _ -> raise (CHFailure (STR "Internal error in iterator: breakout block expected"))
       end
    | BREAK s ->
       begin
	 try
	   List.iter (fun mode ->
               match mode with
	       | STABLE_MODE -> 
		  ()
	       | BREAKOUT_POINT (s', breakout_inv) when not(s#equal s') ->
		  ()
	       | BREAKOUT_POINT (s', breakout_inv) when s#equal s' ->
		  breakout_inv := pre#join (!breakout_inv);
		  raise Found_breakout_fwd
	       | _ -> 
		  raise Not_stable)
		     iteration_stack#listFromTop;
	   raise (CHFailure (STR "Break statement encountered outside of a matching breakout block"))
	 with Found_breakout_fwd | Not_stable -> pre#mkBottom
       end
    | GOTO_BLOCK code ->
       let sym = new symbol_t "goto_block" in
       let _ = goto_table_stack#push (new CFGAtlasTable.atlas_table_t) in
       let post =
         self#analyzeFwd
           ~in_transaction:false
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~pre:pre
           ~cmd:(CODE (sym, code)) in
       let _ = goto_table_stack#pop in
       post
    | GOTO label ->
       let goto_table = goto_table_stack#top in
       let _ = goto_table#add label pre in
       pre#mkBottom
    | LABEL label ->
       let goto_table = goto_table_stack#top in
       let post = match goto_table#get label with
	 | None -> pre
	 | Some pre' -> pre#join pre'
       in
       post
    | SKIP ->
       pre
    | TRANSACTION (sym, code, post_code) ->
       let tmps = tmp_vars_in_code code in
       let tmps = match post_code with
	 | None -> tmps
	 | Some post_code -> tmps @ (tmp_vars_in_code post_code)
       in
       let mods = new VariableCollections.set_t in
       let post =
         if pre#hasRelationalDomain || not(iterate_on_transactions) then
	   self#analyzeFwd
             ~in_transaction:true
             ~iterate_on_transactions:iterate_on_transactions
             ~iterate_on_relations:iterate_on_relations 
	     ~fwd_bwd:fwd_bwd
             ~modified:mods
             ~context:context
             ~domains:domains
             ~pre:pre#clone
             ~cmd:(CODE (sym, code))
	 else
	   self#analyzeFwd_FwdBwd
             ~in_transaction:true
             ~iterate_on_transactions:iterate_on_transactions
             ~iterate_on_relations:iterate_on_relations 
	     ~modified:mods
             ~context:context
             ~domains:domains
             ~pre:pre#clone
             ~code:code 
       in
       let post' = match post_code with
	 | None -> post
	 | Some post_code ->
            self#analyzeFwd
              ~in_transaction:false
              ~iterate_on_transactions:iterate_on_transactions
              ~iterate_on_relations:iterate_on_relations 
	      ~fwd_bwd:fwd_bwd
              ~modified:mods
              ~context:context
              ~domains:domains
              ~pre:post
              ~cmd:(CODE (sym, post_code))
       in
       let post'' =
         self#analyzeFwd
           ~in_transaction:true
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:mods
           ~context:context
           ~domains:domains
           ~pre:post'
           ~cmd:(ABSTRACT_VARS tmps) in
       let mods' = mods#filter (fun v -> not(v#isTmp)) in
       let _ = modified#addSet mods' in
       post''
    | ASSIGN_STRUCT (s1, s2) ->
       let assignments = expand_structure_assignment s1 s2 in
       List.fold_left (fun pre' cmd -> 
	   let mods = modified_vars_in_cmd_fwd cmd in
	   let _ = modified#addList mods in
	   (if in_transaction then
              pre'#analyzeFwdInTransaction
            else
              pre'#analyzeFwd) cmd) pre assignments
    | ASSERT RANDOM ->
       pre
    | ABSTRACT_VARS l ->
       let l' = expand_struct_vars_in_list l in
       let _ = modified#addList l' in
       (if in_transaction then
          pre#analyzeFwdInTransaction
        else
          pre#analyzeFwd) (ABSTRACT_VARS l')
    | ABSTRACT_ELTS _
      | ASSIGN_NUM _
      | ASSIGN_ARRAY _
      | INCREMENT _
      | ASSIGN_SYM _
      | ASSIGN_NUM_ELT _
      | ASSIGN_SYM_ELT _
      | READ_NUM_ELT _
      | READ_SYM_ELT _
      | SHIFT_ARRAY _
      | BLIT_ARRAYS _
      | SET_ARRAY_ELTS _
      | ASSERT _ ->
       let mods = modified_vars_in_cmd_fwd cmd in
       let _ = modified#addList mods in
       (if in_transaction then pre#analyzeFwdInTransaction else pre#analyzeFwd) cmd
    | SELECT _ ->
       if db_enabled then
	 pre#analyzeDBQuery cmd
       else
	 pre#analyzeDBQueryNoDB cmd
    | INSERT _
      | DELETE _
      | ASSIGN_TABLE _ ->
       if db_enabled then 
	 pre#analyzeDBUpdate cmd
       else
	 pre
    | BRANCH cl ->
       let sym = new symbol_t "branch" in
       let mods = new VariableCollections.set_t in
       let post_l =
         List.map (fun code ->
             self#analyzeFwd
               ~in_transaction:false
               ~iterate_on_transactions:iterate_on_transactions
	       ~iterate_on_relations:iterate_on_relations
               ~fwd_bwd:fwd_bwd
               ~modified:mods
               ~context:context
               ~domains:domains
               ~pre:pre
               ~cmd:(CODE (sym, code))) cl in
       let mod_list = mods#toList in
       let _ = modified#addList mod_list in
       List.fold_left (fun acc post ->
           acc#join ?variables:(Some mod_list) post) pre#mkBottom post_l
    | LOOP (loop_true, loop_false, body) ->
       let sym = new symbol_t "loop" in
       let loop_counter = loop_counter_factory#mkCounter in
       let pre_loop =
         if do_loop_counters then
	   self#analyzeFwd
             ~in_transaction:false
             ~iterate_on_transactions:iterate_on_transactions
             ~iterate_on_relations:iterate_on_relations 
	     ~fwd_bwd:fwd_bwd
             ~modified:modified
             ~context:context
             ~domains:domains
             ~pre:pre
             ~cmd:(ASSIGN_NUM (loop_counter, NUM numerical_zero))
	 else
	   pre
       in
       let mods = new VariableCollections.set_t in
       let stride pre =
	 let pre =
           if do_loop_counters then
	     self#analyzeFwd
               ~in_transaction:false
               ~iterate_on_transactions:iterate_on_transactions
               ~iterate_on_relations:iterate_on_relations 
	       ~fwd_bwd:fwd_bwd
               ~modified:mods
               ~context:context
               ~domains:domains
               ~pre:pre
               ~cmd:(INCREMENT (loop_counter, numerical_one))
	   else
	     pre
	 in
	 let t = self#analyzeFwd
                   ~in_transaction:false
                   ~iterate_on_transactions:iterate_on_transactions
                   ~iterate_on_relations:iterate_on_relations 
	           ~fwd_bwd:fwd_bwd
                   ~modified:mods
                   ~context:context
                   ~domains:domains
                   ~pre:pre ~cmd:(CODE (sym, loop_true)) in
	 let b = self#analyzeFwd
                   ~in_transaction:false
                   ~iterate_on_transactions:iterate_on_transactions
                   ~iterate_on_relations:iterate_on_relations 
	           ~fwd_bwd:fwd_bwd
                   ~modified:mods
                   ~context:context
                   ~domains:domains
                   ~pre:t ~cmd:(CODE (sym, body)) in
	 pre_loop#join ?variables:(Some mods#toList) b
       in
       let finish pre =
	 let _ = iteration_stack#push STABLE_MODE in
	 let _ = stride pre in
	 let _ = iteration_stack#pop in
	 let _ = modified#addList mods#toList in
	 let pre =
           if do_loop_counters then
	     let pre' =
               self#analyzeFwd
                 ~in_transaction:false
                 ~iterate_on_transactions:iterate_on_transactions
                 ~iterate_on_relations:iterate_on_relations 
		 ~fwd_bwd:fwd_bwd
                 ~modified:modified
                 ~context:context
                 ~domains:domains
                 ~pre:pre
                 ~cmd:(ABSTRACT_VARS [loop_counter]) in
	     let _ = modified#remove loop_counter in
	     pre'
	   else
	     pre
	 in
	 self#analyzeFwd
           ~in_transaction:false
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~pre:pre
           ~cmd:(CODE (sym, loop_false))
       in	    
       let rec down_iteration pre i =
	 let _ = iteration_stack#push NARROWING_MODE in
	 let post = stride pre in
	 let _ = iteration_stack#pop in
	 let mods_l = mods#toList in
	 let narrowed =
           if strategy.narrowing i then
             pre#narrowing ?variables:(Some mods_l) post
           else
             pre#meet ?variables:(Some mods_l) post in
	 if pre#leq ?variables:(Some mods_l) narrowed then
	   finish pre
	 else
	   down_iteration narrowed (i + 1)
       in
       let rec up_iteration pre i =		      
	 let _ = iteration_stack#push WIDENING_MODE in
	 let post = stride pre in
	 let _ = iteration_stack#pop in
	 let mods_l = mods#toList in
	 if post#leq ?variables:(Some mods_l) pre then
	   if do_narrowing then
	     down_iteration post 1
	   else
	     finish post
	 else
	   let widening = strategy.widening i in		
	   let widened =
             if fst widening then 
	       let kind = snd widening in
	       if kind = "" then
		 pre#widening ?kind:None ?variables:(Some mods_l) post 
	       else
		 pre#widening ?kind:(Some kind) ?variables:(Some mods_l) post 
	     else 
	       pre#join ?variables:(Some mods_l) post 
	   in
	   up_iteration widened (i + 1)
       in
       up_iteration pre_loop 1
    | OPERATION operation ->
       let mods =
         List.filter (fun (_, _, mode) ->
             match mode with READ -> false | _ -> true) operation.op_args in
       let mods_l = List.map (fun (_, v, _) -> v) mods in
       begin
	 match op_semantics with
	 | Some semantics -> 
	    let _ = modified#addList mods_l in
	    semantics
              ~invariant:pre
              ~fwd_direction:true
              ~context:context
              ~stable:self#stable
              ~operation:operation
	 | None ->
	    self#analyzeFwd
              ~in_transaction:in_transaction
              ~iterate_on_transactions:iterate_on_transactions
              ~iterate_on_relations:iterate_on_relations 
	      ~fwd_bwd:fwd_bwd
              ~modified:modified
              ~context:context
              ~domains:domains
              ~pre:pre
              ~cmd:(ABSTRACT_VARS mods_l)
       end
    | DOMAIN_OPERATION (domains, operation) ->
       pre#domainOperation true domains operation
    | CALL (proc, args) ->
       let signature = (system#getProcedure proc)#getSignature in
       let arg_set = new SymbolCollections.set_t in
       let _ =
         List.iter (fun (arg, _, mode) ->
             match mode with READ -> () | _ -> arg_set#add arg) signature in
       let mods =
         List.fold_left (fun l (arg, v) ->
             if arg_set#has arg then v :: l else l) [] args in
       begin
	 match proc_semantics with
	 | Some semantics ->
	    let _ = modified#addList mods in
	    semantics
              ~stable:self#stable
              ~context:context
              ~invariant:pre
              ~procedure:proc
              ~args:args
	 | None ->
	    self#analyzeFwd
              ~in_transaction:false
              ~iterate_on_transactions:iterate_on_transactions
              ~iterate_on_relations:iterate_on_relations 
	      ~fwd_bwd:fwd_bwd
              ~modified:modified
              ~context:context
              ~domains:domains
              ~pre:pre
              ~cmd:(ABSTRACT_VARS mods)
       end
    | DOMAINS (doms, code) ->
       let sym = new symbol_t "domains" in
       let active = self#activeDomains domains in
       let activated = List.filter (fun dom -> not (active#has dom)) doms in
       let _ = domains#push doms in
       let pre' = pre#activateDomains activated in
       let post =
         self#analyzeFwd
           ~in_transaction:in_transaction
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~pre:pre'
           ~cmd:(CODE (sym, code)) in
       let _ = domains#pop in
       post#deactivateDomains activated
    | CONTEXT (symbol, code) ->
       let sym = new symbol_t "context" in
       let _ = context#push symbol in
       let post =
         self#analyzeFwd
           ~in_transaction:in_transaction
           ~iterate_on_transactions:iterate_on_transactions
           ~iterate_on_relations:iterate_on_relations 
	   ~fwd_bwd:fwd_bwd
           ~modified:modified
           ~context:context
           ~domains:domains
           ~pre:pre
           ~cmd:(CODE (sym, code)) in
       let _ = context#pop in
       post
    | DOMAIN_CMD (dom, cmd, args) ->
       pre#sendCmd dom cmd args
    | MOVE_VALUES (vars, src, tgt) ->
       pre#move ~relational:false ~vars:vars ~src:src ~tgt:tgt
    | MOVE_RELATIONS (vars, src, tgt) ->
       pre#move ~relational:true ~vars:vars ~src:src ~tgt:tgt
      
  method runFwd
           ?(iterate_on_transactions = true)
           ?(iterate_on_relations = true)
           ?domains:doms ~atlas:(init: atlas_t)
           cmd =
    let _ = iteration_stack#clear in
    let _ = goto_table_stack#clear in
    let _ = loop_counter_factory#reset in
    let context = new stack_t in
    let domains = new stack_t in
    let pre = match doms with
      | None -> init
      | Some l -> 
	 let _ = domains#push l in
	 init#activateDomains l
    in
    self#analyzeFwd
      ~in_transaction:false
      ~iterate_on_transactions:iterate_on_transactions
      ~iterate_on_relations:iterate_on_relations
      ~fwd_bwd:None
      ~modified:(new VariableCollections.set_t)
      ~context:context
      ~domains:domains
      ~pre:pre
      ~cmd:cmd

  method runBwd
           ?(must_terminate = false)
           ?(iterate_on_transactions = true)
           ?(iterate_on_relations = true)
           ?domains:doms ~atlas:(init: atlas_t)
           cmd =
    let _ = iteration_stack#clear in
    let _ = goto_table_stack#clear in
    let _ = loop_counter_factory#reset in
    let context = new stack_t in
    let domains = new stack_t in
    let post = match doms with
      | None -> init
      | Some l -> 
	 let _ = domains#push l in
	 init#activateDomains l
    in
    self#analyzeBwd
      ~in_transaction:false
      ~must_terminate:must_terminate
      ~iterate_on_transactions:iterate_on_transactions
      ~iterate_on_relations:iterate_on_relations
      ~fwd_bwd:None
      ~modified:(new VariableCollections.set_t)
      ~context:context
      ~domains:domains
      ~post:post
      ~cmd:cmd

  method runFwdBwd
           ?domains:doms ~pre:(init_pre: atlas_t)
           ~post:(init_post: atlas_t)
           cmd =
    let _ = iteration_stack#clear in
    let _ = goto_table_stack#clear in
    let _ = loop_counter_factory#reset in
    let context = new stack_t in
    let domains = new stack_t in
    let pre_0 = match doms with
      | None -> init_pre
      | Some l -> 
	 let _ = domains#push l in
	 init_pre#activateDomains l
    in
    let post_0 = match doms with
      | None -> init_post
      | Some l -> 
	 let _ = domains#push l in
	 init_post#activateDomains l
    in
    let onePass pre post =
      let fwd_bwd_table = new FwdBwdTable.simple_table_t in
      let post' =
        self#analyzeFwd
          ~in_transaction:false
          ~iterate_on_transactions:false
          ~iterate_on_relations:false
          ~fwd_bwd:(Some fwd_bwd_table)
	  ~modified:(new VariableCollections.set_t)
          ~context:context
          ~domains:domains
          ~pre:pre
          ~cmd:cmd
      in
      let post'' = post#meet ?variables:None post' in
      let pre' =
        self#analyzeBwd
          ~in_transaction:false
          ~must_terminate:true
          ~iterate_on_transactions:false
          ~iterate_on_relations:false
          ~fwd_bwd:(Some fwd_bwd_table)
	  ~modified:(new VariableCollections.set_t)
          ~context:context
          ~domains:domains
          ~post:post''
          ~cmd:cmd
      in      
      (pre#meet ?variables:None pre', post'')
    in
    let rec iterate i pre post =
      let (pre', post') = onePass pre post in
      let (pre'', post'') = 
	if strategy.narrowing i then
	  (pre#narrowing ?variables:None pre', post#narrowing ?variables:None post')
	else
	  (pre#meet ?variables:None pre', post#meet ?variables:None post')
      in
      if (pre#leq ?variables:None pre'') && (post#leq ?variables:None post'') then
	(pre, post)
      else
	iterate (i + 1) pre'' post''
    in
    iterate 1 pre_0 post_0
    
end

