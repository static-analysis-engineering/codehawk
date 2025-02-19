(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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
open CHLanguage
open CHPretty

(* chutil *)
open CHLoopStructure
open CHPrettyUtil

(* jchlib *)
open JCHDictionary

(* jchpre *)
open JCHCodegraph
open JCHCostBoundsModel


module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory

let dbg = ref false

let make_label pc = new symbol_t (string_of_int pc)

let getloopstructure (bblocks:(int * int * int list) list) =
  let succ = List.concat
    (List.map (fun (pc,_,succ) -> List.map (fun s -> (pc,s)) succ) bblocks) in
  get_loop_structure 0 succ

let _loopstruct_to_pretty (loopstruct: loop_structure_int) =
  let pp_loop lh =
    LBLOCK [STR "loop "; INT lh; STR " ";
            pp_list_int (loopstruct#get_loop lh); NL] in
  LBLOCK (List.map pp_loop loopstruct#get_loopheads)

class method_cost_abstractor_t
  ~(cmsix:int)
  ~(basicblocks: (int * int * int list) list)
  ~(costmodel: costmodel_t) =
object (self)

  val graph = make_code_graph ()
  val scope = LF.mkScope ()
  val vartable = H.create 3
  val loopstructure =
    let res = getloopstructure basicblocks in
    costmodel#set_loopstructure cmsix res;
    res

  method private isinloop (loophead:int) (pc:int) =
    loopstructure#is_inloop_with_loophead pc loophead

  method private getloop (loophead:int) = loopstructure#get_loop loophead

  method private get_nosuccessor_pcs =
    List.map
      (fun (pc,_,_) -> pc)
      (List.filter
         (fun (_,_,l) -> match l with [] -> true | _ -> false) basicblocks)

  method private getpredecessors (pc:int) =
    List.map (fun (ppc,_,_) -> ppc)
      (List.filter (fun (_,_,succ) -> List.mem pc succ) basicblocks)

  method private getsuccessors (pc:int) =
    let (_,_,succ) = List.find (fun (spc,_,_) -> spc = pc) basicblocks in succ

  method private do_sink_transform (decpc:int) (obspc:int) =
    let node = make_label obspc in
    let preds = self#getpredecessors obspc in
    let preds =
      List.map (fun p ->
          let atts =
            [ string_of_int decpc ; string_of_int p ; string_of_int obspc ] in
      let invop = OPERATION ( { op_name = new symbol_t ~atts "sink" ;
				op_args = [] }) in
      (make_label p,[invop])) preds in
    graph#sink_transform ~node ~preds

  method private do_exit_sink_transform decpc =
    let node = new symbol_t "exit" in
    let preds = self#get_nosuccessor_pcs in
    let preds = List.map (fun p ->
      let atts = [ string_of_int decpc ; string_of_int p ; "exit" ] in
      let invop =
        OPERATION ( { op_name = new symbol_t ~atts "sink" ;
		      op_args = [] }) in
      (make_label p,[invop])) preds in
    graph#sink_transform ~node ~preds

  method private request_num_var (name:symbol_t) =
    let v = scope#mkVariable name NUM_VAR_TYPE in
    begin
      H.add vartable name#getBaseName v ;
      v
    end

  method get_blocks = basicblocks

  method get_block_count = List.length basicblocks

  method iter (f:(int * int * int list) -> unit) = List.iter f self#get_blocks

  method private get_costcommand bvar _cvar pcstart pcend =
    let _ = costmodel#compute_block_cost cmsix pcstart pcend in
    let op_sym =
      new symbol_t
        ~atts:[string_of_int pcstart; string_of_int pcend] "block_cost" in
    OPERATION ({op_name = op_sym; op_args = [("dst", bvar, WRITE)]})

  method to_chifproc =
    let cms = retrieve_cms cmsix in
    let procname = new symbol_t ~atts:[cms#name] "cost_proc" in
    let cvar = self#request_num_var (new symbol_t "costvar") in
    JCHCostUtils.set_cost_var cvar ;
    let bvar = self#request_num_var (new symbol_t "bcost") in

    (* add a side-channel cost variable for each pair of decision-pc and
       observation-pc that gets initialized to zero at the decision-pc and
       gets incremented with the block cost at every other pc. *)
    let scvars =
      List.map (fun (decpc,obspc) ->
          let name = "sink_" ^ (string_of_int decpc) ^ "_" ^
                       (if obspc = (-1) then "exit" else (string_of_int obspc)) in
          let scvar = self#request_num_var (new symbol_t name) in
          (decpc,obspc,scvar)) (costmodel#get_sidechannelspecs cmsix) in
    let initassign =
      OPERATION ({op_name = new symbol_t ~atts:["0"] "set_to_0" ;
		   op_args = [("dst", cvar, WRITE)] }) in
    let invop =
      OPERATION ({op_name = new symbol_t ~atts:["methodexit"] "invariant" ;
		   op_args = [("cvar", cvar, READ_WRITE)] }) in
    let _ = graph#add_node (new symbol_t "entry") [ initassign ] in
    let _ = graph#add_node (new symbol_t "exit") [ invop ] in
    let _ = self#iter (fun (pcstart,pcend,successors) ->
      let cost_command = self#get_costcommand bvar cvar pcstart pcend in
      let asg =
	OPERATION
          ({op_name =
              new symbol_t
                  ~atts:[string_of_int pcstart;
                         string_of_int pcend] "add_block_cost" ;
	    op_args = [("dst_src", cvar, READ_WRITE); ("src", bvar, READ)] }) in

      (* assign zero to side channel variable at the decision pc, otherwise
       * increment with the blockcost *)
      let scasgs =
	List.map (fun (decpc,_,scvar) ->
          if decpc = pcstart then
	    OPERATION ({op_name = new symbol_t ~atts:["0"] "set_to_0" ;
			 op_args = [("dst", scvar, WRITE)] })
          else
	    OPERATION
              ({op_name =
                  new symbol_t
                      ~atts:[string_of_int pcstart;
                             string_of_int pcend] "add_block_cost" ;
		op_args =
                  [("dst_src", scvar, READ_WRITE); ("src", bvar, READ)]})) scvars in
      let node_cmds =
	if loopstructure#is_loophead pcstart then
	  begin
	    let op =
              OPERATION
		({op_name =
                    new symbol_t ~atts:[string_of_int pcstart] "add_loop_cost";
		  op_args = [("dst", cvar, WRITE)]}) in
            let scops =
	      List.map (fun (_,_,scvar) ->
		  OPERATION
                    ({ op_name =
                         new symbol_t
                             ~atts:[string_of_int pcstart] "add_loop_cost" ;
                       op_args = [ ("dst", scvar, WRITE)]})) scvars in
	    (op :: scops) @ (cost_command :: asg :: scasgs)
	  end
	else cost_command :: asg :: scasgs in
      graph#add_node (make_label pcstart) node_cmds ;
      (if pcstart = 0 then
	graph#add_edge (new symbol_t "entry") (make_label pcstart)) ;
      match successors with
      | [] -> graph#add_edge (make_label pcstart) (new symbol_t "exit")
      | l -> List.iter (fun s ->
	  graph#add_edge (make_label pcstart) (make_label s)) l) in

    (* insert observation operations for the side-channel variables on all
       incoming paths to the observation pc *)
    let _ =
      List.iter (fun (decpc,obspc,_) ->
          if obspc >= 0 then
            self#do_sink_transform decpc obspc
          else if obspc = (-1) then
            self#do_exit_sink_transform decpc
          else
            ()) scvars in
    let cfg = graph#to_cfg (new symbol_t "entry") (new symbol_t "exit") in
    let body = LF.mkCode [ CFG (procname, cfg) ] in
    let chif_proc =
      LF.mkProcedure procname ~signature:[] ~bindings:[] ~scope ~body in
    let chif_proc = JCHLoopCostAbstractor.remove_loops chif_proc loopstructure in

    (* sort the loops so that inner loops are analyzed before outer loops *)
    let sorted_loop_heads =
      let compare_heads h1 h2 =
	compare (loopstructure#get_nesting_level h2)
                (loopstructure#get_nesting_level h1) in
      List.sort compare_heads loopstructure#get_loopheads in
    let make_loop_proc hpc =
      let res =
        (hpc, JCHLoopCostAbstractor.reduce_to_loop
                chif_proc cvar bvar hpc (loopstructure#get_loop hpc)) in
      res in
    try
      (JCHLoopCostAbstractor.remove_dead_end_states chif_proc loopstructure,
       List.map make_loop_proc sorted_loop_heads)
    with _ ->
      (* remove_dead_end_states does not work for servers *)
      (chif_proc, List.map make_loop_proc sorted_loop_heads)


  method toPretty =
    LBLOCK (List.map (fun (pc,_,succ) ->
      LBLOCK [ INT pc ; pretty_print_list succ (fun i -> INT i)  "" ", " "]" ; NL ])
	      basicblocks)

end
