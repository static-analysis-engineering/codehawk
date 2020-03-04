(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

open Big_int_Z

(* chlib *)
open CHPretty
open CHPrettyUtil
open CHLanguage
open CHAtlas
open CHIntervalsDomainExtensiveArrays
open CHIterator
open CHStack
open CHNumerical
open CHUtils

(* chutil *)
open CHXmlDocument

(* jchpre *)
open JCHPreFileIO
open JCHTaintOrigin

open JCHGlobals
open JCHSystem
open JCHPrintUtils


let analysis_pass start bottom_up = 
  if start then 
    JCHFields.int_field_manager#start 
  else 
    begin
      JCHIntStubs.int_stub_manager#reset_calls ; 
      JCHFields.int_field_manager#reset 
    end ;
  JCHNumericAnalysis.make_numeric_analysis bottom_up 

let numeric_analysis_1_2 () =
  pr__debug [NL; STR "Numeric analysis - First Pass"; NL; NL] ;
  analysis_pass true true ;
  JCHSystemUtils.add_timing "numeric analysis - first pass" ;
  pr__debug [NL; STR "Numeric analysis - Second Pass"; NL; NL] ;
  analysis_pass false false ;
  JCHSystemUtils.add_timing "numeric analysis - second pass" 

let numeric_analysis_1 () = 
  analysis_pass true true ;
  JCHSystemUtils.add_timing "numeric analysis" 

let analyze_system
      ~(analysis_level:int)
      ~(use_intervals:bool)
      ~(number_joins:int)
      ~(max_poly_coeff:int)
      ~(max_nb_constraints:int)
      ~(use_time_limits:bool)
      ~(poly_analysis_time_limit:int)
      ~(num_analysis_time_limit:int)
      ~(use_overflow:bool) = 

  if not (Sys.file_exists "codehawk") then Unix.mkdir "codehawk" 0o750 ;
  if not (Sys.file_exists "codehawk/temp") then Unix.mkdir "codehawk/temp" 0o750 ;
  JCHBasicTypes.set_permissive true ;
  pr__debug [STR "Start the analysis."; NL] ;
  JCHSystem.jsystem#set ((JCHIFSystem.chif_system)#get_system JCHIFSystem.base_system);
  pr__debug [STR "System was translated."; NL];

  JCHAnalysisUtils.numeric_params#set_analysis_level analysis_level;
  JCHAnalysisUtils.numeric_params#set_system_use_intervals use_intervals; 
  JCHAnalysisUtils.numeric_params#set_number_joins number_joins;
  JCHAnalysisUtils.numeric_params#set_max_poly_coefficient max_poly_coeff;
  JCHAnalysisUtils.numeric_params#set_max_number_constraints_allowed max_nb_constraints ;
  JCHAnalysisUtils.numeric_params#set_use_time_limits false;
  JCHAnalysisUtils.numeric_params#set_use_time_limits use_time_limits; 
  JCHAnalysisUtils.numeric_params#set_constraint_analysis_time_limit poly_analysis_time_limit;
  JCHAnalysisUtils.numeric_params#set_numeric_analysis_time_limit num_analysis_time_limit;
  JCHAnalysisUtils.numeric_params#set_use_overflow use_overflow;

  numeric_analysis_1_2 () ;
  JCHNumericAnalysis.set_pos_fields () ; (* needed for cost analysis *)
  pr__debug [STR "Polyhedra invariants were produced."; NL];
  pr__debug [STR "Loops were reported."; NL]

let analyze_taint () =
  pr__debug [STR "analyze_taint "; NL] ;
  JCHSystem.jsystem#set (JCHIFSystem.chif_system#get_system JCHIFSystem.base_system);
  JCHTaintOrigin.set_use_one_top_target false;
  JCHTGraphAnalysis.make_tgraphs true 


let analyze_taint_origins taint_origin_ind local_vars_only = 
  pr__debug [STR "analyze_taint "; NL] ;
  JCHSystem.jsystem#set (JCHIFSystem.chif_system#get_system JCHIFSystem.base_system);
  JCHTaintOrigin.set_use_one_top_target true;
  JCHTGraphAnalysis.make_tgraphs false ;
  pr__debug [STR "Start making origin graphs "; NL] ;
  let res_table =
    JCHTOriginGraphs.get_taint_origin_graph local_vars_only taint_origin_ind in
  pr__debug [NL; STR "result: "; NL; res_table#toPretty; NL];
  JCHSystemUtils.add_timing "origin graphs" ;
  JCHTNode.save_taint_trail res_table taint_origin_ind
