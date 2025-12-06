(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 HennyB.  Sipma
   Coprygith (c) 2023-2025 Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHTraceResult

(* cchlib *)
open CCHBasicTypes

(* cchpre *)
open CCHPreTypes

(** File organization

All intermediate and final results are saved in xml/json files with fixed
names derived from the names of the c files and c functions. The functions in
this file parse the xml/json files and return the top functional xml element
of these files (xml) or the dictionary (json). The filenames themselves can
be retrieved as well.

File-naming schema:

A file x.c in a project is identified by three components:
- a project path <pp>, which can be either the directory of the file
    (in case of a single file) or the location of the Makefile (in
    case of a multi file project);
- a project name <pn>, which is the x in the case of a single c file,
    and is user-specified name otherwise;
- a file path <fp>, which is the path of the directory in which the
    file resides relative to the project path. In case of a single
    c file fp is omitted.
- the file name <x> (without extension)

The user can specify a different directory to store the analysis artifacts,
which is designated by <tp> (targetpath).

Given a file x.c with project path pp, project name pn, and file path fp,
and specified target path tp, the following artifacts are produced in
multiple stages:

1. A new analysis directory is created: tp/pn.cch with two subdirectories:
   tp/pn.cch/a and tp/pn.cch/s

2. x.c is preprocessed with the gcc preprocessor, producing the file
   pp/fp/x.i. Both pp/fp/x.c and pp/fp/x.i are copied to tp/pn.cch/s/fp.

3. x.c is parsed by the CodeHawk/CIL parser, producing the following files
   tp/pn.cch/a/fp/x/x_cdict.xml
                   /x_cfile.xml
                   /functions/<x_fn>/x_fn_cfun.xml  (for every function fn in x)

3a. In case of multiple c files, the files are linked, resolving dependencies
    between globally visible functions, variables, and data structures,
    producing the files:
    tp/pn.cch/a/fp/x/x_gxrefs
                globaldefinitions.xml
                target_files.xml

4. When all c files in the project (that is, indicated by the Makefile)
   have been parsed the directory tp/pn.cch is saved as a gzipped tar file,
   tp/pn.cch.tar.gz, to enable redoing the analysis without having to
   reparse, or sharing the same parsing results with others (this is
   because the preprocessing is performed against the local environment,
   including header files, availability of other libraries, etc., and
   thus may be different for different computers).

5. Primary proof obligations are generated for x.c, producing the following
   files:
   tp/pn.cch/a/fp/x/x_cgl.xml
                    x_ctxt.xml
                    x_ixf.xml
                    x_prd.xml
                    functions/<x_fn>/x_fn_api.xml
                                    /x_fn_pod.xml
                                    /x_fn_ppo.xml
                    logfiles/x_primary.chlog
                             x_primary.errorlog
                             x_primary.infolog

6. Invariants are generated and proof obligations are checked, producing
   the following files:
   tp/pn.cch/a/fp/x/functions/<x_fn>/x_fn_invs.xml
                                    /x_fn_vars.xml
                   /logfiles/x_gencheck.chlog
                             x_gencheck.errorlog
                             x_gencheck.infolog

7. Supporting proof obligations are generated for dependencies across
   functions and files, producing
   tp/pn.cch/a/fp/x/functions/<x_fn>/x_fn_spo.xml

Steps 6 and 7 are repeated until convergence.
 *)


val save_logfile: logger_int -> string -> string -> unit

val append_to_logfile: logger_int -> string -> string -> unit

val read_cfile: unit -> file

val read_cfile_dictionary: unit -> unit

val save_cfile_dictionary: unit -> unit

val read_cfile_assignment_dictionary: unit -> unit

val save_cfile_assignment_dictionary: unit -> unit

val read_cfile_predicate_dictionary: unit -> unit

val save_cfile_predicate_dictionary: unit -> unit

val read_cfile_interface_dictionary: unit -> unit

val save_cfile_interface_dictionary: unit -> unit

val read_cfile_context: unit -> unit

val save_cfile_context: unit -> unit

val read_function_semantics: string -> fundec

val save_chif: string -> pretty_t -> unit

val read_proof_files: string -> cfundeclarations_int -> unit

val save_proof_files: string -> unit

val save_analysis_digests: string -> unit

val read_analysis_digests: string -> unit traceresult

val save_api: string -> unit

val read_api: string -> cfundeclarations_int -> unit

val save_vars: string -> variable_manager_int -> unit

val read_vars: string -> cfundeclarations_int -> variable_manager_int

val save_invs: string -> invariant_io_int -> unit

val read_invs: string -> vardictionary_int -> invariant_io_int

val read_ppos: string -> unit




(** {1 Currently not used} *)

val get_target_files_name: unit -> string
val read_target_files: unit -> (int * string) list
val get_src_directory: unit -> string
val save_cfile_logfile: logger_int -> string -> string -> unit
val get_xml_summaryresults_name: unit -> string
val read_cfile_contract: unit -> unit
val save_cfile_contract: unit -> unit
val get_savedsource_path: unit -> string
val get_cfile_basename: unit -> string
