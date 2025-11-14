(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2025  Aarno Labs LLC

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

(** {1 Test specification for proof obligation checkers}

   Test specifications contain the following information:

   - {b title:} name of the test

   - {b file/function identification:}
     + filename: name of the c-file to be loaded
     + funname: name of the function to be checked

   - {b selection of proof obligation to check:}

     + reqargs: list of strings that represent the arguments to the
     proof obligation predicate; this may be an empty list or a list
     that has the right length, but individual arguments may be omitted
     by specifying the empty string ("")
     + line: the line number to which the proof obligation applies (can be
     left unspecified by giving -1)
     + byte: the byte number at which the proof obligation is located (can
     be left unspecified by giving -1)

   - {b check that proof obligation is discharged as expected:}

     + xdetail: identification of the discharge method in the checker
     + expl: explanation given for the discharge (can be left unspecified
      by giving the empty string)

   {2 Example specification}

   {[
      ("gl-inv-001",
       "locally_initialized_gl_inv_001", "gl_inv_001",
       [], -1, -1,
       "inv_implies_safe", "local assignment(s): assignedAt#4")
   ]}

 *)


(** [analysis_setup domains predicate filename] performs the following actions:
    - remove any prior expanded .cch directory for this [filename]
    - unpack the gzipped tar file with path:
      ["testinputs"/predicate//filename.cch.tar.gz] into the directory
      [filename.cch]
    - set the project name and filename in system_settings to [filename]
    - create primary proof obligations for the analysis set in system_settings
    - reset the proof scaffolding
    - generate invariants and run the proof obligation checkers for the proof
      obligation present.
 *)
val analysis_setup: ?domains:string list -> string -> string -> unit


(** [analysis_take_down filename] removes the directory [filename.cch] from
    the current directory.
 *)
val analysis_take_down: string -> unit


(** [select_target_po reqargs line byte po_s] attempts to select the one
    proof obligation that matches the attributes specified as follows:
    - {b reqargs:} the required arguments of the target proof obligation;
        this can be either an empty list (no requirements), or a list
        with length matching the number of arguments of the proof
        obligation where each argument can either be the empty string
        (no requirement) or the printed version of the argument.
    - {b line:} the source line to which the proof obligation applies
         (or -1, if left unspecified)
    - {b byte:} the source byte to which the proof obligation applies
         (or -1, if left unspecified).

    [po_s] is the list of proof obligations to select from. This list
    is expected to have been filtered by the caller for the target
    predicate (e.g., [PInitialized]), so no selection is made on
    predicate in this function.

    The function returns [Some po] if a unique match was found, and
    [None] otherwise.

    If a unique match was not found, the test will fail and display a
    message with the list of proof obligations fully specified, to
    aid in refining the specification to provide to this function.

    An example of a test specification is given at the beginning of
    this page.
 *)
val select_target_po:
  ?reqargs:string list
  -> ?line:int
  -> ?byte:int
  -> CCHPreTypes.proof_obligation_int list
  -> CCHPreTypes.proof_obligation_int option


val located_po_to_string: CCHPreTypes.proof_obligation_int -> string
