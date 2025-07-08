(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2025  Aarno Labs, LLC

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


(** {1 Instruction aggregates: Overview} *)

(** {2 Description}

    An instruction aggregate is a (usually, but not always, contiguous)
    sequence of two or more instructions that is treated as a single
    semantic unit. The semantics for the entire sequence is assigned to
    one of the instructions (often the last one in the sequence) and all
    other instructions are considere no-ops by all subsequent analyses.

    Instruction aggregates cover a variety of constructs ranging from
    predicate and ternary assignments to jump tables.

    {2 Motivation}

    The rationale behind combining a sequence of instructions into an
    aggregate is that the collective action of the individual instructions
    combined is not easily apparent from considering their semantics in
    isolation. The instructions usually collaborate in a very specific
    way to achieve a particular result, with operands from different instructions
    playing playing a specific role. This is especially true of the jump
    table aggregates. For some of the other aggregate kinds the semantics
    of the individual instructions combined would be similar, but analysis
    of the aggregate is more efficient and precise. For example, this is
    the case with the predicate assignment:
    {[
    <test>
    MOVcc   Rx, #1
    MOVcc'  Rx, #0   where cc' is (not cc)
    ]}
    The two MOV instructions can be combined into one assignment of the
    boolean <test-cc>:
    {[
    Rx := <test-cc>
    ]}
    Translating and analyzing the two instructions in isolation produces
    two joins, and potentially three reaching definitions for a subsequent
    use of Rx. In contrast, the two instructions combined into one
    predicate assignment produces zero joins, and only a single reaching
    definition for a subsequent use of Rx, a considerable improvement.

    {2 Identification}

    Instruction aggregates are identified during disassembly by pattern
    matching. Identification is entirely syntactic, so only the information
    present in the instructions themselves, such as opcode and operands,
    are used; not the possible values that those operands may have, unless
    they are immediates.

    {2 Representation}

    The aggregate is represented by objects of the class type
    [arm_instruction_aggregate_int]. These objects contain the kind of
    aggregate, a list of the contributing instructions, and information
    about its entry, exit, and anchor address. The anchor is the
    instruction to which the full semantics of the aggregate is assigned.

    Cross references to instances are recorded in the [arm_assembly_instruction_int]
    instances of the instructions that make up the aggregate to enable
    triggering proper translation and analysis. The collection of all
    aggregates themselves is maintained in the singleton object of type
    [arm_assembly_instructions_int].

    Most aggregates are contained within a single basic block and do not
    affect control flow. The exceptions are jump tables, whose components
    are directly incorporated into the CFG during disassembly and require
    no further semantic handling.

    {2 Translation into CHIF}

    The semantics of the aggregate is explicated in the translation into
    CHIF. In general, instructions are individually translated into CHIF
    (in the function [translate_arm_instruction]). In the case of aggregates
    CHIF is generated for the full semantics at the anchor instruction,
    while all other other instructions in the aggregate are treated as
    no-ops. In the case of jump tables the full semantics is already
    incorporated in the CFG during disassembly and all instructions in
    the aggregate are treated as no-ops.

    {2 Transfer to front end}

    The kind and structure of aggregates and analysis results involving
    their components are communicated to the (python) front end in the
    instruction results data contained in the function opcode dictionary
    (see bCHFnARMDictionary). The format varies with the kind of aggregate,
    as each kind has different types of values that characterize its
    operation. In the (python) front end these values are made accessible
    to the various instructions in the [InstrXData] objects created for
    each instruction. The documentation of each aggregate kind below and
    elsewhere presents more details on the actual format for each of these.

    {2 Tests}

    Currenly only two of the kinds of aggregates have associated unit tests:
    - bCHARMJumpTableTest
    - bCHThumbITSequenceTest
    These tests contain instances of code fragments encountered in actual
    binaries and give some insight in their use.


    {1 Predicate Assignments}

    {2 Description}

    A predicate assignment aggregate consists of two assignment instructions
    that combine into a single assignment of a boolean predicate. The pattern
    for the aggregate is two adjacent MOV instructions of the form:
    {[
    <test>
    MOVcc  Rx, #1
    MOVcc' Rx, #0  where cc' is (not cc)
    ]}
    or
    {[
    <test>
    MOVcc' Rx, #0
    MOVcc  Rx, #1  where cc is not (cc')
    ]}
    In all executions exactly one of these two MOV instructions is executed.
    If the joint condition <test-cc> is true Rx is assigned 1, if it is false
    Rx is assigned 0, and thus the postcondition of these two instructions
    is essentially the assignment of the boolean <test-cc>.

    {3 Example}

    {[
    <CMP R0, #5>
    MOVNE  R1, #0
    MOVEQ  R1, #1
    ]}
    is translated into
    {[ R1 := (R0 == 5)  ]}

    {2 Representation}

    The [arm_instruction_aggregate] instance of the predicate assignment
    records the address of the second instruction as the anchor, the
    destination operand, and whether the <test-cc> predicate is to be
    inverted, where cc is the condition code for the anchor instruction.
    The predicate is to be inverted if the anchor instruction assigns 0.

    {2 Translation to CHIF}

    The first MOV instruction is translated into a no-op. The second
    MOV instruction is translated into the assignment
    {[ Rx := [not] predicate ]}
    with the single defined variable Rx, and with variables used all
    variables referenced in the predicate.

    If a predicate cannot be constructed or derived, the destination
    variable Rx is abstracted.

    {2 Transfer to front end}

    The first instruction is tagged as 'subsumed' by the second
    instruction, and thus to be treated as a no-op. The second
    instruction is tagged with 'agg:predassign' with a list of
    dependents (the first instruction in this case). It lists as
    a variable the destination operand, along with its (high)
    uses. If a predicate was construction, it lists
    (the possibly inverse of) the predicate in its original and
    rewritten form, along with its reaching definitions.
 *)

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


val make_arm_instruction_aggregate:
  kind:arm_aggregate_kind_t
  -> instrs:arm_assembly_instruction_int list
  -> entry:arm_assembly_instruction_int
  -> exitinstr:arm_assembly_instruction_int
  -> anchor:arm_assembly_instruction_int
  -> arm_instruction_aggregate_int


val make_arm_jumptable_aggregate:
  jt:arm_jumptable_int
  -> instrs:arm_assembly_instruction_int list
  -> entry:arm_assembly_instruction_int
  -> exitinstr:arm_assembly_instruction_int
  -> anchor:arm_assembly_instruction_int
  -> arm_instruction_aggregate_int


val identify_arm_aggregate:
  pushback_stream_int
  -> arm_assembly_instruction_int
  -> arm_instruction_aggregate_int option
