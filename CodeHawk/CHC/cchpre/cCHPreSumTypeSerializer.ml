(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHPEPRTypes

(* chutil *)
open CHSumTypeSerializer

(* cchpre *)
open CCHPreTypes

module H = Hashtbl


let bound_type_mfts: bound_type_t mfts_int =
  mk_mfts "bound_type_t" [(LB, "LB"); (UB, "UB")]


let po_status_mfts: po_status_t mfts_int =
  mk_mfts
    "po_status_t"
    [(Green, "g");
     (Orange, "o");
     (Red, "r");
     (Purple, "p");
     (Blue, "b");
     (Grey, "x")]


let address_type_mfts: address_type_t mfts_int =
  mk_mfts  "address_type_t" [(Heap, "h"); (Stack, "s"); (External, "x")]


class assignment_mcts_t: [assignment_t] mfts_int =
object

  inherit [assignment_t] mcts_t "assignemnt_t"

  method! ts (a:assignment_t) =
    match a with
    | InitAssignment _ -> "init"
    | GlobalAssignment _ -> "g"
    | GlobalIndexAssignment _ -> "gi"
    | StaticAssignment _ -> "s"
    | StaticIndexAssignment _ -> "si"
    | FieldAssignment _ -> "f"
    | UnknownAssignment _ -> "u"

  method! tags = ["f"; "g"; "gi"; "init"; "s"; "si"; "u"]

end

let assignment_mcts:assignment_t mfts_int =
  new assignment_mcts_t


class global_value_mcts_t: [global_value_t] mfts_int =
object

  inherit [global_value_t] mcts_t "global_value_t"

  method! ts (g:global_value_t) =
    match g with
    | GlobalValue _ -> "gv"

  method! tags = ["gv"]

end

let global_value_mcts:global_value_t mfts_int = new global_value_mcts_t


class dependencies_mcts_t:[dependencies_t] mfts_int =
object

  inherit [dependencies_t] mcts_t "dependencies_t"

  method! ts (d:dependencies_t) =
    match d with
    | DStmt -> "s"
    | DLocal _ -> "f"
    | DReduced _ -> "r"
    | DEnvC _ -> "a"
    | DUnreachable _ -> "x"

  method! tags = ["a"; "f"; "r"; "s"; "x"]

end

let dependencies_mcts:dependencies_t mfts_int = new dependencies_mcts_t


class po_predicate_mcts_t:[po_predicate_t] mfts_int =
object

  inherit [po_predicate_t] mcts_t "po_predicate_t"

  method! ts (p:po_predicate_t) =
    match p with
    | PGlobalAddress _ -> "ga"
    | PHeapAddress _ -> "ha"
    | PControlledResource _ -> "cr"
    | PNotNull _ -> "nn"
    | PNull _ -> "null"
    | PValidMem _ -> "vm"
    | PInScope _ -> "is"
    | PStackAddressEscape _ -> "sae"
    | PAllocationBase _ -> "ab"
    | PTypeAtOffset _ -> "tao"
    | PLowerBound _ -> "lb"
    | PUpperBound _ -> "ub"
    | PIndexLowerBound _ -> "ilb"
    | PIndexUpperBound _ -> "iub"
    | PInitialized _ -> "i"
    | PInitializedRange _ -> "ir"
    | PCast _ -> "c"
    | PFormatCast _ -> "fc"
    | PPointerCast _ -> "pc"
    | PSignedToUnsignedCastLB _ -> "csul"
    | PSignedToUnsignedCastUB _ -> "csuu"
    | PUnsignedToSignedCast _ -> "cus"
    | PUnsignedToUnsignedCast _ -> "cuu"
    | PSignedToSignedCastLB _ -> "cssl"
    | PSignedToSignedCastUB _ -> "cssu"
    | PNotZero _ -> "z"
    | PNonNegative _ -> "nneg"
    | PNullTerminated _ -> "nt"
    | PIntUnderflow _ -> "iu"
    | PIntOverflow _ -> "io"
    | PUIntUnderflow _ -> "uiu"
    | PUIntOverflow _ -> "uio"
    | PWidthOverflow _ -> "w"
    | PPtrLowerBound _ -> "plb"
    | PPtrUpperBound _ -> "pub"
    | PPtrUpperBoundDeref _ -> "pubd"
    | PCommonBase _ -> "cb"
    | PCommonBaseType _ -> "cbt"
    | PFormatString _ -> "ft"
    | PVarArgs _ -> "va"
    | PNoOverlap _ -> "no"
    | PValueConstraint _ -> "vc"
    | PDSCondition _ -> "ds"
    | PContract _ -> "ctt"
    | PConfined _ -> "cf"
    | PMemoryPreserved _ -> "pm"
    | PValuePreserved _ -> "pv"
    | PUniquePointer _ -> "up"
    | PPreservedAllMemory -> "prm"
    | PPreservedAllMemoryX _ -> "prmx"
    | PContractObligation _ ->  "cob"
    | PBuffer _ -> "b"
    | PRevBuffer _ -> "rb"
    | PNewMemory _ -> "nm"
    | PDistinctRegion _ -> "dr"

  method! tags = [
      "ab"; "b"; "c"; "cb"; "cbt"; "cf"; "cob"; "cr"; "cssl"; "cssu"; "csul";
      "csuu"; "ctt"; "cus"; "cuu"; "dr"; "ds"; "fc"; "ft"; "ga"; "ha"; "ilb";
      "i"; "io"; "ir"; "is"; "iu"; "iub"; "lb"; "nm"; "nn"; "nneg"; "no";
      "nt"; "null"; "pc"; "plb"; "pm"; "prm";  "prmx"; "pub"; "pubd"; "pv";
      "rb"; "sae"; "tao"; "ub"; "uio"; "uiu"; "up"; "va"; "vc"; "vm"; "w";
      "z"]

end

let po_predicate_mcts: po_predicate_t mfts_int = new po_predicate_mcts_t


class assumption_type_mcts_t:[assumption_type_t] mfts_int =
object

  inherit [assumption_type_t] mcts_t "assumption_type_t"

  method! ts (a:assumption_type_t) =
    match a with
    | ApiAssumption _ -> "aa"
    | GlobalApiAssumption _ -> "gi"
    | PostAssumption _ -> "ca"
    | GlobalAssumption _ -> "ga"
    | LocalAssumption _ -> "la"

  method! tags = ["aa"; "ca"; "ga"; "gi"; "la"]

end

let assumption_type_mcts: assumption_type_t mfts_int = new assumption_type_mcts_t


class ppo_type_mcts_t: [ppo_type_t] mfts_int =
object

  inherit [ppo_type_t] mcts_t "ppo_type_t"

  method! ts (p:ppo_type_t) =
    match p with
    | PPOprog _ -> "p"
    | PPOlib _ -> "pl"

  method! tags = ["p"; "pl"]

end

let ppo_type_mcts: ppo_type_t mfts_int = new ppo_type_mcts_t


class spo_type_mcts_t: [spo_type_t] mfts_int =
object

  inherit [spo_type_t] mcts_t "spo_type_t"

  method! ts (s:spo_type_t) =
    match s with
    | CallsiteSPO _ -> "cs"
    | ReturnsiteSPO _ -> "rs"
    | LocalSPO _ -> "ls"

  method! tags = ["cs"; "ls"; "rs"]

end

let spo_type_mcts: spo_type_t mfts_int = new spo_type_mcts_t


class memory_base_mcts_t:[memory_base_t] mfts_int =
object

  inherit [memory_base_t] mcts_t "memory_base_t"

  method! ts (b:memory_base_t) =
    match b with
    | CNull _ -> "null"
    | CStringLiteral _ -> "str"
    | CStackAddress _ -> "sa"
    | CGlobalAddress _ -> "ga"
    | CBaseVar _ -> "bv"
    | CUninterpreted _ -> "ui"

  method! tags = ["bv"; "ga"; "null"; "sa"; "str"; "ui"]

end

let memory_base_mcts:memory_base_t mfts_int = new memory_base_mcts_t


class constant_value_variable_mcts_t: [constant_value_variable_t] mfts_int =
object

  inherit [constant_value_variable_t] mcts_t "constant_value_variable_t"

  method! ts (c:constant_value_variable_t) =
    match c with
    | InitialValue _ -> "iv"
    | FunctionReturnValue _ -> "frv"
    | ExpReturnValue _ -> "erv"
    | FunctionSideEffectValue _ -> "fsev"
    | ExpSideEffectValue _ -> "esev"
    | SymbolicValue _ -> "sv"
    | TaintedValue _ -> "tv"
    | ByteSequence _ -> "bs"
    | MemoryAddress _ -> "ma"

  method! tags = ["bs"; "erv"; "esev"; "frv"; "fsev"; "iv"; "ma"; "sv"; "tv"]

end

let constant_value_variable_mcts:constant_value_variable_t mfts_int =
  new constant_value_variable_mcts_t


class c_variable_denotation_mcts_t:[c_variable_denotation_t] mfts_int =
object

  inherit [c_variable_denotation_t] mcts_t "c_variable_denotation_t"

  method! ts (v:c_variable_denotation_t) =
    match v with
    | LocalVariable _ -> "lv"
    | GlobalVariable _ -> "gv"
    | ExternalStateVariable _ -> "es"
    | MemoryVariable _ -> "mv"
    | MemoryRegionVariable _ -> "mrv"
    | ReturnVariable _ -> "rv"
    | FieldVariable _ -> "fv"
    | CheckVariable _ -> "cv"
    | AuxiliaryVariable _ -> "av"
    | AugmentationVariable _ -> "xv"

  method! tags = ["av"; "cv"; "es"; "fv"; "gv"; "lv"; "mrv"; "mv"; "rv"; "xv"]

end

let c_variable_denotation_mcts:c_variable_denotation_t mfts_int =
  new c_variable_denotation_mcts_t


class non_relational_value_mcts_t:[non_relational_value_t] mfts_int =
object

  inherit [non_relational_value_t] mcts_t "non_relational_value_t"

  method! ts (v:non_relational_value_t) =
    match v with
    | FSymbolicExpr _ -> "sx"
    | FSymbolicBound _ -> "sb"
    | FIntervalValue _ -> "iv"
    | FBaseOffsetValue _ -> "bv"
    | FRegionSet _ -> "rs"
    | FInitializedSet _ -> "iz"
    | FPolicyStateSet _ -> "ps"

  method! tags = ["bv"; "iv"; "iz"; "ps"; "sb"; "rs"; "sx"]
end

let non_relational_value_mcts:non_relational_value_t mfts_int =
  new non_relational_value_mcts_t
