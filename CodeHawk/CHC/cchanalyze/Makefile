CODEHAWK = ../..
CCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
CCHLIB = $(CCH)/cchlib
CCHPRE = $(CCH)/cchpre

CAMLC := ocamlopt -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(CHLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \

CAMLLINK := ocamlopt  \
	-I $(EXTLIB) \
	-I $(CHLIB)\cmi \
	-I $(CHUTIL)\cmi \
	-I $(XPRLIB)\cmi \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \

OCAMLDEP := ocamldep

MLIS := \
	cCHAnalysisTypes \
	cCHNumericalConstraints \
	cCHExpr \
	cCHEngineUtil \
	cCHCommand \
	cCHEnvironment \
	cCHOrakel \
	cCHControlFlowGraph \
	cCHExpTranslator \
	cCHAssignmentTranslator \
	cCHCallTranslator \
	cCHOperationsProvider \
	cCHCfgTranslator \
	cCHInvariantStore \
	cCHFunctionTranslator \
	cCHPostCondition \
	cCHExtractInvariantFacts \
	cCHAnalyze \
	cCHCheckImplication \
	cCHPOQuery \
	cCHPOCheckAllocationBase \
	cCHPOCheckBuffer \
	cCHPOCheckCast \
	cCHPOCheckCommonBase \
	cCHPOCheckCommonBaseType \
	cCHPOCheckControlledResource \
	cCHPOCheckFormatCast \
	cCHPOCheckInScope \
	cCHPOCheckIndexLowerBound \
	cCHPOCheckIndexUpperBound \
	cCHPOCheckInitialized \
	cCHPOCheckInitializedRange \
	cCHPOCheckIntUtil \
	cCHPOCheckIntOverflow \
	cCHPOCheckIntUnderflow \
	cCHPOCheckUIntUnderflow \
	cCHPOCheckLowerBound \
	cCHPOCheckUpperBound \
	cCHPOCheckNoOverlap \
	cCHPOCheckNotNull \
	cCHPOCheckNotZero \
	cCHPOCheckNonNegative \
	cCHPOCheckPreservedAllMemory \
	cCHPOCheckStackAddressEscape \
	cCHPOCheckWidthOverflow \
	cCHPOCheckNullTerminated \
	cCHPOCheckPointerCast \
	cCHPOCheckPtrLowerBound \
	cCHPOCheckPtrUpperBound \
	cCHPOCheckSignedToSignedCastLB \
	cCHPOCheckSignedToSignedCastUB \
	cCHPOCheckSignedToUnsignedCastLB \
	cCHPOCheckSignedToUnsignedCastUB \
	cCHPOCheckUnsignedToSignedCast \
	cCHPOCheckUnsignedToUnsignedCast \
	cCHPOCheckValidMem \
	cCHPOCheckValueConstraint \
	cCHPOCheckValuePreserved \
	cCHPOChecker \
	cCHGenerateLocalInvariants \
	cCHCheckValidity \
	cCHGenerateAndCheck \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cCHNumericalConstraints \
	cCHExpr \
	cCHEngineUtil \
	cCHCommand \
	cCHEnvironment \
	cCHControlFlowGraph \
	cCHOrakel \
	cCHExpTranslator \
	cCHAssignmentTranslator \
	cCHCallTranslator \
	cCHOperationsProvider \
	cCHCfgTranslator \
	cCHInvariantStore \
	cCHFunctionTranslator \
	cCHExtractInvariantFacts \
	cCHPostCondition \
	cCHAnalyze \
	cCHCheckImplication \
	cCHPOQuery \
	cCHPOCheckAllocationBase \
	cCHPOCheckBuffer \
	cCHPOCheckCast \
	cCHPOCheckCommonBase \
	cCHPOCheckCommonBaseType \
	cCHPOCheckControlledResource \
	cCHPOCheckFormatCast \
	cCHPOCheckInScope \
	cCHPOCheckIndexLowerBound \
	cCHPOCheckIndexUpperBound \
	cCHPOCheckInitialized \
	cCHPOCheckInitializedRange \
	cCHPOCheckIntUtil \
	cCHPOCheckIntOverflow \
	cCHPOCheckIntUnderflow \
	cCHPOCheckUIntUnderflow \
	cCHPOCheckLowerBound \
	cCHPOCheckNoOverlap \
	cCHPOCheckUpperBound \
	cCHPOCheckNotNull \
	cCHPOCheckNotZero \
	cCHPOCheckNonNegative \
	cCHPOCheckWidthOverflow \
	cCHPOCheckNullTerminated \
	cCHPOCheckPointerCast \
	cCHPOCheckPreservedAllMemory \
	cCHPOCheckStackAddressEscape \
	cCHPOCheckPtrLowerBound \
	cCHPOCheckPtrUpperBound \
	cCHPOCheckSignedToSignedCastLB \
	cCHPOCheckSignedToSignedCastUB \
	cCHPOCheckSignedToUnsignedCastLB \
	cCHPOCheckSignedToUnsignedCastUB \
	cCHPOCheckUnsignedToSignedCast \
	cCHPOCheckUnsignedToUnsignedCast \
	cCHPOCheckValidMem \
	cCHPOCheckValueConstraint \
	cCHPOCheckValuePreserved \
	cCHPOChecker \
	cCHGenerateLocalInvariants \
	cCHCheckValidity \
	cCHGenerateAndCheck \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: cchanalyze.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cchanalyze.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa
	$(CAMLLINK) -a -o cchanalyze.cmxa $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.d
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -f generateinvariants
	rm -f call_generateinvariants
	rm -f generateglobalinvariants
	rm -f testinvariants
	rm -f checkpo
	rm -f call_checkpo

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
