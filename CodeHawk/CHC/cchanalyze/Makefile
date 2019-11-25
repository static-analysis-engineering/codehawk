CODEHAWK = ../..
CCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
CCHLIB = $(CCH)/cchlib
CCHPRE = $(CCH)/cchpre

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(CHLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \

CAMLLINK := ocamlopt  \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB)\cmi \
	-I $(CHUTIL)\cmi \
	-I $(XPRLIB)\cmi \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \

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

all: make_dirs cchanalyze

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cchanalyze: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa
	$(CAMLLINK) -a -o cchanalyze.cmxa $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml
	$(CAMLC) -o $@ -c $<

clean:
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
