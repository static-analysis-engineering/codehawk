CODEHAWK = ../..

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	bCHBCTypes \
	bCHBCSumTypeSerializer \
	bCHBCTypeTransformer \
	bCHLibTypes \
	bCHVersion \
	bCHXprUtil \
	bCHXmlUtil \
	bCHUtilities \
	bCHBasicTypes \
	bCHSystemSettings \
	bCHSumTypeSerializer \
	bCHBCTypePretty \
	bCHBCTypeUtil \
	bCHBCTypeXml \
	bCHBCDictionary \
	bCHDictionary \
	bCHBCFunDeclarations \
	bCHBCWriteXml \
	bCHBCFiles \
	bCHInterfaceDictionary \
	bCHVarDictionary \
	bCHInvDictionary \
	bCHVarInvDictionary \
	bCHTypeInvDictionary \
	bCHJavaBasicTypes \
	bCHTypeDefinitions \
	bCHJavaSignatures \
	bCHVariableNames \
	bCHDemangler \
	bCHCodegraph \
	bCHDoubleword \
	bCHFunctionData \
	bCHSystemData \
	bCHConstantDefinitions \
	bCHStructTables \
	bCHCallbackTables \
	bCHImmediate \
	bCHStreamWrapper \
	bCHDataExportSpec \
	bCHLocation \
	bCHStrings \
	bCHByteUtilities \
	bCHCPURegisters \
	bCHMemoryReference \
	bCHFtsParameter \
	bCHARMFunctionInterface \
	bCHFunctionInterface \
	bCHFunctionStub \
	bCHCallTarget \
	bCHBTerm \
	bCHCStructConstant \
	bCHExternalPredicate \
	bCHPrecondition \
	bCHPostcondition \
	bCHSideeffect \
	bCHFunctionSemantics \
	bCHFunctionSummary \
	bCHVariable \
	bCHLocationInvariant \
	bCHTypeInvariants \
	bCHLocationVarInvariant \
	bCHDataBlock \
	bCHJumpTable \
	bCHPreFileIO \
	bCHSpecializations \
	bCHUserProvidedDirections \
	bCHJni \
	bCHCStruct \
	bCHCppClass \
	bCHSectionHeadersInfo \
	bCHSystemInfo \
	bCHFunctionSummaryLibrary \
	bCHXPODictionary \
	bCHCallTargetInfo \
	bCHProofObligations \
	bCHFunctionStackframe \
	bCHFunctionInfo \
	bCHMakeCallTargetInfo \
	bCHGlobalState \
	bCHMemoryRecorder \
	bCHXPOPredicate \
	bCHCallSemanticsRecorder \
	bCHFloc \
	bCHCallgraph \
	bCHMetricsHandler \
	bCHDisassemblySummary \
	bCHMetrics \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHVersion \
	bCHXprUtil \
	bCHUtilities \
	bCHBasicTypes \
	bCHDoubleword \
	bCHXmlUtil \
	bCHLocation \
	bCHSystemSettings \
	bCHBCSumTypeSerializer \
	bCHBCTypeTransformer \
	bCHBCTypePretty \
	bCHBCDictionary \
	bCHBCFunDeclarations \
	bCHBCWriteXml \
	bCHBCFiles \
	bCHBCTypeUtil \
	bCHBCTypeXml \
	bCHSumTypeSerializer \
	bCHDictionary \
	bCHInterfaceDictionary \
	bCHDemangler \
	bCHFunctionData \
	bCHMemoryReference \
	bCHVarDictionary \
	bCHInvDictionary \
	bCHVarInvDictionary \
	bCHTypeInvDictionary \
	bCHTypeDefinitions \
	bCHJavaSignatures \
	bCHVariableNames \
	bCHCodegraph \
	bCHSystemData \
	bCHConstantDefinitions \
	bCHStructTables \
	bCHCallbackTables \
	bCHImmediate \
	bCHStreamWrapper \
	bCHDataExportSpec \
	bCHStrings \
	bCHByteUtilities \
	bCHCPURegisters \
	bCHFtsParameter \
	bCHARMFunctionInterface \
	bCHFunctionInterface \
	bCHBTerm \
	bCHFunctionStub \
	bCHCallTarget \
	bCHCStructConstant \
	bCHExternalPredicate \
	bCHPrecondition \
	bCHPostcondition \
	bCHSideeffect \
	bCHFunctionSemantics \
	bCHFunctionSummary \
	bCHVariable \
	bCHLocationInvariant \
	bCHTypeInvariants \
	bCHLocationVarInvariant \
	bCHDataBlock \
	bCHJumpTable \
	bCHPreFileIO \
	bCHSpecializations \
	bCHUserProvidedDirections \
	bCHJni \
	bCHCStruct \
	bCHCppClass \
	bCHSectionHeadersInfo \
	bCHSystemInfo \
	bCHFunctionSummaryLibrary \
	bCHXPODictionary \
	bCHCallTargetInfo \
	bCHProofObligations \
	bCHFunctionStackframe \
	bCHFunctionInfo \
	bCHMakeCallTargetInfo \
	bCHGlobalState \
	bCHMemoryRecorder \
	bCHXPOPredicate \
	bCHCallSemanticsRecorder \
	bCHFloc \
	bCHCallgraph \
	bCHMetricsHandler \
	bCHDisassemblySummary \
	bCHMetrics \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchlib

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlib: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa
	$(CAMLLINK) -a -o bchlib.cmxa $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml $(CMIS)
	$(CAMLC) -o $@ -c $<

clean:
	rm -f cmx/*.cm*
	rm -f cmi/*.cmi
	rm -f cmx/*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~ 
	rm -f bchlib.cmxa
	rm -rf doc
