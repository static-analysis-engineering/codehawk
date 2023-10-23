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
	bCHLibTypes \
	bCHVersion \
	bCHXprUtil \
	bCHXmlUtil \
	bCHUtilities \
	bCHBasicTypes \
	bCHSystemSettings \
	bCHSumTypeSerializer \
	bCHBCDictionary \
	bCHDictionary \
	bCHBCFunDeclarations \
	bCHBCWriteXml \
	bCHBCUtil \
	bCHBCFiles \
	bCHBCTypeUtil \
	bCHInterfaceDictionary \
	bCHVarDictionary \
	bCHInvDictionary \
	bCHVarInvDictionary \
	bCHTypeInvDictionary \
	bCHJavaBasicTypes \
	bCHVariableType \
	bCHTypeDefinitions \
	bCHVariableTypeUtil \
	bCHJavaSignatures \
	bCHVariableNames \
	bCHProofObligationTypes \
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
	bCHFunctionInterface \
	bCHFunctionStub \
	bCHCallTarget \
	bCHBTerm \
	bCHCStructConstant \
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
	bCHParseBCFunctionSummary \
	bCHUserProvidedDirections \
	bCHJni \
	bCHCStruct \
	bCHCppClass \
	bCHSectionHeadersInfo \
	bCHSystemInfo \
	bCHFunctionSummaryLibrary \
	bCHCallTargetInfo \
	bCHFunctionInfo \
	bCHMakeCallTargetInfo \
	bCHGlobalState \
	bCHFloc \
	bCHCallgraph \
	bCHProofObligations \
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
	bCHSystemSettings \
	bCHBCSumTypeSerializer \
	bCHSumTypeSerializer \
	bCHBCDictionary \
	bCHDictionary \
	bCHBCFunDeclarations \
	bCHBCWriteXml \
	bCHBCUtil \
	bCHBCFiles \
	bCHBCTypeUtil \
	bCHInterfaceDictionary \
	bCHVariableType \
	bCHDemangler \
	bCHFunctionData \
	bCHMemoryReference \
	bCHVarDictionary \
	bCHInvDictionary \
	bCHVarInvDictionary \
	bCHTypeInvDictionary \
	bCHTypeDefinitions \
	bCHVariableTypeUtil \
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
	bCHLocation \
	bCHStrings \
	bCHByteUtilities \
	bCHCPURegisters \
	bCHFtsParameter \
	bCHFunctionInterface \
	bCHBTerm \
	bCHFunctionStub \
	bCHCallTarget \
	bCHCStructConstant \
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
	bCHParseBCFunctionSummary \
	bCHUserProvidedDirections \
	bCHJni \
	bCHCStruct \
	bCHCppClass \
	bCHSectionHeadersInfo \
	bCHSystemInfo \
	bCHFunctionSummaryLibrary \
	bCHCallTargetInfo \
	bCHFunctionInfo \
	bCHMakeCallTargetInfo \
	bCHGlobalState \
	bCHFloc \
	bCHCallgraph \
	bCHProofObligations \
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
