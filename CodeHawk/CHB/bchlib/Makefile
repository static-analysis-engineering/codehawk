CODEHAWK = ../..

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
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
	bCHLibTypes \
	bCHXprUtil \
	bCHXmlUtil \
	bCHUtilities \
	bCHBasicTypes \
	bCHSystemSettings \
	bCHSumTypeSerializer \
	bCHDictionary \
	bCHInterfaceDictionary \
	bCHVarDictionary \
	bCHInvDictionary \
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
	bCHImmediate \
	bCHStreamWrapper \
	bCHDataExportSpec \
	bCHLocation \
	bCHStrings \
	bCHByteUtilities \
	bCHCPURegisters \
	bCHMemoryReference \
	bCHMemoryAccesses \
	bCHApiParameter \
	bCHFunctionApi \
	bCHFunctionStub \
	bCHCallTarget \
	bCHBTerm \
	bCHCStructConstant \
	bCHPrecondition \
	bCHPostcondition \
	bCHSideeffect \
	bCHFunctionSummary \
	bCHVariable \
	bCHLocationInvariant \
	bCHTypeInvariants \
	bCHDataBlock \
	bCHJumpTable \
	bCHPreFileIO \
	bCHUserProvidedDirections \
	bCHJni \
	bCHCStruct \
	bCHCppClass \
	bCHSystemInfo \
	bCHFunctionSummaryLibrary \
	bCHCallTargetSemantics \
	bCHFunctionInfo \
	bCHGlobalState \
	bCHFloc \
	bCHCallgraph \
	bCHProofObligations \
	bCHMetricsHandler \
	bCHDisassemblySummary \
	bCHMetrics \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHXprUtil \
	bCHUtilities \
	bCHBasicTypes \
	bCHDoubleword \
	bCHXmlUtil \
	bCHSystemSettings \
	bCHSumTypeSerializer \
	bCHDictionary \
	bCHInterfaceDictionary \
	bCHVariableType \
	bCHDemangler \
	bCHFunctionData \
	bCHMemoryReference \
	bCHVarDictionary \
	bCHInvDictionary \
	bCHTypeInvDictionary \
	bCHTypeDefinitions \
	bCHVariableTypeUtil \
	bCHJavaSignatures \
	bCHVariableNames \
	bCHCodegraph \
	bCHSystemData \
	bCHConstantDefinitions \
	bCHImmediate \
	bCHStreamWrapper \
	bCHDataExportSpec \
	bCHLocation \
	bCHStrings \
	bCHByteUtilities \
	bCHCPURegisters \
	bCHMemoryAccesses \
	bCHApiParameter \
	bCHFunctionApi \
	bCHBTerm \
	bCHFunctionStub \
	bCHCallTarget \
	bCHCStructConstant \
	bCHPrecondition \
	bCHPostcondition \
	bCHSideeffect \
	bCHFunctionSummary \
	bCHVariable \
	bCHLocationInvariant \
	bCHTypeInvariants \
	bCHDataBlock \
	bCHJumpTable \
	bCHPreFileIO \
	bCHUserProvidedDirections \
	bCHJni \
	bCHCStruct \
	bCHCppClass \
	bCHSystemInfo \
	bCHFunctionSummaryLibrary \
	bCHCallTargetSemantics \
	bCHFunctionInfo \
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
