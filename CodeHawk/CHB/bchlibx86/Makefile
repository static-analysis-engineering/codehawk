CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
PELIB  = $(CHB)/bchlibpe
ELFLIB = $(CHB)/bchlibelf

CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(PELIB)/cmi \
	-I $(ELFLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	bCHLibx86Types \
	bCHFileFormatUtil \
	bCHX86SumTypeSerializer \
	bCHFunctionLoops \
	bCHOperand \
	bCHX86Opcodes \
	bCHX86OpcodeRecords \
	bCHX86Dictionary \
	bCHFunctionHashes \
	bCHPredefinedUtil \
	bCHPredefinedAllocaSemantics \
	bCHPredefined64bitEDKSemantics \
	bCHPredefinedDelphiRTLSemantics \
	bCHPredefinedDelphiRTLClassSemantics \
	bCHPredefinedDelphiRTLSysUtilsSemantics \
	bCHPredefinedDelphiRTLTypesSemantics \
	bCHPredefinedErrnoSemantics \
	bCHPredefinedFPSemantics \
	bCHPredefinedGettersSemantics \
	bCHPredefinedPredicatesSemantics \
	bCHPredefinedSettersSemantics \
	bCHPredefinedUpdatersSemantics \
	bCHPredefinedProlog3Semantics \
	bCHPredefinedProlog4Semantics \
	bCHPredefinedLibInternalCRTSemantics \
	bCHPredefinedLibMemSemantics \
	bCHPredefinedLibMiscSemantics \
	bCHPredefinedLibStrSemantics \
	bCHPredefinedLibWcsSemantics \
	bCHPredefinedWrappedCallSemantics \
	bCHPredefinedELFSemantics \
	bCHPredefinedCallSemantics \
	bCHConditionalJumpExpr \
	bCHDisassemblyUtils \
	bCHAssemblyInstruction \
	bCHAssemblyInstructions \
	bCHAssemblyInstructionAnnotations \
	bCHAssemblyBlock \
	bCHAssemblyFunction \
	bCHAssemblyFunctions \
	bCHCodePC \
	bCHDisassembleX0 \
	bCHDisassembleX8 \
	bCHDisassembleX9 \
	bCHDisassembleXc \
	bCHDisassembleXd \
	bCHDisassembleXf \
	bCHDisassembleInstruction \
	bCHPullData \
	bCHDisassemble \
	bCHDisassembleELF \
	bCHDisassembleStream \
	bCHIFSystem \
	bCHLoopStructure \
	bCHTranslateToCHIF \
	bCHTranslateToTypeCHIF \
	bCHRecordMemoryAccesses \
	bCHGlobalVariables \
	bCHDisassemblyMetrics \
	bCHX86Metrics \
	bCHFnX86Dictionary \
	bCHX86AnalysisResults \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHFunctionLoops \
	bCHFileFormatUtil \
	bCHX86SumTypeSerializer \
	bCHOperand \
	bCHX86Opcodes \
	bCHX86OpcodeRecords \
	bCHX86Dictionary \
	bCHDisassemblyUtils \
	bCHFunctionHashes \
	bCHPredefinedUtil \
	bCHPredefinedAllocaSemantics \
	bCHPredefined64bitEDKSemantics \
	bCHPredefinedDelphiRTLSemantics \
	bCHPredefinedDelphiRTLClassSemantics \
	bCHPredefinedDelphiRTLSysUtilsSemantics \
	bCHPredefinedDelphiRTLTypesSemantics \
	bCHPredefinedErrnoSemantics \
	bCHPredefinedFPSemantics \
	bCHPredefinedGettersSemantics \
	bCHPredefinedPredicatesSemantics \
	bCHPredefinedSettersSemantics \
	bCHPredefinedUpdatersSemantics \
	bCHPredefinedProlog3Semantics \
	bCHPredefinedProlog4Semantics \
	bCHPredefinedLibInternalCRTSemantics \
	bCHPredefinedLibMemSemantics \
	bCHPredefinedLibMiscSemantics \
	bCHPredefinedLibStrSemantics \
	bCHPredefinedLibWcsSemantics \
	bCHPredefinedWrappedCallSemantics \
	bCHPredefinedELFSemantics \
	bCHPredefinedCallSemantics \
	bCHConditionalJumpExpr \
	bCHAssemblyInstruction \
	bCHAssemblyInstructions \
	bCHAssemblyInstructionAnnotations \
	bCHAssemblyBlock \
	bCHAssemblyFunction \
	bCHAssemblyFunctions \
	bCHCodePC \
	bCHDisassembleX0 \
	bCHDisassembleX8 \
	bCHDisassembleX9 \
	bCHDisassembleXc \
	bCHDisassembleXd \
	bCHDisassembleXf \
	bCHDisassembleInstruction \
	bCHPullData \
	bCHDisassemble \
	bCHDisassembleELF \
	bCHDisassembleStream \
	bCHIFSystem \
	bCHLoopStructure \
	bCHTranslateToCHIF \
	bCHTranslateToTypeCHIF \
	bCHRecordMemoryAccesses \
	bCHGlobalVariables \
	bCHDisassemblyMetrics \
	bCHX86Metrics \
	bCHFnX86Dictionary \
	bCHX86AnalysisResults \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchlibx86

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibx86: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(PELIB)/bchlibpe.cmxa $(ELFLIB)/bchlibelf.cmxa
	$(CAMLLINK) -a -o bchlibx86.cmxa $(OBJECTS)

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
	rm -rf doc
