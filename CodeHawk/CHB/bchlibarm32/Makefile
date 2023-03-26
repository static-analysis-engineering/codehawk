CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
BCHCIL = $(CHB)/bchcil
ELFLIB = $(CHB)/bchlibelf

CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHCIL)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(ELFLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	bCHARMTypes \
	bCHARMTestSupport \
	bCHARMPseudocode \
	bCHARMSumTypeSerializer \
	bCHARMOperand \
	bCHARMOpcodeRecords \
	bCHARMDictionary \
	bCHARMConditionalExpr \
	bCHARMDisassemblyUtils \
	bCHARMAssemblyInstruction \
	bCHDisassembleARMInstruction \
	bCHDisassembleThumbInstruction \
	bCHARMCallSitesRecords \
	bCHARMAssemblyInstructions \
	bCHARMAssemblyBlock \
	bCHARMAssemblyFunction \
	bCHARMAssemblyFunctions \
	bCHARMCodePC \
	bCHARMCHIFSystem \
	bCHThumbITSequence \
	bCHARMJumptable \
	bCHARMInstructionAggregate \
	bCHConstructARMFunction \
	bCHDisassembleARM \
	bCHDisassembleARMStream \
	bCHARMLoopStructure \
	bCHTranslateARMToCHIF \
	bCHARMMetrics \
	bCHFnARMDictionary \
	bCHARMAnalysisResults \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHARMTestSupport \
	bCHARMPseudocode \
	bCHARMSumTypeSerializer \
	bCHARMOperand \
	bCHARMOpcodeRecords \
	bCHARMDictionary \
	bCHARMConditionalExpr \
	bCHARMDisassemblyUtils \
	bCHARMAssemblyInstruction \
	bCHDisassembleARMInstruction \
	bCHDisassembleThumbInstruction \
	bCHARMCallSitesRecords \
	bCHARMAssemblyInstructions \
	bCHARMAssemblyBlock \
	bCHARMAssemblyFunction \
	bCHARMAssemblyFunctions \
	bCHARMCodePC \
	bCHARMCHIFSystem \
	bCHThumbITSequence \
	bCHARMJumptable \
	bCHARMInstructionAggregate \
	bCHConstructARMFunction \
	bCHDisassembleARM \
	bCHDisassembleARMStream \
	bCHARMLoopStructure \
	bCHTranslateARMToCHIF \
	bCHARMMetrics \
	bCHFnARMDictionary \
	bCHARMAnalysisResults \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchlibarm32

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibarm32: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(ELFLIB)/bchlibelf.cmxa
	$(CAMLLINK) -a -o bchlibarm32.cmxa $(OBJECTS)

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
