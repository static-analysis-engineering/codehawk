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

CAMLLINK := ocamlopt
OCAMLDEP := ocamldep

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

all: bchlibarm32.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibarm32.cmxa: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(ELFLIB)/bchlibelf.cmxa
	$(CAMLLINK) -a -o $@ $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
	rm -f cmx/*.cm*
	rm -f cmi/*.cmi
	rm -f cmx/*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~ 
	rm -rf doc

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
