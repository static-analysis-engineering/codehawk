CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
ELFLIB = $(CHB)/bchlibelf

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(ELFLIB)/cmi \

CAMLLINK := ocamlopt
OCAMLDEP := ocamldep

MLIS := \
	bCHMIPSTypes \
	bCHMIPSSumTypeSerializer \
	bCHMIPSOperand \
	bCHMIPSOpcodeRecords \
	bCHMIPSDictionary \
	bCHMIPSDisassemblyUtils \
	bCHAssembleMIPSInstruction \
	bCHMIPSAssemblyInstruction \
	bCHMIPSAssemblyInstructions \
	bCHMIPSAssemblyBlock \
	bCHMIPSAssemblyFunction \
	bCHMIPSAssemblyFunctions \
	bCHMIPSCodePC \
	bCHDisassembleMIPSInstruction \
	bCHDisassembleMIPS \
	bCHMIPSCHIFSystem \
	bCHMIPSLoopStructure \
	bCHTranslateMIPSToCHIF \
	bCHMIPSMetrics \
	bCHFnMIPSDictionary \
	bCHMIPSAnalysisResults \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHMIPSSumTypeSerializer \
	bCHMIPSOperand \
	bCHMIPSOpcodeRecords \
	bCHMIPSDictionary \
	bCHMIPSDisassemblyUtils \
	bCHAssembleMIPSInstruction \
	bCHMIPSAssemblyInstruction \
	bCHMIPSAssemblyInstructions \
	bCHMIPSAssemblyBlock \
	bCHMIPSAssemblyFunction \
	bCHMIPSAssemblyFunctions \
	bCHMIPSCodePC \
	bCHDisassembleMIPSInstruction \
	bCHDisassembleMIPS \
	bCHMIPSCHIFSystem \
	bCHMIPSLoopStructure \
	bCHTranslateMIPSToCHIF \
	bCHMIPSMetrics \
	bCHFnMIPSDictionary \
	bCHMIPSAnalysisResults \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: bchlibmips32.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibmips32.cmxa: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(ELFLIB)/bchlibelf.cmxa
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
