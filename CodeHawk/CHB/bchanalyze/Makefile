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
X86LIB = $(CHB)/bchlibx86
MIPSLIB = $(CHB)/bchlibmips32
ARMLIB = $(CHB)/bchlibarm32
PWRLIB = $(CHB)/bchlibpower32

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(PELIB)/cmi \
	-I $(ELFLIB)/cmi \
	-I $(X86LIB)/cmi \
	-I $(MIPSLIB)/cmi \
	-I $(ARMLIB)/cmi \
	-I $(PWRLIB)/cmi \

CAMLLINK := ocamlopt
OCAMLDEP := ocamldep

MLIS := \
	bCHAnalysisTypes \
	bCHInterrupt \
	bCHNumericalConstraints \
	bCHExtractInvariants \
	bCHAnalyzeProcedure \
	bCHReachingDefs \
	bCHFileIO \
	bCHTrace \
	bCHAnalyzeApp \
	bCHSaveExports \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHInterrupt \
	bCHNumericalConstraints \
	bCHExtractInvariants \
	bCHAnalyzeProcedure \
	bCHReachingDefs \
	bCHFileIO \
	bCHTrace \
	bCHAnalyzeApp \
	bCHSaveExports \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: bchanalyze.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchanalyze.cmxa: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(PELIB)/bchlibpe.cmxa $(ELFLIB)/bchlibelf.cmxa $(X86LIB)/bchlibx86.cmxa $(MIPSLIB)/bchlibmips32.cmxa $(ARMLIB)/bchlibarm32.cmxa $(PWRLIB)/bchlibpower32.cmxa
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
