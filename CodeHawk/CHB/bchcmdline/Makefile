CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

ZARITHLIB = $(shell ocamlfind query zarith)
CIL = $(shell ocamlfind query goblint-cil)

THISDIR=$(shell pwd)
COBJ=$(THISDIR)/cobj

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
BCHCIL = $(CHB)/bchcil
PELIB  = $(CHB)/bchlibpe
ELFLIB = $(CHB)/bchlibelf
X86LIB = $(CHB)/bchlibx86
MIPSLIB = $(CHB)/bchlibmips32
ARMLIB = $(CHB)/bchlibarm32
PWRLIB = $(CHB)/bchlibpower32
ANALYZ = $(CHB)/bchanalyze

CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(BCHCIL)/cmi \
	-I $(PELIB)/cmi \
	-I $(ELFLIB)/cmi \
	-I $(X86LIB)/cmi \
	-I $(MIPSLIB)/cmi \
	-I $(ARMLIB)/cmi \
	-I $(PWRLIB)/cmi \
	-I $(ANALYZ)/cmi \

CAMLLINK := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extlib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(CIL)/goblintCil.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(BCHCIL)/bchcil.cmxa \
	$(PELIB)/bchlibpe.cmxa \
	$(ELFLIB)/bchlibelf.cmxa \
	$(X86LIB)/bchlibx86.cmxa \
	$(MIPSLIB)/bchlibmips32.cmxa \
	$(ARMLIB)/bchlibarm32.cmxa \
	$(PWRLIB)/bchlibpower32.cmxa \
	$(ANALYZ)/bchanalyze.cmxa \

OCAMLDEP := ocamldep

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: chx86_analyze chx86_inspect_summaries

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

defs: make_dirs libsum appsum constsum classsum structdef

chx86_analyze:  $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHCIL)/bchcil.cmxa $(BCHLIB)/bchlib.cmxa $(PELIB)/bchlibpe.cmxa $(X86LIB)/bchlibx86.cmxa $(MIPSLIB)/bchlibmips32.cmxa $(ARMLIB)/bchlibarm32.cmxa $(PWRLIB)/bchlibpower32.cmxa $(ANALYZ)/bchanalyze.cmxa cmi/bCHXBinaryAnalyzer.cmi cmx/bCHXBinaryAnalyzer.cmx
	$(CAMLLINK) -o $@ cmx/bCHXBinaryAnalyzer.cmx

chx86_inspect_summaries: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa cmi/bCHXInspectSummaries.cmi cmx/bCHXInspectSummaries.cmx
	$(CAMLLINK) -o $@ $(OBJECTS) cmx/bCHXInspectSummaries.cmx

chx86_save_exports:  $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(PELIB)/bchlibpe.cmxa cmx/bCHXSaveExports.cmx
	$(CAMLLINK) -o $@ $(OBJECTS) cmx/bCHXSaveExports.cmx

chx86_make_lib_summary: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmi/bCHXMakeLibSummary.cmi cmx/bCHXMakeLibSummary.cmx
	$(CAMLLINK) -o $@ cmx/bCHXMakeLibSummary.cmx

chx86_make_app_summary: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmi/bCHXMakeAppSummary.cmi cmx/bCHXMakeAppSummary.cmx
	$(CAMLLINK) -o $@ cmx/bCHXMakeAppSummary.cmx

chx86_make_const_summary: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmi/bCHXMakeConstSummary.cmi cmx/bCHXMakeConstSummary.cmx
	$(CAMLLINK) -o $@ cmx/bCHXMakeConstSummary.cmx

chx86_make_class_summary: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmi/bCHXMakeClassSummary.cmi cmx/bCHXMakeClassSummary.cmx
	$(CAMLLINK) -o $@ cmx/bCHXMakeClassSummary.cmx

chx86_make_structdef: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmi/bCHXMakeStructDefinition.cmi cmx/bCHXMakeStructDefinition.cmx
	$(CAMLLINK) -o $@ cmx/bCHXMakeStructDefinition.cmx

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
	rm -f cmx/*.cm*
	rm -f cmi/*.cmi
	rm -f cmx/*.o
	rm -f cobj/*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~ 
	rm -rf chx86_analyze
	rm -rf chx86_inspect_summaries
	rm -rf chx86_save_exports
	rm -rf chx86_make_lib_summary
	rm -rf chx86_make_app_summary
	rm -rf chx86_make_class_summary
	rm -rf chx86_make_const_summary
	rm -rf chx86_make_structdef
	rm -rf doc

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
