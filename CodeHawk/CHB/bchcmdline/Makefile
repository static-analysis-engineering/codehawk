CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

ZARITHLIB = $(shell ocamlfind query zarith)

THISDIR=$(shell pwd)
COBJ=$(THISDIR)/cobj

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
PELIB  = $(CHB)/bchlibpe
ELFLIB = $(CHB)/bchlibelf
X86LIB = $(CHB)/bchlibx86
MIPSLIB = $(CHB)/bchlibmips32
ANALYZ = $(CHB)/bchanalyze

CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(PELIB)/cmi \
	-I $(ELFLIB)/cmi \
	-I $(X86LIB)/cmi \
	-I $(MIPSLIB)/cmi \
	-I $(ANALYZ)/cmi \

CAMLLINK := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extLib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(PELIB)/bchlibpe.cmxa \
	$(ELFLIB)/bchlibelf.cmxa \
	$(X86LIB)/bchlibx86.cmxa \
	$(MIPSLIB)/bchlibmips32.cmxa \
	$(ANALYZ)/bchanalyze.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs xanalyzer inspect

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

defs: make_dirs libsum appsum constsum classsum structdef

xanalyzer:  $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(PELIB)/bchlibpe.cmxa $(X86LIB)/bchlibx86.cmxa $(ANALYZ)/bchanalyze.cmxa cmi/bCHVersion.cmi cmx/bCHVersion.cmx cmi/bCHXBinaryAnalyzer.cmi cmx/bCHXBinaryAnalyzer.cmx
	$(CAMLLINK) -o chx86_analyze cmx/bCHVersion.cmx cmx/bCHXBinaryAnalyzer.cmx

inspect: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa cmi/bCHXInspectSummaries.cmi cmx/bCHXInspectSummaries.cmx
	$(CAMLLINK) -o chx86_inspect_summaries $(OBJECTS) cmx/bCHXInspectSummaries.cmx

export:  $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(PELIB)/bchlibpe.cmxa cmx/bCHXSaveExports.cmx
	$(CAMLLINK) -o chx86_save_exports $(OBJECTS) cmx/bCHXSaveExports.cmx

libsum: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmx/bCHXMakeLibSummary.cmx
	$(CAMLLINK) -o chx86_make_lib_summary cmx/bCHXMakeLibSummary.cmx

appsum: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmx/bCHXMakeAppSummary.cmx
	$(CAMLLINK) -o chx86_make_app_summary cmx/bCHXMakeAppSummary.cmx

constsum: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmx/bCHXMakeConstSummary.cmx
	$(CAMLLINK) -o chx86_make_const_summary cmx/bCHXMakeConstSummary.cmx

classsum: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmx/bCHXMakeClassSummary.cmx
	$(CAMLLINK) -o chx86_make_class_summary cmx/bCHXMakeClassSummary.cmx

structdef: $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa cmx/bCHXMakeStructDefinition.cmx
	$(CAMLLINK) -o chx86_make_structdef cmx/bCHXMakeStructDefinition.cmx

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml $(CMIS)
	$(CAMLC) -o $@ -c $<

clean:
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
