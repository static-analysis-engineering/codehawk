CODEHAWK = ../..
CCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

CAML=$(shell ocamlopt -where)

THISDIR=$(shell pwd)
COBJ=$(THISDIR)/cobj

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
CCHLIB = $(CCH)/cchlib
CCHPRE = $(CCH)/cchpre
CCHANALYZE = $(CCH)/cchanalyze

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \
	-I $(CCHANALYZE)/cmi \

CAMLBUILD := ocamlopt str.cmxa unix.cmxa  \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	$(EXTLIB)/extlib.cmxa \
	$(ZARITHLIB)/zarith.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CCHLIB)/cchlib.cmxa \
	$(CCHPRE)/cchpre.cmxa \
	$(CCHANALYZE)/cchanalyze.cmxa

all: dirs canalyzer inspect

dirs:
	@mkdir -p cmx
	@mkdir -p cmi

inspect: dirs $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa cmx/cCHXInspectSummaries.cmx
	$(CAMLBUILD) -o inspectsummaries cmx/cCHXInspectSummaries.cmx

canalyzer: $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa $(CCHANALYZE)/cchanalyze.cmxa cmi/cCHVersion.cmi cmx/cCHVersion.cmx cmi/cCHXCAnalyzer.cmi cmx/cCHXCAnalyzer.cmx
	$(CAMLBUILD) -o canalyzer cmx/cCHVersion.cmx cmx/cCHXCAnalyzer.cmx

capplication: dirs $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa $(CCHANALYZE)/cchanalyze.cmxa cmi/cCHVersion.cmi cmx/cCHVersion.cmx cmi/cCHXCAnalyzer.cmi cmx/cCHXCApplication.cmx
	$(CAMLBUILD) -o capplication cmx/cCHVersion.cmx cmx/cCHXCApplication.cmx

canalyzer_object: dirs $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa $(CCHANALYZE)/cchanalyze.cmxa cmi/cCHVersion.cmi cmx/cCHVersion.cmx cmi/cCHXCAnalyzer.cmi cmx/cCHXCAnalyzer.cmx
	$(CAMLBUILD) -output-obj -o $(COBJ)/canalyzer.o cmx/cCHVersion.cmx cmx/cCHXCAnalyzer.cmx

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c $<

cmx/%.cmx: %.ml
	$(CAMLC) -o $@ -c $<

clean:
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f */*.d
	rm -f *.o
	rm -f *.d
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -f inspectsummaries
	rm -f canalyzer
	rm -f capplication
