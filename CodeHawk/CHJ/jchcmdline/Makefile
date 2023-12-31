CODEHAWK = ../..
JCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \

CAMLBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extlib.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(JCHLIB)/jchlib.cmxa \
	$(JCHPRE)/jchpre.cmxa \

CAMLDOC := ocamldoc
JAVAC = javac
OCAMLDEP := ocamldep

all: chj_template chj_integrate chj_inspect chj_native chj_experiment

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

# program to experiment with applying certain functionality to a single class
chj_experiment: cmi/jCHXClassExperiment.cmi cmx/jCHXClassExperiment.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXClassExperiment.cmx

# program to generate xml starting point for library method summaries
chj_template: cmi/jCHXTemplate.cmi cmx/jCHXTemplate.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXTemplate.cmx

# program to integrate platform-independent and platform dependent library summaries
chj_integrate: cmi/jCHXIntegrateSummaries.cmi cmx/jCHXIntegrateSummaries.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXIntegrateSummaries.cmx

# program to inspect library method summaries for syntactic correctness and semantic consistency
chj_inspect: cmi/jCHXInspectSummaries.cmi cmx/jCHXInspectSummaries.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXInspectSummaries.cmx

# program to generate class xml files with the signatures of native methods (NM)
chj_native: cmi/jCHXNativeMethodSignatures.cmi cmx/jCHXNativeMethodSignatures.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXNativeMethodSignatures.cmx


cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<


cleanjava:
	rm -f *.class

clean:
	rm -f .depend
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.exe
	rm -f *.ml~
	rm -f Makefile~
	rm -f chj_experiment
	rm -f chj_template
	rm -f chj_integrate
	rm -f chj_inspect
	rm -f chj_native

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
