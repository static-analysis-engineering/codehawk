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

all: make_dirs template integrate inspect native experiment

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

# program to experiment with applying certain functionality to a single class
experiment: cmi/jCHXClassExperiment.cmi cmx/jCHXClassExperiment.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_experiment cmx/jCHXClassExperiment.cmx

# program to generate xml starting point for library method summaries
template: cmi/jCHXTemplate.cmi cmx/jCHXTemplate.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_template cmx/jCHXTemplate.cmx

# program to integrate platform-independent and platform dependent library summaries
integrate: cmi/jCHXIntegrateSummaries.cmi cmx/jCHXIntegrateSummaries.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_integrate cmx/jCHXIntegrateSummaries.cmx

# program to inspect library method summaries for syntactic correctness and semantic consistency
inspect: cmi/jCHXInspectSummaries.cmi cmx/jCHXInspectSummaries.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_inspect cmx/jCHXInspectSummaries.cmx

# program to generate class xml files with the signatures of native methods (NM)
native: cmi/jCHXNativeMethodSignatures.cmi cmx/jCHXNativeMethodSignatures.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_native cmx/jCHXNativeMethodSignatures.cmx


cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c $<

cmx/%.cmx: %.ml
	$(CAMLC) -o $@ -c $<


cleanjava:
	rm -f *.class

clean:
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
