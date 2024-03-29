CODEHAWK := ../..
JCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre
JCHCOST= $(JCH)/jchcost
JCHSYS = $(JCH)/jchsys
JCHPOLY= $(JCH)/jchpoly

DEP_INCLUDES := -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHSYS)/cmi \
	-I $(JCHPOLY)/cmi \
	-I $(JCHCOST)/cmi \

INCLUDES := $(DEP_INCLUDES)

CAMLC := ocamlopt

CAMLLINK := ocamlopt -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB)    \
	-I $(CHLIB) \
	-I $(CHUTIL) \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHSYS)/cmi \
	-I $(JCHPOLY)/cmi \
	-I $(JCHCOST)/cmi \

CAMLBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	$(EXTLIB)/extlib.cmxa \
	$(ZARITHLIB)/zarith.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(JCHLIB)/jchlib.cmxa \
	$(JCHPRE)/jchpre.cmxa \
	$(JCHSYS)/jchsys.cmxa \
	$(JCHPOLY)/jchpoly.cmxa \
	$(JCHCOST)/jchcost.cmxa \

CAMLPREBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	$(EXTLIB)/extlib.cmxa \
	$(ZARITHLIB)/zarith.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(JCHLIB)/jchlib.cmxa \
	$(JCHPRE)/jchpre.cmxa \

OCAMLDEP := ocamldep

all: chj_initialize chj_class_invariants chj_translate_class

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

chj_initialize: cmi/jCHVersion.cmi cmx/jCHVersion.cmx cmi/jCHXInitializeAnalysis.cmi cmx/jCHXInitializeAnalysis.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_initialize cmx/jCHVersion.cmx cmx/jCHXInitializeAnalysis.cmx

chj_class_invariants: cmi/jCHXClassInvariants.cmi cmx/jCHXClassInvariants.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXClassInvariants.cmx

chj_translate_class: cmi/jCHXTranslateClass.cmi cmx/jCHXTranslateClass.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLPREBUILD) -o $@ cmx/jCHXTranslateClass.cmx

chj_template: cmi/jCHXTemplate.cmi cmx/jCHXTemplate.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXTemplate.cmx


cmi/%.cmi: %.mli make_dirs
	$(CAMLC) $(INCLUDES) -o $@ -c $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) $(INCLUDES) -o $@ -c $<

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
	rm -f chj_initialize
	rm -f chj_template
	rm -f chj_translate_class
	rm -f chj_class_invariants
	rm -f .depend

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
