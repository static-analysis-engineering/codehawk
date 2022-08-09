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

DEP_INCLUDES := -I cmi -I cmx \
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

CAMLLINK := ocamlopt -I cmi -I cmx \
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


all: make_dirs initialize classinvariants translateclass

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

initialize: cmi/jCHVersion.cmi cmx/jCHVersion.cmx cmi/jCHXInitializeAnalysis.cmi cmx/jCHXInitializeAnalysis.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_initialize cmx/jCHVersion.cmx cmx/jCHXInitializeAnalysis.cmx

classinvariants: cmi/jCHXClassInvariants.cmi cmx/jCHXClassInvariants.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_class_invariants cmx/jCHXClassInvariants.cmx

translateclass: cmi/jCHXTranslateClass.cmi cmx/jCHXTranslateClass.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLPREBUILD) -o chj_translate_class cmx/jCHXTranslateClass.cmx

usertemplate: cmi/jCHXTemplate.cmi cmx/jCHXTemplate.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_template cmx/jCHXTemplate.cmx


cmi/%.cmi: %.mli
	$(CAMLC) $(INCLUDES) -o $@ -c $<

cmx/%.cmx: %.ml
	$(CAMLC) $(INCLUDES) -o $@ -c $<

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
	rm -f chj_initialize
	rm -f chj_template
	rm -f chj_translate_class
	rm -f chj_class_invariants
	rm -f .depend
