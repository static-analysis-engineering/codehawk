CODEHAWK := ../..
JCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre
JCHFEA = $(JCH)/jchfeatures
JCHSYS = $(JCH)/jchsys
JCHPOLY= $(JCH)/jchpoly

DEP_INCLUDES := -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHSYS)/cmi \
	-I $(JCHPOLY)/cmi \

CAMLCPOLY := ocamlopt $(DEP_INCLUDES) -I cmi -I cmx 

CAMLC := ocamlopt -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHFEA)/cmi \

CAMLLINK := ocamlopt -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB) \
	-I $(CHUTIL) \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHFEA)/cmi \

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
	$(JCHFEA)/jchfeatures.cmxa \

CAMLBUILDPOLY := ocamlopt str.cmxa unix.cmxa \
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

OCAMLDEP := ocamldep


CAMLDOC := ocamldoc
JAVAC = javac

all: chj_features chj_efeatures chj_patterns chj_invariants

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi


# program to generate key-value pairs (MUSE)
chj_features: cmi/jCHXExtractFeatures.cmi cmx/jCHXExtractFeatures.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHFEA)/jchfeatures.cmxa
	$(CAMLBUILD) -o chj_features cmx/jCHXExtractFeatures.cmx

chj_efeatures: cmi/jCHXExtractExprFeatures.cmi cmx/jCHXExtractExprFeatures.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHFEA)/jchfeatures.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXExtractExprFeatures.cmx

chj_invariants: cmi/jCHXClassPoly.cmi cmx/jCHXClassPoly.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILDPOLY) -o $@ cmx/jCHXClassPoly.cmx

chj_patterns: cmi/jCHXCollectPatterns.cmi cmx/jCHXCollectPatterns.cmx  $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o $@ cmx/jCHXCollectPatterns.cmx

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c $<

cmx/jCHXClassPoly.cmx: jCHXClassPoly.ml make_dirs
	$(CAMLCPOLY)  -o $@ -c $<

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
	rm -f chj_features
	rm -f chj_efeatures
	rm -f chj_patterns
	rm -f chj_invariants

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean cleanjava
