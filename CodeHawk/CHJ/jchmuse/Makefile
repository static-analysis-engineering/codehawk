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


CAMLDOC := ocamldoc
JAVAC = javac

all: make_dirs features exprfeatures pattern poly

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi


# program to generate key-value pairs (MUSE)
features: cmi/jCHXExtractFeatures.cmi cmx/jCHXExtractFeatures.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHFEA)/jchfeatures.cmxa
	$(CAMLBUILD) -o chj_features cmx/jCHXExtractFeatures.cmx

exprfeatures: cmi/jCHXExtractExprFeatures.cmi cmx/jCHXExtractExprFeatures.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHFEA)/jchfeatures.cmxa
	$(CAMLBUILD) -o chj_efeatures cmx/jCHXExtractExprFeatures.cmx

poly: cmi/jCHXClassPoly.cmi cmx/jCHXClassPoly.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILDPOLY) -o chj_invariants cmx/jCHXClassPoly.cmx

pattern: cmi/jCHXCollectPatterns.cmi cmx/jCHXCollectPatterns.cmx  $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLBUILD) -o chj_patterns cmx/jCHXCollectPatterns.cmx

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c $<

cmx/jCHXClassPoly.cmx: jCHXClassPoly.ml
	$(CAMLCPOLY)  -o $@ -c $<

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
	rm -f chj_features
	rm -f chj_efeatures
	rm -f chj_patterns
	rm -f chj_invariants

