CODEHAWK = ../../../..
CH = $(CODEHAWK)/CH
CHT = $(CODEHAWK)/CHT

ZARITHLIB = $(shell ocamlfind query zarith)
CIL = $(shell ocamlfind query goblint-cil)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib

CCHLIB = $(CODEHAWK)/CHC/cchlib
CCHPRE = $(CODEHAWK)/CHC/cchpre
CCHANALYZE = $(CODEHAWK)/CHC/cchanalyze

TESTLIB = $(CHT)/tchlib
CCHANALYZETESTLIB = $(CHT)/CHC_tests/cchanalyze_tests/tcchanalyze

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \
	-I $(CCHANALYZE)/cmi \
	-I $(CCHANALYZETESTLIB)/cmi \

CAMLLINK := ocamlopt str.cmxa unix.cmxa \
	-I $(ZARITHLIB) \
	-I $(ZIPLIB) \
	-I $(CIL) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extlib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(CCHLIB)/cchlib.cmxa \
	$(CCHPRE)/cchpre.cmxa \
	$(CCHANALYZE)/cchanalyze.cmxa \
	$(CCHANALYZETESTLIB)/tcchanalyze.cmxa


MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs cCHPOCheckInitializedTest cCHPOCheckLocallyInitializedTest cCHPOCheckOutputParameterInitializedTest

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cCHPOCheckInitializedTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa $(CCHANALYZE)/cchanalyze.cmxa cmi/cCHPOCheckInitializedTest.cmi cmx/cCHPOCheckInitializedTest.cmx
	$(CAMLLINK) -o cCHPOCheckInitializedTest $(OBJECTS) cmx/cCHPOCheckInitializedTest.cmx

cCHPOCheckLocallyInitializedTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa $(CCHANALYZE)/cchanalyze.cmxa cmi/cCHPOCheckLocallyInitializedTest.cmi cmx/cCHPOCheckLocallyInitializedTest.cmx
	$(CAMLLINK) -o cCHPOCheckLocallyInitializedTest $(OBJECTS) cmx/cCHPOCheckLocallyInitializedTest.cmx

cCHPOCheckOutputParameterInitializedTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa $(CCHANALYZE)/cchanalyze.cmxa cmi/cCHPOCheckOutputParameterInitializedTest.cmi cmx/cCHPOCheckOutputParameterInitializedTest.cmx
	$(CAMLLINK) -o cCHPOCheckOutputParameterInitializedTest $(OBJECTS) cmx/cCHPOCheckOutputParameterInitializedTest.cmx

run: cCHPOCheckInitializedTest cCHPOCheckLocallyInitializedTest cCHPOCheckOutputParameterInitializedTest
	./cCHPOCheckInitializedTest
	./cCHPOCheckLocallyInitializedTest
	./cCHPOCheckOutputParameterInitializedTest

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml $(CMIS)
	$(CAMLC) -o $@ -c $<

doc: $(CMIS) $(OBJECTS)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -I cmi -I cmx -warn-error -d doc -html -I $(CHUTIL) $(MLIS:%=%.mli)

clean:
	rm -f cmx/*.cm*
	rm -f cmi/*.cmi
	rm -f cmx/*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~
	rm -f cCHPOCheckInitializedTest
	rm -f cCHPOCheckLocallyInitializedTest
	rm -f cCHPOCheckOutputParameterInitialized
