CODEHAWK = ../../../..
CH = $(CODEHAWK)/CH
CHT = $(CODEHAWK)/CHT

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
TESTLIB = $(CHT)/tchlib
XTESTLIB = $(CHT)/CH_tests/xprlib_tests/txprlib

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(XTESTLIB)/cmi \

CAMLLINK := ocamlopt str.cmxa unix.cmxa \
	-I $(ZARITHLIB) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extlib.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(XTESTLIB)/txprlib.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs xsimplifyTest xconsequenceTest

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

xsimplifyTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(TESTLIB)/tchlib.cmxa cmi/xsimplifyTest.cmi cmx/xsimplifyTest.cmx
	$(CAMLLINK) -o xsimplifyTest $(OBJECTS) cmx/xsimplifyTest.cmx

xconsequenceTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(TESTLIB)/tchlib.cmxa cmi/xconsequenceTest.cmi cmx/xconsequenceTest.cmx
	$(CAMLLINK) -o xconsequenceTest $(OBJECTS) cmx/xconsequenceTest.cmx

run: xsimplifyTest xconsequenceTest
	./xsimplifyTest
	./xconsequenceTest

xprlib: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(XPRLIB)/xpr.cmxa $(TESTLIB)/tchlib.cmxa $(XTESTLIB)/txprlib.cmxa
	$(CAMLLINK) -a -o txprlib.cmxa $(OBJECTS)

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
	rm -f xsimplifyTest
	rm -r xconsequenceTest
	rm -rf doc
