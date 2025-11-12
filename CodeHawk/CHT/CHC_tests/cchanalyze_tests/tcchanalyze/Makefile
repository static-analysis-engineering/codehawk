CODEHAWK = ../../../..
CH = $(CODEHAWK)/CH
CHT = $(CODEHAWK)/CHT

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
CCHLIB = $(CODEHAWK)/CHC/cchlib
CCHPRE = $(CODEHAWK)/CHC/cchpre
CCHANALYZE = $(CODEHAWK)/CHC/cchanalyze
TESTLIB = $(CHT)/tchlib

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \
	-I $(CCHANALYZE)/cmi \
	-I $(TESTLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	tCHCchanalyzeAssertion \
	tCHCchanalyzeUtils \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	tCHCchanalyzeAssertion \
	tCHCchanalyzeUtils \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs tcchanalyze

doc:

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

tcchanalyze: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(XPRLIB)/xpr.cmxa $(CCHLIB)/cchlib.cmxa $(CCHPRE)/cchpre.cmxa $(CCHANALYZE)/cchanalyze.cmxa $(TESTLIB)/tchlib.cmxa
	$(CAMLLINK) -a -o tcchanalyze.cmxa $(OBJECTS)

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
	rm -rf doc
