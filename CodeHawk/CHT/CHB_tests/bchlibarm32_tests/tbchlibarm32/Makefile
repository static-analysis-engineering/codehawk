CODEHAWK = ../../../..
CH = $(CODEHAWK)/CH
CHT = $(CODEHAWK)/CHT

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CODEHAWK)/CHB/bchlib
ARMLIB = $(CODEHAWK)/CHB/bchlibarm32
TESTLIB = $(CHT)/tchlib
TBCHLIB = $(CHT)/CHB_tests/bchlib_tests/tbchlib

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(ARMLIB)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(TBCHLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	tCHBchlibarm32Assertion \
	tCHBchlibarm32Utils \
	tCHBchlibarm32Generator \


CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	tCHBchlibarm32Assertion \
	tCHBchlibarm32Generator \
	tCHBchlibarm32Utils \


OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs tbchlibarm32

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

tbchlibarm32: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(XPRLIB)/xpr.cmxa $(BCHLIB)/bchlib.cmxa $(ARMLIB)/bchlibarm32.cmxa $(TESTLIB)/tchlib.cmxa $(TBCHLIB)/tbchlib.cmxa
	$(CAMLLINK) -a -o tbchlibarm32.cmxa $(OBJECTS)

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
	rm -f tbchlibarm32.cmxa
	rm -rf doc
