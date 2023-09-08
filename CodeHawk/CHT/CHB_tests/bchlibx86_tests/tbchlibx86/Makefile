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
X86LIB = $(CODEHAWK)/CHB/bchlibx86
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
	-I $(X86LIB)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(TBCHLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	tCHBchlibx86Assertion \
	tCHBchlibx86Utils \
	tCHBchlibx86Generator \


CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	tCHBchlibx86Assertion \
	tCHBchlibx86Generator \
	tCHBchlibx86Utils \


OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs tbchlibx86

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

tbchlibx86: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(XPRLIB)/xpr.cmxa $(BCHLIB)/bchlib.cmxa $(X86LIB)/bchlibx86.cmxa $(TESTLIB)/tchlib.cmxa $(TBCHLIB)/tbchlib.cmxa
	$(CAMLLINK) -a -o tbchlibx86.cmxa $(OBJECTS)

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
	rm -f tbchlibx86.cmxa
	rm -rf doc
