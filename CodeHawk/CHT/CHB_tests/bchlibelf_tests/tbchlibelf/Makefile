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
ELFLIB = $(CODEHAWK)/CHB/bchlibelf
TESTLIB = $(CHT)/tchlib

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(ELFLIB)/cmi \
	-I $(TESTLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	tCHBchlibelfAssertion \


CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	tCHBchlibelfAssertion \


OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs tbchlibelf

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

tbchlibelf: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(XPRLIB)/xpr.cmxa $(BCHLIB)/bchlib.cmxa $(ELFLIB)/bchlibelf.cmxa $(TESTLIB)/tchlib.cmxa
	$(CAMLLINK) -a -o tbchlibelf.cmxa $(OBJECTS)

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
