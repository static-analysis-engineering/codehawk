CODEHAWK = ../..

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	tCHTestApi \
	tCHUtils \
	tCHAssertion \
	tCHGenerator \
	tCHReducer \
	tCHSpecification \
	tCHTest \
	tCHTestSuite

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	tCHUtils \
	tCHAssertion \
	tCHGenerator \
	tCHReducer \
	tCHSpecification \
	tCHTest \
	tCHTestSuite

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs tchlib

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

tchlib: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa
	$(CAMLLINK) -a -o tchlib.cmxa $(OBJECTS)

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
	rm -f tchlib.cmxa
	rm -rf doc
