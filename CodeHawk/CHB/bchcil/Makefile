CODEHAWK = ../..
CIL = $(shell ocamlfind query goblint-cil)
ZARITHLIB = $(shell ocamlfind query zarith)
CHB = $(CODEHAWK)/CHB

CHLIB = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
BCHLIB = $(CHB)/bchlib

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \

CAMLLINK := ocamlopt \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extlib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CIL)/goblintCil.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(BCHLIB)/bchlib.cmxa \

OCAMLDEP := ocamldep

CAMLLINKL := ocamlopt

MLIS := \
	bCHCilToCBasic \
	bCHParseCilFile \
	bCHXParseFile \


CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHCilToCBasic \
	bCHParseCilFile \
	bCHXParseFile \


OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: bchcil.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchcil.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(EXTLIB) $(BCHLIB)/bchlib.cmxa
	$(CAMLLINKL) -a -o $@ $(OBJECTS)

parse: 	$(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(EXTLIB) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa
	$(CAMLLINK) -I $(ZARITHLIB) -o parseFile str.cmxa unix.cmxa $(ZARITHLIB)/zarith.cmxa $(CIL)/goblintCil.cmxa $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(OBJECTS)


cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -f bchcil.cmxa

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
