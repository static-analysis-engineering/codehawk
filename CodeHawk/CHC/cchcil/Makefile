CODEHAWK = ../..
CIL = $(shell ocamlfind query goblint-cil)
ZARITHLIB = $(shell ocamlfind query zarith)
EXTLIB = $(shell ocamlfind query extlib)

CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \

CAMLLINK := ocamlopt  \
	-I $(ZARITHLIB) \
	$(EXTLIB)/extlib.cmxa \
	$(ZARITHLIB)/zarith.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \

CAMLLINKLIB := ocamlopt
OCAMLDEP = ocamldep

MLIS := \
	cHCilFileUtil \
	cHCilTypes \
	cHCilSumTypeSerializer \
	cHCilDictionary \
	cHCilDeclarations \
	cHCilFunDeclarations \
	cHCilWriteXml \
	cCHXParseFile \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cHCilFileUtil \
	cHCilSumTypeSerializer \
	cHCilDictionary \
	cHCilDeclarations \
	cHCilFunDeclarations \
	cHCilWriteXml \
	cCHXParseFile \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: parseFile cchcil.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

parseFile: 	$(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(EXTLIB) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa
	$(CAMLLINK) -I $(ZARITHLIB) -o parseFile str.cmxa unix.cmxa $(ZARITHLIB)/zarith.cmxa $(CIL)/goblintCil.cmxa $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(OBJECTS)

cchcil.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(EXTLIB) $(CHUTIL)/chutil.cmxa
	$(CAMLLINKLIB) -a -o $@ $(OBJECTS)


cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c $<

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
	rm -f parseFile

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
