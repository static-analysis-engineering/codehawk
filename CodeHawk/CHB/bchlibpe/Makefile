CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib

CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \

CAMLLINK := ocamlopt
OCAMLDEP := ocamldep

MLIS := \
	bCHLibPETypes \
	bCHPEStringTable \
	bCHPESymbolTable \
	bCHPEExportDirectory \
	bCHPEAssemblyTableLayout \
	bCHPEImportDirectory \
	bCHPELoadConfigurationStructure \
	bCHPEResourceDirectory \
	bCHPESectionHeader \
	bCHPESection \
	bCHPESections \
	bCHPEExnHandler \
	bCHPEHeader \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHPEStringTable \
	bCHPESymbolTable \
	bCHPEExportDirectory \
	bCHPEAssemblyTableLayout \
	bCHPEImportDirectory \
	bCHPELoadConfigurationStructure \
	bCHPEResourceDirectory \
	bCHPESectionHeader \
	bCHPESection \
	bCHPESections \
	bCHPEExnHandler \
	bCHPEHeader \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: bchlibpe.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibpe.cmxa: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa
	$(CAMLLINK) -a -o $@ $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
	rm -f cmx/*.cmx
	rm -f cmi/*.cmi
	rm -f cmx/*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~ 
	rm -rf bchlibpe
	rm -rf doc

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
