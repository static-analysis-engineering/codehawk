CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib

CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \

CAMLLINK := ocamlopt \

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

all: make_dirs bchlibpe

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibpe: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa
	$(CAMLLINK) -a -o bchlibpe.cmxa $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml $(CMIS)
	$(CAMLC) -o $@ -c $<

clean:
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
