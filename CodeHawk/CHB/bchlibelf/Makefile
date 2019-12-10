CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
PELIB  = $(CHB)/bchlibpe
CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(PELIB)/cmi \

CAMLLINK := ocamlopt -I str.cmxa -I unix.cmxa \

CAMLBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	$(CHLIB)/chlib.cmxa \
	$(EXTLIB)/extLib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(PELIB)/bchlibpe.cmxa

MLIS := \
	bCHELFTypes \
	bCHELFPrettyStrings \
	bCHELFUtil \
	bCHELFDictionary \
	bCHELFSection \
	bCHELFStringTable \
	bCHELFSymbolTable \
	bCHELFDynamicTable \
	bCHELFRelocationTable \
	bCHELFProgramHeader \
	bCHELFSectionHeader \
	bCHELFHeader \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHELFPrettyStrings \
	bCHELFUtil \
	bCHELFDictionary \
	bCHELFSection \
	bCHELFStringTable \
	bCHELFSymbolTable \
	bCHELFRelocationTable \
	bCHELFDynamicTable \
	bCHELFProgramHeader \
	bCHELFSectionHeader \
	bCHELFHeader \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchlibelf

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

mtest: $(OBJECTS) cmx/test.cmx $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(X86LIB)/bchlibx86.cmxa
	$(CAMLBUILD) -o mtest $(OBJECTS) cmx/test.cmx

bchlibelf: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(PELIB)/bchlibpe.cmxa
	$(CAMLLINK) -a -o bchlibelf.cmxa $(OBJECTS)

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
	rm -rf bchlibelf
	rm -rf doc
	rm -f mtest
