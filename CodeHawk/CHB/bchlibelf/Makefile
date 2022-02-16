CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
BCHCIL = $(CHB)/bchcil
PELIB  = $(CHB)/bchlibpe
CAMLDOC := ocamldoc

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(BCHCIL)/cmi \
	-I $(PELIB)/cmi \

CAMLLINK := ocamlopt -I str.cmxa -I unix.cmxa \

CAMLBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	$(CHLIB)/chlib.cmxa \
	$(EXTLIB)/extLib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(BCHCIL)/bchcil.cmxa \
	$(PELIB)/bchlibpe.cmxa

MLIS := \
	bCHELFTypes \
	bCHELFPrettyStrings \
	bCHELFUtil \
	bCHELFDictionary \
	bCHELFSection \
	bCHELFSegment \
	bCHELFProgramSection \
	bCHELFStringTable \
	bCHELFSymbolTable \
	bCHELFDynamicTable \
	bCHELFDynamicSegment \
	bCHELFRelocationTable \
	bCHELFProgramHeader \
	bCHELFSectionHeader \
	bCHELFSectionHeaderCreator \
	bCHELFHeader \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHELFPrettyStrings \
	bCHELFUtil \
	bCHELFDictionary \
	bCHELFSection \
	bCHELFSegment \
	bCHELFProgramSection \
	bCHELFStringTable \
	bCHELFSymbolTable \
	bCHELFRelocationTable \
	bCHELFDynamicTable \
	bCHELFDynamicSegment \
	bCHELFProgramHeader \
	bCHELFSectionHeader \
	bCHELFSectionHeaderCreator \
	bCHELFHeader \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchlibelf

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

mtest: $(OBJECTS) cmx/test.cmx $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(X86LIB)/bchlibx86.cmxa
	$(CAMLBUILD) -o mtest $(OBJECTS) cmx/test.cmx

bchlibelf: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(BCHCIL)/bchcil.cmxa $(PELIB)/bchlibpe.cmxa
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
