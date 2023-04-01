CODEHAWK = ../../../..
CH = $(CODEHAWK)/CH
CHT = $(CODEHAWK)/CHT

ZARITHLIB = $(shell ocamlfind query zarith)
CIL = $(shell ocamlfind query goblint-cil)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHCIL = $(CODEHAWK)/CHB/bchcil
BCHLIB = $(CODEHAWK)/CHB/bchlib
PELIB = $(CODEHAWK)/CHB/bchlibpe
ELFLIB = $(CODEHAWK)/CHB/bchlibelf
TESTLIB = $(CHT)/tchlib
BCHLIBTESTLIB = $(CHT)/CHB_tests/bchlib_tests/tbchlib
BCHELFTESTLIB = $(CHT)/CHB_tests/bchlibelf_tests/tbchlibelf

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(PELIB)/cmi \
	-I $(ELFLIB)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(BCHLIBTESTLIB)/cmi \
	-I $(BCHELFTESTLIB)/cmi \


CAMLLINK := ocamlopt str.cmxa unix.cmxa \
	-I $(ZARITHLIB) \
	-I $(ZIPLIB) \
	-I $(CIL) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extlib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(CIL)/goblintCil.cmxa \
	$(BCHCIL)/bchcil.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(PELIB)/bchlibpe.cmxa \
	$(ELFLIB)/bchlibelf.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(BCHLIBTESTLIB)/tbchlib.cmxa \
	$(BCHELFTESTLIB)/tbchlibelf.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs \
	bCHELFDebugAbbrevSectionTest \
	bCHELFDebugLocSectionTest \

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bCHELFDebugAbbrevSectionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHELFTESTLIB)/tbchlibelf.cmxa cmi/bCHELFDebugAbbrevSectionTest.cmi cmx/bCHELFDebugAbbrevSectionTest.cmx
	$(CAMLLINK) -o bCHELFDebugAbbrevSectionTest $(OBJECTS) cmx/bCHELFDebugAbbrevSectionTest.cmx

bCHELFDebugLocSectionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHELFTESTLIB)/tbchlibelf.cmxa cmi/bCHELFDebugLocSectionTest.cmi cmx/bCHELFDebugLocSectionTest.cmx
	$(CAMLLINK) -o bCHELFDebugLocSectionTest $(OBJECTS) cmx/bCHELFDebugLocSectionTest.cmx

bCHDwarfTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHELFTESTLIB)/tbchlibelf.cmxa cmi/bCHDwarfTest.cmi cmx/bCHDwarfTest.cmx
	$(CAMLLINK) -o bCHDwarfTest $(OBJECTS) cmx/bCHDwarfTest.cmx

run: bCHELFDebugAbbrevSectionTest bCHDwarfTest
	./bCHELFDebugAbbrevSectionTest
	./bCHELFDebugLocSectionTest
	./bCHDwarfTest

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
	rm -f bCHELFDebugAbbrevSectionTest
	rm -f bCHELFDebugLocSectionTest
	rm -f bCHDwarfTest
	rm -rf doc
