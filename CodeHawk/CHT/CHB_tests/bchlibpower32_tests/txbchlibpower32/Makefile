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
ELFLIB = $(CODEHAWK)/CHB/bchlibelf
PWRLIB = $(CODEHAWK)/CHB/bchlibpower32
TESTLIB = $(CHT)/tchlib
BCHLIBTESTLIB = $(CHT)/CHB_tests/bchlib_tests/tbchlib

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
	-I $(PWRLIB)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(BCHLIBTESTLIB)/cmi \

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
	$(CIL)/cil.cmxa \
	$(BCHCIL)/bchcil.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(ELFLIB)/bchlibelf.cmxa \
	$(PWRLIB)/bchlibpower32.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(BCHLIBTESTLIB)/tbchlib.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs \
	bCHDisassemblePowerInstructionTest \
	bCHDisassembleVLEInstructionTest \

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bCHDisassemblePowerInstructionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDisassemblePowerInstructionTest.cmi cmx/bCHDisassemblePowerInstructionTest.cmx
	$(CAMLLINK) -o bCHDisassemblePowerInstructionTest $(OBJECTS) cmx/bCHDisassemblePowerInstructionTest.cmx

bCHDisassembleVLEInstructionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDisassembleVLEInstructionTest.cmi cmx/bCHDisassembleVLEInstructionTest.cmx
	$(CAMLLINK) -o bCHDisassembleVLEInstructionTest $(OBJECTS) cmx/bCHDisassembleVLEInstructionTest.cmx

run: bCHDisassemblePowerInstructionTest bCHDisassembleVLEInstructionTest
	./bCHDisassemblePowerInstructionTest
	./bCHDisassembleVLEInstructionTest


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
	rm -f bCHDisassembleVLEInstructionTest
	rm -rf doc
