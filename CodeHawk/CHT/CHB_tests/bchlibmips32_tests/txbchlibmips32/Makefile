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
MIPSLIB = $(CODEHAWK)/CHB/bchlibmips32
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
	-I $(MIPSLIB)/cmi \
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
	$(MIPSLIB)/bchlibmips32.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(BCHLIBTESTLIB)/tbchlib.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs \
	bCHDisassembleMIPSInstructionTest \
	bCHAssembleMIPSInstructionTest \

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bCHDisassembleMIPSInstructionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDisassembleMIPSInstructionTest.cmi cmx/bCHDisassembleMIPSInstructionTest.cmx
	$(CAMLLINK) -o bCHDisassembleMIPSInstructionTest $(OBJECTS) cmx/bCHDisassembleMIPSInstructionTest.cmx

bCHAssembleMIPSInstructionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHAssembleMIPSInstructionTest.cmi cmx/bCHAssembleMIPSInstructionTest.cmx
	$(CAMLLINK) -o bCHAssembleMIPSInstructionTest $(OBJECTS) cmx/bCHAssembleMIPSInstructionTest.cmx

run: bCHDisassembleMIPSInstructionTest bCHAssembleMIPSInstructionTest
	./bCHDisassembleMIPSInstructionTest
	./bCHAssembleMIPSInstructionTest

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
	rm -f bCHDisassembleMIPSInstructionTest
	rm -f bCHAssembleMIPSInstructionTest
	rm -rf doc
