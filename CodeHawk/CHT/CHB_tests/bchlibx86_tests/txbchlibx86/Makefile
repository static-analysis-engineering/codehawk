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
X86LIB = $(CODEHAWK)/CHB/bchlibx86
ARMLIB = $(CODEHAWK)/CHB/bchlibarm32
MIPSLIB = $(CODEHAWK)/CHB/bchlibmips32
PWRLIB = $(CODEHAWK)/CHB/bchlibpower32
ANALYZE = $(CODEHAWK)/CHB/bchanalyze
TESTLIB = $(CHT)/tchlib
BCHLIBTESTLIB = $(CHT)/CHB_tests/bchlib_tests/tbchlib
BCHX86TESTLIB = $(CHT)/CHB_tests/bchlibx86_tests/tbchlibx86

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
	-I $(X86LIB)/cmi \
	-I $(MIPSLIB)/cmi \
	-I $(ARMLIB)/cmi \
	-I $(PWRLIB)/cmi \
	-I $(ANALYZE)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(BCHLIBTESTLIB)/cmi \
	-I $(BCHX86TESTLIB)/cmi \


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
	$(X86LIB)/bchlibx86.cmxa \
	$(ARMLIB)/bchlibarm32.cmxa \
	$(MIPSLIB)/bchlibmips32.cmxa \
	$(PWRLIB)/bchlibpower32.cmxa \
	$(ANALYZE)/bchanalyze.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(BCHLIBTESTLIB)/tbchlib.cmxa \
	$(BCHX86TESTLIB)/tbchlibx86.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs \
	bCHDisassembleInstructionTest \
	bCHDisassembleX0Test \

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bCHDisassembleInstructionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDisassembleInstructionTest.cmi cmx/bCHDisassembleInstructionTest.cmx
	$(CAMLLINK) -o bCHDisassembleInstructionTest $(OBJECTS) cmx/bCHDisassembleInstructionTest.cmx

bCHDisassembleX0Test: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDisassembleX0Test.cmi cmx/bCHDisassembleX0Test.cmx
	$(CAMLLINK) -o bCHDisassembleX0Test $(OBJECTS) cmx/bCHDisassembleX0Test.cmx


run: bCHDisassembleInstructionTest bCHDisassembleX0Test
	./bCHDisassembleInstructionTest
	./bCHDisassembleX0Test

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
	rm -f bCHDisassembleInstructionTest
	rm -f bCHDisassembleXOTest
	rm -rf doc
