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
ANALYZE = $(CODEHAWK)/CHB/bchanalyze
TESTLIB = $(CHT)/tchlib
BCHLIBTESTLIB = $(CHT)/CHB_tests/bchlib_tests/tbchlib
BCHARMTESTLIB = $(CHT)/CHB_tests/bchlibarm32_tests/tbchlibarm32

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
	-I $(ANALYZE)/cmi \
	-I $(TESTLIB)/cmi \
	-I $(BCHLIBTESTLIB)/cmi \
	-I $(BCHARMTESTLIB)/cmi \


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
	$(PELIB)/bchlibpe.cmxa \
	$(ELFLIB)/bchlibelf.cmxa \
	$(X86LIB)/bchlibx86.cmxa \
	$(ARMLIB)/bchlibarm32.cmxa \
	$(MIPSLIB)/bchlibmips32.cmxa \
	$(ANALYZE)/bchanalyze.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(BCHLIBTESTLIB)/tbchlib.cmxa \
	$(BCHARMTESTLIB)/tbchlibarm32.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs \
	bCHARMDictionaryTest \
	bCHDisassembleARMInstructionTest \
	bCHDisassembleThumbInstructionTest \
	bCHThumbITSequenceTest \
	bCHARMJumptableTest \
	bCHARMAssemblyFunctionTest \
	bCHTranslateARMToCHIFTest \
	bCHFnARMDictionaryTest \

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bCHARMDictionaryTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHARMDictionaryTest.cmi cmx/bCHARMDictionaryTest.cmx
	$(CAMLLINK) -o bCHARMDictionaryTest $(OBJECTS) cmx/bCHARMDictionaryTest.cmx

bCHDisassembleARMInstructionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDisassembleARMInstructionTest.cmi cmx/bCHDisassembleARMInstructionTest.cmx
	$(CAMLLINK) -o bCHDisassembleARMInstructionTest $(OBJECTS) cmx/bCHDisassembleARMInstructionTest.cmx

bCHDisassembleThumbInstructionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDisassembleThumbInstructionTest.cmi cmx/bCHDisassembleThumbInstructionTest.cmx
	$(CAMLLINK) -o bCHDisassembleThumbInstructionTest $(OBJECTS) cmx/bCHDisassembleThumbInstructionTest.cmx

bCHThumbITSequenceTest:  $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHARMTESTLIB)/tbchlibarm32.cmxa cmi/bCHThumbITSequenceTest.cmi cmx/bCHThumbITSequenceTest.cmx
	$(CAMLLINK) -o bCHThumbITSequenceTest $(OBJECTS) cmx/bCHThumbITSequenceTest.cmx

bCHARMJumptableTest:  $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHARMTESTLIB)/tbchlibarm32.cmxa cmi/bCHARMJumptableTest.cmi cmx/bCHARMJumptableTest.cmx
	$(CAMLLINK) -o bCHARMJumptableTest $(OBJECTS) cmx/bCHARMJumptableTest.cmx

bCHTranslateARMToCHIFTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHARMTESTLIB)/tbchlibarm32.cmxa cmi/bCHTranslateARMToCHIFTest.cmi cmx/bCHTranslateARMToCHIFTest.cmx
	$(CAMLLINK) -o bCHTranslateARMToCHIFTest $(OBJECTS) cmx/bCHTranslateARMToCHIFTest.cmx

bCHARMAssemblyFunctionTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHARMTESTLIB)/tbchlibarm32.cmxa cmi/bCHARMAssemblyFunctionTest.cmi cmx/bCHARMAssemblyFunctionTest.cmx
	$(CAMLLINK) -o bCHARMAssemblyFunctionTest $(OBJECTS) cmx/bCHARMAssemblyFunctionTest.cmx

bCHFnARMDictionaryTest:  $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa $(BCHARMTESTLIB)/tbchlibarm32.cmxa cmi/bCHFnARMDictionaryTest.cmi cmx/bCHFnARMDictionaryTest.cmx
	$(CAMLLINK) -o bCHFnARMDictionaryTest $(OBJECTS) cmx/bCHFnARMDictionaryTest.cmx


run: bCHDisassembleARMInstructionTest bCHDisassembleThumbInstructionTest bCHThumbITSequenceTest bCHARMJumptableTest bCHARMAssemblyFunctionTest bCHTranslateARMToCHIFTest bCHFnARMDictionaryTest
	./bCHDisassembleARMInstructionTest
	./bCHDisassembleThumbInstructionTest
	./bCHThumbITSequenceTest
	./bCHARMJumptableTest
	./bCHARMAssemblyFunctionTest
	./bCHTranslateARMToCHIFTest
	./bCHFnARMDictionaryTest

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
	rm -f bCHDisassembleThumbInstructionTest
	rm -f bCHDisassembleARMInstructionTest
	rm -f bCHThumbITSequenceTest
	rm -f bCHARMJumptableTest
	rm -f bCHTranslateARMToCHIFTest
	rm -f bCHARMAssemblyFunctionTest
	rm -f bCHFnARMDictionaryTest
	rm -rf doc
