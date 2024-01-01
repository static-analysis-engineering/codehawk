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
	-I $(BCHCIL)/cmi \
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
	$(CIL)/goblintCil.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(BCHCIL)/bchcil.cmxa \
	$(TESTLIB)/tchlib.cmxa \
	$(BCHLIBTESTLIB)/tbchlib.cmxa \

MLIS := \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bCHDoublewordTest bCHImmediateTest bCHLocationTest bCHStreamWrapperTest bCHFunctionInterfaceTest bCHARMFunctionInterfaceTest

doc: 

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bCHDoublewordTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHDoublewordTest.cmi cmx/bCHDoublewordTest.cmx
	$(CAMLLINK) -o bCHDoublewordTest $(OBJECTS) cmx/bCHDoublewordTest.cmx

bCHImmediateTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(BCHCIL)/bchcil.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHImmediateTest.cmi cmx/bCHImmediateTest.cmx
	$(CAMLLINK) -o bCHImmediateTest $(OBJECTS) cmx/bCHImmediateTest.cmx

bCHLocationTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHLocationTest.cmi cmx/bCHLocationTest.cmx
	$(CAMLLINK) -o bCHLocationTest $(OBJECTS) cmx/bCHLocationTest.cmx

bCHStreamWrapperTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHStreamWrapperTest.cmi cmx/bCHStreamWrapperTest.cmx
	$(CAMLLINK) -o bCHStreamWrapperTest $(OBJECTS) cmx/bCHStreamWrapperTest.cmx

bCHFunctionInterfaceTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(CHUTIL)/chutil.cmxa $(BCHCIL)/bchcil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHFunctionInterfaceTest.cmi cmx/bCHFunctionInterfaceTest.cmx
	$(CAMLLINK) -o bCHFunctionInterfaceTest $(OBJECTS) cmx/bCHFunctionInterfaceTest.cmx

bCHARMFunctionInterfaceTest: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(CHUTIL)/chutil.cmxa $(BCHCIL)/bchcil.cmxa $(ZIPLIB)/zip.cmxa $(TESTLIB)/tchlib.cmxa $(BCHLIBTESTLIB)/tbchlib.cmxa cmi/bCHARMFunctionInterfaceTest.cmi cmx/bCHARMFunctionInterfaceTest.cmx
	$(CAMLLINK) -o bCHARMFunctionInterfaceTest $(OBJECTS) cmx/bCHARMFunctionInterfaceTest.cmx

run: bCHDoublewordTest bCHImmediateTest bCHLocationTest bCHStreamWrapperTest
	./bCHDoublewordTest
	./bCHImmediateTest
	./bCHLocationTest
	./bCHStreamWrapperTest
	./bCHFunctionInterfaceTest
	./bCHARMFunctionInterfaceTest

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
	rm -f bCHDoublewordTest
	rm -f bCHImmediateTest
	rm -f bCHLocationTest
	rm -f bCHFunctionInterfaceTest
	rm -rf doc
