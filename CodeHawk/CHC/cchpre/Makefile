CODEHAWK = ../..
CCH = ..

EXTLIB = $(shell ocamlfind query extlib)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
CCHLIB = $(CCH)/cchlib

CAMLC := ocamlopt -I str -I nums -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(CCHLIB)/cmi \

CAMLLINK := ocamlopt  \
	-I $(EXTLIB) \
	-I $(CHLIB) \
	-I $(CHUTIL) \
	-I $(XPRLIB) \
	-I $(CCHLIB)/cmi \

CAMLBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(CCHLIB)/cmi \
	$(EXTLIB)/extLib.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CCHLIB)/cchlib.cmxa \

MLIS := \
	cCHPreTypes \
	cCHPreSumTypeSerializer \
	cCHVarDictionary \
	cCHInvDictionary \
	cCHMemoryBase \
	cCHMemoryRegion \
	cCHMemoryReference \
	cCHVariable \
	cCHPODictionary \
	cCHPredicateDictionary \
	cCHPOPredicate \
	cCHPOExplanations \
	cCHProofObligation \
	cCHAssignDictionary \
	cCHApiAssumption \
	cCHContractAssumption \
	cCHPostRequest \
	cCHGlobalAssumption \
	cCHDsAssumption \
	cCHGlobalAssignment \
	cCHFunctionAPI \
	cCHInvariantFact \
	cCHDataStructureInvariants \
	cCHPPO \
	cCHCallsite \
	cCHReturnsite \
	cCHSPO \
	cCHProofScaffolding \
	cCHPreFileIO \
	cCHPrimaryProofObligations \
	cCHCheckValid \
	cCHCreatePrimaryProofObligations \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cCHPreSumTypeSerializer \
	cCHVarDictionary \
	cCHInvDictionary \
	cCHMemoryBase \
	cCHMemoryRegion \
	cCHMemoryReference \
	cCHVariable \
	cCHPredicateDictionary \
	cCHPOPredicate \
	cCHPOExplanations \
	cCHPODictionary \
	cCHProofObligation \
	cCHAssignDictionary \
	cCHApiAssumption \
	cCHContractAssumption \
	cCHPostRequest \
	cCHGlobalAssumption \
	cCHDsAssumption \
	cCHGlobalAssignment \
	cCHFunctionAPI \
	cCHInvariantFact \
	cCHDataStructureInvariants \
	cCHPPO \
	cCHCallsite \
	cCHReturnsite \
	cCHSPO \
	cCHProofScaffolding \
	cCHPreFileIO \
	cCHPrimaryProofObligations \
	cCHCheckValid \
	cCHCreatePrimaryProofObligations \


OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs cchpre

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cchpre: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa
	$(CAMLLINK) -a -o cchpre.cmxa $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml
	$(CAMLC) -o $@ -c $<

clean:
	rm -f *.cmx
	rm -f *.cmi
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.d
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -f linkxml
	rm -f chlink
	rm -f call_chlink
	rm -f createprimary
	rm -f createsecondary
