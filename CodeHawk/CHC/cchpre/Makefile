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

OCAMLDEP := ocamldep

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
	cCHCandidateOutputParameter \
	cCHOutputParameterAnalysis \
	cCHAnalysisDigest \
	cCHProofScaffolding \
	cCHPreFileIO \
	cCHPrimaryProofObligations \
	cCHCheckValid \
	cCHCreatePrimaryProofObligations \
	cCHCreateOutputParameterPOs \

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
	cCHCandidateOutputParameter \
	cCHOutputParameterAnalysis \
	cCHAnalysisDigest \
	cCHProofScaffolding \
	cCHPreFileIO \
	cCHPrimaryProofObligations \
	cCHCheckValid \
	cCHCreatePrimaryProofObligations \
	cCHCreateOutputParameterPOs \


OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: cchpre.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cchpre.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CCHLIB)/cchlib.cmxa
	$(CAMLLINK) -a -o $@ $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
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

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
