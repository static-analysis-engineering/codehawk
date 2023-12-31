ZARITHLIB = $(shell ocamlfind query zarith)

CAMLC := ocamlopt -I $(ZARITHLIB) -I str -I +unix -I cmi -I cmx 
CAMLLINK := ocamlopt
CAMLDOC := ocamldoc
OCAMLDEP := ocamldep

MLIS := \
	cHPretty \
	cHCommon \
	cHInternalization \
	cHNumerical \
	cHCollections \
	cHStack \
	cHUnionFind \
	cHLanguage \
	cHUtils \
	cHSymbolicTypeRefinement \
	cHStaticChecker \
	cHStaticInliner \
	cHOnlineCodeSet \
	cHBounds \
	cHIntervals \
	cHPEPRTypes \
	cHIndexedHTable \
	cHPEPRDictionary \
	cHPEPRBounds \
	cHTIntervals \
	cHPEPRange \
	cHStridedIntervals \
	cHValueSets \
	cHConstants \
	cHSymbolicSets \
	cHNumericalConstraints \
	cHExternalValues \
	cHNonRelationalDomainValues \
	cHPolyhedraGlobalData \
	cHVector \
	cHBitstring \
	cHSaturationMatrix \
	cHMatrix \
	cHChernikova \
	cHPolyhedra \
	cHDomainObserver \
	cHDomain \
	cHCommunications \
	cHSigmaCombinator \
	cHNonRelationalTable \
	cHNonRelationalDatabase \
	cHAtlas \
	cHAtlasTable \
	cHLocalIterationSigmaCombinator \
	cHGaussSeidelSigmaCombinator \
	cHStridedGaussSeidelSigmaCombinator \
	cHSCC \
	cHIterator \
	cHNonRelationalDomainBase \
	cHNonRelationalDomainNoArrays \
	cHNonRelationalDomainExtensiveArrays \
	cHNumericalConstantsDomainNoArrays \
	cHSymbolicConstantsDomainNoArrays \
	cHIntervalsDomainNoArrays \
	cHStridedIntervalsDomainNoArrays \
	cHPEPRDomainNoArrays \
	cHSymbolicSetsDomainNoArrays \
	cHStateSetsDomainNoArrays \
	cHTimedSymbolicSetsDomainNoArrays \
	cHConstantPropagationNoArrays \
	cHNumericalConstantsDomainExtensiveArrays \
	cHSymbolicConstantsDomainExtensiveArrays \
	cHIntervalsDomainExtensiveArrays \
	cHStridedIntervalsDomainExtensiveArrays \
	cHValueSetsDomainNoArrays \
	cHSymbolicSetsDomainExtensiveArrays \
	cHLinearEqualitiesDomainNoArrays \
	cHPolyhedraDomainNoArrays \
	cHBooleanConstantsDomainNoArrays

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cHPretty \
	cHCommon \
	cHInternalization \
	cHNumerical \
	cHCollections \
	cHStack \
	cHUnionFind \
	cHLanguage \
	cHUtils \
	cHSymbolicTypeRefinement \
	cHStaticChecker \
	cHStaticInliner \
	cHOnlineCodeSet \
	cHBounds \
	cHIntervals \
	cHIndexedHTable \
	cHPEPRDictionary \
	cHPEPRBounds \
	cHPEPRange \
	cHTIntervals \
	cHStridedIntervals \
	cHValueSets \
	cHConstants \
	cHSymbolicSets \
	cHNumericalConstraints \
	cHExternalValues \
	cHNonRelationalDomainValues \
	cHPolyhedraGlobalData \
	cHVector \
	cHBitstring \
	cHSaturationMatrix \
	cHMatrix \
	cHChernikova \
	cHPolyhedra \
	cHDomainObserver \
	cHDomain \
	cHCommunications \
	cHSigmaCombinator \
	cHNonRelationalTable \
	cHNonRelationalDatabase \
	cHAtlas \
	cHAtlasTable \
	cHLocalIterationSigmaCombinator \
	cHGaussSeidelSigmaCombinator \
	cHStridedGaussSeidelSigmaCombinator \
	cHSCC \
	cHIterator \
	cHNonRelationalDomainBase \
	cHNonRelationalDomainNoArrays \
	cHNonRelationalDomainExtensiveArrays \
	cHNumericalConstantsDomainNoArrays \
	cHSymbolicConstantsDomainNoArrays \
	cHIntervalsDomainNoArrays \
	cHStridedIntervalsDomainNoArrays \
	cHPEPRDomainNoArrays \
	cHSymbolicSetsDomainNoArrays \
	cHStateSetsDomainNoArrays \
	cHTimedSymbolicSetsDomainNoArrays \
	cHConstantPropagationNoArrays \
	cHNumericalConstantsDomainExtensiveArrays \
	cHSymbolicConstantsDomainExtensiveArrays \
	cHIntervalsDomainExtensiveArrays \
	cHStridedIntervalsDomainExtensiveArrays \
	cHValueSetsDomainNoArrays \
	cHSymbolicSetsDomainExtensiveArrays \
	cHLinearEqualitiesDomainNoArrays \
	cHPolyhedraDomainNoArrays \
	cHBooleanConstantsDomainNoArrays 

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: chlib.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cmi/%.cmi: %.mli make_dirs 
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs 
	$(CAMLC) -o $@ -c $<

chlib.cmxa: $(CMIS) $(OBJECTS)
	$(CAMLLINK) -a -o $@ $(OBJECTS)

doc: $(OBJECTS)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . $(OBJECTS)

clean:
	rm -f .depend
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -rf doc

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
