CODEHAWK = ../..
JCH = ..

EXTLIB = $(shell ocamlfind query extlib)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \

OCAMLDEP := ocamldep

MLIS = \
	jCHFeaturesAPI \
	jCHSubgraph \
	jCHFeatureSumTypeSerializer \
	jCHFeatureDictionary \
	jCHFeatureExtraction \
	jCHMethodExprs \
	jCHExprFeatureExtraction \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES = \
	jCHSubgraph \
	jCHFeatureSumTypeSerializer \
	jCHFeatureDictionary \
	jCHFeatureExtraction \
	jCHMethodExprs \
	jCHExprFeatureExtraction \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: jchfeatures.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

jchfeatures.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLC) -a -o $@ $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~	

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
