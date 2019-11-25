# Makefile contributed by Alain Frisch

# the list is topologically sorted
MODULES := \
 extBytes enum bitSet dynArray extArray extHashtbl extList extString extBuffer \
 global IO option pMap std uChar uTF8 base64 unzip refList optParse dllist extLib \

ifdef minimal
MODULES := $(filter-out unzip uChar uTF8, $(MODULES))
endif

CPPO_ARGS := $(shell ocaml configure.ml -cppo-args)
CPPO := cppo $(CPPO_ARGS)

OCAML_ARGS := -pp "$(CPPO)" -g
OCAML_ARGS += $(shell ocaml configure.ml -compile-args)

#OCAMLC = ocamlfind ocamlc $(OCAML_ARGS)
OCAMLC = ocamlfind ocamlc
#OCAMLOPT = ocamlfind ocamlopt $(OCAML_ARGS)
OCAMLOPT = ocamlfind ocamlopt
OCAMLDOC = ocamldoc -pp "$(CPPO)"

MLI = $(filter-out extLib.mli, $(MODULES:=.mli))
CMI = $(MODULES:=.cmi)
CMO = $(MODULES:=.cmo)
CMX = $(MODULES:=.cmx)
CMT = $(MODULES:=.cmt)
CMTI = $(MODULES:=.cmti)

.NOTPARALLEL:
.SUFFIXES:
.PHONY: build all opt cmxs doc install uninstall clean release

build: all opt cmxs

all: extLib.cma
opt: extLib.cmxa
cmxs: extLib.cmxs

doc: $(MLI)
	$(OCAMLC) -c $(MLI)
	$(OCAMLDOC) -sort -html -d doc/ $(MLI) extLib.ml

extLib.cma: $(CMO)
	$(OCAMLC) -a -o $@ $^
extLib.cmxa: $(CMX)
	$(OCAMLOPT) -a -o $@ $^
%.cmxs: %.cmxa
	$(OCAMLOPT) -shared -linkall $< -o $@
%.cmo: %.mli %.ml
	$(OCAMLC) -c $^
%.cmx: %.mli %.ml
	$(OCAMLOPT) -c $^
extLib.cmo: extLib.ml
	$(OCAMLC) -c $<
extLib.cmx: extLib.ml
	$(OCAMLOPT) -c $<
extBytes.mli: extBytes.ml
	$(OCAMLC) -i $< > $@

install:
	ocamlfind install -patch-version $(VERSION) extlib META extLib.cma $(MLI) $(CMI) -optional extLib.cmxa $(CMX) extLib.cmxs extLib.a extLib.lib $(CMT) $(CMTI)

uninstall:
	ocamlfind remove extlib

clean:
	rm -f *.cmo *.cmx *.o *.obj *.cmi *.cma *.cmxa *.cmxs *.a *.lib doc/*.html extBytes.mli
