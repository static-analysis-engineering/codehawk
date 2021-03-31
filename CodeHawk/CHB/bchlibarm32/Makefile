CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
ELFLIB = $(CHB)/bchlibelf

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

CAMLLINK := ocamlopt \

MLIS := \
	bCHARMTypes \
	bCHARMPseudocode \
	bCHARMSumTypeSerializer \
	bCHARMOperand \
	bCHARMOpcodeRecords \
	bCHARMDictionary \
	bCHARMDisassemblyUtils \
	bCHARMAssemblyInstruction \
	bCHARMAssemblyInstructions \
	bCHARMAssemblyBlock \
	bCHARMAssemblyFunction \
	bCHARMAssemblyFunctions \
	bCHDisassembleARMInstruction \
	bCHDisassembleARM \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHARMPseudocode \
	bCHARMSumTypeSerializer \
	bCHARMOperand \
	bCHARMOpcodeRecords \
	bCHARMDictionary \
	bCHARMDisassemblyUtils \
	bCHARMAssemblyInstruction \
	bCHARMAssemblyInstructions \
	bCHARMAssemblyBlock \
	bCHARMAssemblyFunction \
	bCHARMAssemblyFunctions \
	bCHDisassembleARMInstruction \
	bCHDisassembleARM \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchlibarm32

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibarm32: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(ELFLIB)/bchlibelf.cmxa
	$(CAMLLINK) -a -o bchlibarm32.cmxa $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml $(CMIS)
	$(CAMLC) -o $@ -c $<

clean:
	rm -f cmx/*.cm*
	rm -f cmi/*.cmi
	rm -f cmx/*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~ 
	rm -rf doc
