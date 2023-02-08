CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
ELFLIB = $(CHB)/bchlibelf

CAMLDOC := ocamldoc

CAMLC := ocamlopt  -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(BCHLIB)/cmi \
	-I $(ELFLIB)/cmi \

CAMLLINK := ocamlopt \

MLIS := \
	bCHPowerTypes \
	bCHPowerPseudocode \
	bCHPowerOperand \
	bCHPowerOpcodeRecords \
	bCHPowerAssemblyInstruction \
	bCHPowerAssemblyInstructions \
	bCHDisassemblePowerInstruction \
	bCHDisassembleVLEInstruction \
	bCHDisassemblePower \


CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHPowerPseudocode \
	bCHPowerOperand \
	bCHPowerOpcodeRecords \
	bCHPowerAssemblyInstruction \
	bCHPowerAssemblyInstructions \
	bCHDisassemblePowerInstruction \
	bCHDisassembleVLEInstruction \
	bCHDisassemblePower \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchlibpower32

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchlibpower32: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(BCHLIB)/bchlib.cmxa $(ELFLIB)/bchlibelf.cmxa
	$(CAMLLINK) -a -o bchlibpower32.cmxa $(OBJECTS)

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
