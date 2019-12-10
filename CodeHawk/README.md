## System Requirements and Build instructions

### System Requirements

Building codehawk requires the following applications and libraries:

- Objective Caml (version 4.07 or higher)
- The Findlib / ocamlfind library manager
- The Zlib C library, version 1.1.3 or up
- The Zarith library

### Build instructions

The CodeHawk Tool Suite consists of subsystems that can be built
individually, with the following dependencies:

#### External libraries

CodeHawk depends on two external libraries that have been included here
for convenience. 

- CH_extern: external libraries extlib and camlzip with no dependencies

#### Language-independent Abstract Interpretation Engnine

- CH/chlib: the core abstract interpretation engine, with no dependencies
- CH/chutil: general utilities, dependent on extlib and camlzip
- CH/xprlib: expression utilities, dependent on extlib

#### CodeHawk C Analyzer

- CHC/cil-1.7.3-develop: CIL parser, developed by George Necula at Berkeley,
   modified for use in the CodeHawk C Analyzer.
- CHC/cchcil: CodeHawk C source code parser, dependent on cil-1.7.3-develop
- CHC/cchlib: dependent on CH_extern, CH
- CHC/cchpre: dependent on CH_extern, CH, CHC/cchlib
- CHC/cchanalyze: dependent on CH_extern, CH, CHC/cchlib,cchpre
- CHC/cchcmdline: dependent on CH_extern, CH, CHC/cchlib,cchpre,cchanalyze

Building the analyzer can be accomplished by invoking **make** in all of these
directories in the given sequence.

#### CodeHawk Binary Analyzer

- CHB/bchlib: dependent on CH_extern, CH
- CHB/bchlibpe: dependent on CH_extern, CH, CHB/bchlib
- CHB/bchlibelf: dependent on CH_extern, CH, CHB/bchlib
- CHB/bchlibx86: dependent on CH_extern, CH, CHB/bchlib,bchlibpe,bchlibelf
- CHB/bchlibmips32: dependent on CH_extern, CH, CHB/bchlib,bchlibelf
- CHB/bchanalyze: dependent on CH_extern, CH, CHB/bchlib,bchlibpe,bchlibelf,bchlibx86,bchlibmips32
- CHB/bchcmdline: dependent on CH_extern, CH, CHB/bchlib,bchlibpe,bchlibelf,bchlibx86,bchlibmips32,bchanalyze

Building the analyzer can be accomplished by invoking **make** in all
of these directories in the given sequence.


