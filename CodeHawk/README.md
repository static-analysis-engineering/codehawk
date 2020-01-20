# Building with make

## System Requirements

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

# Building with shake

### High-level process:

1. Install dependencies
2. Install the shake build system
3. Install ocaml
4. Build CodeHawk

The top-level dependencies needed to build CodeHawk are zlib for compression, the shake build
system, and the ocaml package manager (opam). The relevant opam packages are `extlib` and
`camlzip`.

### Generic Unix

Other dependencies: `pkg-config`, `m4`

```
sudo apt update -y
sudo apt install curl -y
curl -sSL https://get.haskellstack.org/ | sh
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
stack install shake
git clone https://github.com/kestreltechnology/codehawk.git
cd codehawk/CodeHawk
stack runghc Shakefile.hs -- --opam
```

### Arch Linux

```
sudo pacman -Syu opam haskell-shake
git clone https://github.com/kestreltechnology/codehawk.git
cd codehawk/CodeHawk
shake --opam
```

### Fedora

```
sudo yum install opam shake ghc-compiler ghc-shake-devel diffutils zlib-devel -y
git clone https://github.com/kestreltechnology/codehawk.git
cd codehawk/CodeHawk
shake --opam
```

### Homebrew

```
brew install opam
brew install cabal-install
cabal update
cabal install shake
git clone https://github.com/kestreltechnology/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### MacPorts

```
sudo port install opam
sudo port install hs-cabal-install
cabal update
cabal install shake
git clone https://github.com/kestreltechnology/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### Ubuntu 19.04 or later, Debian Buster or later

```
sudo apt update -y
sudo apt install cabal-install pkg-config m4 zlib1g-dev opam -y
cabal update
cabal install shake
git clone https://github.com/kestreltechnology/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### Ubuntu 16.04 or later

```
sudo apt update -y
sudo apt install software-properties-common cabal-install pkg-config m4 zlib1g-dev -y
sudo add-apt-repository ppa:avsm/ppa -y
sudo apt update -y
sudo apt install opam
cabal update
cabal install shake
git clone https://github.com/kestreltechnology/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### Manually configured opam

Before the final "shake" command in one of the above instructions:

```
opam init --bare --no-setup --disable-sandboxing --bare
opam switch codehawk-4.07.1 4.07.1 --no-switch
eval $(opam env --switch=codehawk-4.07.1 --set-switch)
opam install ocamlfind zarith camlzip extlib
/path/to/shake
```
