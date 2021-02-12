# Building with make

## System Requirements

Building codehawk requires the following applications and libraries:

- Objective Caml (version 4.07 or higher)
- The Findlib / ocamlfind library manager
- The Zlib C library, version 1.1.3 or up
- The Zarith library

The CodeHawk Tool Suite contains three analyzers that can all be built
individually. All three analyzers have an optional gui that can be built
separately (and that requires additional dependencies to be installed).


### Install dependencies: Ubuntu 16.04 or later (without gui)

```
sudo apt update -y
sudo apt install software-properties-common pkg-config m4 zlib1g-dev -y
sudo add-apt-repository ppa:avsm/ppa -y
sudo apt update -y
sudo apt install opam
git clone https://github.com/static-analysis-engineering/codehawk.git
opam init --bare --no-setup --disable-sandboxing
opam switch create codehawk-4.07.1 4.07.1 --no-switch
eval $(opam env --switch=codehawk-4.07.1 --set-switch)
opam install ocamlfind zarith camlzip extlib
cd codehawk/CodeHawk
```

Depending on which analyzer you want to build:
- **Binary:** `./make_binary_analyzer.sh`
  - analyzer binary: CHB/bchcmdline/chx86_analyze
- **C:** `./make_c_analyzer.sh`
  - parser binary: CHC/cchcil/parseFile
  - analyzer binary: CHC/cchcmdline/canalyzer
- **Java:** `./make_java_analyzer.sh`
  - analyzer binary: CHJ/jchstac/chj_initialize
- **all:** `./full_make_no_gui.sh`
  - analyzer/parser binaries: all of the above


### Install dependencies and build: Ubuntu 16.04 or later (including gui)

```
sudo apt update -y
sudo apt install software-properties-common pkg-config m4 zlib1g-dev liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev -y
sudo add-apt-repository ppa:avsm/ppa -y
sudo apt update -y
sudo apt install opam
git clone https://github.com/static-analysis-engineering/codehawk.git
opam init --bare --no-setup --disable-sandboxing
opam switch create codehawk-4.07.1 4.07.1 --no-switch
eval $(opam env --switch=codehawk-4.07.1 --set-switch)
opam install ocamlfind zarith camlzip extlib lablgtk lablgtk-extras
cd codehawk/CodeHawk
./full_make.sh
```

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
git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
stack runghc Shakefile.hs -- --opam
```

### Arch Linux

```
sudo pacman -Syu opam haskell-shake lablgtk2
git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
shake --opam
```

### Fedora

```
sudo yum install opam shake ghc-compiler ghc-shake-devel diffutils zlib-devel ocaml-lablgtk-devel -y
git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
shake --opam
```

### Homebrew

```
brew install opam
brew install cabal-install
brew install lablgtk
cabal update
cabal install --lib shake
cabal install --lib unordered-containers
git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### MacPorts

```
sudo port install opam
sudo port install hs-cabal-install
sudo port install lablgtk2
cabal update
cabal install --lib shake
cabal install --lib unordered-containers
git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### Ubuntu 19.04 or later, Debian Buster or later

```
sudo apt update -y
sudo apt install cabal-install pkg-config m4 zlib1g-dev opam liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev -y
cabal update
cabal install shake
git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### Ubuntu 16.04 or later

```
sudo apt update -y
sudo apt install software-properties-common cabal-install pkg-config m4 zlib1g-dev liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev -y
sudo add-apt-repository ppa:avsm/ppa -y
sudo apt update -y
sudo apt install opam
cabal update
cabal install shake
git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
~/.cabal/bin/shake --opam
```

### Manually configured opam

Before the final "shake" command in one of the above instructions:

```
opam init --bare --no-setup --disable-sandboxing
opam switch create codehawk-4.07.1 4.07.1 --no-switch
eval $(opam env --switch=codehawk-4.07.1 --set-switch)
opam install ocamlfind zarith camlzip extlib lablgtk lablgtk-extras
/path/to/shake
```
