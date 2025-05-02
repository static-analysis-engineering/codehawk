# Building with make

## System Requirements

Building codehawk requires the following applications and libraries:

- Objective Caml (version 4.09 or higher)
- The Findlib / ocamlfind library manager
- The Zlib C library, version 1.1.3 or up
- The Zarith library
- goblint-cil, version 2.0.6

The CodeHawk Tool Suite contains three analyzers that can all be built
individually. All three analyzers have an optional gui that can be built
separately (and that requires additional dependencies to be installed).
The gui is current out-of-date and will require additional work to revive.


### Install Dependencies:

These commands should work for Ubuntu 22.04+:

```
sudo apt update -y
sudo apt install --no-install-recommends software-properties-common \
                     build-essential unzip \
                     pkg-config m4 zlib1g-dev libgmp-dev bubblewrap -y

# Run with sudo if you wish to install globally
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
opam init --bare

git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
opam switch create . 5.2.0 && eval $(opam env)
opam install dune ocamlfind zarith camlzip extlib goblint-cil.2.0.6
```

Depending on which analyzer you want to build:
- **Binary:** `dune build CHB`
- **C:** `dune build CHC`
- **Java:** `dune build CHJ`
- **all:** `dune build`

These targets can be combined, e.g. `dune build CHB CHC`.

The Makefiles in the repository are to help CodeHawk's developers
debug circular module dependencies, they are not intended for users.

Dependencies for other OS flavors:
- Arch Linux: `sudo pacman -Syu opam`
- Fedora: `sudo yum install opam diffutils zlib-devel ocaml-lablgtk-devel -y`
- macOS: `brew install opam`
