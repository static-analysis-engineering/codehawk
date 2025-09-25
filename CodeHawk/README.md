# Install Dependencies

<details>
<summary>Ubuntu 22.04+ and Debian 11+</summary>

```
sudo apt update -y
sudo apt install --no-install-recommends \
                     git ca-certificates \
                     build-essential opam unzip default-jdk \
                     pkg-config m4 zlib1g-dev libgmp-dev bubblewrap -y
```
</details>

<details>
<summary>Fedora</summary>

```
sudo yum install awk diffutils git gmp-devel opam \
    perl-ExtUtils-MakeMaker perl-FindBin perl-Pod-Html zlib-devel -y
```
</details>


<details>
<summary>Arch Linux</summary>

```
sudo pacman -Syu base-devel git opam
```
</details>

<details>
<summary>macOS</summary>

```
brew install opam
```
</details>

# Build CodeHawk

Note that on Ubuntu 24.04 you must also pass `--disable-sandboxing` to `opam init`,
or create an AppArmor profile with `userns` permissions. This is also required
if you are running in `docker` without `--privileged`.
[Yes, this is a mess!](https://github.com/containers/bubblewrap/issues/505#issuecomment-2093203129)

```
opam init --bare

git clone https://github.com/static-analysis-engineering/codehawk.git
cd codehawk/CodeHawk
opam switch create . 5.2.0
eval $(opam env)
opam install --deps-only ./codehawk.opam

dune build @install
```

The Makefiles in the repository are to help CodeHawk's developers
debug circular module dependencies, they are not intended for users.

