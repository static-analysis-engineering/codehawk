#!/usr/bin/env bash
# Checks how gcc, clang, and the CHC parser (goblint-cil) handle the
# arguments of CodeHawk function attributes (chk_pre/chk_post), so that
# header files stay exchangeable between CodeHawk-C and CodeHawk-Binary and
# valid for C compilers. See README.md.
#
# usage: run.sh            (from any directory)
# env:   CC_LIST   compilers to test (default: "gcc clang"; missing ones are skipped)
#        PARSEFILE CHC parser executable (default: _build/default/CHC/cchcil/cCHXParseFile.exe)

set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CODEHAWK="$(cd "$HERE/../.." && pwd)"
CC_LIST="${CC_LIST:-gcc clang}"
PARSEFILE="${PARSEFILE:-$CODEHAWK/_build/default/CHC/cchcil/cCHXParseFile.exe}"
WORK="$(mktemp -d)"
trap 'rm -rf -- "$WORK"' EXIT

pass=0; fail=0; skip=0
ok()   { echo "PASS  $1"; pass=$((pass+1)); }
bad()  { echo "FAIL  $1"; fail=$((fail+1)); }
skp()  { echo "SKIP  $1"; skip=$((skip+1)); }

cflags() {   # strict flags: only the unknown-attribute warning is suppressed
  case "$1" in
    clang*) echo "-std=gnu11 -fsyntax-only -Wall -Wextra -Werror -Wno-unknown-attributes" ;;
    *)      echo "-std=gnu11 -fsyntax-only -Wall -Wextra -Werror -Wno-attributes" ;;
  esac
}

for cc in $CC_LIST; do
  if ! command -v "$cc" >/dev/null 2>&1; then skp "$cc not found"; continue; fi
  # accepted forms must compile cleanly
  for f in "$HERE"/accept/*.c; do
    if "$cc" $(cflags "$cc") "$f" >"$WORK/out" 2>&1; then ok "$cc accepts $(basename "$f")"
    else bad "$cc accepts $(basename "$f")"; cat "$WORK/out"; fi
  done
  # rejected forms must fail
  for f in "$HERE"/reject/*.c; do
    if "$cc" $(cflags "$cc") -Werror=implicit-function-declaration "$f" >/dev/null 2>&1
    then bad "$cc rejects $(basename "$f")"; else ok "$cc rejects $(basename "$f")"; fi
  done
  # C2x scoped attributes: arguments unparsed, accepted
  if "$cc" -std=gnu2x -fsyntax-only -Wno-attributes -Wno-unknown-attributes \
       "$HERE/scoped/c2x_scoped.c" >"$WORK/out" 2>&1
  then ok "$cc accepts c2x_scoped.c (-std=gnu2x)"
  else bad "$cc accepts c2x_scoped.c (-std=gnu2x)"; cat "$WORK/out"; fi
  # macro expansion inside attribute arguments
  if "$cc" -E "$HERE/macro_expansion.c" 2>/dev/null | grep -q 'chk_pre(deref_read, 2, ((3) < (4)'
  then ok "$cc expands macros in attribute arguments"
  else bad "$cc expands macros in attribute arguments"; fi
done

# CHC parser (goblint-cil): structure of the parsed attribute arguments
cil_parse() {   # $1 = source file; preprocesses and parses into $WORK/p/<name>
  local name; name="$(basename "$1" .c)"
  mkdir -p "$WORK/p/src" "$WORK/p/out"
  cp "$1" "$WORK/p/src/"; cp "$HERE/ch_terms_test.h" "$WORK/p/"
  gcc -E -I "$HERE" "$1" -o "$WORK/p/src/$name.i" 2>/dev/null || return 1
  "$PARSEFILE" -projectpath "$WORK/p" -targetdirectory "$WORK/p/out" -keepUnused \
     "$WORK/p/src/$name.i" >"$WORK/p/$name.log" 2>&1
  [ -f "$WORK/p/out/src/$name/${name}_cdict.xml" ] || \
    [ -n "$(find "$WORK/p/out" -name "${name}_cdict.xml" 2>/dev/null)" ]
}

if [ ! -x "$PARSEFILE" ] || ! command -v gcc >/dev/null 2>&1; then
  skp "CHC parser checks (parseFile or gcc not found)"
else
  if cil_parse "$HERE/accept/accept_terms.c"; then
    ok "CIL parses accept_terms.c"
    dict="$(find "$WORK/p/out" -name accept_terms_cdict.xml | head -1)"
    for t in 't="acons,deref_write"' 't="acons,chk_min"' 't="acons,chk_ntp"' \
             't="abinop,plusa"' 't="acons,chk_arg"' 't="astr"' 't="chk_post"'; do
      if grep -q "$t" "$dict"; then ok "CIL tree contains $t"
      else bad "CIL tree contains $t"; fi
    done
    # enum constant folded to an integer: chk_post(not_null, ch_test_return)
    # becomes the same attribute as chk_post(not_null, 0)
    if ! grep -q 't="acons,ch_test_return"' "$dict" && \
       [ "$(grep -c 't="chk_post"' "$dict")" -eq 1 ]
    then ok "CIL folds enum constant to AInt (same entry as index 0)"
    else bad "CIL folds enum constant to AInt (same entry as index 0)"; fi
  else
    bad "CIL parses accept_terms.c"; cat "$WORK/p/accept_terms.log" 2>/dev/null
  fi
  rm -rf -- "$WORK/p"
  # attributes on struct types and fields: where CIL attaches them
  if cil_parse "$HERE/accept/accept_types.c"; then
    ok "CIL parses accept_types.c"
    dict="$(find "$WORK/p/out" -name accept_types_cdict.xml | head -1)"
    while IFS= read -r line; do
      case "$line" in
        PASS*) ok "${line#PASS  }" ;;
        *)     bad "${line#FAIL  }" ;;
      esac
    done < <(python3 "$HERE/tools/check_cil_types.py" "$dict" 2>&1)
  else
    bad "CIL parses accept_types.c"; cat "$WORK/p/accept_types.log" 2>/dev/null
  fi
  rm -rf -- "$WORK/p"
  if cil_parse "$HERE/scoped/c2x_scoped.c"; then bad "CIL rejects c2x_scoped.c"
  else ok "CIL rejects c2x_scoped.c"; fi
fi

echo "passed: $pass  failed: $fail  skipped: $skip"
[ "$fail" -eq 0 ]
