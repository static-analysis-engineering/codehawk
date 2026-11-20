# Attribute syntax tests (CodeHawk-C and CodeHawk-Binary)

Function contracts (preconditions, postconditions, side effects) are written as GNU attributes
(`chk_pre`, `chk_post`, ...) on prototypes in header files. These headers should be exchangeable
between CodeHawk-C and CodeHawk-Binary, and valid input for C compilers and other tools. These tests
record how gcc, clang, and the CHC parser (goblint-cil, `cCHXParseFile`) treat attribute arguments.

Run: `./run.sh` (optional: `CC_LIST="gcc gcc-12 clang"`, `PARSEFILE=<path to cCHXParseFile.exe>`).
Requires a built CHC parser for the CIL checks; missing tools are skipped.

## Findings (gcc 11.4, gcc-12, clang 14, goblint-cil 2.0.6; 2026-11-19)

gcc and clang parse every argument of an *unknown* GNU attribute as a C expression, except a bare
identifier in the first position (as `printf` in `format(printf, 2, 3)`).

| Argument | gcc / clang | CIL |
|---|---|---|
| bare identifier, first argument (`deref_read`) | accepted | `ACons "deref_read"` |
| integer index | accepted | `AInt` |
| undeclared identifier, later argument | error | - |
| parameter name (prototype scope, C11 6.2.1p4) | error | - |
| `return` | syntax error | - |
| call to undeclared function (`min(...)`) | implicit-declaration warning; error by default in GCC 14 / clang 16 | `ACons` tree |
| call to declared constructor (`chk_min(...)`) | clean | `ACons` tree, `ABinOp` for operators |
| string | accepted | `AStr` (opaque) |
| enum constant | accepted | folded to `AInt` (name lost) |
| identifier that is a macro | silently expanded | sees the expansion |
| C2x `[[chk::pre(...)]]` | arguments unparsed, anything accepted (`-std=gnu2x`) | parse error (no grammar) |

`-Wno-attributes` silences only the "attribute ignored" warning, not errors in the arguments.

## Conventions that follow

1. Predicate name as a bare first argument.
2. Parameters as 1-based indices, 0 = return value.
3. Term constructors declared (never defined) in a shared CodeHawk header with a reserved prefix
   (`ch_terms_test.h` here stands in for it): `long chk_min(long, long); long chk_ntp(int); ...`.
4. Keywords in a non-first position (e.g., a comparison operator) must be declared to be valid C.
   Enum constants are not an option: CIL folds them to `AInt`, so `chk_post(not_null, e)` with
   `enum { e = 0 }` becomes the same attribute as `chk_post(not_null, 0)` (tested in
   `accept_terms.c` only to rule this out). Instead:
   - fold the keyword into the predicate name, which comes first: `chk_pre(rel_leq, 1, 2)`
     (preferred for small closed sets such as the six comparison operators); or
   - use a bare, declared constructor name: declare `long chk_leq(void);` and write
     `chk_pre(relational_expr, chk_leq, 1, 2)`. A function designator is a valid expression
     (C11 6.3.2.1p4), compiles cleanly under `-Werror`, and CIL yields `ACons ("chk_leq", [])`.
     Write it without parentheses: `chk_leq()` compiles too, but CIL adds a spurious empty
     `ACons ("", [])` argument.

The current CodeHawk-Binary forms `chk_pre(deref_read(ntp), i)` and `chk_pre(relational_expr(op), i, j)`
are rejected by gcc and clang (`reject/chb_*.c`); see CHB-4 in the CHC analyzer issues file and the
CHC contracts design ("Compiler checking").

## Attributes on types (data-structure invariants)

| Placement | Example | gcc / clang | CIL |
|---|---|---|---|
| after `struct` | `struct __attribute__((chk_inv(...))) s { ... };` | ignored (warning) | compinfo `cattr` |
| after closing brace | `struct s { ... } __attribute__((chk_inv(...)));` | ignored (warning) | compinfo `cattr` |
| on a field | `unsigned len __attribute__((chk_inv(...)));` | ignored (warning) | fieldinfo `fattr` |
| redeclaration after definition | `struct __attribute__((chk_inv(...))) s5;` | accepted | **dropped** |
| typedef carrier | `typedef struct s5 chk_inv_s5 __attribute__((chk_inv(...)));` | ignored (warning) | attributes of the `TComp s5` type |
| typedef carrier, anonymous struct (`typedef struct { ... } rec_t;`) | `typedef rec_t chk_inv_rec_t __attribute__((chk_inv(...)));` | ignored (warning) | attributes of `TNamed rec_t`; the struct is `__anonstruct_rec_t_<n>` (no attribute) |
| function carrier | `void chk_invariant_s5(struct s5 *) __attribute__((chk_inv(...)));` | ignored (warning) | varinfo `vattr` |

Field names are not ordinary identifiers (each struct has its own member name space, C11 6.2.3p1),
so `chk_inv(rel_leq, len, cap)` is an error (`reject/field_name.c`); fields are referenced by name
strings through a declared constructor, `chk_fld("len")`, which can be checked against the struct.
For types defined in project headers (which are not modified), only the carriers attach a
specification after the definition; the redeclaration form is silently lost in CIL.
For a typedef of an anonymous struct (the common cFE style) the attribute is on the typedef name,
not on the struct, and the struct's generated name may differ between files: resolve `chk_fld` names
by unrolling the typedef chain, and key the invariant by the typedef name.
Checked by `tools/check_cil_types.py` on `accept/accept_types.c`.

## Files

- `accept/accept_terms.c`: must compile cleanly (`-Wall -Wextra -Werror`, unknown-attribute warning
  off) and parse with CIL into the expected trees.
- `reject/*.c`: each must fail to compile (one form per file).
- `scoped/c2x_scoped.c`: accepted by gcc/clang with `-std=gnu2x`, rejected by CIL.
- `macro_expansion.c`: macro expansion inside attribute arguments (`gcc -E`).
- `accept/accept_types.c`: attributes on struct types and fields; `tools/check_cil_types.py`
  checks where CIL attaches them.
- `ch_terms_test.h`: declarations of term constructors.
