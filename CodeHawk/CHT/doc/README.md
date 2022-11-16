# CHT: CodeHawk Testing Framework

## Organization and Dependencies

### tchlib

General-purpose ocaml testing framework, adapted from
[Kaputt](https://kaputt.x9c.fr/index.html). Depends on
CH/chlib and CH/chutil for pretty printing and xml input/output.

### CH_tests

CH engine and utilities tests; mirrors CodeHawk/CH.

Currently provided:
- **xprlib_tests**
  - xsimplifyTest
  - xconsequenceTest

### CHB_tests

Binary analyzer tests; mirrors CodeHawk/CHB

Currently provided:
- **bchlib_tests**
  - bCHDoublewordTest
  - bCHImmediateTest
  - bCHLocationTest


## Naming conventions

Tests are organized in test suites, with roughly one test suite per
ocaml class or ocaml source file. Naming conventions roughly follow
the [Google style guide](https://google.github.io/styleguide/javaguide.html).

### Test suites

An ocaml source file source.ml has an associated test-suite file named
sourceTest.ml, with executable test suite named sourceTest.


## Test inputs

Test inputs can be specified directly in the test-suite source file or
read in from file. Test-input files are saved in a subdirectory of the
test suite directory called <code>testinputs</code>.


## Makefile

- <code>make</code> or <code>make all</code> will build all tests
- <code>make run</code> will build and run all tests (in a test directory)
