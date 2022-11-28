#!/bin/bash
set -e
make -C tchlib
make -C CH_tests/xprlib_tests/txprlib
make -C CH_tests/xprlib_tests/xprlib
make -C CHB_tests/bchlib_tests/tbchlib
make -C CHB_tests/bchlib_tests/bchlib
make -C CHB_tests/bchlibarm32_tests/bchlibarm32
make -C CHB_tests/bchlibpower32_tests/bchlibpower32
