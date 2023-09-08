#!/bin/bash
set -e
make -C tchlib
make -C CH_tests/xprlib_tests/txprlib
make -C CH_tests/xprlib_tests/txxprlib
make -C CHB_tests/bchlib_tests/tbchlib
make -C CHB_tests/bchlib_tests/txbchlib
make -C CHB_tests/bchlibelf_tests/tbchlibelf
make -C CHB_tests/bchlibelf_tests/txbchlibelf
make -C CHB_tests/bchlibarm32_tests/tbchlibarm32
make -C CHB_tests/bchlibarm32_tests/txbchlibarm32
make -C CHB_tests/bchlibmips32_tests/txbchlibmips32
make -C CHB_tests/bchlibpower32_tests/txbchlibpower32
make -C CHB_tests/bchlibx86_tests/tbchlibx86
make -C CHB_tests/bchlibx86_tests/txbchlibx86
