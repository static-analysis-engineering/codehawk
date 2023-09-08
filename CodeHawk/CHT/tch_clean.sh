#!/bin/bash
set -e
make -C tchlib clean
make -C CH_tests/xprlib_tests/txprlib clean
make -C CH_tests/xprlib_tests/txxprlib clean
make -C CHB_tests/bchlib_tests/tbchlib clean
make -C CHB_tests/bchlib_tests/txbchlib clean
make -C CHB_tests/bchlibelf_tests/tbchlibelf clean
make -C CHB_tests/bchlibelf_tests/txbchlibelf clean
make -C CHB_tests/bchlibarm32_tests/tbchlibarm32 clean
make -C CHB_tests/bchlibarm32_tests/txbchlibarm32 clean
make -C CHB_tests/bchlibmips32_tests/txbchlibmips32 clean
make -C CHB_tests/bchlibpower32_tests/txbchlibpower32 clean
make -C CHB_tests/bchlibx86_tests/tbchlibx86 clean
make -C CHB_tests/bchlibx86_tests/txbchlibx86 clean
