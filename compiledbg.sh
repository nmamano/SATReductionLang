#!/bin/bash
g++ -O1 -g -Wall -std=c++0x -Wno-parentheses -Isatsolvers/minisat-2.2.0/core/.. -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -D USE_MINISAT -c -o lenguajereduccionesnpdbg.o lenguajereduccionesnp.cc
g++ lenguajereduccionesnpdbg.o -Wall -Lsatsolvers/minisat-2.2.0/core -lminisat_release -o juezejecutabledbg
rm lenguajereduccionesnpdbg.o