@echo off

rem Ocaml is VS2013, so need VS2013 command prompt for it to work!
python scripts/mk_make.py -b bld_dbg_2013 --java --ml --debug --vs --parallel=12
