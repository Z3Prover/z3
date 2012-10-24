@echo off
call .\build.cmd
sd edit test_capi.regress.txt test_capi.regress.err test_mlapi.regress.txt test_mlapi.regress.err queen.regress.txt queen.regress.err
move test_capi.txt test_capi.regress.txt
move test_capi.err test_capi.regress.err
move test_mlapi.txt test_mlapi.regress.txt
move test_mlapi.err test_mlapi.regress.err
move queen.txt queen.regress.txt
move queen.err queen.regress.err
sd revert -a test_capi.regress.txt test_capi.regress.err test_mlapi.regress.txt test_mlapi.regress.err queen.regress.txt queen.regress.err
