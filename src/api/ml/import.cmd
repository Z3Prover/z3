@echo off
SETLOCAL

:CHECKARG1
if not "%1"=="" (
  set SDTROOT=%1
  goto :CHECKARG2
)

goto :FAIL


:CHECKARG2
if "%2"=="" (
  goto :IMPORT
)

goto :FAIL


:IMPORT
cd import
sd edit ...
del z3.h z3_api.h z3_macros.h z3lib.lib msbig_rational.lib z3.exe test_capi.c test_mlapi_header.html z3_mlapi_header.html mldoc_footer.html tabs.css z3.png z3_ml.css
copy %SDTROOT%\lib\z3.h
copy %SDTROOT%\lib\z3_api.h
copy %SDTROOT%\lib\z3_macros.h
copy %SDTROOT%\release_mt\z3lib.lib
copy %SDTROOT%\release_mt\msbig_rational.lib
copy %SDTROOT%\release_mt\z3.exe
copy %SDTROOT%\test_capi\test_capi.c
copy %SDTROOT%\doc\test_mlapi_header.html
copy %SDTROOT%\doc\z3_mlapi_header.html
copy %SDTROOT%\doc\mldoc_footer.html
copy %SDTROOT%\doc\html\tabs.css
copy %SDTROOT%\doc\z3.png
copy %SDTROOT%\doc\z3_ml.css
sd add ...
sd revert -a ...
cd ..
goto :END

:FAIL
echo "Usage:"
echo "  %0 SDTROOT"
echo ""
echo "Examples:"
echo "  %0 \\risebuild\drops\z32\2.0.51220.7"
echo "  %0 \\risebuild\drops\z32\latest"
echo "  %0 J:\SD\other\sdt1\src\z3_2"
echo ""
goto :END

:END
ENDLOCAL
