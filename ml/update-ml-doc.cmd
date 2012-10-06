@echo off
SETLOCAL

REM Script to generate Z3 OCaml API documentation
REM
REM Assumes that environment variables are set to provide access to the OCaml compilers, as well as the following commands: sed

rd 2>NUL /s /q doc
md doc
cd doc
set MLDIR=..
set DOCDIR=..\%1

ocamldoc.opt -hide Z3,Z3.V3,Test_mlapi -html -css-style z3_ml.css -I %MLDIR% %MLDIR%\test_mlapi.ml %MLDIR%\z3.mli

sed "s|<pre><span class=\"keyword\">val\(.*\)</pre>|<div class=\"function\"><span class=\"keyword\">val\1</div>|g;s|<pre><span class=\"keyword\">type\(.*\)</pre>|<div class=\"function\"><span class=\"keyword\">type\1</div>|g;s|<code><span class=\"keyword\">type\(.*\) = </code>|<div class=\"function\"><span class=\"keyword\">type\1 = </div>|g" Z3.html > Z3.new.html
move >NUL Z3.new.html Z3.html

sed "s|<pre><span class=\"keyword\">val\(.*\)</pre>|<div class=\"function\"><span class=\"keyword\">val\1</div>|g" Test_mlapi.html > Test_mlapi.new.html
move >NUL Test_mlapi.new.html Test_mlapi.html

sed "s|<h1>Index of values</h1>|<h1>OCaml: Index</h1>|" Index_values.html > Index_values.new.html
move >NUL Index_values.new.html Index_values.html

copy >NUL %DOCDIR%\tabs.css
copy >NUL %DOCDIR%\z3.png
copy >NUL %DOCDIR%\z3_ml.css

sed "1,23d" Test_mlapi.html | sed "$d" > Test_mlapi.new.html

type 2>NUL %DOCDIR%\test_mlapi_header.html Test_mlapi.new.html %DOCDIR%\mldoc_footer.html >Test_mlapi.html

sed "1,37d" Z3.html > Z3.new.html

type 2>NUL %DOCDIR%\z3_mlapi_header.html Z3.new.html >Z3.html

exit /B 0
ENDLOCAL
