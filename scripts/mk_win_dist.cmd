
call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars64.bat"

python scripts\mk_win_dist.py --x64-only --dotnet-key=$(Build.SourcesDirectory/resources/z3.snk

call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars32.bat"

python scripts\mk_win_dist.py --x86-only --dotnet-key=$(Build.SourcesDirectory)/resources/z3.snk

