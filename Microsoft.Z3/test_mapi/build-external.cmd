copy ..\..\bin\Microsoft.Z3.dll .
copy ..\..\bin\Z3.dll .

csc /reference:Microsoft.Z3.dll /debug:full /platform:x86 /reference:System.Numerics.dll Program.cs