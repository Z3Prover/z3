copy ..\..\x64\release\Microsoft.Z3.dll .
copy ..\..\x64\release\Z3.dll .

csc /reference:..\..\x64\release\Microsoft.Z3.dll /debug:full /platform:x64 /reference:System.Numerics.dll Program.cs