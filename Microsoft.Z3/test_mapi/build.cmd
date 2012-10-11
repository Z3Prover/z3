copy ..\..\external\Microsoft.Z3.dll .
copy ..\..\external\Z3.dll .

csc /reference:..\..\external\Microsoft.Z3.dll /platform:anycpu /reference:System.Numerics.dll Program.cs