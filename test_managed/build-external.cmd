csc /reference:..\..\bin\Microsoft.Z3.dll /platform:x86 test_managed.cs
@rem Copy DLL to allow test_managed.exe to find it.
copy ..\..\bin\Microsoft.Z3.dll