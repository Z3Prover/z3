Z3 API for .NET Core

Z3's .NET API uses Code Contracts, which are not included in .NET Core. The
enclosed file called DummyContracts.cs provides stubs for the Code Contracts
functions, so that the API will compile, but not perform any contract
checking. To build this using .NET core, run (in this directory):

dotnet restore
dotnet build core.csproj -c Release

If you are building with the cmake system, you should first
copy over files that are produced by the compiler into
this directory. You need to copy over Native.cs and Enumeration.cs

-- good luck!
