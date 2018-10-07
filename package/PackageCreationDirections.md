# Z3 NuGet packaging

## Creation

 1. After tagging a commit for release, sign Microsoft.Z3.dll and libz3.dll (both x86 and x64 versions) with Microsoft's Authenticode certificate
 2. Test the signed DLLs with the `Get-AuthenticodeSignature` PowerShell commandlet
 3. Create the following directory structure for the x64 package (for x86, substitute the "x64" strings for "x86" and use x86 DLLs):
 ```
 +-- Microsoft.Z3.x64
 |   +-- Microsoft.Z3.x64.nuspec
 |   +-- lib
 |       +-- net40
 |           +-- Microsoft.Z3.dll
 |   +-- build
 |       +-- Microsoft.Z3.x64.targets
 |       +-- libz3.dll
 ```
 4. Open the nuspec file and fill in the appropriate macro values (note that for all URLs, preserve link integrity by linking to a specific commit):
    * $(releaseVersion) - the Z3 version being released in this package
    * $(iconUrlFromReleaseCommit) - URL for the Z3 icon file
    * $(licenseUrlFromReleaseCommit) - URL for the Z3 repo license
    * $(releaseCommitHash) - hash of the release commit
 5. Run `nuget pack Microsoft.Z3.x64\Microsoft.Z3.x64.nuspec`
 6. Test the resulting nupkg file (described below) then submit the package for signing before uploading to NuGet.org

## Testing

 1. Create a directory on your machine at C:\nuget-test-source
 2. Put the Microsoft.Z3.x64.nupkg file in the directory
 3. Open Visual Studio 2017, create a new C# project, then right click the project and click "Manage NuGet packages"
 4. Add a new package source - your C:\nuget-test-source directory
 5. Find the Microsoft.Z3.x64 package, ensuring in preview window that icon is present and all fields correct
 6. Install the Microsoft.Z3.x64 package, ensuring you are asked to accept the license
 7. Build your project. Check the output directory to ensure both Microsoft.Z3.dll and libz3.dll are present
 8. Import Microsoft.Z3 to your project then add a simple line of code like `using (var ctx = new Context()) { }`; build then run your project to ensure the assemblies load properly
 