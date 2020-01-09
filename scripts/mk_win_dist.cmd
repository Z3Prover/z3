
IF "%1" == "x64" (

    call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars64.bat"

    python scripts\mk_win_dist.py ^
        --x64-only ^
        --dotnet-key=$(Build.SourcesDirectory)/resources/z3.snk ^
        --build=$(Build.ArtifactStagingDirectory)

) ELSE (
    IF "%1" == "x86" (

        call "C:\Program Files (x86)\Microsoft Visual Studio\2017\Enterprise\VC\Auxiliary\Build\vcvars32.bat"

        python scripts\mk_win_dist.py ^
            --x86-only ^
            --dotnet-key=$(Build.SourcesDirectory)/resources/z3.snk ^
            --build=$(Build.ArtifactStagingDirectory)

    ) ELSE (
        ECHO "Must specify x64 or x86"
        EXIT /B 1
    )
)

