param(
    [Parameter(Mandatory=$true)][string]$FileListPath,
    [Parameter(Mandatory=$true)][string]$ConfigName,
    [string]$ExtraArgsStr = "",
    [Parameter(Mandatory=$true)][string]$OutCsv,
    [int]$Throttle = 32,
    [string]$Z3 = "C:\z3\build-ninja\z3.exe"
)

$files = Get-Content $FileListPath
$ExtraArgsArr = if ($ExtraArgsStr) { $ExtraArgsStr -split ',' } else { @() }

$results = $files | ForEach-Object -ThrottleLimit $Throttle -Parallel {
    $file = $_
    $z3 = $using:Z3
    $extra = $using:ExtraArgsArr
    $argList = @('-tptp', '-T:10') + $extra + @($file)
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $z3
    foreach ($a in $argList) { $psi.ArgumentList.Add($a) }
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.UseShellExecute = $false
    $proc = New-Object System.Diagnostics.Process
    $proc.StartInfo = $psi
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    [void]$proc.Start()
    $stdoutTask = $proc.StandardOutput.ReadToEndAsync()
    $stderrTask = $proc.StandardError.ReadToEndAsync()
    $finished = $proc.WaitForExit(20000)
    if (-not $finished) {
        try { $proc.Kill($true) } catch {}
        $exitCode = -1
    } else {
        $exitCode = $proc.ExitCode
    }
    [System.Threading.Tasks.Task]::WaitAll(@($stdoutTask, $stderrTask), 2000) | Out-Null
    $stdout = if ($stdoutTask.IsCompleted) { $stdoutTask.Result } else { "" }
    $stderr = if ($stderrTask.IsCompleted) { $stderrTask.Result } else { "" }
    $sw.Stop()
    $combined = $stdout + "`n" + $stderr
    $szs = "NoStatus"
    if ($combined -match 'SZS status (\S+)') { $szs = $matches[1] }
    [PSCustomObject]@{
        File = $file
        SZS = $szs
        ExitCode = $exitCode
        Seconds = [math]::Round($sw.Elapsed.TotalSeconds,2)
    }
}

$results | Export-Csv -Path $OutCsv -NoTypeInformation
Write-Host "Config '$ConfigName' done. Results: $OutCsv"
