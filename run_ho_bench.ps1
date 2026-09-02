param(
    [string]$Z3Exe = "C:\z3\build-ninja\z3.exe",
    [string]$FileList = "C:\z3\ho_files.txt",
    [string]$OutCsv = "C:\z3\results.csv",
    [string]$ExtraArgs = "",
    [int]$TimeoutSec = 10,
    [int]$Jobs = 32
)

$files = Get-Content $FileList
$total = $files.Count
Write-Output "Running $total problems with args: $ExtraArgs, jobs=$Jobs"

$results = $files | ForEach-Object -Parallel {
    $file = $_
    $z3 = $using:Z3Exe
    $extra = $using:ExtraArgs
    $timeout = $using:TimeoutSec
    $argList = @("-T:$timeout")
    if ($extra -ne "") { $argList += $extra.Split(" ") }
    $argList += $file

    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $z3
    $psi.Arguments = ($argList -join " ")
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.UseShellExecute = $false
    $proc = New-Object System.Diagnostics.Process
    $proc.StartInfo = $psi
    $proc.Start() | Out-Null
    $stdoutTask = $proc.StandardOutput.ReadToEndAsync()
    $stderrTask = $proc.StandardError.ReadToEndAsync()
    # Hard kill safety net in case -T:10 fails to terminate the process (e.g. stuck in native code)
    $killMs = ($timeout + 15) * 1000
    if (-not $proc.WaitForExit($killMs)) {
        try { $proc.Kill() } catch {}
        $proc.WaitForExit()
    }
    [System.Threading.Tasks.Task]::WaitAll(@($stdoutTask, $stderrTask), 5000) | Out-Null
    $sw.Stop()
    $stdout = $stdoutTask.Result
    $stderr = $stderrTask.Result
    $exitCode = $proc.ExitCode

    $szs = "Unknown"
    if ($stdout -match "SZS status (\S+)") {
        $szs = $matches[1]
    } elseif ($stderr -match "SZS status (\S+)") {
        $szs = $matches[1]
    } elseif ($exitCode -ne 0) {
        $szs = "Crash"
    }

    [PSCustomObject]@{
        File = $file
        SZS = $szs
        ExitCode = $exitCode
        Seconds = [math]::Round($sw.Elapsed.TotalSeconds, 2)
    }
} -ThrottleLimit $Jobs

$results | Export-Csv -Path $OutCsv -NoTypeInformation
Write-Output "Done. Results in $OutCsv"
