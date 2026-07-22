$ErrorActionPreference = "Stop"
$env:ELAN_HOME = Join-Path $PSScriptRoot ".elan"
$lake = Join-Path $env:ELAN_HOME "bin\lake.exe"
if (!(Test-Path $lake)) { throw "Project-local Lean toolchain is missing. Run .\setup.ps1." }
$exe = Join-Path $PSScriptRoot ".lake\build\bin\pnp_experiments.exe"
if (!(Test-Path $exe)) { & $lake build pnp_experiments }
& $exe
exit $LASTEXITCODE
