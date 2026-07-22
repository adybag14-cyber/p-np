$ErrorActionPreference = "Stop"
$env:ELAN_HOME = Join-Path $PSScriptRoot ".elan"
$lake = Join-Path $env:ELAN_HOME "bin\lake.exe"
if (!(Test-Path $lake)) { throw "Project-local Lean toolchain is missing. Run .\setup.ps1." }
& $lake build
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
Write-Host "Build succeeded with project-local Lean."
