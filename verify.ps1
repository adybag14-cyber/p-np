$ErrorActionPreference = "Stop"

$env:ELAN_HOME = Join-Path $PSScriptRoot ".elan"
$lake = Join-Path $env:ELAN_HOME "bin\lake.exe"
if (!(Test-Path $lake)) {
  throw "Project-local Lean toolchain is missing. Run .\setup.ps1."
}

& $lake build
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

$bad = Select-String -Path (Join-Path $PSScriptRoot "*.lean") `
  -Pattern "(^|\s)(sorry|axiom)(\s|$)" -CaseSensitive
if ($bad) {
  $bad | Format-Table Path, LineNumber, Line -AutoSize
  throw "Forbidden placeholder proof or project axiom declaration found."
}

& $lake env lean (Join-Path $PSScriptRoot "Audit.lean")
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

Write-Host "Verification succeeded: all Lean targets compile and no placeholders/project axioms were found."
