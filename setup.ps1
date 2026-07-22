$ErrorActionPreference = "Stop"
$env:ELAN_HOME = Join-Path $PSScriptRoot ".elan"
$bootstrap = Join-Path $PSScriptRoot "elan-bootstrap\elan-init.exe"
if (!(Test-Path $bootstrap)) { throw "Missing bundled elan bootstrapper: $bootstrap" }
if (!(Test-Path (Join-Path $env:ELAN_HOME "bin\elan.exe"))) {
  & $bootstrap -y --no-modify-path --default-toolchain stable
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}
$lake = Join-Path $env:ELAN_HOME "bin\lake.exe"
& $lake update
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& $lake exe cache get
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& $lake build
exit $LASTEXITCODE