$ErrorActionPreference = "Stop"

$venv = Join-Path $PSScriptRoot ".venv"
$python = Join-Path $venv "Scripts\python.exe"

if (!(Test-Path $python)) {
  py -3.11 -m venv $venv
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}

& $python -m pip install --upgrade pip
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

& $python -m pip install -r (Join-Path $PSScriptRoot "requirements.txt")
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

& $python -c "import numpy, networkx; print('Python research environment ready:', 'numpy', numpy.__version__, 'networkx', networkx.__version__)"
