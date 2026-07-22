$ErrorActionPreference = "Stop"

$python = Join-Path $PSScriptRoot ".venv\Scripts\python.exe"
if (!(Test-Path $python)) {
  throw "Project-local Python environment is missing. Run .\setup-python.ps1."
}

$experiments = @(
  "residual_search.py",
  "frontier_experiment.py",
  "symbolic_cnf.py",
  "memo_dpll.py",
  "structural_dispatch.py",
  "hybrid_portfolio.py",
  "xor_affine.py",
  "xor_hard_search.py",
  "elimination_width.py",
  "xor_core.py",
  "certified_dag.py",
  "optimal_obdd.py",
  "adaptive_semantic_dag.py",
  "adaptive_policy_search.py",
  "overlap_potential.py",
  "contextual_interning.py",
  "coherent_policy_dp.py",
  "transform_then_observe.py",
  "nonlinear_observable_search.py",
  "reversible_beam_search.py",
  "linear_basis_obdd.py",
  "symmetry_residual_quotient.py",
  "restriction_collapse.py",
  "reversible_transform_obdd.py"
)

foreach ($experiment in $experiments) {
  Write-Host "=== $experiment ==="
  & $python (Join-Path $PSScriptRoot $experiment)
  if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}

Write-Host "All research experiments completed."
