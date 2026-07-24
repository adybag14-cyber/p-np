# Open-source cube and knowledge-compilation phase

This phase connects the repository's exact residual quotients to current open-source work on
backdoor DNFs and certified knowledge compilation. It does not claim a proof of P = NP.

## External sources inspected

- Backdoor DNFs supplementary artefact, Zenodo record 11259842 and GitHub repository
  `ASchidler/backdoor_cube`.
- CPOG / Certifying Projected Knowledge Compilation repository `rebryant/cpog`.
- The D4 knowledge compiler repository `crillab/d4`.
- The Ganak model counter repository `meelgroup/ganak`.

External repositories were cloned under `D:\pnp-external`; no third-party source code was
copied into this repository.

## Backdoor DNF artefact verification

The Zenodo supplementary archive was downloaded and its published MD5 checksum was
verified:

```text
file: backdoor_dnf_supplementary.zip
MD5: 990a570ff89066755b575971fcedc4b3
```

The published environment is no longer directly reproducible from the current Python
package index because it pins `python-sat==1.8.dev13`, which is no longer available.
The Windows host also uses Python 3.14, while that older PySAT source assumes Unix headers.

The artefact was therefore copied unchanged to Ubuntu WSL2 with Python 3.10.12. The only
dependency substitution was:

```text
python-sat==1.8.dev13 -> python-sat==1.8.dev12
```

All other pinned versions were retained. Running the authors' checked SAT-cube encoder on
`instances/vc/Bull.edge.cnf.bz2` produced:

```text
Finding sets of size 1
Finding sets of size 2
Finding sets of size 3
Found UNSAT
Found 4 partial assignments
Backdoor cube size 4
Result: [[-2, -3], [-2, 3], [2, 3], [2, -3]]
Done in approximately 0.0031 seconds
```

The bundled Linux MUSER2 binary independently minimized the cube family. This validates
the central operational idea: a complete family of partial assignments may replace all
total assignments while making every residual belong to a chosen tractable class.

## CPOG source and reproducibility result

The CPOG Lean source was inspected directly. Its counting core uses two distinct rules:

- decomposable AND nodes multiply child counts;
- partitioned OR nodes add child counts.

This distinction motivated A601-A615: overlapping cube terms are logically sound for SAT,
but adding their model counts is invalid unless they are disjoint or overlap is corrected.

A complete build of the current CPOG checkout was attempted with its pinned Lean
`v4.4.0-rc1` toolchain. The build did not complete because `lake-manifest.json` references
the LeanSAT branch `ppa-tauto` and commit
`1e13508a3f8d035175e86f4eaeda0193945f0eeb`; neither is currently fetchable from the
upstream repository. This is recorded as an external reproducibility failure, not as a
failure of the CPOG theorems.

## Exact semantic DNF and MTBDD experiment

`residual_dnf_cover.py` labels every full cut assignment by its exact residual truth
function, enumerates all `3^k` partial cubes, retains only monochromatic cubes, extracts
prime cubes, solves a minimum set cover for each residual class, and independently checks
the returned cover. It also computes the exact best fixed-order multi-terminal BDD over
all cut-variable orders for `k <= 8`.

### Random DAG, 12 inputs and 40 gates

At eight cut variables:

```text
256 raw assignments
2 semantic residual classes
2 prime-cube DNF terms
2 literals
3 MTBDD nodes: 1 decision and 2 terminals
```

### Random DAG, 12 inputs and 60 gates

At eight cut variables:

```text
256 raw assignments
3 semantic residual classes
4 minimum DNF terms
8 literals
6 MTBDD nodes
```

### Random 3-SAT circuit, 12 variables and 30 clauses

At eight cut variables:

```text
256 raw assignments
16 semantic residual classes
79 prime cubes
35 minimum DNF terms
193 literals
70 optimal fixed-order MTBDD nodes
```

### Random 3-SAT circuit, 14 variables and 45 clauses

At seven cut variables:

```text
128 raw assignments
9 semantic residual classes
30 prime cubes
20 minimum DNF terms
87 literals
31 optimal fixed-order MTBDD nodes
```

## Formal conclusions

### A586-A600: safe semantic cubes

A cube is a partial Boolean assignment. A `SafeTerm` carries a representative assignment
and proves that every total extension has exactly the representative's residual function.
Lean proves that representative-only solving and output-image reconstruction are exact.
The complete cube candidate space has cardinality `3^n`; singleton cubes give the generic
`2^n` fallback.

### A601-A615: SAT versus counting

Lean proves that overlap is harmless for existential SAT, but a duplicated singleton
already causes naive arithmetic overcounting. Exact addition requires partitioned OR;
exact multiplication requires a Cartesian/decomposable product. General overlap requires
an intersection correction or explicit disjointisation.

### A616-A630: proof-carrying classified plans

Accepting terms carry a reusable representative payload. Rejecting terms carry a universal
rejection proof for the representative, transported across the entire safe cube. A complete
classified plan has an executable Boolean decider, and Lean proves its answer is exactly
the original existential witness problem.

### A631-A645: representation lower bounds

Every safe term has one semantic residual label. Lean proves:

```text
number of semantic residual classes <= number of safe DNF terms
number of semantic residual classes <= number of decision-DAG terminals
number of decision-DAG terminals <= total DAG nodes
```

The semantic quotient is therefore a universal lower bound, not a complete prediction of
representation size. DNF, decision DAG, structural certificates, and exact residual tables
can have substantially different overheads. A baseline-safe portfolio may choose the
cheapest independently verified representation.

## Revised frontier

A useful universal compiler must construct, in polynomial time:

1. a polynomial-size complete cover of cut assignments;
2. a polynomial-time safety proof for every term;
3. a polynomial-time coverage proof;
4. one polynomial-cost exact residual solver or certificate per represented class;
5. an independently checkable global answer;
6. partition/disjointness evidence only when arithmetic model counts are used.

The experiments show that exact semantic classes and cube covers can both be very small on
some structured circuits. They also show that random 3-SAT can have a small semantic
quotient while requiring considerably larger DNF or decision-DAG representations. The
remaining breakthrough is a uniform polynomial construction theorem, not the finite
existence of compact covers.