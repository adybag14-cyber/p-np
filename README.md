# PIsNPOrNot — Lean 4 attack laboratory

A native Windows Lean 4 research workspace containing **165 mechanically checked approaches** to P versus NP, verified CNF transformations, executable finite experiments, and structural SAT prototypes.

The project does **not** claim a proof of `P = NP` or `P != NP`. It is designed to expose exactly which additional theorem each attempted route would require.

## Local toolchains

Everything is installed below the project root:

- Workspace: `D:\pisnpornot`
- elan 4.2.3: `D:\pisnpornot\.elan`
- Lean 4.32.0
- Lake 5.0.0
- Mathlib v4.32.0
- Python 3.11 virtual environment: `D:\pisnpornot\.venv`
- Python dependencies: NumPy 2.4.6 and NetworkX 3.6.1

## Reproduce

```powershell
cd D:\pisnpornot

.\setup.ps1
.\setup-python.ps1
.\build.ps1
.\verify.ps1
.\run.ps1
.\run-research.ps1
```

## Formalization layers

### `PIsNPOrNot.lean` — approaches 1–15

The first layer tests direct witness-search and compression routes:

1. exhaustive witness enumeration;
2. prefix self-reduction;
3. random sampling;
4. isolation hashing;
5. meet-in-the-middle splitting;
6. separator dynamic programming;
7. symmetry quotienting;
8. behavioural traces;
9. state merging;
10. arithmetization;
11. monotone satisfiability;
12. low Boolean-rank aggregation;
13. kernelization;
14. candidate generators;
15. residual-state automata.

Lean verifies the exact finite algorithms and reductions. The dominant obstruction is that an arbitrary compact verifier can still induce exponentially many acceptance-relevant residual states.

### `ResearchNext.lean` — approaches 16–32

The second layer establishes barriers and order-sensitive opportunities:

- trivial acceptance quotients versus recoverable trace lower bounds;
- equality-row and distinguishable-residual cardinality lower bounds;
- singleton hitting-set and black-box spike barriers;
- truth-table advice counting;
- compositional local residual models;
- variable-order sensitivity and frontier signatures;
- Shannon branching and forced literals;
- isomorphism merging;
- certified structural dispatch and finite solver portfolios.

The important experimental observation is that variable ordering can dramatically alter residual width. Equality on two six-bit halves has width 64 in the split order but width 3 in a paired order.

### `ResearchThird.lean` — approaches 33–47

The third layer develops **certified decomposition plus canonical residual search**:

- totality and soundness of a covered solver portfolio;
- exact disjunctive and independent conjunctive decomposition;
- dominance pruning;
- semantic normalization and canonical memo keys;
- backdoor enumeration and explicit polynomial accounting;
- entailed clause learning and Boolean resolution;
- semantics-preserving preprocessing pipelines;
- forced-descent versus full binary branching cost;
- representative families;
- exact decomposition trees;
- structural recognition with residual fallback.

The logical composition works cleanly. The missing theorem is a uniform polynomial-size cover of every NP instance by these tractable pieces.

### `ResearchFourth.lean` — approaches 48–55

The fourth layer adds canonical affine structure and proof-carrying recognition:

- exact four-clause encoding of a three-variable XOR equation;
- reversible Boolean Gaussian row addition;
- zero-row contradiction detection;
- dependent proof-carrying recognizers;
- exact affine dispatch with fallback;
- polynomial cost certificates;
- finite unions of tractable structural families;
- an abstract uniform certified-cover collapse criterion.

### `ResearchAgenda.lean` — approaches 56–58

The fifth layer moves from solver components to exact class-level statements:

- a uniform certified polynomial-decider cover plus the standard inclusion `P ⊆ NP` yields equality of the two language classes;
- under explicit bridges between class membership and polynomial deciders, `P = NP` is equivalent to every NP language having such a decider;
- if `P ≠ NP`, at least one NP language must escape every certified polynomial decider.

This does not assume the missing deciders. It localizes the global obstruction without hiding it in a field or axiom.
### `ResearchFifth.lean` — approaches 59–68

The sixth layer formalizes concrete SAT reductions and their costs:

- separator conditioning;
- certified pure-literal elimination;
- subsumption and autarky pruning;
- exact Davis–Putnam variable elimination through all pairwise resolvents;
- quadratic local resolvent bounds under bounded elimination width;
- total work bounds for bounded elimination schedules;
- three-budget composition for preprocessing, leaf count, and leaf cost;
- an obstruction theorem localizing excessive total cost to an expensive residual leaf;
- polynomial enumeration across logarithmic-size interfaces.

These results sharpen the frontier from “find structure” to explicit parameters that must remain polynomial: separator bits, elimination width, number of leaves, and worst residual cost.
### `ResearchSixth.lean` — approaches 69–75

The seventh layer isolates peelable private variables and the residual core:

- any private variable in a locally solvable constraint can be eliminated without constraining the remainder;
- every 3-XOR equation is solvable for any chosen one of its variables;
- private XOR leaf equations therefore peel exactly;
- chains of equisatisfiable peeling steps preserve the original answer;
- all remaining difficulty is localized to the unpeeled core;
- polynomial peeling plus a polynomially enumerable core gives polynomial total work;
- if peeling is cheap but total work is excessive, the core itself must be expensive.
## Verified CNF core

`CNFCore.lean` defines literals, clauses, CNFs, variable restriction, and evaluation. Lean proves that restricting a formula by an assigned variable preserves evaluation for every agreeing assignment and preserves the corresponding satisfiability branch.

This is the formally checked semantic core used by the DPLL experiments.

## Computational findings

### Residual-state growth

The executable `pnp_experiments` compares three machines:

- parity: two reachable states;
- capped counting: linear growth followed by a fixed cap;
- identity history: all `2^n` states.

This demonstrates that residual compression is powerful but not automatic.

### Residual-width search

`residual_search.py` exhaustively studies all 65,536 Boolean functions on four variables and samples larger functions. Most arbitrary functions retain substantial width even after reordering, while structured functions such as parity, exact-one, majority, and paired equality have small tuned widths.

### Memoized symbolic DPLL

`memo_dpll.py` combines canonical CNF normalization, unit propagation, component splitting, memoization, and a structural branching heuristic. Small cases are cross-checked by brute force.

### Isomorphism-aware memoization

`iso_dpll.py` merges isomorphic residual CNFs. On pigeonhole formulas it reduced representatives, for example:

- pigeonhole 8 into 7 holes: 282 exact states to 175 isomorphism representatives;
- pigeonhole 9 into 8 holes: 599 exact states to 370 representatives.

The growth remains substantial, so symmetry helps without proving a polynomial bound.

### Certified structural dispatch

`structural_dispatch.py` recognizes complete CNF encodings of left-covering bipartite matching and solves them through maximum matching. The recognizer validates the entire clause language before dispatching.

For pigeonhole 8 into 7 holes:

- plain memoized DPLL: 5,354 states and roughly four seconds;
- certified matching dispatch: one recognized structural instance and roughly seven milliseconds.

### Hybrid structural portfolio

`hybrid_portfolio.py` combines:

- Horn SAT;
- dual-Horn SAT;
- 2-SAT through implication-graph SCCs;
- disjoint exact-one blocks;
- canonical 3-XOR plus Gaussian elimination;
- bipartite matching;
- connected-component decomposition;
- memoized DPLL fallback.

It passed **1,440 brute-force comparisons** on small generated instances. A satisfiable 200-variable mixed formula exercised Horn, dual-Horn, 2-SAT, exact-one, affine XOR, decomposition, and DPLL fallback in one run.

### Davis–Putnam elimination width

`elimination_width.py` passed 600 brute-force checks and measured exact clause growth under five orders. On one random 24-variable 3-SAT instance, natural elimination reached 1,094 clauses and 40,448 pair incidences, while min-product ordering held the peak to 198 clauses and 1,240 incidences. On a sparse 24-variable XOR instance, natural ordering generated 22,713 raw resolvents, while greedy peeling generated only 80 and retained none.

### Private-variable affine cores

`xor_core.py` passed 760 full-system versus peeled-core checks. In finite random 240-variable samples, cores were empty in every trial through density 0.55, mostly empty at 0.70, and large in every trial from 0.90 upward. This is experimental evidence only, not an asymptotic theorem; it points to the residual core as the correct target for further compression or decomposition.
### Affine XOR dispatch

`xor_affine.py` recognizes canonical four-clause encodings of 3-XOR equations and solves the resulting system by Gaussian elimination over GF(2). It passed 400 brute-force comparisons.

`xor_hard_search.py` then searched 720 sparse random and planted systems. The tested DPLL implementation handled these particular encodings surprisingly well—the worst sampled case used 63 states—so this experiment did not reveal an exponential separation. The affine recognizer remains exact, but XOR alone is not the missing family for this solver.

## Current strongest formulation

The experiments and Lean theorems point to a **certified structural cover conjecture**:

> Every NP verifier instance can be transformed, uniformly in polynomial time, into a polynomial-size decomposition whose leaves are either members of certified polynomial-time structural families or admit polynomial-state canonical residual models.

If such a theorem were proved with explicit size and construction bounds, the Lean composition theorems would turn it into `NP ⊆ P`, and therefore `P = NP` together with the standard inclusion `P ⊆ NP`.

The unresolved part is coverage. Individual families, transformations, and dispatch mechanisms are not enough: arbitrary instances must be shown to enter the portfolio after only polynomially much decomposition, normalization, learning, and residual construction.

## Integrity

- No `sorry` proofs.
- No project-defined `axiom` declarations.
- Lean compiles every library target.
- `Audit.lean` prints the axiom dependencies of selected frontier theorems.
- `verify.ps1` scans every Lean source file for forbidden placeholders and project axioms.

Lean's normal foundations may appear in audit output, including `propext`, `Classical.choice`, and `Quot.sound`. These are not assumptions about P versus NP.


### `ResearchSeventh.lean` - approaches 76-90

Proof-carrying AND/OR trees and DAGs, local-to-global correctness, semantic memo
keys, layered-width accounting, and a uniform exact DAG-cover criterion.

### `ResearchEighth.lean` - approaches 91-105

Concrete CNF theorems: restriction removes the branch variable, unused-bit
invariance, exact Shannon branching, assignment merging for variable-disjoint
components, exact AND decomposition, and valid CNF proof trees.

### `ResearchNinth.lean` - approaches 106-120

Semantic residual minimality. Every exact memoization state space is at least as
large as the image of distinct residual completion functions; the residual
function itself is the canonical exact state.


### `ResearchTenth.lean` - approaches 121-135

An explicit acceptable-proof skeleton: exact ordered witness machines,
polynomial layer/state/construction accounting, a non-circular compiled-language
predicate, the conditional `P = NP` theorem, and the corresponding obstruction
if the classes are separated.



### `ResearchEleventh.lean` - approaches 136-150

Adaptive residual branching over partial assignments. The next variable may depend
on the current residual. Lean proves adaptive Shannon branching, exact rank decrease,
local-to-global tree correctness, depth bounded by unset variables, semantic alias
safety, polynomial layer accounting, and an explicit adaptive compiler criterion.

### `ResearchTwelfth.lean` - approaches 151-165

Global policy accounting. The adaptive model embeds every fixed-order model, safe
selection never exceeds its ordered baseline, shared-state overlap is measured by
set union/intersection, monotone improvement chains preserve the baseline bound,
and polynomial policy portfolios compose.

## Adaptive paradigm experiment

Two separate experiments are retained because they reveal different facts:

- `adaptive_semantic_dag.py` chooses each variable by a local recurrence. It often
  produces a larger shared DAG than the exact optimal OBDD, proving that local tree
  cost is the wrong objective for a globally shared graph.
- `adaptive_policy_search.py` begins from the exact best OBDD and accepts an override
  only after rebuilding and measuring the entire DAG. In a deterministic sample of
  2,056 four-variable tables it found 17 strict one-node improvements. It also found
  improvements in 7/60 random five-variable functions and 2/15 random six-variable
  functions. No tested candidate was allowed to become worse than its OBDD baseline.

This establishes a real but limited paradigm advantage: residual-dependent order can
strictly beat every fixed order, but discovering the useful overrides is itself a
global optimization problem.


## Main files

- `PIsNPOrNot.lean` — approaches 1–15 and residual synthesis.
- `ResearchNext.lean` — approaches 16–32 and structural barriers.
- `ResearchThird.lean` — approaches 33–47 and decomposition portfolio logic.
- `ResearchFourth.lean` — approaches 48–55 and affine/proof-carrying dispatch.
- `ResearchAgenda.lean` — approaches 56–58 and the exact set-level frontier.
- `ResearchFifth.lean` — approaches 59–68 and concrete SAT elimination/accounting.
- `ResearchSixth.lean` — approaches 69–75 and private-variable/core localization.
- `ResearchSeventh.lean` - approaches 76-90 and proof-carrying AND/OR DAGs.
- `ResearchEighth.lean` - approaches 91-105 and concrete CNF proof trees.
- `ResearchNinth.lean` - approaches 106-120 and semantic residual minimality.
- `ResearchTenth.lean` - approaches 121-135 and the acceptable ordered-residual compiler skeleton.
- `ResearchEleventh.lean` - approaches 136-150 and adaptive partial-assignment branching.
- `ResearchTwelfth.lean` - approaches 151-165 and global policy accounting.
- `CNFCore.lean` - verified CNF restriction semantics.
- `Audit.lean` - selected theorem axiom audit.
- `FORMULATIONS.md` - compact status of all 165 approaches.
- `ACCEPTABLE_TARGET.md` - precise obligations still required for a publishable result.
- `Main.lean` - residual-state executable.
- `hybrid_portfolio.py` - heterogeneous structural solver portfolio.
- `certified_dag.py` - emitted and independently checked AND/OR DAG certificates.
- `optimal_obdd.py` - exact reduced OBDD minimization across variable orders.
- `xor_affine.py` and `xor_hard_search.py` - affine recognizer and stress search.
- `elimination_width.py` - Davis-Putnam order and clause-growth experiment.
- `xor_core.py` - private-variable peeling and affine-core experiment.
- `*-output.txt` - captured experiment results.
