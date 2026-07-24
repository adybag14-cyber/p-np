# PIsNPOrNot — Lean 4 attack laboratory

A native Windows Lean 4 research workspace containing **750 mechanically checked approaches** to P versus NP, verified CNF transformations, executable finite experiments, and structural SAT prototypes.

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



### `ResearchThirteenth.lean` - approaches 166-180

Exact overlap accounting, common-core credit, portfolio-union bounds, separator cross-products, and monotone globally measured replacement.

### `ResearchFourteenth.lean` - approaches 181-195

Canonical semantic-state to node representations, contextual replacement, node/state cardinality transfer, and polynomial state-to-node bounds.

### `ResearchFifteenth.lean` - approaches 196-210

Least policy closures, coherent policy merging on shared residuals, uniqueness, minimality, and exact coherent composition cost.

### `ResearchSixteenth.lean` - approaches 211-225

Dominance, compatibility transfer, safe coherent-frontier pruning, frontier product bounds, and the polynomial-frontier collapse criterion.


### `ResearchSeventeenth.lean` - approaches 226-240

Feature quotients, orbit representatives, sparse support, tensor separators, isolation families, proof traces, and a heterogeneous radical-cover criterion.

### `ResearchEighteenth.lean` - approaches 241-255

Bijective coordinate transforms, affine/spectral sketches, transformed state budgets, proof-carrying radical certificates, and transform-sketch portfolios.

### `ResearchNineteenth.lean` - approaches 256-270

GF(2) basis-search cardinality, one-bit parity and k-bit syndrome bounds, concrete parity machines, polynomial candidate-basis families, and the linear-sketch collapse criterion.

### `ResearchTwentieth.lean` - approaches 271-285

Canonical equivalence, strict symmetry compression, permutation-family cost, automorphism orbits, product features, and symmetry-linear portfolios.

### `ResearchTwentyFirst.lean` - approaches 286-300

Exact restriction covers, residual solver composition, shallow-tree and common-core accounting, exact kernels, restricted proof traces, and the restriction-cover criterion.

### `ResearchTwentySecond.lean` - approaches 301-315

Involutive gates, reversible nonlinear networks, monotone network search, post-transform feature compression, checked networks, and the reversible-compiler criterion.

### `ResearchTwentyThird.lean` - approaches 316-330

Exact finite witness counting, zero/nonzero residue criteria, modulus `2^n + 1`, independent product counts, separator partitions, tensor width, and modular compilers.

## Radical paradigm experiments

The strongest experimental extension replaces original-variable queries with transformed coordinates:

- `linear_basis_obdd.py` exhaustively tests all 20,160 ordered GF(2) bases for selected four-variable functions and samples larger bases. It reduced parity-8 from 17 nodes to 3 and equality-halves from 14 to 6.
- `symmetry_residual_quotient.py` canonicalizes residual truth tables under remaining-variable permutations. Structured six-variable functions compressed by roughly 10-12x.
- `restriction_collapse.py` verifies exact restriction covers. Residuals collapse rapidly, but the exponential number of cover branches can erase the gain.
- `reversible_transform_obdd.py` adds reversible X, CNOT, and Toffoli preprocessing. It improved 16 of 17 tested six-variable functions over the exact ordinary OBDD baseline.

Full measurements and barriers are recorded in `RADICAL_PARADIGMS_RESULTS.md`.


### `ResearchTwentyFourth.lean` - approaches 331-345

Certified reversible-network candidate search, baseline-retaining beams, exact replay,
finite gate-network counting, polynomial portfolio accounting, and the learned-compiler
collapse criterion.

### `ResearchTwentyFifth.lean` - approaches 346-360

Arbitrary nonlinear Boolean observables, exact feature-fiber factorization, the 2^k
signature bound, explicit observable-evaluation cost, collision certificates, and the
uniform nonlinear-compiler criterion.

### `ResearchTwentySixth.lean` - approaches 361-375

Opposite-label witness pairs, observable separation covers, finite collision universes,
cover-union accounting, the 2^(2n) exhaustive validation barrier, and structural
separation certificates.

### `ResearchTwentySeventh.lean` - approaches 376-390

Pullback of arbitrary features through reversible bijections, exact feature-image
transport, baseline-safe original/transformed portfolios, composed certificate replay,
and the combined transform-feature compiler criterion.

## Learned compiler experiments

- `reversible_beam_search.py` crosses local plateaus while retaining the exact linear
  baseline. It beat greedy reversible search on 16 of 18 tested six-variable functions.
- `nonlinear_observable_search.py` learns exact feature quotients from parity, low-degree
  conjunction, majority, and Hamming-weight observables.
- `transform_then_observe.py` composes both approaches and motivates a baseline-safe
  portfolio because transformations help some relations but damage already-optimal
  symmetric quotients.

Full results and the precise remaining theorem are recorded in
`LEARNED_COMPILER_RESULTS.md`.

### `ResearchTwentyEighth.lean` - approaches 391-405

Reachable-image enumerators and representatives, the exact distinction between image
cardinality and image generation, the two-state verifier-output circularity theorem,
ambient-signature enumeration cost, and a reachability-aware compiler criterion.

### `ResearchTwentyNinth.lean` - approaches 406-420

Exact image composition for independent products, alternative branches, separator
buckets, bijective transforms, and finite layered machines. These lemmas show when local
reachable-image generators compose without hidden witness enumeration.

### `ResearchThirtieth.lean` - approaches 421-435

Proof-carrying exact image tables with complete rows and representative witnesses,
projection/product/branch/separator constructors, materialization accounting, output-table
circularity, and the corrected structural-image-plan criterion.

### `ResearchThirtyFirst.lean` - approaches 436-450

Representative-producing syndrome generators, exact coordinate images, rank bounds,
coordinate witness recovery, product and transform composition, output-syndrome
circularity, and the uniform polynomial syndrome-compiler criterion.

## Reachable-image experiment

`observable_image_elimination.py` eliminates witness variables from exact relational
feature factors while retaining feature outputs. Local feature systems produced exact
images with hundreds or thousands of intermediate rows. Global parity, majority,
exact-one, and verifier-output features all ended with only two rows, but generic
materialization still reached all 262,144 assignments for 18 variables. Algebraic or
combinatorial generators rescue the first three; reaching `true` for the verifier-output
feature is exactly SAT.

The corrected formulation and full measurements are recorded in
`REACHABLE_IMAGE_RESULTS.md`.

### `ResearchThirtySecond.lean` - approaches 451-465

Exact boundary messages, output maps, independent joins, alternative branches,
finite-separator elimination, root image tables, and explicit message-width accounting.

### `ResearchThirtyThird.lean` - approaches 466-480

A concrete read-once Boolean-formula language with dependent witness types, exact
bottom-up possible-output computation, a linear-work solver, and a mechanized
reconvergence counterexample showing why repeated variables require equality coupling.

### `ResearchThirtyFourth.lean` - approaches 481-495

Boolean relation-table cardinality, deterministic gate-row bounds, join and projection
accounting, equality-coupling rows, total materialization bounds, and the bounded-width
elimination criterion.

### `ResearchThirtyFifth.lean` - approaches 496-510

Exact cutset conditioning, branch-image unions, per-cut exact tables, cutset work and
obstruction arithmetic, certified branch coverage, and baseline-safe fallback.

### `ResearchThirtySixth.lean` - approaches 511-525

Immediate substitution semantics for input or internal-wire cutsets, exact residual-image
reconstruction, impossible-branch elimination, total branch-work scoring, baseline-safe
cutset selection, and monotone cutset-improvement chains.

## Circuit message and cutset experiments

- `circuit_message_width.py` performs exact relational elimination on deterministic
  circuits and passed 392 brute-force validation cases. Read-once trees stayed at 4-8
  peak rows, while random 3-SAT circuits reached 131,072 rows or the one-million cutoff.
- `circuit_cutset_conditioning.py` substitutes selected inputs before elimination and
  measures the full `2^k` branch cost.
- `circuit_graph_cutset.py` conditions input or internal wires selected by a min-fill
  graph heuristic. On one 12-variable 3-SAT circuit, one internal wire reduced peak rows
  from 65,536 to 18,514 and total checks from 236,586 to 168,935.

Full results and the remaining theorem are recorded in `CIRCUIT_MESSAGE_RESULTS.md`.

### `ResearchThirtySeventh.lean` - approaches 526-540

Exact residual signatures for cut assignments, semantic equivalence, representative
covers, exact representative-only existence and image reconstruction, impossible-branch
merging, quotient work bounds, and the semantic-quotient collapse criterion.

### `ResearchThirtyEighth.lean` - approaches 541-555

Safe decodable certificate systems, certificate covers, Boolean expression certificates,
certificate-to-signature refinement, construction and class-work accounting, baseline-safe
certificate portfolios, and the safe-certificate collapse criterion.

### `ResearchThirtyNinth.lean` - approaches 556-570

Raw branch count versus unique residual classes, strict quotient savings, layered semantic
state bounds, exponential path versus linear memo-state accounting, transition and memo
work budgets, and recursive quotient compilers.

### `ResearchFortieth.lean` - approaches 571-585

Exact certificate factorization through residual functions, the theorem that semantic
signatures are the coarsest exact decodable quotient, residual-kernel work accounting,
strict collision savings, and the residual-kernel compiler criterion.

## Residual quotient experiments

- `cutset_residual_quotient.py` computes exact residual input/output relations for every
  finite cut assignment. Seven input cuts reduced 128 raw branches to 2-9 exact residual
  classes on tested random DAG and random 3-SAT circuits.
- `cutset_structural_certificates.py` uses sound constant folding and canonical circuit
  syntax as a polynomially checkable but generally finer certificate. It captured 87.2%
  of available exact branch savings on one 12-variable random 3-SAT instance, but only
  28.8% on a harder 14-variable instance.

Full results and the semantic-optimality theorem are recorded in
`RESIDUAL_QUOTIENT_RESULTS.md`.

### `ResearchFortyFirst.lean` - approaches 586-600

Safe semantic cubes, exact cube regions, representative residual transport, complete cube
covers, singleton-cube fallback, the `3^n` candidate-space bound, and the safe-cube
compiler criterion.

### `ResearchFortySecond.lean` - approaches 601-615

The exact distinction between overlapping SAT covers and partitioned counting circuits:
existential union, duplicate overcounting, partitioned OR, decomposable AND, overlap
correction, disjointisation, family coverage, and cost composition.

### `ResearchFortyThird.lean` - approaches 616-630

Proof-carrying accepting, rejecting, and classified cube terms; exact answer transport;
complete classified plans; executable plan decisions; witness recovery; rejection
certificates; coverage obligations; and baseline-safe plan selection.

### `ResearchFortyFourth.lean` - approaches 631-645

Labelled safe covers, the semantic-class lower bound on DNF terms and DAG terminals,
`2^n` singleton and `3^n` cube-space barriers, representation portfolios, abstract
Backdoor DNF obligations, and the multi-representation compiler criterion.

### `ResearchFortyFifth.lean` - approaches 646-660

Recursive parity, one-bit-flip sensitivity, singleton monochromatic cubes, injective cover
ownership, and the exact `2^n` parity cube-cover lower bound.

### `ResearchFortySixth.lean` - approaches 661-675

Linear two-state parity DAGs, disjoint subcube-partition lower bounds, exponential versus
linear growth, literal-cost accounting, and the cube-only compiler obstruction.

### `ResearchFortySeventh.lean` - approaches 676-690

Point sensitivity, sensitive-coordinate support lower bounds, exact parity sensitivity,
full-width parity terms, the `n * 2^n` literal lower bound, and the fully sensitive-function
generalisation.

### `ResearchFortyEighth.lean` - approaches 691-705

XOR-fold agreement, the exact conventional `2n + 1` reduced OBDD size, full-tree versus
DAG sharing, and the complete parity representation profile.

### `ResearchFortyNinth.lean` - approaches 706-720

Exact two-class parity semantics, prefix residual equivalence, strict layer compression,
and minimality of the two-state residual quotient.

### `ResearchFiftieth.lean` - approaches 721-735

Complemented references, one physical node for paired parity residuals, exact `n + 1`
physical-node accounting, and complemented-edge versus cube-cover separation.

### `ResearchFiftyFirst.lean` - approaches 736-750

General semantic complement pairing, the `states <= 2 * bases` cardinality theorem,
complement-closure obstructions, parity's minimal one-base encoding, and representation
portfolios with explicit accounting conventions.

## Parity and subcube-partition phase

- `parity_representation_gap.py` exhaustively checks all partial cubes through nine
  variables and independently builds/evaluates reduced OBDDs.
- Every parity-safe cube is formally proved to be a singleton, giving exactly `2^n` terms
  and `n * 2^n` literals despite only two semantic residual classes.
- The conventional reduced OBDD has `2n + 1` nodes, while a complemented-edge BDD has
  `n + 1` physical nodes.
- `validate_dd_parity.py` reproduces the complemented count with the current
  `tulip-control/dd` pure-Python backend; it remains an optional external validation and is
  not part of the default dependency set.

The literature bridge, formal theorems, exact measurements, and external validation are
recorded in `PARITY_SUBCUBE_RESULTS.md`.

## Open-source cube and knowledge-compilation phase

- `residual_dnf_cover.py` computes exact residual labels, all monochromatic partial cubes,
  prime cubes, exact minimum DNF covers, and optimal fixed-order multi-terminal BDDs.
- The Zenodo Backdoor DNF artefact was checksum-verified and successfully run in Ubuntu
  WSL2 after replacing only the vanished `python-sat==1.8.dev13` pin with `1.8.dev12`.
- The current CPOG source was inspected, but its old pinned build is no longer reproducible
  because the referenced LeanSAT branch and commit are absent from the current upstream.

The measurements, external reproduction record, SAT/counting distinction, and revised
proof obligations are recorded in `OPEN_SOURCE_CUBE_RESULTS.md`.

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
- `ResearchThirteenth.lean` - approaches 166-180 and overlap-aware global accounting.
- `ResearchFourteenth.lean` - approaches 181-195 and canonical semantic-state/node correspondence.
- `ResearchFifteenth.lean` - approaches 196-210 and coherent least-policy closures.
- `ResearchSixteenth.lean` - approaches 211-225 and safe frontier dominance pruning.
- `ResearchSeventeenth.lean` - approaches 226-240 and exact feature/orbit quotients.
- `ResearchEighteenth.lean` - approaches 241-255 and transformed/sketched representations.
- `ResearchNineteenth.lean` - approaches 256-270 and GF(2) linear-basis sketches.
- `ResearchTwentieth.lean` - approaches 271-285 and symmetry canonicalization.
- `ResearchTwentyFirst.lean` - approaches 286-300 and restriction-cover ensembles.
- `ResearchTwentySecond.lean` - approaches 301-315 and reversible nonlinear transforms.
- `ResearchTwentyThird.lean` - approaches 316-330 and exact modular counting.
- `ResearchTwentyFourth.lean` - approaches 331-345 and certified reversible beam search.
- `ResearchTwentyFifth.lean` - approaches 346-360 and nonlinear observable quotients.
- `ResearchTwentySixth.lean` - approaches 361-375 and opposite-pair feature covers.
- `ResearchTwentySeventh.lean` - approaches 376-390 and baseline-safe transform-feature portfolios.
- `ResearchTwentyEighth.lean` - approaches 391-405 and reachability-aware quotient correction.
- `ResearchTwentyNinth.lean` - approaches 406-420 and structural image-generator composition.
- `ResearchThirtieth.lean` - approaches 421-435 and exact image tables/materialization.
- `ResearchThirtyFirst.lean` - approaches 436-450 and representative-producing syndrome generators.
- `ResearchThirtySecond.lean` - approaches 451-465 and exact boundary-message composition.
- `ResearchThirtyThird.lean` - approaches 466-480 and read-once formula message passing.
- `ResearchThirtyFourth.lean` - approaches 481-495 and exact circuit relation-width accounting.
- `ResearchThirtyFifth.lean` - approaches 496-510 and exact finite cutset conditioning.
- `ResearchThirtySixth.lean` - approaches 511-525 and internal-wire substitution/cutset search.
- `ResearchThirtySeventh.lean` - approaches 526-540 and exact semantic branch quotients.
- `ResearchThirtyEighth.lean` - approaches 541-555 and safe structural residual certificates.
- `ResearchThirtyNinth.lean` - approaches 556-570 and recursive quotient/memo accounting.
- `ResearchFortieth.lean` - approaches 571-585 and semantic quotient optimality.
- `ResearchFortyFirst.lean` - approaches 586-600 and safe semantic cube covers.
- `ResearchFortySecond.lean` - approaches 601-615 and partition-aware SAT/counting covers.
- `ResearchFortyThird.lean` - approaches 616-630 and proof-carrying classified cube plans.
- `ResearchFortyFourth.lean` - approaches 631-645 and representation lower bounds.
- `ResearchFortyFifth.lean` - approaches 646-660 and exact parity cube complexity.
- `ResearchFortySixth.lean` - approaches 661-675 and linear parity DAG separation.
- `ResearchFortySeventh.lean` - approaches 676-690 and sensitivity-based cube lower bounds.
- `ResearchFortyEighth.lean` - approaches 691-705 and conventional parity OBDD size.
- `ResearchFortyNinth.lean` - approaches 706-720 and minimal parity residual quotients.
- `ResearchFiftieth.lean` - approaches 721-735 and complemented-edge parity BDDs.
- `ResearchFiftyFirst.lean` - approaches 736-750 and general complement-pair encodings.
- `CNFCore.lean` - verified CNF restriction semantics.
- `Audit.lean` - selected theorem axiom audit.
- `FORMULATIONS.md` - compact status of all 750 approaches.
- `ACCEPTABLE_TARGET.md` - precise obligations still required for a publishable result.
- `CANONICAL_FRONTIER_RESULTS.md` - canonical-state, coherent-policy, and frontier-pruning results.
- `RADICAL_PARADIGMS_RESULTS.md` - linear, symmetry, restriction, reversible, and modular results.
- `LEARNED_COMPILER_RESULTS.md` - beam-search, nonlinear-feature, and combined-portfolio results.
- `REACHABLE_IMAGE_RESULTS.md` - exact reachable-image generation and syndrome results.
- `CIRCUIT_MESSAGE_RESULTS.md` - factorized circuit messages, reconvergence, and cutset results.
- `RESIDUAL_QUOTIENT_RESULTS.md` - exact semantic branch quotients and safe certificate results.
- `OPEN_SOURCE_CUBE_RESULTS.md` - Backdoor DNF, CPOG, exact cube-cover, and MTBDD results.
- `PARITY_SUBCUBE_RESULTS.md` - parity cube lower bounds, OBDD sharing, and complement edges.
- `Main.lean` - residual-state executable.
- `hybrid_portfolio.py` - heterogeneous structural solver portfolio.
- `certified_dag.py` - emitted and independently checked AND/OR DAG certificates.
- `optimal_obdd.py` - exact reduced OBDD minimization across variable orders.
- `xor_affine.py` and `xor_hard_search.py` - affine recognizer and stress search.
- `elimination_width.py` - Davis-Putnam order and clause-growth experiment.
- `xor_core.py` - private-variable peeling and affine-core experiment.
- `*-output.txt` - captured experiment results.
