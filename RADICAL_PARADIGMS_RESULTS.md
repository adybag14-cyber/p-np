# Radical representation phase: A226-A330

This phase deliberately abandons the assumption that SAT must be attacked by branching on original variables. It formalizes and tests five broader representation families:

1. exact feature quotients and sketches;
2. invertible GF(2) coordinate changes;
3. variable-renaming symmetry quotients;
4. restriction-cover ensembles;
5. reversible nonlinear coordinate networks;
6. exact modular model counting.

No theorem in this phase asserts `P = NP`. Each collapse theorem states the explicit uniform polynomial construction that would be sufficient.

## 1. Linear-basis decision diagrams

`linear_basis_obdd.py` replaces each queried variable with an arbitrary independent GF(2) linear form. An invertible basis maps the original assignment bijectively to new coordinates, so the truth value and number of satisfying assignments are preserved exactly.

### Experimental results

For 96 four-variable functions, every one of the 20,160 ordered GF(2) bases was tested:

| Improvement over exact optimal OBDD | Functions |
|---:|---:|
| 0 nodes | 9 |
| 1 node | 24 |
| 2 nodes | 25 |
| 3 nodes | 18 |
| 4 nodes | 19 |
| 6 nodes | 1 |

The strongest example was truth table `0x6996`:

- optimal ordinary OBDD: 9 nodes;
- linear-basis OBDD: 3 nodes;
- basis masks: `(1, 2, 4, 15)`.

For 20 five-variable samples, every sample improved under 2,500 random invertible bases. Improvements ranged from one to eight nodes.

Structured eight-variable examples:

| Function | Ordinary OBDD | Linear basis | Saving |
|---|---:|---:|---:|
| parity | 17 | 3 | 14 |
| equality of two four-bit halves | 14 | 6 | 8 |
| majority | 22 | 22 | 0 |
| exact-one | 17 | 17 | 0 |
| four-pair inner product | 16 | 16 | 0 |

### Formal conclusion

Lean proves:

- every bijective coordinate transform preserves existential acceptance;
- a one-bit exact feature has at most two reachable states;
- parity factors through one bit;
- a `k`-bit exact sketch has at most `2^k` states;
- a relation depending only on a syndrome is safely quotientable.

The construction barrier is also explicit: all ordered `n`-tuples of Boolean masks form a space of size `2^(n*n)`. The useful basis must therefore be found without exhaustive search.

## 2. Symmetry residual quotients

`symmetry_residual_quotient.py` enumerates all `3^6` partial assignments and canonicalizes each residual truth table under every permutation of its remaining variables.

| Function | Raw residuals | Symmetry quotient | Compression |
|---|---:|---:|---:|
| parity-6 | 127 | 13 | 9.77x |
| majority-6 | 218 | 19 | 11.47x |
| exact-one-6 | 183 | 17 | 10.76x |
| equality halves | 253 | 25 | 10.12x |
| inner product | 307 | 30 | 10.23x |
| K4 contains triangle | 313 | 28 | 11.18x |
| K4 connected | 323 | 26 | 12.42x |

Random six-variable functions still compressed by approximately 2.7-3.0x, mostly because low-dimensional residuals become isomorphic.

Lean proves:

- canonical images never exceed raw state sets;
- one genuine collision gives strict compression;
- invariant answers factor through canonical states;
- relabeling by an equivalence preserves existential acceptance;
- automorphism orbits safely merge invariant states.

The full permutation family has `n!` members. A useful result therefore needs a polynomial canonicalizer or polynomial generator method rather than enumeration.

## 3. Restriction-cover ensembles

`restriction_collapse.py` verifies exact covers by assigning every value to a chosen six-variable set and checking that the OR of all residual SAT answers equals the original answer.

### Pigeonhole 7 into 6

- baseline DPLL calls: 1,757;
- after fixing six variables, 90.6% of 64 residuals were terminal;
- total residual calls: 1,936.

The residuals became dramatically easier, but exact coverage paid for 64 branches and lost overall.

### Random 32-variable 3-SAT samples

Random restrictions fixing half the variables made approximately 87% of residuals terminal or 2-CNF. Fixing 75% made every sampled residual terminal. This is structural evidence only: those samples are not a complete cover.

Lean proves exact restriction-cover soundness and the cost equation

`restriction count * residual-solver cost`.

The obstruction is therefore sharp: residual simplification is real, but a useful cover must contain only polynomially many restrictions.

## 4. Reversible nonlinear preprocessing

`reversible_transform_obdd.py` starts with an invertible GF(2) basis and greedily appends reversible X, CNOT, and Toffoli gates. Every network is a bijection, so all assignments and satisfying assignments are preserved exactly.

| Function | Ordinary | Linear | Nonlinear reversible |
|---|---:|---:|---:|
| parity-6 | 13 | 3 | 3 |
| majority-6 | 14 | 14 | 13 |
| exact-one-6 | 13 | 11 | 10 |
| equality halves | 11 | 5 | 5 |
| inner product-3 | 12 | 12 | 10 |
| threshold 2 of 6 | 12 | 12 | 11 |
| exact-two-6 | 16 | 13 | 10 |

Among ten random six-variable functions, nine improved over the best ordinary OBDD. One fell from 24 nodes to 16 after a five-gate reversible network.

Lean proves:

- every involution produces an exact reversible transform;
- reversible gates compose into a network transform;
- transformed existential acceptance is unchanged;
- monotone network search cannot exceed its seed cost;
- compression must occur in the post-transform feature image, because a bijection alone preserves assignment cardinality.

This is the strongest broad experimental paradigm in the project so far. The missing theorem is a polynomial-time method that constructs a polynomial-size useful network for every SAT instance.

## 5. Exact modular model counting

For an `n`-bit witness relation, the number of accepting witnesses is at most `2^n`. Lean proves:

`count mod (2^n + 1) = 0` if and only if `count = 0`.

Therefore one exact residue modulo `2^n + 1` decides whether a witness exists. There is no probability of error and no need for multiple primes.

This does not make SAT easy by itself. Computing that residue is exact model counting in disguise. The remaining target becomes an efficient modular tensor contraction or another compressed residue compiler.

## Combined research target

The best current target is a heterogeneous compiler that may choose among:

- linear or affine sketches;
- symmetry canonicalization;
- reversible nonlinear preprocessing;
- polynomial restriction covers;
- modular tensor contraction;
- the earlier adaptive coherent-policy DAGs.

A complete result needs a polynomial-time certificate that at least one route produces a polynomial state space for every NP verifier. The project now formalizes correctness and cost transfer for each route separately and for finite portfolios.
