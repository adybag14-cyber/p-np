# Canonical Semantic-State and Coherent Frontier Results

This phase extends the adaptive semantic-width approach from local policy moves to exact coherent policy composition.

## 1. Overlap is exact accounting, but not a sufficient heuristic

For child reachable-state sets `L` and `R`, Lean proves:

```text
|L union R| + |L intersection R| = |L| + |R|.
```

Therefore overlap is a real sharing credit. With equal child-state sums, greater overlap strictly lowers union cost.

However, the `overlap_potential.py` experiment showed that overlap alone is not a useful standalone policy rule:

- 804 truth tables were tested across 4 and 5 variables.
- 6,539 single-residual overrides were checked against exact optimal-OBDD baselines.
- Lower local semantic-union cost found 23 of 32 true global improvements, but precision was only 17%.
- A simple overlap-increase rule found none of the true improvements.

Most successful moves reduced total descendant work while also reducing overlap. The correct objective is the complete globally reachable semantic-state set, not overlap by itself.

## 2. Canonical semantic signatures tracked concrete node count exactly

`contextual_interning.py` tested 6,597 single-policy overrides.

In every tested case, the sign of the globally reachable reduced-signature change matched the sign of the reduced DAG-node change:

```text
semantic shrink -> node shrink: 38
semantic equal  -> node equal:  1,582
semantic growth -> node growth: 4,977
all other sign combinations:    0
```

Every strict improvement was a semantic-state reduction. No improvement was caused by an unexplained node-interning collision while semantic-state count stayed fixed or grew.

This motivated `ResearchFourteenth.lean`, where a proof-carrying canonical representation includes:

- a finite set of semantic states;
- a finite set of concrete nodes;
- an injective state-to-node encoding;
- an exact image theorem.

Lean then proves the node and semantic-state cardinalities are equal, so all `<`, `<=`, and `=` comparisons transfer exactly.

## 3. Exact coherent adaptive-policy dynamic programming

A policy must make one choice for each residual signature. Child policies may be combined only when they agree on all signatures appearing in both child closures.

`ResearchFifteenth.lean` formalizes:

- policy-closed reachable sets;
- least closure certificates;
- uniqueness and cardinality minimality of least closures;
- policy agreement on finite sets;
- finite-domain policy merging;
- compatibility on overlapping child closures;
- closure of the merged policy over the union;
- exact overlap accounting for coherent composition.

`coherent_policy_dp.py` computes the exact nondominated coherent-policy frontier for small Boolean functions.

On 64 deterministic four-variable functions:

```text
best fixed-order OBDD = exact adaptive optimum: 60
exact adaptive saves one node:                  4
```

The monotone greedy adaptive search missed 3 of those 4 exact improvements.

Examples:

```text
table 0x4f68: ordered 10, greedy 10, exact adaptive 9
table 0xb2e1: ordered 10, greedy 10, exact adaptive 9
table 0xd342: ordered 9,  greedy 9,  exact adaptive 8
table 0xf819: ordered 10, greedy 9,  exact adaptive 9
```

The coherent frontier contained as many as 408 candidates for a four-variable function. This shows that exact adaptive optimization can improve on both fixed order and greedy search, but the policy frontier itself can grow rapidly.

## 4. Safe dominance pruning

`ResearchSixteenth.lean` formalizes a candidate as:

- a finite reachable-state closure;
- one policy choice for every relevant state.

Candidate `A` dominates candidate `B` when:

1. `A.states` is a subset of `B.states`;
2. `A` and `B` make identical choices on every state retained by `A`.

Lean proves:

- dominance is reflexive and transitive;
- if `B` is compatible with an external policy, then dominating `A` is also compatible;
- `A union external` is a subset of `B union external`;
- the composed state cost cannot increase;
- proper inclusion gives a strict saving;
- dominated candidates may therefore be pruned without losing an optimal compatible composition.

## Current target

The remaining theorem is now:

> For every SAT instance or NP verifier, construct in polynomial time a polynomial-size undominated coherent-policy frontier, or directly construct one polynomial-size coherent policy closure.

The local correctness, exact state/node correspondence, coherent merging, overlap accounting, and dominance pruning are all mechanically checked. The unresolved issue is a universal polynomial bound on the exact or sufficiently complete coherent frontier.
