# Adaptive Semantic-Width Paradigm

## Question

Can a solver beat every single global variable order by allowing each residual
subproblem to choose its own next variable?

The formal answer is **yes in principle**: fixed-order OBDDs are a subset of the
adaptive model. The computational answer is more subtle: the choice objective must
measure the globally shared DAG, not an independently expanded decision tree.

## Fully checked Lean results

`ResearchEleventh.lean` proves:

1. Any currently unset variable gives an exact Shannon split.
2. The selected variable may be different at every residual state.
3. Assigning it removes exactly one unassigned variable.
4. Every valid adaptive tree has depth at most the number of unset variables.
5. Completion-equivalent partial assignments may be merged safely.
6. Polynomial semantic width times polynomial depth gives polynomial DAG size.
7. An exact adaptive compiler with an explicit polynomial node bound decides its
   residual acceptance problem correctly.

`ResearchTwelfth.lean` proves:

1. Every fixed-order policy can be embedded into an adaptive model at equal cost.
2. Therefore a genuinely optimal adaptive result cannot be worse than the best
   fixed-order baseline.
3. DAG sharing is governed by the union of reachable child-state sets.
4. Nonempty child-state intersection gives a strict saving over separate expansion.
5. A locally smaller recurrence score need not imply a globally smaller DAG.
6. Starting from an exact baseline and accepting only globally smaller exact
   candidates preserves both correctness and the baseline cost guarantee.
7. Polynomially many polynomial-cost policies still have polynomial total cost.

## Experiment 1: local adaptive recurrence

`adaptive_semantic_dag.py` chooses each residual variable by minimizing a recursive
local tree score and only afterward shares identical semantic residuals.

This frequently performed worse than the exact best OBDD order:

- In all 65,536 four-variable functions, the local adaptive result was larger than
  the optimal OBDD for a substantial fraction of functions.
- Random five- and six-variable functions showed the same failure pattern.
- The structured eight-variable functions tested showed no advantage.

This is not evidence against adaptive branching. It is evidence that the objective
was wrong: it minimized duplicated child work rather than the union of globally
reachable shared states.

## Experiment 2: monotone global policy search

`adaptive_policy_search.py` uses a safer procedure:

1. Compute the exact optimal OBDD order.
2. Use that order as the adaptive policy baseline.
3. Change one residual-specific variable choice.
4. Rebuild and verify the entire DAG.
5. Keep the override only when the complete DAG is strictly smaller.

Results:

- Deterministic sample of 2,056 four-variable tables plus known hard OBDD tables:
  17 strict improvements, each saving one node.
- 60 random five-variable functions: 7 strict improvements.
- 15 random six-variable functions: 2 strict improvements.
- Tested parity, majority, exact-one, equality, inner product, and three
  eight-variable CNFs: no improvement over the exact best OBDD.
- No candidate became worse than its OBDD baseline because worsening moves were
  rejected by construction.

## What this establishes

Residual-dependent ordering can strictly beat every fixed global order on concrete
Boolean functions. Therefore the ordered-BDD frontier is not the final semantic
compression frontier.

However, the improvements found so far are small and sparse. The new obstacle is:

> Efficiently discover a polynomial-size globally shared adaptive policy, rather
> than merely proving that a good residual-dependent policy may exist.

A useful global objective must account for:

- overlap between descendant semantic-state sets;
- future sharing created or destroyed by a variable choice;
- decomposition into independent components;
- certified structural leaves;
- construction cost of the policy itself.

## Honest status

The adaptive paradigm has passed three meaningful tests:

1. **Soundness:** formalized in Lean.
2. **Strict expressiveness advantage:** witnessed computationally over optimal OBDD.
3. **Failure-mode identification:** local recurrence optimization is formally and
   experimentally separated from global DAG optimization.

It has not yet supplied the universal polynomial construction required to prove
`P = NP`. That remains the central theorem to discover.
