# What an acceptable P versus NP proof must still establish

The workspace now proves many finite and structural facts, but it does **not**
claim that P equals NP or that P differs from NP.  A publishable result must
close all of the following obligations in one standard complexity model.

## 1. Uniform executable construction

It is not enough to prove that each SAT instance has a small semantic quotient,
proof tree, circuit, or decision DAG.  One algorithm must construct the object
from the encoded input.  The construction itself may not inspect an exponential
truth table or invoke an NP oracle.

## 2. Exact semantics

For every CNF formula `F`, the constructed object must return `true` exactly
when `F` has a satisfying assignment.  The Lean project now proves the concrete
local rules needed for such a construction:

- restriction removes the selected variable;
- Shannon branching preserves satisfiability;
- assignments for variable-disjoint components can be merged;
- disjoint conjunction decomposition is exact;
- locally valid AND/OR proof trees are globally exact.

## 3. Polynomial construction and evaluation time

A size bound alone is insufficient if finding or checking each node is hard.
The number of machine steps used to:

1. normalize a residual,
2. choose a transformation,
3. verify its local certificate,
4. locate or construct its memo key, and
5. evaluate the completed DAG

must be bounded by one polynomial in the original input length.

## 4. Polynomial state bound

`ResearchNinth.lean` proves that every exact memoization scheme has at least as
many states as there are distinct residual completion functions.  Therefore a
successful equality proof must establish a uniform polynomial bound on those
residuals, or use a richer representation whose evaluation avoids enumerating
them while still running in polynomial time.

The exact unresolved statement is conceptually:

> There is a uniform deterministic algorithm which, for every encoded CNF
> formula, constructs and evaluates an exact proof-carrying decision object in
> polynomial time and visits only polynomially many states.

Proving only that favourable orders or small cores exist is not enough; the
algorithm must find them efficiently.

## 5. Complexity-class bridge

Finally, the SAT algorithm must be connected to a conventional machine model
and to the standard polynomial-time reduction from every NP language to SAT.
Only then does a polynomial SAT algorithm imply `P = NP`.

## Current closest candidate

The most defensible candidate pipeline currently represented in the workspace
is:

1. canonical CNF normalization;
2. unit and pure-literal propagation;
3. entailed learning and subsumption;
4. private-variable and autarky peeling;
5. variable-disjoint AND decomposition;
6. proof-carrying structural dispatch;
7. Shannon OR branching on the residual core;
8. canonical semantic memoization;
9. reuse of equal residual completion functions.

The local correctness of these ingredients is increasingly formalized.  The
remaining global theorem is a polynomial bound on construction time and on the
number of irreducible semantic residuals for every input.

## Formal conditional theorem now available

`ResearchTenth.lean` packages these requirements into a single non-circular
conditional theorem.  Its compiler must expose witness length, finite state
count, construction cost, exact semantics, and polynomial bounds.  The theorem
proves equality of the language classes only after receiving a separate bridge
showing that such a compiler executes in the conventional definition of P.