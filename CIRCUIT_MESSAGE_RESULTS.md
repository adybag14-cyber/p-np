# Circuit Message Passing and Internal Cutsets

This phase replaces the vague requirement “the final feature image is small” with an explicit factorized construction model. A circuit is represented by exact local gate relations. Variable elimination joins those relations and projects hidden variables until only the output remains.

The repository does **not** claim a proof of `P = NP`. The objective is to identify a structural theorem that would be sufficient without hiding witness search inside a feature oracle.

## Formal results: A451–A465

`ResearchThirtySecond.lean` defines an exact boundary message:

```lean
structure Message (feature : Boundary -> Payload -> Output) where
  rows : Boundary -> Finset Output
  exact : forall boundary output,
    output ∈ rows boundary <->
      exists payload, feature boundary payload = output
```

Lean proves exact constructors for:

- mapping outputs;
- joining conditionally independent children over a shared boundary;
- unioning alternative branches;
- hiding a finite separator by union over its assignments;
- converting a unit-boundary message into an exact root image table.

It also proves the corresponding width accounting:

- output maps cannot increase row count;
- independent joins multiply child row counts;
- branch unions cost at most the child-row sum;
- hiding a separator costs at most separator assignments times residual width.

## Formal results: A466–A480

`ResearchThirtyThird.lean` gives a fully concrete positive class: read-once Boolean formula trees.

The formula has a dependent witness type. Every binary node receives independent witnesses for its two children. A bottom-up `possible` function computes the reachable Boolean outputs of every subtree.

Lean proves:

```lean
output ∈ possible formula ↔
  ∃ witness, evaluate formula witness = output
```

Consequences:

- every subtree has at most two possible output states;
- the executable satisfiability solver is exact;
- total message work is at most four times the formula-node count.

This proves linear-time exact message passing for arbitrary unary and binary Boolean operations on read-once trees.

### Reconvergence counterexample

Lean also formalizes why this result does not automatically extend to circuits with reused variables.

The relaxed formula with independent leaves can satisfy:

```text
x₁ ∧ ¬x₂
```

by choosing `x₁ = true` and `x₂ = false`.

The shared-variable circuit:

```text
x ∧ ¬x
```

has no satisfying witness. Treating both occurrences as independent therefore changes the language. Equality coupling or a shared boundary is mandatory.

## Formal results: A481–A495

`ResearchThirtyFourth.lean` formalizes relation-table width.

- A width-`k` Boolean boundary has exactly `2^k` assignments.
- Any explicit relation over that boundary has at most `2^k` rows.
- Deterministic unary, binary, and ternary Boolean gates require at most 2, 4, and 8 rows respectively.
- Projection cannot increase row count.
- Total materialization is bounded by step count times maximum table size.
- Equality coupling itself has only two satisfying Boolean rows.

The important negative statement is that a final output image of size two says nothing about intermediate table width. The intermediate relation may still contain exponentially many rows.

## Formal results: A496–A510

`ResearchThirtyFifth.lean` proves exact cutset conditioning.

For a cutset value `c`, let `Image(c)` be the exact output image of the residual instance. Lean proves:

```text
global image = union of Image(c) over every cut assignment
```

and:

```text
|global image| ≤ number of cut assignments × residual image width.
```

The total exact work must include all cut branches. A `k`-bit cutset has exactly `2^k` assignments.

## Formal results: A511–A525

`ResearchThirtySixth.lean` strengthens cutset semantics to immediate substitution.

- Substituting a cut value is exact Shannon decomposition.
- The original output image is exactly the union of the substituted residual images.
- Exact residual tables reconstruct the original image table.
- Impossible internal-wire assignments contribute empty branches.
- Internal wires are legitimate cut coordinates when a decomposition can rebuild every complete assignment.
- Total work is the sum over all substituted branches.
- Halving residual work only breaks even with one extra branch bit.
- Lower peak width alone does not imply lower total work.
- Baseline-safe selection keeps a candidate only when its fully measured total work is lower.

## Exact circuit experiment

`circuit_message_width.py` encodes each deterministic gate as a local relational factor and eliminates all variables except the output.

It passed **392 brute-force validation cases**.

| Circuit | Inputs | Gates | Peak rows | Peak scope |
|---|---:|---:|---:|---:|
| Balanced AND tree | 32 | 31 | 4 | 3 |
| Balanced XOR tree | 32 | 31 | 4 | 3 |
| Parity chain | 32 | 31 | 4 | 3 |
| Majority tree | 27 | 13 | 8 | 4 |
| Random read-once tree | 32 | 31 | 4 | 3 |
| Random DAG | 12 | 60 | 960 | 13 |
| Random 3-SAT circuit | 12 | 101 | 131,072 | 20 |
| Random 3-SAT circuit | 14 | 148 | over 1,000,000 | at least 22 |

Every case has only one Boolean output, so its final image is at most `{0,1}`. The table growth occurs entirely before the final projection.

## Input cutset conditioning

`circuit_cutset_conditioning.py` substitutes selected inputs immediately into every factor before elimination.

On one 12-variable random 3-SAT circuit:

| Cut bits | Branches | Peak rows | Total join checks |
|---:|---:|---:|---:|
| 0 | 1 | 131,072 | 679,284 |
| 1 | 2 | 65,536 | 695,000 |
| 2 | 4 | 32,768 | 719,576 |
| 5 | 32 | 4,096 | 725,023 |

Five cuts reduced peak memory by a factor of 32 while total relation checks remained close to the original run. This is a real space reduction, but not an asymptotic proof: the branch factor is also 32.

## Graph-guided internal-wire cutsets

`circuit_graph_cutset.py` allows input variables and internal gate wires as cut coordinates. A greedy min-fill score chooses the variable whose removal most reduces the circuit primal graph.

For a 12-variable random 3-SAT circuit:

| Cut wires | Graph width | Peak rows | Total checks |
|---:|---:|---:|---:|
| 0 | 19 | 65,536 | 236,586 |
| 1 | 18 | 18,514 | 168,935 |
| 2 | 17 | 9,554 | 154,521 |
| 6 | 13 | 708 | 251,358 |

The first internal-wire cut improved both memory and total measured work. Six wires reduced peak rows by more than 90 times while keeping total checks near baseline.

The harder 14-variable 3-SAT circuit still exceeded the one-million-row cutoff in many branches after five graph-guided cuts. This is important negative evidence: small finite cutsets are not automatically enough.

## Current precise target

The strongest remaining route is:

```text
factorized verifier circuit
→ exact local gate relations
→ polynomial-time cutset / elimination-plan discovery
→ polynomially many branches
→ polynomial residual table width in every branch
→ exact output image
```

The missing theorem is:

> Every polynomial-size NP verifier circuit has a polynomial-time discoverable cutset and elimination plan for which the number of branches times the exact residual relation-construction work is polynomial in the input length.

The project proves every semantic and cost-composition bridge around that statement. It does not prove the universal cutset-width theorem itself.
