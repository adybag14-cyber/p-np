# Residual-signature quotient results

This phase attacks the exponential `2^k` cutset multiplier directly.

Conditioning a cutset normally creates one residual problem for every cut assignment.
However, different cut assignments can induce exactly the same remaining input/output
relation. Such branches need to be solved only once if equality of their residual
behaviour can be certified.

The phase adds approaches A526-A585 and two executable experiments.

## Exact semantic residual signatures

For a feature or residual relation

```text
feature : Cut -> Payload -> Output
```

the complete residual signature of a cut is the function

```text
Payload -> Output.
```

Two cuts are semantically equivalent precisely when these functions are equal.
Lean proves that:

- equivalent signatures agree on every residual payload;
- they have identical reachable output images;
- one representative per signature preserves existential acceptance exactly;
- representative output tables reconstruct the complete output image;
- quotient work is bounded by representative count times maximum class work;
- semantic quotient work never exceeds raw branch work.

The semantic signature image is the smallest possible exact quotient among all
certificates that can be decoded into complete residual behaviour.

## Exact branch-quotient experiment

`cutset_residual_quotient.py` enumerates every complete input assignment for small
circuits and records an exact residual relation for each cut assignment. For input cuts,
the relation is a Boolean function over the remaining inputs. For internal-wire cuts,
each remaining input can map to no output, false, true, or both outputs.

This is an exact finite experiment, not a heuristic hash.

### Random DAG, 12 inputs and 40 gates

For the input-reuse cut order:

| Cut bits | Raw branches | Unique exact residuals | Quotient ratio |
|---:|---:|---:|---:|
| 4 | 16 | 4 | 4x |
| 5 | 32 | 4 | 8x |
| 6 | 64 | 4 | 16x |
| 7 | 128 | 2 | 64x |

For the graph-guided internal-wire order, seven cuts produced 128 raw assignments but
only 19 nonempty exact residual relations. Ninety cut assignments were impossible.

### Random DAG, 12 inputs and 60 gates

Seven input cuts produced:

```text
128 raw branches -> 9 exact residual classes
```

The quotient ratio was approximately 14.22x.

Seven internal or mixed cuts produced 37 reachable exact residual classes and 91
impossible assignments.

### Random 3-SAT circuit, 12 variables and 30 clauses

For the input-reuse order:

| Cut bits | Raw branches | Unique exact residuals | Quotient ratio |
|---:|---:|---:|---:|
| 3 | 8 | 5 | 1.60x |
| 4 | 16 | 6 | 2.67x |
| 5 | 32 | 8 | 4x |
| 6 | 64 | 8 | 8x |
| 7 | 128 | 9 | 14.22x |

At seven cuts, one exact residual class contained 118 of the 128 assignments.

The graph-guided internal cutset was less quotient-friendly: seven cuts produced 49
nonempty classes and 68 impossible assignments. This reinforces that a cutset optimized
only for elimination width need not optimize semantic quotient size.

### Random 3-SAT circuit, 14 variables and 45 clauses

Six input cuts produced:

```text
64 raw branches -> 6 exact residual classes
```

The quotient ratio was approximately 10.67x, and the largest equivalence class contained
52 assignments.

Six internal graph-guided cuts produced 37 nonempty classes and 27 impossible
assignments. Internal cuts helped table width in the previous phase, but input cuts were
far better for semantic quotienting in this instance.

## Safe structural certificates

Exact truth-table signatures are optimal but expensive to construct. The second
experiment, `cutset_structural_certificates.py`, uses a checkable certificate:

1. substitute selected input values into the circuit;
2. propagate constants;
3. apply sound Boolean simplifications;
4. canonicalize commutative gate syntax;
5. hash the resulting expression tree.

Equal structural certificates are guaranteed to denote equal residual functions. The
certificate partition can be finer than the semantic quotient, but it cannot unsafely
merge different residuals.

### Structural-certificate results

On one random 12-input, 60-gate DAG, the structural certificate matched the exact
semantic quotient at every tested cut depth. At seven cuts:

```text
128 raw branches
3 exact semantic classes
3 structural certificate classes
```

On the 12-variable random 3-SAT circuit:

```text
k=7
128 raw branches
11 exact semantic classes
26 structural classes
87.2% of available branch savings captured
```

On the harder 14-variable random 3-SAT circuit:

```text
k=6
64 raw branches
5 exact semantic classes
47 structural classes
28.8% of available branch savings captured
```

The structural system remained sound but missed many semantic equivalences. This is the
expected tradeoff: inexpensive certificates are generally finer than the optimal
semantic quotient.

## Formal optimality result

Suppose a certificate system provides:

```text
certificate : Cut -> Certificate
decode      : Certificate -> Payload -> Output
```

and Lean proves:

```text
decode (certificate cut) payload = feature cut payload.
```

Then the semantic-signature image is exactly the decoded image of the certificate set.
Consequently:

```text
number of semantic residuals <= number of certificate classes.
```

Thus no exact decodable certificate can use fewer classes than complete residual
behaviour. Structural syntax, algebraic forms, BDDs, circuit normal forms, and learned
hashes can only seek an efficiently constructible refinement that remains close to this
optimum.

## Recursive quotienting

The new Lean layer also distinguishes raw path count from memoized class count.

With two branches at every level:

```text
raw paths after depth d = 2^d
```

but if each layer contains only two canonical residual states:

```text
total memoized states across d layers = 2d.
```

This does not prove that every verifier has narrow semantic layers. It proves the exact
resource that would remove the path explosion when residual classes recur and are
memoized globally.

## Current strongest target

The new target is not merely to discover a small cutset. It is to construct:

1. a cutset or recursive conditioning policy;
2. a polynomial number of safe residual certificates;
3. one representative and exact message plan per certificate;
4. polynomial certificate-construction, quotienting, and message costs.

The experimentally optimal quotient may be tiny even when the raw cutset has exponentially
many assignments. The unresolved issue is generating or recognizing those semantic
classes without enumerating every cut assignment or every residual input.

The repository does not prove `P = NP`. It now proves that semantic residual signatures
are the optimal exact branch quotient and isolates efficient certificate discovery as the
remaining constructive problem.
