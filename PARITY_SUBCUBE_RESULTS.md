# Parity, subcube partitions, and complemented decision diagrams

This phase studies a precise failure mode of cube-cover compilation:

> A function can have a tiny semantic quotient and still require exponentially many
> monochromatic partial-assignment cubes.

Parity is the canonical exact example. The phase connects the repository's safe-cube
formalism to subcube-partition complexity, ordinary reduced ordered BDDs, and
complemented-edge BDD implementations.

The project still does **not** claim a proof of `P = NP` or `P != NP`.

## Literature bridge

A subcube is a partial Boolean assignment. A monochromatic subcube fixes enough
coordinates that every total extension has the same output. Decision-tree leaves form a
disjoint monochromatic subcube partition, but subcube partitions and decision trees are
distinct complexity measures. This viewpoint is developed in:

- Robin Kothari, David Racicot-Desloges, and Miklos Santha,
  *Separating decision tree complexity from subcube partition complexity*, 2015,
  https://arxiv.org/abs/1504.01339
- Yuval Filmus et al., *Irreducible subcube partitions*, 2022,
  https://arxiv.org/abs/2212.14685
- Shalev Ben-David et al., *Low-Sensitivity Functions from Unambiguous Certificates*,
  2016, https://arxiv.org/abs/1605.07084

Our safe-cube terms are stronger than plain monochromatic output cubes when the term must
preserve an entire residual function. For ordinary parity output, however, the same
one-bit-flip argument already forces every monochromatic cube to be a singleton.

## Formal results: A646-A660

`ResearchFortyFifth.lean` defines recursive parity and proves:

1. Flipping any coordinate flips parity.
2. Flipping a coordinate omitted by a cube preserves membership in that cube.
3. Therefore a parity-safe cube cannot omit any coordinate.
4. A fully specified cube has at most one total extension.
5. The owner map from assignments to terms in any complete parity cube cover is
   injective.

Consequently every complete parity-safe cube cover has at least

```text
2^n terms.
```

The singleton-cube construction has exactly `2^n` terms, so this lower bound is exact.
Parity has only two output labels, yet its minimum safe cube cover is exponential.

## Formal results: A661-A675

`ResearchFortySixth.lean` contrasts cube covers with shared-state decision structures.
A parity computation needs only the accumulated parity bit at each layer. An explicit
layered representation therefore has at most

```text
2 * (n + 1)
```

state-layer nodes. From `n >= 5`, this is strictly smaller than every parity cube cover.
The same exponential lower bound applies to disjoint subcube partitions because they are
also complete safe cube covers.

## Formal results: A676-A690

`ResearchFortySeventh.lean` generalises the argument through Boolean sensitivity.

For a function `f`, a coordinate is sensitive at `x` when flipping that coordinate changes
`f(x)`. The formal theorems prove:

```text
sensitive coordinates at representative
    subset of
support of every safe cube containing representative.
```

Therefore point sensitivity lower-bounds safe-cube width. Parity has sensitivity exactly
`n` at every input, so every parity term has width exactly `n`. Combining width and term
count gives the exact literal-work lower bound

```text
n * 2^n.
```

The term-count theorem is also proved for every fully sensitive Boolean function, not only
parity.

## Formal results: A691-A705

`ResearchFortyEighth.lean` connects recursive parity to the existing XOR-fold coordinate
and gives a conventional reduced ordered BDD accounting.

With two explicit residual states and two explicit terminals, the structured node type has
exactly

```text
2n + 1 nodes                 for n >= 1.
```

The repository proves:

```text
2n + 1 < 2^n                 for n >= 3,
2n + 1 < 2^(n+1) - 1         for n >= 2.
```

Thus sharing equal residual states changes an exponential full decision tree into a linear
DAG.

## Formal results: A706-A720

`ResearchFortyNinth.lean` proves the quotient itself is exact and minimal:

- nonempty parity has exactly two semantic output classes;
- a prefix induces the residual `suffix -> prefixParity XOR suffixParity`;
- two prefixes induce the same residual exactly when their accumulated parity bits agree;
- the two residual functions are distinct;
- any exact residual decoder therefore needs at least two semantic states;
- the Boolean parity-state encoding attains this lower bound.

This separates semantic width from representation geometry:

```text
semantic residual states: 2
safe cube terms:          2^n
ordinary reduced OBDD:    2n + 1
```

## Formal results: A721-A735

The current `tulip-control/dd` implementation uses signed node identifiers for complemented
references. This lets one physical node represent a Boolean function and its complement.
The repository formalises this convention separately rather than silently mixing node
metrics.

For parity:

- the odd residual is the pointwise complement of the even residual;
- one physical residual node plus one polarity bit represents both states;
- one terminal plus one physical decision node per variable gives

```text
n + 1 physical nodes;
```

- this saves exactly `n` nodes over the explicit `2n + 1` convention;
- every parity cube cover still needs `2^n` terms.

## Formal results: A736-A750

`ResearchFiftyFirst.lean` abstracts complement pairing.

A semantic complemented encoding maps every state to a pair

```text
(base physical node, polarity bit)
```

and decodes that reference back to the exact residual meaning. Exact decoding plus
semantic distinguishability makes this reference map injective, proving

```text
number of semantic states <= 2 * number of physical bases.
```

The phase also proves a necessary complement-closure condition: every represented residual
must equal a base meaning or the complement of a base meaning. A residual outside all such
pairs obstructs an exact complemented encoding with that base family.

Parity has two distinguishable residual states, one physical base is sufficient, and the
general cardinality theorem proves that zero bases cannot suffice.

## Independent exact experiment

`parity_representation_gap.py` independently performs two checks:

1. It enumerates all `3^n` partial cubes through `n = 9` and tests every total extension.
   Every monochromatic parity cube is a singleton.
2. It constructs a reduced ordered BDD with a unique table and evaluates it on every
   assignment through `n = 12`.

The resulting identities are:

```text
semantic classes         = 2
minimum cube terms       = 2^n
minimum cube literals    = n * 2^n
full decision-tree nodes = 2^(n+1) - 1
ordinary reduced OBDD    = 2n + 1
```

At `n = 16`:

```text
semantic classes:             2
cube terms:               65,536
cube literals:         1,048,576
full tree nodes:          131,071
ordinary OBDD nodes:           33
```

The complete deterministic output is stored in
`parity-representation-gap-output.txt`.

## Open-source BDD validation

The repository https://github.com/tulip-control/dd was cloned independently at:

```text
commit 2596de454f95031f6f92d9796aab41fc8e273947
commit date 2025-10-16T09:43:00+03:00
installed package version 0.6.1
```

`validate_dd_parity.py` built parity using `dd.autoref`, checked every assignment through
`n = 12`, and checked the reachable DAG size through `n = 32`.

The package's `Function.dag_size` reports:

```text
reachable complemented-edge nodes = n + 1.
```

At `n = 16`, the reachable root has 17 nodes. The manager contains more allocated nodes
because intermediate XOR-construction nodes remain in its unique table; only root-reachable
nodes are relevant to the represented function's DAG size.

The full reproduction record is in `dd-parity-validation-output.txt`. The optional external
validator is not included in the default experiment runner because the main repository does
not require the third-party `dd` package.

## Main conclusion

Three quantities must not be conflated:

```text
semantic quotient cardinality
cube or subcube-cover complexity
shared decision-DAG complexity
```

Parity has the smallest nontrivial semantic quotient but the largest possible
monochromatic-cube width at every input. Cube-only compilation is therefore not a safe
universal strategy, even when the quotient itself is tiny.

The constructive lesson is to search a representation portfolio:

- safe cubes where regions are geometrically simple;
- ordinary residual DAGs where repeated residual states can be shared;
- complemented-edge DAGs where residuals occur in complement pairs;
- other certified representations when neither cube geometry nor complement pairing is
  favourable.

The remaining P-versus-NP obligation is still uniform construction: for arbitrary NP
verifiers, construct one polynomial-size exact representation, together with polynomial
proofs of semantics, coverage or reachability, and total construction work.
