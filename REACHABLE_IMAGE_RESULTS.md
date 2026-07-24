# Reachable-Image Generation Results

This phase corrects an important weakness in the earlier nonlinear-feature formulation.

A feature map may have a tiny reachable image while deciding which feature values are
reachable remains as hard as the original existential problem. Image cardinality and
image generation are separate computational resources.

## The output-feature circularity

For any Boolean witness relation `R`, define the one-bit feature

```text
feature(w) = R(w).
```

Its reachable image contains at most two values. However,

```text
true is reachable  <->  exists w, R(w) = true.
```

Therefore, the small image does not provide an algorithm. Any exact procedure that
generates the `true` row of this feature image already decides the original SAT or NP
witness-existence instance.

Lean formalizes this in approaches A396-A399 and again for exact image tables in A432.

## Corrected certificate

A useful feature quotient now carries one of the following:

1. An exact finite image table with:
   - completeness: every witness maps to a listed row;
   - soundness: every listed row has a concrete witness.
2. A syndrome generator with:
   - coordinate encoder;
   - representative witness for every coordinate;
   - proof that every witness signature is encoded by some coordinate;
   - proof that every encoded coordinate has the advertised representative.
3. A structural composition plan built from independently certified product, branch,
   separator, projection, or bijective-transform image tables.

The compiler cost now explicitly includes construction, image materialization, and
scanning costs.

## Exact relational elimination experiment

`observable_image_elimination.py` constructs local truth-relation factors and eliminates
all witness variables while retaining feature-output variables. The final relation is
the exact reachable signature image.

The experiment used 18 witness variables.

| Feature system | Final image | Maximum intermediate rows | Maximum scope |
|---|---:|---:|---:|
| Nine disjoint pair parities | 512 | 512 | 9 |
| Ten overlapping local parities | 1,024 | 4,096 | 12 |
| Ten local majority triples | 496 | 634 | 12 |
| Ten random local features | 992 | 2,208 | 12 |
| One global parity | 2 | 262,144 | 19 |
| One global majority | 2 | 262,144 | 19 |
| One global exact-one test | 2 | 262,144 | 19 |
| One random 3-SAT output feature | 2 | 262,144 | 19 |

The experiment demonstrates two distinct facts:

- Local structure can make exact image generation substantially cheaper than enumerating
  all witnesses.
- A two-row final image says almost nothing about the cost of obtaining those rows.

Global parity, majority, and exact-one have specialised algebraic or combinatorial image
generators, so their 262,144-row generic tables can be bypassed. The random 3-SAT output
feature has no such supplied generator; reaching its `true` row is the SAT problem.

## Product, branch, and separator composition

Lean proves exact constructors for image tables:

- Independent products use Cartesian products of component tables.
- Alternative branches use finite unions.
- Separator-conditioned systems use a finite union of bucket tables.
- Projection cannot increase row count.
- Bijective preprocessing transports a table without changing its rows.

The principal bounds are:

```text
product rows = left rows * right rows
branch rows <= left rows + right rows
separator rows <= separator assignments * maximum bucket width
```

These lemmas turn local image generators into larger exact generators without hidden
witness enumeration.

## Syndrome generators

A rank-r syndrome generator parameterizes all reachable output signatures by r Boolean
coordinates and supplies a representative witness for every coordinate.

Lean proves:

```text
reachable image = image of the coordinate encoder
reachable image cardinality <= 2^r
```

If the encoder is injective, the cardinality is exactly `2^r`.

This closes the missing reachability obligation for parity and linear-sketch-style
features. It also exposes the remaining limit: enumerating all coordinates is polynomial
only when `2^r` is polynomially bounded, or when the acceptance predicate over coordinates
has additional exploitable structure.

## Corrected frontier

The target is no longer merely:

> Find a polynomial-size exact feature image.

It is:

> Uniformly construct in polynomial time an exact reachable-image generator, exact image
> table, or representative-producing syndrome system whose construction, intermediate
> materialization, reachable row count, and acceptance scan are all polynomial.

Promising routes under this corrected requirement are:

- bounded-width local observable elimination;
- logarithmic-rank syndrome generators;
- separator-conditioned image tables;
- product decompositions with polynomial total image size;
- reversible preprocessing that preserves or reduces generator complexity;
- structural proof certificates for global features such as weight, parity, matching,
  or affine consistency.

A tiny feature codomain without a reachability generator is now explicitly rejected by
the formal compiler criteria.
