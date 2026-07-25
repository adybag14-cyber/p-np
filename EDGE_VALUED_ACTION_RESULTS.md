# Finite-action edge-valued decision diagrams

This phase generalises complemented Boolean edges to finite action-labelled decision diagrams.
It adds approaches A751-A840, two dependency-free exact experiments, and an external
validation against MEDDLY 0.18.1.

The repository still does not claim a proof of `P = NP` or `P != NP`.

## 1. Representation model

An action-labelled reference separates:

- a physical base node;
- a finite edge label;
- a decoder that applies the label action to the base meaning.

For semantic state type `State`, physical base type `Base`, and label type `Label`, an
exact encoding has the form

```text
State -> Base x Label -> Residual
```

with exact decoding for every state.

When distinct semantic states have distinct residual meanings, Lean proves

```text
|State| <= |Base| * |Label|.
```

Therefore edge labels can reduce physical nodes only by supplying independently counted
semantic capacity.

## 2. Orbit closure and obstructions

Every represented residual must lie in the labelled orbit of some physical base. A
residual outside every available base orbit obstructs exact representation.

For lawful finite group actions, orbit membership is formally proved reflexive,
symmetric, and transitive. Inverse labels recover the original residual, and nested labels
normalise to one composed label.

An action invariant is a classifier unchanged by every label action. Lean proves that every
semantic invariant class must appear among the physical base classes. Consequently,

```text
|semantic invariant classes| <= |physical bases|.
```

This gives lower bounds that are independent of the raw number of labels. Two semantic
meanings with different invariant values cannot share one physical base, no matter how
large the edge-label set is.

## 3. Cyclic additive labels

The first non-Boolean family uses labels in `ZMod q` acting by addition:

```text
label · residual = label + residual mod q.
```

One physical base plus `q` labels exactly represents all `q` cyclic residual states. The
encoding saturates the general capacity bound:

```text
q semantic states = 1 physical base * q labels.
```

Complemented edges are the special case `q = 2`.

## 4. Modular population sums

For Boolean inputs, define

```text
F_q(x) = sum_i x_i mod q, q >= 2.
```

Lean proves that flipping any coordinate changes `F_q`. Therefore the function is fully
coordinate-sensitive. As a consequence:

- every monochromatic cube fixes every coordinate;
- every safe cube has one total extension;
- every complete safe cube cover needs at least `2^n` terms.

This extends the parity subcube lower bound to all nontrivial modular population sums.

## 5. Exact streaming representation

The stream transition

```text
state <- state + bit mod q
```

is proved equal to the modular population sum. The edge-labelled chain uses one physical
decision node per input plus one terminal:

```text
physical nodes = n + 1.
```

By contrast, an explicit-state layered representation stores all `q` cyclic states at each
layer. The formal profile separates:

- semantic state count;
- physical node count;
- edge count;
- edge-label cardinality;
- cube-cover term count.

## 6. Encoded label cost

Labels are not free semantic oracles. If every label has an injective `b`-bit code, Lean
proves

```text
|State| <= |Base| * 2^b.
```

The physical cost record separately charges:

```text
node storage
edge storage
label bits on every edge
label-composition arithmetic
```

A small physical-node count alone is therefore not accepted as a polynomial compiler.

## 7. Exact dependency-free experiments

### `modular_edge_diagram.py`

The experiment exhaustively checks monochromatic cubes in small cases, independently
constructs canonical multi-terminal BDDs, and validates an additive edge-valued chain.

It verifies:

```text
safe cube terms      = 2^n
safe cube literals   = n * 2^n
MTBDD internal nodes = sum_{k=0}^{n-1} min(q, k+1)
MTBDD terminals      = min(q, n+1)
EV chain nodes       = n + 1
EV label storage     = 2n * ceil(log2 q) bits
```

At 16 variables:

| q | Cube terms | Cube literals | MTBDD nodes | EV physical nodes | EV label bits |
|---:|---:|---:|---:|---:|---:|
| 2 | 65,536 | 1,048,576 | 33 | 17 | 32 |
| 3 | 65,536 | 1,048,576 | 48 | 17 | 64 |
| 4 | 65,536 | 1,048,576 | 62 | 17 | 64 |
| 5 | 65,536 | 1,048,576 | 75 | 17 | 96 |
| 7 | 65,536 | 1,048,576 | 98 | 17 | 96 |

Deterministic output SHA-256:

```text
86cf013616e80e360bee0bf88c50451575cd4c6bd094a1effcfe79bd69a7cff9
```

### `edge_label_normalization.py`

An additive chain admits gauge-equivalent raw edge labels. Constants may be moved from a
node's outgoing edges toward the root without changing the represented function.

For `n` levels over `ZMod q`, the experiment checks up to `q^n` raw gauge assignments and
normalises every tested diagram to the convention

```text
low edge  = 0
high edge = 1
root      = 0
terminal  = 0.
```

It verifies semantic preservation, idempotence, and a unique canonical result across every
exhaustively checked gauge family.

Deterministic output SHA-256:

```text
b11075416d8f8f7b7305a828a09d8adfc5f8ada4a755bb3ead590074bbaa9aec
```

## 8. MEDDLY 0.18.1 validation

The official SourceForge archive was downloaded and checksum-verified:

```text
meddly-0.18.1.tar.gz
SHA-256 6a1bbcfa129a11d8426421cf5dc72aacac3672927ba404283495f785f6011ebf
```

It was configured with

```text
./configure --disable-shared --without-gmp
```

and built unchanged. Its full test suite passed:

```text
TOTAL 121
PASS  121
SKIP  0
FAIL  0
ERROR 0
```

The suite includes EV+ arithmetic, pre/post, minterm, copy, storage, and user-operation
coverage.

The purpose-built `meddly_modsum_validation.cc` constructs every Boolean variable as an
integer EV+ function valued `0/1`, combines them using MEDDLY `PLUS`, and evaluates every
assignment through 16 variables for moduli 2, 3, 4, 5, and 7.

The optional `validate_meddly_evplus.sh` script reproduces the archive download, strict
SHA-256 verification, build, complete upstream test suite, custom harness compilation, and
custom execution under Linux or WSL. It is intentionally excluded from the default research
runner because it downloads and builds a third-party dependency.

MEDDLY reports

```text
nonterminal nodes = n
edges              = 2n
```

so including the terminal agrees with the formal `n + 1` physical-node convention.

### Git-release reproducibility issue

The current Git release commit

```text
fb5d4831d53ff607832809c2cd1881ec04483a5e
```

contains a malformed committed `src/defines.h`: the include guard and header prefix were
replaced by repeated release-date lines. The parent commit contains a valid header. The
official 0.18.1 SourceForge archive contains the corrected header and builds successfully.
The successful validation used the unmodified official archive, not a patched Git checkout.

## 9. Normalisation obligation

Lean defines a normaliser as a transformation on references satisfying:

```text
decode(normalize r) = decode r
normalize(normalize r) = normalize r.
```

Equal normal forms imply equal decoded meanings, and the number of normalised references
never exceeds the raw reference count.

The missing universal theorem is not merely the existence of edge labels. A useful
compiler must uniformly construct:

```text
polynomially many physical bases
polynomial-bit labels
polynomial-time label composition
semantic-preserving canonical normalisation
polynomially checkable exact decoding
polynomial total node, edge, label, and arithmetic cost
```

Only a theorem providing all these obligations for every NP verifier would cross the
conditional collapse bridge formalised in A840.
