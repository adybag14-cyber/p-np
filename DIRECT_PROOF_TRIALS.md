# Direct P = NP proof trials: isolation, symmetry, and prefix descent

This phase deliberately attempted to construct an unconditional polynomial-time witness
algorithm. It did not begin from a conditional compiler criterion. Each route was written as
an executable or finite mathematical construction first, and Lean was used to force every
claimed universal step into an explicit theorem.

No proof of `P = NP` was obtained. The useful result is a set of exact, mechanically checked
obstructions explaining where four concrete proof attempts fail.

## Trial 1: deterministic fixed-target witness isolation

The attempted algorithm was:

1. Prepare a deterministic family of tests or hash fibers.
2. For every nonempty accepting witness set, require one test to retain exactly one witness.
3. Run a unique-witness solver on the isolated residual instance.

`ResearchFiftyEighth.lean` formalises this without assuming that the witness set comes from a
particular representation.

A test isolates `S` when:

```text
card(S intersection test) = 1.
```

Lean proves by deletion induction that any family isolating every nonempty subset of a finite
universe `U` has at least `|U|` tests. For the Boolean witness universe:

```text
|U| = 2^n.
```

For indexed hash fibers with a finite bucket set, the exact lower bound is:

```text
|Hash| * |Bucket| >= |U|.
```

Thus a deterministic black-box strategy that inspects fixed target buckets cannot have a
polynomial total number of targets for all possible witness sets.

This is consistent with the known difficulty of deterministic isolation. Relevant primary
sources include:

- Dell, Kabanets, Watanabe, and van Melkebeek, *Is the Valiant-Vazirani Isolation Lemma
  Improvable?*, ECCC TR11-151.
- Agrawal, Gurjar, and Thierauf, *Impossibility of Derandomizing the Isolation Lemma for all
  Families*, ECCC TR20-098.
- Arvind and Mukhopadhyay, *Derandomizing the Isolation Lemma and Lower Bounds for Circuit
  Size*, ECCC TR08-049.

The Lean theorem is narrower and self-contained: it concerns universal fixed-target finite
families, not every possible formula-dependent isolation algorithm.

## Trial 2: translation symmetrisation

The second attempt used the full Boolean translation group.

For an anchor `a` and mask `m`, define:

```text
translate(a, m) = a xor m.
```

Every Boolean witness is one translation away from every anchor. Therefore the orbit-OR
function:

```text
exists m, verifier(translate(a, m)) = true
```

is independent of `a` and equals ordinary witness existence.

This appears to compress an arbitrary verifier to one semantic state. Lean proves that this
one-state collapse is exact. It also proves the algebraic identity:

```text
product_m (if verifier(a xor m) then 0 else 1) = 0
iff
exists witness, verifier(witness) = true.
```

The failure is aggregation cost. The direct product has `2^n` verifier-dependent factors.
The value stored in the single semantic state is already the SAT answer. Constructing or
evaluating it efficiently is therefore exactly the missing algorithm, not a consequence of
symmetry alone.

## Trial 3: formula-dependent affine isolation

A universal fixed family is too large, so the third attempt tailored an affine map to the
particular accepting witness set.

`deterministic_isolation_experiment.py` performs exact small-instance searches. For each
formula it:

1. Enumerates the full accepting set.
2. Tests linear parity maps of increasing rank.
3. Searches for a bucket containing exactly one accepting witness.
4. Reports affine dimension, minimum observed rank, and maps tested.

At 12 variables, low-rank isolators frequently existed:

```text
random-3cnf-1:   5 witnesses, rank 1 isolator
planted-3cnf-1:  2 witnesses, rank 1 isolator
planted-3cnf-3: 10 witnesses, rank 1 isolator
```

But the target bucket was selected from a complete 4,096-assignment witness histogram.
Even parity required rank 11 and 26,596 tested maps in the configured search.

`ResearchSixtieth.lean` formalises the circularity precisely:

- A known witness gives a one-test tailored isolator.
- A proof-carrying isolated test recovers its accepted witness.
- An identity hash always has singleton buckets.
- Selecting an occupied identity bucket is exactly witness search.
- A compiler producing an isolated certificate therefore already implements a witness-finding
  algorithm.

The distinction is:

```text
small isolator exists
```

versus:

```text
small isolator and occupied target can be discovered uniformly in polynomial time.
```

Only the second would advance `P = NP`.

Known positive isolation results for restricted structures reinforce this distinction. For
example, deterministic or randomness-efficient isolation is available in space-bounded
settings and for polytopes with totally unimodular faces, but those results rely on additional
structure not known for arbitrary NP verifier witness sets.

## Trial 4: exact prefix descent and modular completion counts

The fourth attempted algorithm used self-reduction:

1. Split the current candidate set by the next witness bit.
2. Determine which child remains nonempty.
3. Descend for `n` levels.
4. Return the final witness.

Lean proves:

- child cardinalities add to the parent cardinality;
- every nonempty parent has a nonempty child;
- an exact nonemptiness oracle chooses a sound child;
- exact counts choose a nonempty heavier child;
- only one query per bit is needed at the abstract oracle level.

It also proves the obstruction:

```text
oracle.query(accepted witnesses) = true
iff
there exists an accepted witness.
```

So the root query is already SAT, and every later query is residual SAT.

`prefix_count_descent_experiment.py` tested the construction on a planted 16-variable 3-CNF.
It found and verified a witness in 16 branch levels, but the exact completion queries used
167,847 verifier evaluations. One exhaustive root scan would use 65,536 evaluations.

The model count was 8, so counting modulo 2 returned zero despite satisfiability. Lean proves
the general false-zero example `m mod m = 0` for every positive `m`.

A modulus larger than the entire witness universe makes a zero residue exact:

```text
count < modulus and count mod modulus = 0 implies count = 0.
```

However, computing that exact residue for an arbitrary verifier remains the missing counting
algorithm. A large output modulus does not make the verifier contraction inexpensive.

## What was genuinely established

The four attempts were not rejected by informal intuition. Their central finite semantics are
now theorems:

1. Universal fixed-target deterministic isolation needs exponentially many targets.
2. Full translation symmetry really collapses the semantic answer to one state, but exact
   aggregation remains exponential or circular.
3. Formula-dependent low-rank isolators can exist, but discovering an occupied unique bucket
   is witness search unless additional structure is supplied.
4. Prefix descent really needs only linearly many oracle calls, but each exact oracle call is a
   residual NP decision; modular counts can produce false zeros unless the modulus exceeds the
   full count range.

## Remaining possible opening

The most plausible surviving variant is not a universal black-box test family. It would need a
formula-dependent structural invariant that can be extracted from the verifier without
enumerating witnesses and that supplies one of:

- a provably occupied unique affine bucket;
- an exact orbit aggregate with polynomial construction cost;
- a polynomial residual nonemptiness oracle for the generated branch class;
- or a compact proof-carrying decomposition whose coverage is independently checkable.

The positive restricted isolation literature suggests that such a theorem would have to exploit
specific structure of verifier circuits rather than arbitrary hidden subsets. No theorem in
this phase establishes that all NP verifier circuits possess the required structure.
