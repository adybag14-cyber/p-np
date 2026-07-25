# Direct P != NP Proof Trials

This phase deliberately pursued separation rather than a polynomial SAT algorithm. It does
not claim a proof of `P != NP`. Each route was pushed until the exact missing theorem or
quantifier became explicit in Lean.

## Scope

The formal phase covers approaches A901-A1050:

- Shannon-style circuit counting and hard-function existence;
- exhaustive hard-table selection and uniform explicitness;
- padding deterministic hierarchy languages into NP-style history certificates;
- direct diagonalisation over polynomial-time machine exponents;
- the quantifier gap between per-exponent hard languages and one uniform hard language;
- range avoidance and locally explicit nonimage functions;
- transferring counting hardness through SAT reductions;
- proof-complexity lower bounds and proof-system simulation;
- restricted-circuit lower bounds and transfer to unrestricted computation.

All finite theorems are mechanically checked. No project axiom, placeholder proof, or
unproved asymptotic claim is introduced.

## Trial 1: circuit counting

For n input bits there are

```
2^(2^n)
```

Boolean functions. A b-bit circuit description space contains only `2^b` codes. Lean proves
that if `b < 2^n`, no evaluator from b-bit codes can be surjective onto all n-bit Boolean
functions. Hence some function lies outside every represented circuit.

This is a genuine unconditional lower bound. The failure point is explicitness: the counting
proof does not place the selected function in NP, P, or any desired uniform class.

Lean also proves that counting can separate a chosen target slice only after the slice itself
is shown to contain more functions than the circuit image. That is the missing class-specific
lower bound.

## Trial 2: exhaustive selection

A hard function can be selected noncomputably from the complement of the circuit image.
Exhaustive lexicographic selection can make the choice concrete at finite sizes, but it ranges
over up to

```
2^(2^n)
```

candidate truth tables. Supplying the result directly stores `2^n` output bits.

A one-step table lookup therefore does not make the family uniformly easy: construction and
representation costs remain exponential or double exponential.

## Trial 3: padding a hierarchy language

Suppose a deterministic hard language takes time `T(n)`. Padding to length at least `T(n)`
makes a complete computation history polynomial in the padded length. Lean proves that the
same padding also makes direct deterministic simulation polynomial in the padded length.

For the concrete plan `T(n) = 2^n` and padded length `N = 2^n`, direct simulation is exactly
linear in `N`.

Underpadding leaves the full history too long; sufficient padding destroys the intended
separation. A useful nondeterministic certificate must therefore be substantially shorter
than deterministic recomputation, not merely a complete deterministic trace.

## Trial 4: direct diagonalisation

A machine running in time `n^k` can be defeated at a stage tailored to exponent `k`.
However, a universal simulator that attacks machines with unbounded exponents has no single
fixed polynomial exponent. Lean proves this already at input length two:

```
for every fixed k, 2^(k+1) > 2^k.
```

Capping the simulated exponent misses the next polynomial-time stage. Encoding the exponent
in the input leaves the verifier exponent input-dependent. Padding each stage to its runtime
again makes the simulation linear.

## Trial 5: the quantifier swap

Stage-specific diagonalisation establishes an abstract statement of the form

```
for every exponent k, there exists a language L_k beating stage k.
```

A separation needs

```
there exists one NP language L that beats every exponent k.
```

Lean proves a finite analogue of the failed quantifier swap: choosing candidate `k+1` beats
stage `k`, but no fixed natural-number candidate exceeds every natural-number stage. The
language changes as the attacked exponent changes.

A valid separation package must combine one fixed verifier exponent with hardness against
all deterministic polynomial exponents.

## Trial 6: range avoidance

A range avoider outputs a Boolean function outside the image of a circuit evaluator. Counting
constructs such an avoider noncomputably. Extensional nonmembership is equivalent to

```
for every circuit code, there exists an input on which the code differs from the output.
```

A raw proof stores one distinguishing n-bit input for each b-bit code, requiring

```
n * 2^b
```

bits. Explicitly checking all entries has `2^b` work before circuit evaluation costs are
included.

The separation-grade target is therefore stronger than ordinary range avoidance. It needs:

- one locally evaluable output family;
- polynomial construction and local evaluation;
- one fixed NP verifier for its accepted inputs;
- hardness against every polynomial circuit-code budget;
- a succinct, sound nonimage argument.

Current range-avoidance lower-bound work obtains strong consequences for exponential-time
classes and restricted settings. This project isolates the extra local-NP explicitness needed
for `P != NP`.

## Trial 7: transferring a hard truth table to SAT

Every hard truth table can be written as a direct DNF or encoded into a SAT instance. In the
worst case this carries `n * 2^n` literals and at least the complete `2^n`-bit table.

A SAT algorithm polynomial in the produced instance length can therefore remain exponential
in the original n-bit input length. NP-completeness transfers hardness only from a succinct,
uniform source language through a polynomial-size reduction. It does not convert an
exponentially represented Shannon-hard table into a P lower bound.

## Trial 8: proof complexity

A sound complete proof system has both proof length and checker cost. Exponential lower bounds
for resolution exclude short resolution proofs. They do not exclude another polynomially
checkable proof system unless that system can be simulated by resolution with polynomial
overhead.

Lean formalises this transfer requirement. A restricted lower bound moves to a general proof
system only through an acceptance-preserving, size-bounded proof translation.

Proving `NP != coNP`, and hence `P != NP`, through proof complexity requires excluding every
polynomially bounded sound complete proof system, not only resolution or another fixed
system.

## Trial 9: restricted circuits

Monotone and bounded-depth lower bounds are genuine but model-specific. Lean gives a minimal
transfer counterexample: Boolean negation has a one-gate unrestricted circuit but cannot be
computed by any unary monotone representation.

Thus no monotone simulation can cover every unrestricted Boolean circuit. Similarly, a
function may require an exponential bounded-depth representation while having a linear
unrestricted representation.

A restricted lower bound contributes to `P != NP` only after a polynomial-overhead transfer
or completeness theorem connects general polynomial-time computation to the restricted
model.

## Exact experiments

### Small-circuit enumeration

For gates `NOT`, `AND`, `OR`, and `XOR`, with constants and projections free:

- three variables, at most four gates: 238 of 256 functions represented;
- four variables, at most four gates: 3,876 of 65,536 functions represented.

The lexicographically first missing four-variable truth table was
`1101000000000000`.

### Range nonimage certificates

For the four-variable exact circuit universe:

- hard table storage: 16 bits;
- represented functions: 3,876;
- one distinguishing four-bit input per represented function: 15,504 bits.

For `b = n^2` code bits, the raw certificate scale is `n * 2^(n^2)`.

### Padding and exponent accounting

Padding `2^n`-time computation to length `2^n` makes simulation-to-length ratio exactly one.
At fixed input length two, exponent `k+1` always exceeds exponent `k`. A new stage-specific
candidate beats every selected exponent, while any fixed candidate eventually fails.

## Relation to current lower-bound research

Recent work obtains near-maximum circuit lower bounds for exponential-time classes with
Merlin-Arthur query access, and super-quadratic restricted threshold-circuit lower bounds for
functions in `E^NP`. Range avoidance remains a central route to explicit lower bounds, with
known equivalences and reductions involving `E^NP` and related classes.

Those results are strong evidence that the route is technically meaningful. They also show
where the present frontier lies: current unconditional constructions are not one fixed
NP language with superpolynomial unrestricted circuit or time lower bounds.

Natural-proof and proof-complexity barriers further warn that sufficiently broad, efficiently
recognisable lower-bound properties may themselves have strong consequences or fail against
pseudorandom constructions.

## Current sharp target

A successful separation route must produce one object satisfying all of the following:

```
one uniform Boolean language family
+ one fixed polynomial NP verifier
+ polynomial witness length
+ polynomial local evaluation or reduction
+ hardness against every deterministic polynomial exponent
  or every polynomial-size unrestricted circuit family
+ a lower-bound proof that does not rely on exponential truth-table construction
+ polynomially checkable soundness without hiding the lower-bound computation
```

The project has not constructed this object. It has formalised why counting, padding,
stage-specific diagonalisation, ordinary range avoidance, truth-table reductions, restricted
proof systems, and restricted circuits each omit at least one of these obligations.
