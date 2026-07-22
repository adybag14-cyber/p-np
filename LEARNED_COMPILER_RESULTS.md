# Learned reversible compilers and nonlinear observable quotients

This phase extends the mechanically checked workspace from A330 through A390.
It does not prove P = NP. It tests whether compact reversible preprocessing and
cheap nonlinear observables can expose smaller exact semantic quotients.

## Certified reversible beam search

`reversible_beam_search.py` starts from a verified linear-basis seed, keeps the
identity network as a permanent baseline, explores X/CNOT/Toffoli prefixes, builds
an exact reduced OBDD for each transformed truth table, and exhaustively verifies
the selected reversible network.

Across 18 six-variable functions, beam search beat greedy hill climbing on 16:

- majority: 14 ordinary -> 13 greedy -> 11 beam
- exact-one: 13 ordinary -> 11 greedy -> 7 beam
- exact-two: 16 ordinary -> 12 greedy -> 8 beam
- inner product: 12 ordinary -> 10 greedy -> 7 beam
- random examples commonly improved by another 2-5 nodes beyond greedy

The beam never exceeded its certified linear seed because the baseline candidate
was explicitly retained.

## Nonlinear observable quotients

`nonlinear_observable_search.py` searches exact witness signatures built from:

- arbitrary GF(2) parities;
- degree-two and degree-three conjunctions;
- three-bit majorities;
- Hamming-weight equalities and thresholds.

A candidate feature set is accepted only if every reachable signature fiber has a
constant truth value.

Results:

- parity: one observable, two signatures;
- majority: one threshold observable, two signatures;
- exact-one and exact-two: one weight observable, two signatures;
- equality halves: three parity observables, eight signatures;
- inner product: four nonlinear observables, sixteen signatures instead of the
  sixty-four required by the tested linear family;
- random functions normally still required six observables, but several exact
  images shrank from sixty-four to forty, forty-four, forty-eight, fifty-two, or
  fifty-six signatures.

## Opposite-pair cover interpretation

For a Boolean relation, an exact feature quotient is equivalent to separating
every pair of witnesses with opposite labels. A feature covers an opposite pair
when its values differ on that pair. The Lean layer proves:

- complete opposite-pair coverage implies fiber safety;
- fiber safety implies every opposite pair is separated;
- adding features preserves coverage;
- cover unions have the expected cardinality bound;
- the explicit pair universe over n-bit witnesses has size 2^(2n).

Thus exhaustive collision validation is itself exponential. A scalable result
needs a structural proof that the selected observable family covers all opposite
pairs.

## Transform then observe

`transform_then_observe.py` composes reversible preprocessing with nonlinear
feature learning. The result is mixed:

- equality halves improves from eight original signatures to four transformed
  signatures;
- one random function improves from forty-eight to thirty-four signatures;
- several other random functions improve to forty-eight or fifty-six signatures;
- majority and exact-count predicates become worse after an unnecessary transform
  because their original weight observable is already optimal.

This motivates a baseline-safe portfolio: retain the original quotient and every
transformed quotient, verify all of them, and choose the smallest exact image.
Lean proves that pullback through a bijection preserves fiber safety and reachable
feature-image cardinality.

## Remaining theorem

A P = NP result along this route would require a uniform polynomial-time compiler
that produces a polynomial-size exact portfolio containing at least one candidate
with:

1. a polynomial-length reversible network;
2. polynomially many cheaply evaluable observables;
3. a polynomial reachable signature image;
4. a structural certificate covering every opposite-label witness pair;
5. polynomial construction and replay cost.

The experiments show substantial finite compression, especially when beam search
crosses local plateaus. They do not establish the required universal polynomial
bounds.
