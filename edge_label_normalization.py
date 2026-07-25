#!/usr/bin/env python3
"""Gauge normalisation for additive cyclic edge-valued chains."""
from __future__ import annotations
from itertools import product
from random import Random
from typing import Iterable, Sequence

def evaluate(bits: Sequence[int], modulus: int, root: int,
             lows: Sequence[int], highs: Sequence[int], terminal: int) -> int:
    total = root + terminal
    for i, bit in enumerate(bits):
        total += highs[i] if bit else lows[i]
    return total % modulus

def gauge_chain(gauges: Sequence[int], modulus: int):
    lows = tuple(g % modulus for g in gauges)
    highs = tuple((g + 1) % modulus for g in gauges)
    root = (-sum(lows)) % modulus
    return root, lows, highs, 0

def normalize(root: int, lows: Sequence[int], highs: Sequence[int],
              terminal: int, modulus: int):
    root %= modulus
    new_lows = []
    new_highs = []
    for low, high in zip(lows, highs):
        low %= modulus
        high %= modulus
        root = (root + low) % modulus
        new_lows.append(0)
        new_highs.append((high - low) % modulus)
    return root, tuple(new_lows), tuple(new_highs), terminal % modulus

def test_assignments(n: int, rng: Random) -> Iterable[tuple[int, ...]]:
    if n <= 10:
        return product((0, 1), repeat=n)
    fixed = [(0,) * n, (1,) * n]
    randoms = [tuple(rng.randrange(2) for _ in range(n)) for _ in range(128)]
    return iter(fixed + randoms)

def validate_chain(n: int, modulus: int, raw, normalized, rng: Random) -> None:
    for bits in test_assignments(n, rng):
        expected = sum(bits) % modulus
        raw_value = evaluate(bits, modulus, *raw)
        normalized_value = evaluate(bits, modulus, *normalized)
        if raw_value != expected or normalized_value != expected:
            raise AssertionError((n, modulus, bits, expected, raw_value, normalized_value))
    if normalize(*normalized, modulus) != normalized:
        raise AssertionError(("not idempotent", modulus, n, normalized))

def main() -> None:
    rng = Random(20260725)
    print("Additive edge-label gauge-normalisation experiment")
    print("Canonical convention: every low edge is zero; high edge is one.\n")
    print("q  n gauge_space checked distinct_raw canonical_forms gauge_check assignment_check")
    for modulus in (2, 3, 4, 5, 7, 11):
        for n in (1, 2, 4, 8, 12, 16):
            gauge_space = modulus ** n
            exhaustive_gauges = gauge_space <= 1024
            checked_target = gauge_space if exhaustive_gauges else 250
            gauge_iter: Iterable[tuple[int, ...]]
            if exhaustive_gauges:
                gauge_iter = product(range(modulus), repeat=n)
            else:
                gauge_iter = (
                    tuple(rng.randrange(modulus) for _ in range(n))
                    for _ in range(checked_target)
                )
            raw_seen = set()
            canonical_seen = set()
            checked = 0
            for gauges in gauge_iter:
                raw = gauge_chain(gauges, modulus)
                canonical = normalize(*raw, modulus)
                validate_chain(n, modulus, raw, canonical, rng)
                raw_seen.add(raw)
                canonical_seen.add(canonical)
                checked += 1
            expected_canonical = (0, (0,) * n, (1,) * n, 0)
            if canonical_seen != {expected_canonical}:
                raise AssertionError((modulus, n, canonical_seen))
            if exhaustive_gauges and len(raw_seen) != gauge_space:
                raise AssertionError((modulus, n, len(raw_seen), gauge_space))
            print(
                f"{modulus:2d} {n:2d} {gauge_space:11d} {checked:7d} "
                f"{len(raw_seen):12d} {len(canonical_seen):15d} "
                f"{'exhaustive' if exhaustive_gauges else 'sampled':10s} "
                f"{'exhaustive' if n <= 10 else 'sampled'}"
            )
    print("\nVerified:")
    print("- q^n gauge choices give q^n raw encodings in every exhaustively checked case.")
    print("- Every tested raw encoding computes the same modular population sum.")
    print("- Low-edge-zero normalisation maps every tested encoding to one canonical chain.")
    print("- Normalisation preserves semantics and is idempotent.")

if __name__ == "__main__":
    main()
