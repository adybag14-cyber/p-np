from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from linear_basis_obdd import gf2_rank, random_basis, transform_table
from optimal_obdd import OBDD, best_obdd, build_obdd, function_table, verify_obdd

Gate = tuple[str, tuple[int, ...]]


def bit_at(value: int, n: int, index: int) -> int:
    return (value >> (n - 1 - index)) & 1


def flip_bit(value: int, n: int, index: int) -> int:
    return value ^ (1 << (n - 1 - index))


def apply_gate(value: int, n: int, gate: Gate) -> int:
    kind, args = gate
    if kind == "X":
        return flip_bit(value, n, args[0])
    if kind == "CNOT":
        control, target = args
        return flip_bit(value, n, target) if bit_at(value, n, control) else value
    if kind == "TOFFOLI":
        first, second, target = args
        return (
            flip_bit(value, n, target)
            if bit_at(value, n, first) and bit_at(value, n, second)
            else value
        )
    raise ValueError(gate)


def all_gates(n: int) -> tuple[Gate, ...]:
    gates: list[Gate] = [("X", (target,)) for target in range(n)]
    gates.extend(
        ("CNOT", (control, target))
        for control in range(n)
        for target in range(n)
        if control != target
    )
    gates.extend(
        ("TOFFOLI", (first, second, target))
        for first, second in itertools.combinations(range(n), 2)
        for target in range(n)
        if target not in (first, second)
    )
    return tuple(gates)


def transformed_by_network(
    table: int,
    n: int,
    basis: Sequence[int],
    gates: Sequence[Gate],
) -> int:
    transformed = transform_table(table, n, basis)
    if not gates:
        return transformed
    result = 0
    for before in range(1 << n):
        after = before
        for gate in gates:
            after = apply_gate(after, n, gate)
        value = (transformed >> before) & 1
        result |= value << after
    return result


@dataclass
class SearchResult:
    diagram: OBDD
    basis: tuple[int, ...]
    gates: tuple[Gate, ...]
    table: int


def best_linear_seed(
    table: int,
    n: int,
    ordinary: OBDD,
    rng: random.Random,
    samples: int,
    special_bases: Sequence[Sequence[int]] = (),
) -> SearchResult:
    bases: list[tuple[int, ...]] = [
        tuple(1 << (n - 1 - variable) for variable in ordinary.order),
        tuple(1 << (n - 1 - variable) for variable in range(n)),
    ]
    bases.extend(tuple(basis) for basis in special_bases)
    bases.extend(random_basis(n, rng) for _ in range(samples))
    best: SearchResult | None = None
    for basis in bases:
        if gf2_rank(basis, n) != n:
            continue
        transformed = transformed_by_network(table, n, basis, ())
        diagram = build_obdd(transformed, n, tuple(range(n)))
        candidate = SearchResult(diagram, tuple(basis), (), transformed)
        if best is None or candidate.diagram.size < best.diagram.size:
            best = candidate
    if best is None:
        raise AssertionError("no invertible seed basis")
    return best


def nonlinear_hill_climb(
    original_table: int,
    n: int,
    seed: SearchResult,
    max_rounds: int = 10,
) -> SearchResult:
    current = seed
    candidates = all_gates(n)
    for _ in range(max_rounds):
        best_trial: SearchResult | None = None
        for gate in candidates:
            gates = current.gates + (gate,)
            transformed = transformed_by_network(original_table, n, current.basis, gates)
            diagram = build_obdd(transformed, n, tuple(range(n)))
            if diagram.size >= current.diagram.size:
                continue
            trial = SearchResult(diagram, current.basis, gates, transformed)
            if best_trial is None or trial.diagram.size < best_trial.diagram.size:
                best_trial = trial
        if best_trial is None:
            break
        current = best_trial
    return current


def verify_network(original_table: int, n: int, result: SearchResult) -> None:
    verify_obdd(result.table, n, result.diagram)
    seen: set[int] = set()
    linear = transform_table(original_table, n, result.basis)
    for original in range(1 << n):
        encoded = 0
        for row in result.basis:
            encoded = (encoded << 1) | ((original & row).bit_count() & 1)
        for gate in result.gates:
            encoded = apply_gate(encoded, n, gate)
        if encoded in seen:
            raise AssertionError("non-bijective reversible network")
        seen.add(encoded)
        expected = bool((original_table >> original) & 1)
        actual = result.diagram.evaluate(encoded, n)
        if expected != actual:
            raise AssertionError((original, encoded, expected, actual))
    if len(seen) != 1 << n:
        raise AssertionError(len(seen))
    if linear.bit_count() != result.table.bit_count():
        raise AssertionError("bijection changed model count")


def special_basis_for(label: str, n: int) -> list[tuple[int, ...]]:
    output: list[tuple[int, ...]] = []
    if label.startswith("parity"):
        rows = [(1 << n) - 1]
        for variable in range(n):
            candidate = 1 << (n - 1 - variable)
            if gf2_rank(rows + [candidate], n) > len(rows):
                rows.append(candidate)
        output.append(tuple(rows))
    if label.startswith("equality-halves"):
        half = n // 2
        rows = [
            (1 << (n - 1 - index)) ^ (1 << (n - 1 - (index + half)))
            for index in range(half)
        ]
        for variable in range(n):
            candidate = 1 << (n - 1 - variable)
            if gf2_rank(rows + [candidate], n) > len(rows):
                rows.append(candidate)
        output.append(tuple(rows))
    return output


def format_gate(gate: Gate) -> str:
    return gate[0] + str(gate[1])


def run() -> str:
    seed_value = 0x70FF_011
    rng = random.Random(seed_value)
    started = time.perf_counter()
    n = 6
    orders = tuple(itertools.permutations(range(n)))
    functions: list[tuple[str, int]] = [
        ("parity-6", function_table(n, lambda bits: sum(bits) % 2 == 1)),
        ("majority-6", function_table(n, lambda bits: sum(bits) >= 3)),
        ("exact-one-6", function_table(n, lambda bits: sum(bits) == 1)),
        ("equality-halves-3+3", function_table(n, lambda bits: bits[:3] == bits[3:])),
        (
            "inner-product-3",
            function_table(
                n,
                lambda bits: sum(int(bits[i] and bits[i + 3]) for i in range(3)) % 2 == 1,
            ),
        ),
        ("threshold-2-of-6", function_table(n, lambda bits: sum(bits) >= 2)),
        ("exact-two-6", function_table(n, lambda bits: sum(bits) == 2)),
    ]
    functions.extend((f"random-6-{index + 1}", rng.getrandbits(1 << n)) for index in range(10))

    gaps_linear: Counter[int] = Counter()
    gaps_nonlinear: Counter[int] = Counter()
    lines = [
        "Reversible nonlinear preprocessing experiment",
        f"seed={seed_value}",
        "Coordinates are first changed by an invertible GF(2) basis, then by a greedily selected reversible X/CNOT/Toffoli network.",
        "",
    ]
    for label, table in functions:
        ordinary = best_obdd(table, n, orders)
        linear = best_linear_seed(
            table,
            n,
            ordinary,
            rng,
            samples=1200,
            special_bases=special_basis_for(label, n),
        )
        nonlinear = nonlinear_hill_climb(table, n, linear, max_rounds=8)
        verify_network(table, n, nonlinear)
        gaps_linear[ordinary.size - linear.diagram.size] += 1
        gaps_nonlinear[ordinary.size - nonlinear.diagram.size] += 1
        lines.append(
            f"{label}: ordered={ordinary.size}, linear={linear.diagram.size}, "
            f"reversible={nonlinear.diagram.size}, linear-gain={ordinary.size - linear.diagram.size}, "
            f"extra-nonlinear-gain={linear.diagram.size - nonlinear.diagram.size}, "
            f"gates=[{', '.join(format_gate(gate) for gate in nonlinear.gates)}]"
        )
    lines.append("")
    lines.append("ordinary-minus-linear: " + ", ".join(f"{gap}:{count}" for gap, count in sorted(gaps_linear.items())))
    lines.append("ordinary-minus-reversible: " + ", ".join(f"{gap}:{count}" for gap, count in sorted(gaps_nonlinear.items())))
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("reversible-transform-obdd-output.txt").write_text(output, encoding="utf-8")
