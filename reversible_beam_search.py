from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from optimal_obdd import OBDD, best_obdd, build_obdd, function_table
from reversible_transform_obdd import (
    Gate,
    SearchResult,
    all_gates,
    best_linear_seed,
    format_gate,
    nonlinear_hill_climb,
    special_basis_for,
    transformed_by_network,
    verify_network,
)


@dataclass(frozen=True)
class BeamState:
    gates: tuple[Gate, ...]
    table: int
    size: int


def beam_network_search(
    original_table: int,
    n: int,
    seed: SearchResult,
    *,
    beam_width: int = 16,
    max_depth: int = 6,
) -> SearchResult:
    """Search complete gate prefixes while retaining the seed as a baseline.

    The beam may cross plateaus or temporary regressions. The returned result is
    selected only after exact OBDD construction and exhaustive semantic checking.
    """
    gate_alphabet = all_gates(n)
    identity = BeamState((), seed.table, seed.diagram.size)
    beam: list[BeamState] = [identity]
    best = identity
    seen_tables: dict[int, int] = {seed.table: 0}

    for depth in range(1, max_depth + 1):
        expanded: dict[int, BeamState] = {}
        # Keep the current best, so the search can never lose its certified baseline.
        expanded[best.table] = best
        for state in beam:
            for gate in gate_alphabet:
                gates = state.gates + (gate,)
                transformed = transformed_by_network(original_table, n, seed.basis, gates)
                old_depth = seen_tables.get(transformed)
                if old_depth is not None and old_depth <= depth:
                    continue
                seen_tables[transformed] = depth
                diagram = build_obdd(transformed, n, tuple(range(n)))
                candidate = BeamState(gates, transformed, diagram.size)
                previous = expanded.get(transformed)
                if previous is None or (candidate.size, len(candidate.gates)) < (
                    previous.size,
                    len(previous.gates),
                ):
                    expanded[transformed] = candidate
                if (candidate.size, len(candidate.gates)) < (best.size, len(best.gates)):
                    best = candidate

        # Global score first, then shorter certificates. A small diversity term
        # keeps multiple transformed tables at the same node count.
        beam = sorted(
            expanded.values(),
            key=lambda state: (state.size, len(state.gates), state.table.bit_count(), state.table),
        )[:beam_width]

    diagram = build_obdd(best.table, n, tuple(range(n)))
    result = SearchResult(diagram, seed.basis, best.gates, best.table)
    verify_network(original_table, n, result)
    if result.diagram.size > seed.diagram.size:
        raise AssertionError("beam search lost the certified seed baseline")
    return result


def run() -> str:
    seed_value = 0xBEA7_5EED
    rng = random.Random(seed_value)
    started = time.perf_counter()
    n = 6
    orders = tuple(itertools.permutations(range(n)))
    functions: list[tuple[str, int]] = [
        ("parity-6", function_table(n, lambda bits: sum(bits) % 2 == 1)),
        ("majority-6", function_table(n, lambda bits: sum(bits) >= 3)),
        ("exact-one-6", function_table(n, lambda bits: sum(bits) == 1)),
        ("exact-two-6", function_table(n, lambda bits: sum(bits) == 2)),
        ("equality-halves-3+3", function_table(n, lambda bits: bits[:3] == bits[3:])),
        (
            "inner-product-3",
            function_table(
                n,
                lambda bits: sum(int(bits[i] and bits[i + 3]) for i in range(3)) % 2 == 1,
            ),
        ),
    ]
    functions.extend((f"random-6-{index + 1}", rng.getrandbits(1 << n)) for index in range(12))

    beam_minus_greedy: Counter[int] = Counter()
    ordered_minus_beam: Counter[int] = Counter()
    lines = [
        "Certified reversible beam-search experiment",
        f"seed={seed_value}",
        "The identity network remains in the beam; every returned network is exhaustively verified.",
        "",
    ]

    for label, table in functions:
        ordinary: OBDD = best_obdd(table, n, orders)
        linear = best_linear_seed(
            table,
            n,
            ordinary,
            rng,
            samples=600,
            special_bases=special_basis_for(label, n),
        )
        greedy = nonlinear_hill_climb(table, n, linear, max_rounds=8)
        verify_network(table, n, greedy)
        beam = beam_network_search(table, n, linear, beam_width=18, max_depth=6)
        beam_minus_greedy[greedy.diagram.size - beam.diagram.size] += 1
        ordered_minus_beam[ordinary.size - beam.diagram.size] += 1
        lines.append(
            f"{label}: ordered={ordinary.size}, linear={linear.diagram.size}, "
            f"greedy={greedy.diagram.size}, beam={beam.diagram.size}, "
            f"beam-vs-greedy={greedy.diagram.size - beam.diagram.size}, "
            f"gates=[{', '.join(format_gate(gate) for gate in beam.gates)}]"
        )

    lines.append("")
    lines.append(
        "greedy-minus-beam: "
        + ", ".join(f"{gap}:{count}" for gap, count in sorted(beam_minus_greedy.items()))
    )
    lines.append(
        "ordered-minus-beam: "
        + ", ".join(f"{gap}:{count}" for gap, count in sorted(ordered_minus_beam.items()))
    )
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("reversible-beam-search-output.txt").write_text(output, encoding="utf-8")
