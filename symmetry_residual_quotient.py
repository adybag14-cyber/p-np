from __future__ import annotations

import itertools
import random
import time
from functools import lru_cache
from pathlib import Path

from optimal_obdd import function_table


def assignment_map_for_permutation(m: int, permutation: tuple[int, ...]) -> tuple[int, ...]:
    mapping: list[int] = []
    for new_assignment in range(1 << m):
        old_assignment = 0
        for new_position, old_position in enumerate(permutation):
            bit = (new_assignment >> (m - 1 - new_position)) & 1
            old_assignment |= bit << (m - 1 - old_position)
        mapping.append(old_assignment)
    return tuple(mapping)


@lru_cache(maxsize=None)
def permutation_maps(m: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        assignment_map_for_permutation(m, permutation)
        for permutation in itertools.permutations(range(m))
    )


@lru_cache(maxsize=None)
def canonical_pattern(m: int, pattern: int) -> int:
    if m <= 1:
        return pattern
    best: int | None = None
    for mapping in permutation_maps(m):
        transformed = 0
        for new_assignment, old_assignment in enumerate(mapping):
            transformed |= ((pattern >> old_assignment) & 1) << new_assignment
        if best is None or transformed < best:
            best = transformed
    if best is None:
        raise AssertionError(m)
    return best


def residual_pattern(table: int, n: int, status: tuple[int, ...]) -> tuple[tuple[int, ...], int]:
    remaining = tuple(index for index, value in enumerate(status) if value < 0)
    m = len(remaining)
    pattern = 0
    for reduced_assignment in range(1 << m):
        full_assignment = 0
        reduced_position = 0
        for variable, fixed in enumerate(status):
            if fixed < 0:
                bit = (reduced_assignment >> (m - 1 - reduced_position)) & 1
                reduced_position += 1
            else:
                bit = fixed
            full_assignment |= bit << (n - 1 - variable)
        pattern |= ((table >> full_assignment) & 1) << reduced_assignment
    return remaining, pattern


def quotient_counts(table: int, n: int) -> tuple[int, int, dict[int, tuple[int, int]]]:
    raw: set[tuple[tuple[int, ...], int]] = set()
    quotient: set[tuple[int, int]] = set()
    by_dimension_raw: dict[int, set[tuple[tuple[int, ...], int]]] = {}
    by_dimension_quotient: dict[int, set[int]] = {}

    for status in itertools.product((-1, 0, 1), repeat=n):
        remaining, pattern = residual_pattern(table, n, status)
        m = len(remaining)
        raw_state = (remaining, pattern)
        quotient_state = (m, canonical_pattern(m, pattern))
        raw.add(raw_state)
        quotient.add(quotient_state)
        by_dimension_raw.setdefault(m, set()).add(raw_state)
        by_dimension_quotient.setdefault(m, set()).add(quotient_state[1])

    dimensions = {
        m: (len(by_dimension_raw.get(m, set())), len(by_dimension_quotient.get(m, set())))
        for m in range(n + 1)
    }
    return len(raw), len(quotient), dimensions


def graph_table(n_vertices: int, predicate) -> tuple[int, int]:
    edges = [(i, j) for i in range(n_vertices) for j in range(i + 1, n_vertices)]
    n = len(edges)
    table = 0
    for assignment in range(1 << n):
        present = {
            edge
            for position, edge in enumerate(edges)
            if (assignment >> (n - 1 - position)) & 1
        }
        if predicate(present, n_vertices):
            table |= 1 << assignment
    return n, table


def has_triangle(present: set[tuple[int, int]], vertices: int) -> bool:
    for a, b, c in itertools.combinations(range(vertices), 3):
        if (a, b) in present and (a, c) in present and (b, c) in present:
            return True
    return False


def is_connected(present: set[tuple[int, int]], vertices: int) -> bool:
    seen = {0}
    changed = True
    while changed:
        changed = False
        for a, b in present:
            if a in seen and b not in seen:
                seen.add(b)
                changed = True
            if b in seen and a not in seen:
                seen.add(a)
                changed = True
    return len(seen) == vertices


def format_dimensions(dimensions: dict[int, tuple[int, int]]) -> str:
    return ", ".join(
        f"m={m}:{raw}->{quotient}"
        for m, (raw, quotient) in sorted(dimensions.items(), reverse=True)
    )


def run() -> str:
    seed = 0x5A77_270
    rng = random.Random(seed)
    started = time.perf_counter()
    n = 6
    functions: list[tuple[str, int, int]] = [
        ("parity-6", n, function_table(n, lambda bits: sum(bits) % 2 == 1)),
        ("majority-6", n, function_table(n, lambda bits: sum(bits) >= 3)),
        ("exact-one-6", n, function_table(n, lambda bits: sum(bits) == 1)),
        ("equality-halves-3+3", n, function_table(n, lambda bits: bits[:3] == bits[3:])),
        (
            "inner-product-3",
            n,
            function_table(
                n,
                lambda bits: sum(int(bits[i] and bits[i + 3]) for i in range(3)) % 2 == 1,
            ),
        ),
    ]
    triangle_n, triangle = graph_table(4, has_triangle)
    connected_n, connected = graph_table(4, is_connected)
    functions.extend([
        ("K4-has-triangle", triangle_n, triangle),
        ("K4-connected", connected_n, connected),
    ])
    for index in range(5):
        functions.append((f"random-6-{index + 1}", n, rng.getrandbits(1 << n)))

    lines = [
        "Residual symmetry quotient experiment",
        f"seed={seed}",
        "All 3^n partial assignments are enumerated; residual truth tables are quotiented by all permutations of remaining variables.",
        "",
    ]
    for label, variables, table in functions:
        raw, quotient, dimensions = quotient_counts(table, variables)
        compression = raw / quotient if quotient else float("inf")
        lines.append(
            f"{label}: raw={raw}, permutation-quotient={quotient}, "
            f"compression={compression:.3f}x"
        )
        lines.append("  " + format_dimensions(dimensions))
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("symmetry-residual-quotient-output.txt").write_text(output, encoding="utf-8")
