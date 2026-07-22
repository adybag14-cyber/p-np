from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

from optimal_obdd import OBDD, best_obdd, build_obdd, function_table, verify_obdd


def parity(value: int) -> int:
    return value.bit_count() & 1


def gf2_rank(rows: Sequence[int], n: int) -> int:
    work = list(rows)
    rank = 0
    for bit in range(n - 1, -1, -1):
        pivot = next((i for i in range(rank, len(work)) if (work[i] >> bit) & 1), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for i in range(len(work)):
            if i != rank and ((work[i] >> bit) & 1):
                work[i] ^= work[rank]
        rank += 1
    return rank


def is_basis(rows: Sequence[int], n: int) -> bool:
    return len(rows) == n and gf2_rank(rows, n) == n


def all_ordered_bases(n: int) -> tuple[tuple[int, ...], ...]:
    nonzero = range(1, 1 << n)
    return tuple(rows for rows in itertools.permutations(nonzero, n) if is_basis(rows, n))


def random_basis(n: int, rng: random.Random) -> tuple[int, ...]:
    rows: list[int] = []
    while len(rows) < n:
        candidate = rng.randrange(1, 1 << n)
        if candidate in rows:
            continue
        if gf2_rank(rows + [candidate], n) > len(rows):
            rows.append(candidate)
    return tuple(rows)


def extend_independent(prefix: Sequence[int], n: int) -> tuple[int, ...]:
    rows = list(prefix)
    if gf2_rank(rows, n) != len(rows):
        raise ValueError("prefix is not independent")
    for bit in range(n):
        candidate = 1 << (n - 1 - bit)
        if gf2_rank(rows + [candidate], n) > len(rows):
            rows.append(candidate)
        if len(rows) == n:
            break
    if len(rows) != n:
        for candidate in range(1, 1 << n):
            if gf2_rank(rows + [candidate], n) > len(rows):
                rows.append(candidate)
            if len(rows) == n:
                break
    if not is_basis(rows, n):
        raise AssertionError(rows)
    return tuple(rows)


def transform_table(table: int, n: int, basis: Sequence[int]) -> int:
    if not is_basis(basis, n):
        raise ValueError("rows are not an invertible GF(2) basis")
    transformed = 0
    for assignment in range(1 << n):
        encoded = 0
        for row in basis:
            encoded = (encoded << 1) | parity(assignment & row)
        value = (table >> assignment) & 1
        transformed |= value << encoded
    return transformed


def build_linear_obdd(table: int, n: int, basis: Sequence[int]) -> OBDD:
    transformed = transform_table(table, n, basis)
    return build_obdd(transformed, n, tuple(range(n)))


def best_linear_obdd(table: int, n: int, bases: Iterable[Sequence[int]]) -> tuple[OBDD, tuple[int, ...]]:
    best: OBDD | None = None
    best_basis: tuple[int, ...] | None = None
    for basis_value in bases:
        basis = tuple(basis_value)
        candidate = build_linear_obdd(table, n, basis)
        if best is None or candidate.size < best.size:
            best = candidate
            best_basis = basis
    if best is None or best_basis is None:
        raise ValueError("no bases supplied")
    return best, best_basis


def anf_term_count(table: int, n: int) -> int:
    coefficients = [(table >> assignment) & 1 for assignment in range(1 << n)]
    for bit in range(n):
        for mask in range(1 << n):
            if mask & (1 << bit):
                coefficients[mask] ^= coefficients[mask ^ (1 << bit)]
    return sum(coefficients)


def verify_linear(table: int, n: int, basis: Sequence[int], diagram: OBDD) -> None:
    transformed = transform_table(table, n, basis)
    verify_obdd(transformed, n, diagram)
    for assignment in range(1 << n):
        encoded = 0
        for row in basis:
            encoded = (encoded << 1) | parity(assignment & row)
        expected = bool((table >> assignment) & 1)
        actual = diagram.evaluate(encoded, n)
        if expected != actual:
            raise AssertionError((assignment, expected, actual, basis))


def distribution_line(counter: Counter[int]) -> str:
    total = sum(counter.values())
    return ", ".join(
        f"gap {gap}: {count} ({100.0 * count / total:.2f}%)"
        for gap, count in sorted(counter.items())
    )


def four_variable_sample(rng: random.Random) -> list[str]:
    n = 4
    orders = tuple(itertools.permutations(range(n)))
    bases = list(all_ordered_bases(n))
    if len(bases) != 20160:
        raise AssertionError(len(bases))

    known = [
        0x1260, 0x4F68, 0xB2E1, 0xD342, 0xF819,
        function_table(n, lambda bits: sum(bits) % 2 == 1),
        function_table(n, lambda bits: sum(bits) == 1),
        function_table(n, lambda bits: sum(bits) >= 2),
        function_table(n, lambda bits: bits[:2] == bits[2:]),
        function_table(n, lambda bits: (bits[0] and bits[2]) ^ (bits[1] and bits[3])),
    ]
    tables = list(dict.fromkeys(known + [rng.getrandbits(1 << n) for _ in range(86)]))
    gaps: Counter[int] = Counter()
    strongest: list[str] = []
    max_gap = -10**9
    for table in tables:
        ordered = best_obdd(table, n, orders)
        linear, basis = best_linear_obdd(table, n, bases)
        verify_linear(table, n, basis, linear)
        gap = ordered.size - linear.size
        gaps[gap] += 1
        if gap > max_gap:
            max_gap = gap
            strongest = []
        if gap == max_gap and len(strongest) < 12:
            strongest.append(
                f"table=0x{table:04x}/ordered={ordered.size}/linear={linear.size}/"
                f"anf={anf_term_count(table, n)}/basis={basis}"
            )
    return [
        f"n=4 exact over all {len(bases):,} ordered GF(2) bases; tables={len(tables)}",
        distribution_line(gaps),
        "strongest: " + ", ".join(strongest),
    ]


def five_variable_sample(rng: random.Random) -> list[str]:
    n = 5
    orders = tuple(itertools.permutations(range(n)))
    tables = [rng.getrandbits(1 << n) for _ in range(18)]
    parity_table = function_table(n, lambda bits: sum(bits) % 2 == 1)
    exact_table = function_table(n, lambda bits: sum(bits) == 1)
    tables.extend([parity_table, exact_table])
    gaps: Counter[int] = Counter()
    best_rows: list[str] = []
    for index, table in enumerate(tables):
        bases = [tuple(1 << (n - 1 - i) for i in range(n))]
        if table == parity_table:
            bases.append(extend_independent([(1 << n) - 1], n))
        for _ in range(2500):
            bases.append(random_basis(n, rng))
        ordered = best_obdd(table, n, orders)
        bases.append(tuple(1 << (n - 1 - variable) for variable in ordered.order))
        linear, basis = best_linear_obdd(table, n, bases)
        verify_linear(table, n, basis, linear)
        gap = ordered.size - linear.size
        gaps[gap] += 1
        if gap > 0:
            best_rows.append(
                f"sample={index}/ordered={ordered.size}/linear={linear.size}/"
                f"anf={anf_term_count(table, n)}/basis={basis}"
            )
    return [
        "n=5 exact fixed-order baseline; 2,500 random linear bases per table",
        distribution_line(gaps),
        "improvements: " + (", ".join(best_rows[:12]) if best_rows else "none"),
    ]


def structured_eight(rng: random.Random) -> list[str]:
    n = 8
    orders = tuple(itertools.permutations(range(n)))
    functions = {
        "parity-8": function_table(n, lambda bits: sum(bits) % 2 == 1),
        "majority-8": function_table(n, lambda bits: sum(bits) >= 4),
        "exact-one-8": function_table(n, lambda bits: sum(bits) == 1),
        "equality-halves-4+4": function_table(n, lambda bits: bits[:4] == bits[4:]),
        "inner-product-4": function_table(
            n,
            lambda bits: sum(int(bits[i] and bits[i + 4]) for i in range(4)) % 2 == 1,
        ),
    }
    special = {
        "parity-8": extend_independent([(1 << n) - 1], n),
        "equality-halves-4+4": extend_independent(
            [(1 << (n - 1 - i)) ^ (1 << (n - 1 - (i + 4))) for i in range(4)], n
        ),
    }
    lines: list[str] = []
    for label, table in functions.items():
        bases = [tuple(1 << (n - 1 - i) for i in range(n))]
        if label in special:
            bases.append(special[label])
        for _ in range(1200):
            bases.append(random_basis(n, rng))
        ordered = best_obdd(table, n, orders)
        bases.append(tuple(1 << (n - 1 - variable) for variable in ordered.order))
        linear, basis = best_linear_obdd(table, n, bases)
        verify_linear(table, n, basis, linear)
        lines.append(
            f"{label}: ordered={ordered.size}, linear={linear.size}, "
            f"improvement={ordered.size - linear.size}, anf={anf_term_count(table, n)}, basis={basis}"
        )
    return lines


def run() -> str:
    seed = 0xAFF1_255
    rng = random.Random(seed)
    started = time.perf_counter()
    lines = [
        "Linear-basis decision diagram experiment",
        f"seed={seed}",
        "Each decision variable may be an arbitrary independent GF(2) linear form.",
        "",
    ]
    lines.extend(four_variable_sample(rng))
    lines.append("")
    lines.extend(five_variable_sample(rng))
    lines.append("")
    lines.append("Structured eight-variable functions")
    lines.extend(structured_eight(rng))
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("linear-basis-obdd-output.txt").write_text(output, encoding="utf-8")
