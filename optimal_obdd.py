from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from memo_dpll import random_3cnf
from symbolic_cnf import CNF, eval_cnf


@dataclass
class OBDD:
    order: tuple[int, ...]
    root: int
    nodes: dict[int, tuple[int, int, int]]
    used_terminals: frozenset[int]

    @property
    def size(self) -> int:
        return len(self.nodes) + len(self.used_terminals)

    def evaluate(self, assignment: int, n: int) -> bool:
        node = self.root
        while node >= 2:
            level, low, high = self.nodes[node]
            variable = self.order[level]
            value = bool((assignment >> (n - 1 - variable)) & 1)
            node = high if value else low
        return bool(node)


def reorder_truth_table(table: int, n: int, order: Sequence[int]) -> int:
    result = 0
    for ordered_assignment in range(1 << n):
        canonical_assignment = 0
        for position, variable in enumerate(order):
            bit = (ordered_assignment >> (n - 1 - position)) & 1
            canonical_assignment |= bit << (n - 1 - variable)
        value = (table >> canonical_assignment) & 1
        result |= value << ordered_assignment
    return result


def build_obdd(table: int, n: int, order: Sequence[int]) -> OBDD:
    ordered_table = reorder_truth_table(table, n, order)
    intern: dict[tuple[int, int, int], int] = {}
    nodes: dict[int, tuple[int, int, int]] = {}
    used_terminals: set[int] = set()

    def build(pattern: int, remaining: int, level: int) -> int:
        assignment_count = 1 << remaining
        if pattern == 0:
            used_terminals.add(0)
            return 0
        if pattern == (1 << assignment_count) - 1:
            used_terminals.add(1)
            return 1
        if remaining == 0:
            raise AssertionError("nonconstant zero-variable function")
        half_assignments = 1 << (remaining - 1)
        mask = (1 << half_assignments) - 1
        low = build(pattern & mask, remaining - 1, level + 1)
        high = build(pattern >> half_assignments, remaining - 1, level + 1)
        if low == high:
            return low
        key = (level, low, high)
        existing = intern.get(key)
        if existing is not None:
            return existing
        node_id = len(nodes) + 2
        intern[key] = node_id
        nodes[node_id] = key
        return node_id

    root = build(ordered_table, n, 0)
    return OBDD(tuple(order), root, nodes, frozenset(used_terminals))


def best_obdd(table: int, n: int, orders: Iterable[Sequence[int]]) -> OBDD:
    best: OBDD | None = None
    for order in orders:
        candidate = build_obdd(table, n, order)
        if best is None or candidate.size < best.size:
            best = candidate
    if best is None:
        raise ValueError("no variable orders supplied")
    return best


def verify_obdd(table: int, n: int, diagram: OBDD) -> None:
    for assignment in range(1 << n):
        expected = bool((table >> assignment) & 1)
        actual = diagram.evaluate(assignment, n)
        if actual != expected:
            raise AssertionError((assignment, expected, actual, diagram.order))


def function_table(n: int, predicate) -> int:
    table = 0
    for assignment in range(1 << n):
        values = [bool((assignment >> (n - 1 - variable)) & 1) for variable in range(n)]
        if predicate(values):
            table |= 1 << assignment
    return table


def cnf_table(formula: CNF, n: int) -> int:
    table = 0
    for assignment in range(1 << n):
        if eval_cnf(formula, assignment, n):
            table |= 1 << assignment
    return table


def exact_four_variable_distribution() -> tuple[Counter[int], list[tuple[int, int, tuple[int, ...]]]]:
    orders = tuple(itertools.permutations(range(4)))
    distribution: Counter[int] = Counter()
    hardest: list[tuple[int, int, tuple[int, ...]]] = []
    max_size = -1
    for table in range(1 << (1 << 4)):
        best = best_obdd(table, 4, orders)
        distribution[best.size] += 1
        if best.size > max_size:
            max_size = best.size
            hardest = [(table, best.size, best.order)]
        elif best.size == max_size and len(hardest) < 8:
            hardest.append((table, best.size, best.order))
    return distribution, hardest


def sampled_distribution(n: int, samples: int, rng: random.Random) -> Counter[int]:
    orders = tuple(itertools.permutations(range(n)))
    distribution: Counter[int] = Counter()
    for _ in range(samples):
        table = rng.getrandbits(1 << n)
        best = best_obdd(table, n, orders)
        verify_obdd(table, n, best)
        distribution[best.size] += 1
    return distribution


def format_distribution(distribution: Counter[int]) -> str:
    total = sum(distribution.values())
    return ", ".join(
        f"size {size}: {count} ({100.0 * count / total:.2f}%)"
        for size, count in sorted(distribution.items())
    )


def structured_results() -> list[str]:
    lines: list[str] = []
    n = 8
    all_orders = tuple(itertools.permutations(range(n)))
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
    for label, table in functions.items():
        natural = build_obdd(table, n, tuple(range(n)))
        best = best_obdd(table, n, all_orders)
        verify_obdd(table, n, best)
        lines.append(
            f"{label}: natural-size={natural.size}, best-size={best.size}, best-order={best.order}"
        )
    return lines


def cnf_results(rng: random.Random) -> list[str]:
    lines: list[str] = []
    n = 8
    all_orders = tuple(itertools.permutations(range(n)))
    for index, ratio in enumerate((3.0, 4.2, 5.5), start=1):
        formula = random_3cnf(n, round(ratio * n), rng)
        table = cnf_table(formula, n)
        natural = build_obdd(table, n, tuple(range(n)))
        best = best_obdd(table, n, all_orders)
        verify_obdd(table, n, best)
        satisfying = table.bit_count()
        lines.append(
            f"random-3cnf-{index}: clauses={len(formula)}, satisfying={satisfying}/256, "
            f"natural-size={natural.size}, best-size={best.size}, best-order={best.order}"
        )
    return lines


def run() -> str:
    seed = 0x0BDD_120
    rng = random.Random(seed)
    started = time.perf_counter()
    lines = ["Exact reduced ordered-BDD state experiment", f"seed={seed}", ""]

    distribution4, hardest4 = exact_four_variable_distribution()
    lines.append("All 65,536 four-variable functions; exact best of all 24 orders")
    lines.append(format_distribution(distribution4))
    lines.append(
        "hardest examples: "
        + ", ".join(
            f"table=0x{table:04x}/size={size}/order={order}"
            for table, size, order in hardest4
        )
    )
    lines.append("")

    distribution5 = sampled_distribution(5, 600, rng)
    lines.append("600 random five-variable functions; exact best of all 120 orders")
    lines.append(format_distribution(distribution5))
    lines.append("")

    distribution6 = sampled_distribution(6, 120, rng)
    lines.append("120 random six-variable functions; exact best of all 720 orders")
    lines.append(format_distribution(distribution6))
    lines.append("")

    lines.append("Structured eight-variable functions; exact best of all 40,320 orders")
    lines.extend(structured_results())
    lines.append("")

    lines.append("Eight-variable CNFs; exact best of all 40,320 orders")
    lines.extend(cnf_results(rng))
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("optimal-obdd-output.txt").write_text(output, encoding="utf-8")
