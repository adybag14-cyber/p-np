from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Iterable

from memo_dpll import random_3cnf
from optimal_obdd import best_obdd, build_obdd, cnf_table, function_table, verify_obdd


Signature = tuple[tuple[int, ...], int]


def insert_bit(reduced_assignment: int, reduced_n: int, position: int, bit: int) -> int:
    bits = [
        (reduced_assignment >> (reduced_n - 1 - index)) & 1
        for index in range(reduced_n)
    ]
    bits.insert(position, bit)
    full = 0
    for value in bits:
        full = (full << 1) | value
    return full


def cofactor_pattern(pattern: int, variable_count: int, position: int, bit: int) -> int:
    reduced_n = variable_count - 1
    result = 0
    for reduced_assignment in range(1 << reduced_n):
        full_assignment = insert_bit(reduced_assignment, reduced_n, position, bit)
        value = (pattern >> full_assignment) & 1
        result |= value << reduced_assignment
    return result


def reduce_signature(variables: tuple[int, ...], pattern: int) -> Signature:
    current_variables = variables
    current_pattern = pattern
    while current_variables:
        removed = False
        for position in range(len(current_variables)):
            low = cofactor_pattern(current_pattern, len(current_variables), position, 0)
            high = cofactor_pattern(current_pattern, len(current_variables), position, 1)
            if low == high:
                current_pattern = low
                current_variables = (
                    current_variables[:position] + current_variables[position + 1 :]
                )
                removed = True
                break
        if not removed:
            break
    return current_variables, current_pattern


def cofactor_signature(signature: Signature, position: int, bit: int) -> Signature:
    variables, pattern = signature
    reduced = cofactor_pattern(pattern, len(variables), position, bit)
    remaining = variables[:position] + variables[position + 1 :]
    return reduce_signature(remaining, reduced)


@dataclass
class AdaptiveDag:
    root: int
    nodes: dict[int, tuple[int, int, int]]
    used_terminals: frozenset[int]
    recurrence_cost: int

    @property
    def size(self) -> int:
        return len(self.nodes) + len(self.used_terminals)

    def evaluate(self, assignment: int, n: int) -> bool:
        node = self.root
        while node >= 2:
            variable, low, high = self.nodes[node]
            value = bool((assignment >> (n - 1 - variable)) & 1)
            node = high if value else low
        return bool(node)


def build_adaptive_dag(table: int, n: int) -> AdaptiveDag:
    root_signature = reduce_signature(tuple(range(n)), table)

    @lru_cache(maxsize=None)
    def best_recurrence(signature: Signature) -> tuple[int, int | None]:
        variables, pattern = signature
        if not variables:
            return 1, None
        best: tuple[int, int, int, int] | None = None
        for position, variable in enumerate(variables):
            low = cofactor_signature(signature, position, 0)
            high = cofactor_signature(signature, position, 1)
            low_cost, _ = best_recurrence(low)
            high_cost, _ = best_recurrence(high)
            cost = low_cost if low == high else 1 + low_cost + high_cost
            candidate = (cost, max(low_cost, high_cost), variable, position)
            if best is None or candidate < best:
                best = candidate
        if best is None:
            raise AssertionError("nonterminal signature has no variable")
        return best[0], best[3]

    nodes: dict[int, tuple[int, int, int]] = {}
    intern: dict[tuple[int, int, int], int] = {}
    semantic_memo: dict[Signature, int] = {}
    used_terminals: set[int] = set()

    def build(signature: Signature) -> int:
        previous = semantic_memo.get(signature)
        if previous is not None:
            return previous
        variables, pattern = signature
        if not variables:
            terminal = 1 if pattern & 1 else 0
            used_terminals.add(terminal)
            semantic_memo[signature] = terminal
            return terminal
        _cost, position = best_recurrence(signature)
        if position is None:
            raise AssertionError("missing adaptive branch choice")
        variable = variables[position]
        low_signature = cofactor_signature(signature, position, 0)
        high_signature = cofactor_signature(signature, position, 1)
        low = build(low_signature)
        high = build(high_signature)
        if low == high:
            semantic_memo[signature] = low
            return low
        key = (variable, low, high)
        node = intern.get(key)
        if node is None:
            node = len(nodes) + 2
            intern[key] = node
            nodes[node] = key
        semantic_memo[signature] = node
        return node

    root = build(root_signature)
    recurrence_cost, _ = best_recurrence(root_signature)
    return AdaptiveDag(root, nodes, frozenset(used_terminals), recurrence_cost)


def verify_adaptive(table: int, n: int, diagram: AdaptiveDag) -> None:
    for assignment in range(1 << n):
        expected = bool((table >> assignment) & 1)
        actual = diagram.evaluate(assignment, n)
        if actual != expected:
            raise AssertionError((assignment, expected, actual))


def format_distribution(distribution: Counter[int]) -> str:
    total = sum(distribution.values())
    return ", ".join(
        f"size {size}: {count} ({100.0 * count / total:.2f}%)"
        for size, count in sorted(distribution.items())
    )


def exact_four_variable_comparison() -> tuple[Counter[int], Counter[int], Counter[int], list[str]]:
    orders = tuple(itertools.permutations(range(4)))
    adaptive_distribution: Counter[int] = Counter()
    obdd_distribution: Counter[int] = Counter()
    improvement_distribution: Counter[int] = Counter()
    strongest: list[tuple[int, int, int, int]] = []
    max_improvement = -1
    for table in range(1 << (1 << 4)):
        adaptive = build_adaptive_dag(table, 4)
        verify_adaptive(table, 4, adaptive)
        ordered = best_obdd(table, 4, orders)
        adaptive_distribution[adaptive.size] += 1
        obdd_distribution[ordered.size] += 1
        improvement = ordered.size - adaptive.size
        improvement_distribution[improvement] += 1
        if improvement > max_improvement:
            max_improvement = improvement
            strongest = [(table, ordered.size, adaptive.size, adaptive.recurrence_cost)]
        elif improvement == max_improvement and len(strongest) < 8:
            strongest.append((table, ordered.size, adaptive.size, adaptive.recurrence_cost))
    lines = [
        f"table=0x{table:04x}/obdd={obdd}/adaptive={adaptive}/recurrence={recurrence}"
        for table, obdd, adaptive, recurrence in strongest
    ]
    return adaptive_distribution, obdd_distribution, improvement_distribution, lines


def sampled_comparison(n: int, samples: int, rng: random.Random) -> tuple[Counter[int], Counter[int], Counter[int]]:
    orders = tuple(itertools.permutations(range(n)))
    adaptive_distribution: Counter[int] = Counter()
    obdd_distribution: Counter[int] = Counter()
    improvements: Counter[int] = Counter()
    for _ in range(samples):
        table = rng.getrandbits(1 << n)
        adaptive = build_adaptive_dag(table, n)
        verify_adaptive(table, n, adaptive)
        ordered = best_obdd(table, n, orders)
        verify_obdd(table, n, ordered)
        adaptive_distribution[adaptive.size] += 1
        obdd_distribution[ordered.size] += 1
        improvements[ordered.size - adaptive.size] += 1
    return adaptive_distribution, obdd_distribution, improvements


def structured_comparison() -> list[str]:
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
    lines: list[str] = []
    for label, table in functions.items():
        adaptive = build_adaptive_dag(table, n)
        verify_adaptive(table, n, adaptive)
        ordered = best_obdd(table, n, orders)
        lines.append(
            f"{label}: ordered={ordered.size}, adaptive={adaptive.size}, "
            f"adaptive-recurrence={adaptive.recurrence_cost}, improvement={ordered.size-adaptive.size}"
        )
    return lines


def cnf_comparison(rng: random.Random) -> list[str]:
    n = 8
    orders = tuple(itertools.permutations(range(n)))
    lines: list[str] = []
    for index, ratio in enumerate((3.0, 4.2, 5.5), start=1):
        formula = random_3cnf(n, round(ratio * n), rng)
        table = cnf_table(formula, n)
        adaptive = build_adaptive_dag(table, n)
        verify_adaptive(table, n, adaptive)
        ordered = best_obdd(table, n, orders)
        lines.append(
            f"random-3cnf-{index}: clauses={len(formula)}, sat={table.bit_count()}/256, "
            f"ordered={ordered.size}, adaptive={adaptive.size}, "
            f"adaptive-recurrence={adaptive.recurrence_cost}, improvement={ordered.size-adaptive.size}"
        )
    return lines


def run() -> str:
    seed = 0xADA9_7150
    rng = random.Random(seed)
    started = time.perf_counter()
    lines = ["Adaptive semantic-DAG versus optimal OBDD experiment", f"seed={seed}", ""]

    adaptive4, ordered4, improvement4, strongest = exact_four_variable_comparison()
    lines.append("All 65,536 four-variable functions; exact comparison")
    lines.append("adaptive: " + format_distribution(adaptive4))
    lines.append("ordered:  " + format_distribution(ordered4))
    lines.append("ordered-minus-adaptive: " + format_distribution(improvement4))
    lines.append("strongest improvements: " + ", ".join(strongest))
    lines.append("")

    for n, samples in ((5, 300), (6, 80)):
        adaptive, ordered, improvements = sampled_comparison(n, samples, rng)
        lines.append(f"{samples} random {n}-variable functions; exact best OBDD order")
        lines.append("adaptive: " + format_distribution(adaptive))
        lines.append("ordered:  " + format_distribution(ordered))
        lines.append("ordered-minus-adaptive: " + format_distribution(improvements))
        lines.append("")

    lines.append("Structured eight-variable functions; exact best of all 40,320 OBDD orders")
    lines.extend(structured_comparison())
    lines.append("")

    lines.append("Eight-variable CNFs; exact best of all 40,320 OBDD orders")
    lines.extend(cnf_comparison(rng))
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter()-started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("adaptive-semantic-dag-output.txt").write_text(output, encoding="utf-8")