from __future__ import annotations

import itertools
import math
import random
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

SEED = 0x504E50
rng = random.Random(SEED)


def assignment_index_from_ordered_bits(bits: int, order: Sequence[int], n: int) -> int:
    """Map an assignment encoded in `order`-bit order to the natural variable index."""
    natural = 0
    for position, variable in enumerate(order):
        bit = (bits >> (n - 1 - position)) & 1
        natural |= bit << (n - 1 - variable)
    return natural


def permutation_map(order: Sequence[int]) -> np.ndarray:
    n = len(order)
    return np.fromiter(
        (assignment_index_from_ordered_bits(i, order, n) for i in range(1 << n)),
        dtype=np.int64,
        count=1 << n,
    )


def permute_packed_tables(values: np.ndarray, order: Sequence[int], n: int) -> np.ndarray:
    """Permute packed truth-table bits so prefixes in `order` form contiguous rows."""
    mapping = permutation_map(order)
    dtype = values.dtype
    out = np.zeros_like(values, dtype=dtype)
    for new_index, old_index in enumerate(mapping.tolist()):
        out |= ((values >> np.array(old_index, dtype=dtype)) & np.array(1, dtype=dtype)) << np.array(
            new_index, dtype=dtype
        )
    return out


def packed_widths(values: np.ndarray, order: Sequence[int], n: int) -> np.ndarray:
    """Maximum exact residual width for many packed functions under one order."""
    permuted = permute_packed_tables(values, order, n)
    maximum = np.ones(values.shape[0], dtype=np.uint16)
    for depth in range(1, n):
        suffix_assignments = 1 << (n - depth)
        prefix_assignments = 1 << depth
        mask = (1 << suffix_assignments) - 1
        chunks = np.empty((values.shape[0], prefix_assignments), dtype=values.dtype)
        for prefix in range(prefix_assignments):
            shift = prefix * suffix_assignments
            chunks[:, prefix] = (permuted >> np.array(shift, dtype=values.dtype)) & np.array(
                mask, dtype=values.dtype
            )
        chunks.sort(axis=1)
        width = 1 + np.count_nonzero(chunks[:, 1:] != chunks[:, :-1], axis=1)
        maximum = np.maximum(maximum, width.astype(np.uint16))
    return maximum


def exact_distribution_n4() -> tuple[Counter[int], Counter[int]]:
    n = 4
    values = np.arange(1 << (1 << n), dtype=np.uint16)
    orders = list(itertools.permutations(range(n)))
    best = np.full(values.shape[0], 1 << n, dtype=np.uint16)
    natural = packed_widths(values, tuple(range(n)), n)
    for order in orders:
        best = np.minimum(best, packed_widths(values, order, n))
    return Counter(map(int, natural.tolist())), Counter(map(int, best.tolist()))


def sampled_distribution(n: int, count: int, order_limit: int | None = None) -> Counter[int]:
    if n > 6:
        raise ValueError("packed sampling supports n <= 6")
    bit_count = 1 << n
    dtype = np.uint32 if bit_count <= 32 else np.uint64
    high = 1 << bit_count if bit_count < 64 else None
    if high is None:
        values = np.array([rng.getrandbits(64) for _ in range(count)], dtype=dtype)
    else:
        values = np.array([rng.randrange(high) for _ in range(count)], dtype=dtype)
    orders = list(itertools.permutations(range(n)))
    if order_limit is not None and len(orders) > order_limit:
        orders = rng.sample(orders, order_limit)
        natural = tuple(range(n))
        if natural not in orders:
            orders[0] = natural
    best = np.full(values.shape[0], 1 << n, dtype=np.uint16)
    for order in orders:
        best = np.minimum(best, packed_widths(values, order, n))
    return Counter(map(int, best.tolist()))


def residual_profile(table: np.ndarray, order: Sequence[int]) -> list[int]:
    n = int(round(math.log2(table.size)))
    tensor = table.reshape((2,) * n)
    permuted = np.transpose(tensor, axes=order).reshape(-1)
    profile = [1]
    for depth in range(1, n):
        rows = permuted.reshape(1 << depth, 1 << (n - depth))
        profile.append(int(np.unique(rows, axis=0).shape[0]))
    profile.append(1 if np.all(table == table[0]) else 2)
    return profile


def width(table: np.ndarray, order: Sequence[int]) -> int:
    return max(residual_profile(table, order))


def greedy_order(table: np.ndarray) -> tuple[int, ...]:
    n = int(round(math.log2(table.size)))
    chosen: list[int] = []
    remaining = set(range(n))
    while remaining:
        candidates = []
        for variable in sorted(remaining):
            trial = chosen + [variable]
            tail = [v for v in range(n) if v not in trial]
            profile = residual_profile(table, trial + tail)
            candidates.append((profile[len(trial)], max(profile[: len(trial) + 1]), variable))
        _, _, selected = min(candidates)
        chosen.append(selected)
        remaining.remove(selected)
    return tuple(chosen)


def improve_order(table: np.ndarray, initial: Sequence[int]) -> tuple[tuple[int, ...], int]:
    order = tuple(initial)
    current = width(table, order)
    improved = True
    while improved:
        improved = False
        best_order = order
        best_width = current
        for i in range(len(order)):
            for j in range(i + 1, len(order)):
                trial = list(order)
                trial[i], trial[j] = trial[j], trial[i]
                trial_t = tuple(trial)
                trial_width = width(table, trial_t)
                if trial_width < best_width:
                    best_order, best_width = trial_t, trial_width
        if best_width < current:
            order, current, improved = best_order, best_width, True
    return order, current


def parity_table(n: int) -> np.ndarray:
    return np.array([i.bit_count() & 1 for i in range(1 << n)], dtype=np.uint8)


def majority_table(n: int) -> np.ndarray:
    return np.array([i.bit_count() * 2 >= n for i in range(1 << n)], dtype=np.uint8)


def exact_one_table(n: int) -> np.ndarray:
    return np.array([i.bit_count() == 1 for i in range(1 << n)], dtype=np.uint8)


def equality_halves_table(half: int) -> np.ndarray:
    n = 2 * half
    mask = (1 << half) - 1
    return np.array([((i >> half) & mask) == (i & mask) for i in range(1 << n)], dtype=np.uint8)


@dataclass(frozen=True)
class Clause:
    variables: tuple[int, ...]
    positive: tuple[bool, ...]


def random_k_cnf(n: int, clauses: int, k: int = 3) -> tuple[list[Clause], np.ndarray]:
    formula: list[Clause] = []
    for _ in range(clauses):
        variables = tuple(sorted(rng.sample(range(n), k)))
        signs = tuple(bool(rng.getrandbits(1)) for _ in range(k))
        formula.append(Clause(variables, signs))
    assignments = np.arange(1 << n, dtype=np.uint64)
    result = np.ones(1 << n, dtype=np.uint8)
    for clause in formula:
        clause_value = np.zeros(1 << n, dtype=np.uint8)
        for variable, positive in zip(clause.variables, clause.positive, strict=True):
            values = ((assignments >> np.uint64(n - 1 - variable)) & np.uint64(1)).astype(np.uint8)
            literal = values if positive else 1 - values
            clause_value |= literal
        result &= clause_value
    return formula, result


def tuned_width(table: np.ndarray, restarts: int = 24) -> tuple[int, tuple[int, ...], list[int]]:
    n = int(round(math.log2(table.size)))
    starts: list[tuple[int, ...]] = [tuple(range(n)), greedy_order(table)]
    for _ in range(restarts):
        candidate = list(range(n))
        rng.shuffle(candidate)
        starts.append(tuple(candidate))
    best_order: tuple[int, ...] | None = None
    best_width = 1 << n
    for start in starts:
        order, candidate_width = improve_order(table, start)
        if candidate_width < best_width:
            best_width = candidate_width
            best_order = order
    assert best_order is not None
    return best_width, best_order, residual_profile(table, best_order)


def format_counter(counter: Counter[int]) -> str:
    total = sum(counter.values())
    return ", ".join(
        f"width {key}: {value} ({100.0 * value / total:.2f}%)" for key, value in sorted(counter.items())
    )


def primal_graph(n: int, formula: Sequence[Clause]) -> list[set[int]]:
    graph = [set() for _ in range(n)]
    for clause in formula:
        for i, a in enumerate(clause.variables):
            for b in clause.variables[i + 1 :]:
                graph[a].add(b)
                graph[b].add(a)
    return graph


def frontier_profile(order: Sequence[int], graph: Sequence[set[int]]) -> list[int]:
    processed: set[int] = set()
    remaining = set(order)
    profile = [0]
    for variable in order:
        processed.add(variable)
        remaining.remove(variable)
        frontier = {v for v in processed if graph[v] & remaining}
        profile.append(len(frontier))
    return profile


def frontier_width(order: Sequence[int], graph: Sequence[set[int]]) -> int:
    return max(frontier_profile(order, graph))


def greedy_frontier_order(graph: Sequence[set[int]]) -> tuple[int, ...]:
    n = len(graph)
    processed: set[int] = set()
    remaining = set(range(n))
    order: list[int] = []
    while remaining:
        choices = []
        for candidate in sorted(remaining):
            p2 = processed | {candidate}
            r2 = remaining - {candidate}
            frontier = {v for v in p2 if graph[v] & r2}
            future_degree = len(graph[candidate] & r2)
            choices.append((len(frontier), future_degree, candidate))
        _, _, selected = min(choices)
        order.append(selected)
        processed.add(selected)
        remaining.remove(selected)
    return tuple(order)


def tune_frontier_order(graph: Sequence[set[int]], restarts: int = 128) -> tuple[tuple[int, ...], int]:
    n = len(graph)
    starts = [tuple(range(n)), greedy_frontier_order(graph)]
    for _ in range(restarts):
        candidate = list(range(n))
        rng.shuffle(candidate)
        starts.append(tuple(candidate))
    best_order = starts[0]
    best_width = frontier_width(best_order, graph)
    for start in starts:
        order = start
        current = frontier_width(order, graph)
        improved = True
        while improved:
            improved = False
            local_best = order
            local_width = current
            for i in range(n):
                for j in range(i + 1, n):
                    trial = list(order)
                    trial[i], trial[j] = trial[j], trial[i]
                    trial_t = tuple(trial)
                    w = frontier_width(trial_t, graph)
                    if w < local_width:
                        local_best, local_width = trial_t, w
            if local_width < current:
                order, current, improved = local_best, local_width, True
        if current < best_width:
            best_order, best_width = order, current
    return best_order, best_width


def matching_graph(half: int) -> list[set[int]]:
    graph = [set() for _ in range(2 * half)]
    for i in range(half):
        graph[i].add(i + half)
        graph[i + half].add(i)
    return graph

def main() -> None:
    lines: list[str] = []
    lines.append("Residual-width search")
    lines.append(f"seed={SEED}")
    lines.append("")

    natural_n4, best_n4 = exact_distribution_n4()
    lines.append("All 65,536 Boolean functions on four variables")
    lines.append("natural order: " + format_counter(natural_n4))
    lines.append("best of all 24 orders: " + format_counter(best_n4))
    lines.append("")

    best_n5 = sampled_distribution(5, count=5000)
    lines.append("5,000 uniformly random five-variable functions; best of all 120 orders")
    lines.append(format_counter(best_n5))
    lines.append("")

    best_n6 = sampled_distribution(6, count=500, order_limit=240)
    lines.append("500 uniformly random six-variable functions; best of 240 sampled orders")
    lines.append(format_counter(best_n6))
    lines.append("")

    structured = [
        ("parity-12", parity_table(12)),
        ("majority-12", majority_table(12)),
        ("exact-one-12", exact_one_table(12)),
        ("equality-halves-6+6", equality_halves_table(6)),
    ]
    for label, table in structured:
        best_width, order, profile = tuned_width(table, restarts=4)
        lines.append(f"{label}: tuned width={best_width}, order={order}, profile={profile}")
    lines.append("")

    eq_graph = matching_graph(6)
    split_order = tuple(range(12))
    paired_order = tuple(i for pair in zip(range(6), range(6, 12), strict=True) for i in pair)
    lines.append(
        "equality interaction frontier: "
        f"split-order={frontier_width(split_order, eq_graph)}, "
        f"paired-order={frontier_width(paired_order, eq_graph)}"
    )
    lines.append("")

    for index, clause_count in enumerate((24, 36, 48), start=1):
        formula, table = random_k_cnf(12, clause_count, 3)
        sat_count = int(table.sum())
        natural_order = tuple(range(12))
        natural_width = width(table, natural_order)
        best_width, order, profile = tuned_width(table, restarts=6)
        graph = primal_graph(12, formula)
        graph_order, graph_frontier = tune_frontier_order(graph, restarts=64)
        graph_order_width = width(table, graph_order)
        lines.append(
            f"random-3CNF-{index}: clauses={clause_count}, satisfying={sat_count}/4096, "
            f"natural-width={natural_width}, tuned-width={best_width}, "
            f"tuned-frontier={frontier_width(order, graph)}, graph-frontier={graph_frontier}, "
            f"graph-order-width={graph_order_width}, order={order}, profile={profile}, "
            f"graph-order={graph_order}"
        )

    output = "\n".join(lines) + "\n"
    print(output, end="")
    Path("residual-search-output.txt").write_text(output, encoding="utf-8")


if __name__ == "__main__":
    main()
