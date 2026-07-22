from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from adaptive_policy_search import build_policy_dag, improve_policy, verify_policy
from adaptive_semantic_dag import Signature, cofactor_signature, reduce_signature
from optimal_obdd import best_obdd


@dataclass(frozen=True)
class Candidate:
    closure: frozenset[Signature]
    choices: tuple[tuple[Signature, int], ...]

    @property
    def size(self) -> int:
        return len(self.closure)

    def choice_map(self) -> dict[Signature, int]:
        return dict(self.choices)


def compatible(left: Candidate, right: Candidate) -> bool:
    left_choices = left.choice_map()
    right_choices = right.choice_map()
    for signature in left_choices.keys() & right_choices.keys():
        if left_choices[signature] != right_choices[signature]:
            return False
    return True


def merge_candidates(
    signature: Signature,
    variable: int,
    left: Candidate,
    right: Candidate,
) -> Candidate:
    if not compatible(left, right):
        raise ValueError("incompatible policies")
    choices = left.choice_map()
    choices.update(right.choice_map())
    choices[signature] = variable
    return Candidate(
        frozenset((signature,)) | left.closure | right.closure,
        tuple(sorted(choices.items())),
    )


def dominates(left: Candidate, right: Candidate) -> bool:
    if not left.closure <= right.closure:
        return False
    left_choices = left.choice_map()
    right_choices = right.choice_map()
    for signature, variable in left_choices.items():
        if right_choices.get(signature) != variable:
            return False
    return True


def prune(candidates: list[Candidate]) -> tuple[Candidate, ...]:
    unique: dict[tuple[tuple[Signature, int], ...], Candidate] = {}
    for candidate in candidates:
        previous = unique.get(candidate.choices)
        if previous is None or candidate.size < previous.size:
            unique[candidate.choices] = candidate
    ordered = sorted(unique.values(), key=lambda candidate: (candidate.size, candidate.choices))
    kept: list[Candidate] = []
    for candidate in ordered:
        if any(dominates(existing, candidate) for existing in kept):
            continue
        kept = [existing for existing in kept if not dominates(candidate, existing)]
        kept.append(candidate)
    return tuple(kept)


def exact_frontier(root: Signature) -> tuple[Candidate, ...]:
    @lru_cache(maxsize=None)
    def frontier(signature: Signature) -> tuple[Candidate, ...]:
        variables, _pattern = signature
        if not variables:
            return (Candidate(frozenset((signature,)), ()),)
        generated: list[Candidate] = []
        for position, variable in enumerate(variables):
            low = cofactor_signature(signature, position, 0)
            high = cofactor_signature(signature, position, 1)
            for left in frontier(low):
                for right in frontier(high):
                    if compatible(left, right):
                        generated.append(
                            merge_candidates(signature, variable, left, right)
                        )
        if not generated:
            raise AssertionError("no coherent policy candidate")
        return prune(generated)

    return frontier(root)


def exact_optimal_policy(table: int, n: int) -> Candidate:
    root = reduce_signature(tuple(range(n)), table)
    frontier = exact_frontier(root)
    return min(frontier, key=lambda candidate: (candidate.size, candidate.choices))


def validate_candidate(table: int, n: int, candidate: Candidate) -> int:
    fallback = tuple(range(n))
    dag = build_policy_dag(table, n, fallback, candidate.choice_map())
    verify_policy(table, n, dag)
    if dag.reachable != candidate.closure:
        raise AssertionError((len(dag.reachable), candidate.size))
    if dag.size != candidate.size:
        raise AssertionError((dag.size, candidate.size))
    return dag.size


def deterministic_tables(n: int, count: int, seed: int) -> list[int]:
    rng = random.Random(seed)
    limit = 1 << (1 << n)
    tables = {0, limit - 1}
    while len(tables) < count:
        tables.add(rng.randrange(limit))
    return sorted(tables)


def analyse_table(table: int, n: int, allow_greedy: bool) -> tuple[int, int, int, int]:
    orders = tuple(itertools.permutations(range(n)))
    ordered = best_obdd(table, n, orders)
    exact = exact_optimal_policy(table, n)
    exact_size = validate_candidate(table, n, exact)
    if allow_greedy:
        greedy, _overrides, baseline = improve_policy(
            table, n, ordered.order, pair_search=False, max_rounds=10
        )
        if baseline != ordered.size:
            raise AssertionError((baseline, ordered.size))
        greedy_size = greedy.size
    else:
        greedy_size = ordered.size
    if exact_size > greedy_size or greedy_size > ordered.size:
        raise AssertionError((exact_size, greedy_size, ordered.size))
    return ordered.size, greedy_size, exact_size, len(exact_frontier(reduce_signature(tuple(range(n)), table)))


def run() -> str:
    started = time.perf_counter()
    lines = [
        "Exact coherent adaptive-policy dynamic program",
        "Policies are combined only when their choices agree on every shared residual signature.",
        "",
    ]
    suites = [
        (4, deterministic_tables(4, 64, 0xC0DE_196), True),
        (5, deterministic_tables(5, 2, 0xC0DE_197), False),
    ]
    global_counts: Counter[str] = Counter()
    examples: list[str] = []
    for n, tables, allow_greedy in suites:
        counts: Counter[str] = Counter()
        frontier_sizes: list[int] = []
        for table in tables:
            ordered, greedy, exact, frontier_size = analyse_table(table, n, allow_greedy)
            frontier_sizes.append(frontier_size)
            counts[f"ordered_gap_{ordered - exact}"] += 1
            counts[f"greedy_gap_{greedy - exact}"] += 1
            if exact < ordered and len(examples) < 20:
                examples.append(
                    f"table=0x{table:0{1 << max(0, n - 2)}x}, n={n}, "
                    f"ordered={ordered}, greedy={greedy}, exact={exact}, "
                    f"frontier={frontier_size}"
                )
        for key, value in counts.items():
            global_counts[key] += value
        ordered_dist = ", ".join(
            f"gap {key.split('_')[-1]}={value}"
            for key, value in sorted(counts.items())
            if key.startswith("ordered_gap_")
        )
        greedy_dist = ", ".join(
            f"gap {key.split('_')[-1]}={value}"
            for key, value in sorted(counts.items())
            if key.startswith("greedy_gap_")
        )
        lines.append(f"n={n}, tables={len(tables)}")
        lines.append("optimal OBDD minus exact adaptive: " + ordered_dist)
        lines.append("greedy adaptive minus exact adaptive: " + greedy_dist)
        lines.append(
            f"coherent frontier sizes: min={min(frontier_sizes)}, "
            f"max={max(frontier_sizes)}, mean={sum(frontier_sizes) / len(frontier_sizes):.2f}"
        )
        lines.append("")

    lines.append("strict exact-adaptive improvements:")
    lines.extend(examples if examples else ["none"])
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("coherent-policy-dp-output.txt").write_text(output, encoding="utf-8")
