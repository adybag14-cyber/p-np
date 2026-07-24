from __future__ import annotations

import itertools
import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Sequence


@dataclass(frozen=True)
class Observable:
    name: str
    support: tuple[int, ...]
    evaluate: Callable[[tuple[bool, ...]], bool]


@dataclass
class Factor:
    scope: tuple[int, ...]
    rows: set[int]

    @property
    def mask(self) -> int:
        result = 0
        for variable in self.scope:
            result |= 1 << variable
        return result


@dataclass
class EliminationStats:
    final_image_size: int
    max_rows: int
    max_scope: int
    join_pair_checks: int
    factors_created: int
    order: tuple[int, ...]
    elapsed_seconds: float


def factor_for_observable(n: int, index: int, observable: Observable) -> Factor:
    output = n + index
    rows: set[int] = set()
    for assignment in range(1 << len(observable.support)):
        values = tuple(bool((assignment >> offset) & 1) for offset in range(len(observable.support)))
        row = 0
        for offset, variable in enumerate(observable.support):
            if values[offset]:
                row |= 1 << variable
        if observable.evaluate(values):
            row |= 1 << output
        rows.add(row)
    return Factor(tuple(sorted(observable.support + (output,))), rows)


def join(left: Factor, right: Factor) -> tuple[Factor, int]:
    overlap = left.mask & right.mask
    checks = 0
    if not overlap:
        rows = {a | b for a in left.rows for b in right.rows}
        return Factor(tuple(sorted(set(left.scope) | set(right.scope))), rows), len(left.rows) * len(right.rows)

    if len(left.rows) > len(right.rows):
        left, right = right, left
    index: dict[int, list[int]] = {}
    for row in right.rows:
        index.setdefault(row & overlap, []).append(row)
    rows: set[int] = set()
    for row in left.rows:
        matches = index.get(row & overlap, ())
        checks += len(matches)
        for other in matches:
            rows.add(row | other)
    return Factor(tuple(sorted(set(left.scope) | set(right.scope))), rows), checks


def project_out(factor: Factor, variable: int) -> Factor:
    mask = ~(1 << variable)
    return Factor(tuple(v for v in factor.scope if v != variable), {row & mask for row in factor.rows})


def estimated_join_rows(left: Factor, right: Factor) -> int:
    overlap_count = len(set(left.scope) & set(right.scope))
    return max(1, (len(left.rows) * len(right.rows)) >> overlap_count)


def join_bucket(factors: list[Factor], stats: dict[str, int]) -> Factor:
    work = list(factors)
    while len(work) > 1:
        best: tuple[int, int, int] | None = None
        for i in range(len(work)):
            for j in range(i + 1, len(work)):
                estimate = estimated_join_rows(work[i], work[j])
                candidate = (estimate, i, j)
                if best is None or candidate < best:
                    best = candidate
        assert best is not None
        _, i, j = best
        right = work.pop(j)
        left = work.pop(i)
        merged, checks = join(left, right)
        stats["checks"] += checks
        stats["created"] += 1
        stats["max_rows"] = max(stats["max_rows"], len(merged.rows))
        stats["max_scope"] = max(stats["max_scope"], len(merged.scope))
        work.append(merged)
    return work[0]


def choose_variable(factors: Sequence[Factor], remaining: set[int]) -> int:
    candidates: list[tuple[int, int, int, int]] = []
    for variable in remaining:
        bucket = [factor for factor in factors if variable in factor.scope]
        if not bucket:
            candidates.append((0, 0, 0, variable))
            continue
        union_scope = set().union(*(set(f.scope) for f in bucket))
        estimated = 1
        for factor in bucket:
            estimated *= max(1, len(factor.rows))
        estimated >>= max(0, sum(len(f.scope) for f in bucket) - len(union_scope))
        candidates.append((len(union_scope), estimated, len(bucket), variable))
    return min(candidates)[-1]


def generate_image(n: int, observables: Sequence[Observable]) -> EliminationStats:
    started = time.perf_counter()
    factors = [factor_for_observable(n, i, observable) for i, observable in enumerate(observables)]
    stats = {
        "checks": 0,
        "created": len(factors),
        "max_rows": max((len(f.rows) for f in factors), default=1),
        "max_scope": max((len(f.scope) for f in factors), default=0),
    }
    remaining = set(range(n))
    order: list[int] = []
    while remaining:
        variable = choose_variable(factors, remaining)
        remaining.remove(variable)
        order.append(variable)
        bucket = [factor for factor in factors if variable in factor.scope]
        factors = [factor for factor in factors if variable not in factor.scope]
        if not bucket:
            continue
        merged = join_bucket(bucket, stats)
        projected = project_out(merged, variable)
        stats["created"] += 1
        stats["max_rows"] = max(stats["max_rows"], len(projected.rows))
        stats["max_scope"] = max(stats["max_scope"], len(projected.scope))
        factors.append(projected)
    if factors:
        final = join_bucket(factors, stats)
    else:
        final = Factor((), {0})
    return EliminationStats(
        final_image_size=len(final.rows),
        max_rows=stats["max_rows"],
        max_scope=stats["max_scope"],
        join_pair_checks=stats["checks"],
        factors_created=stats["created"],
        order=tuple(order),
        elapsed_seconds=time.perf_counter() - started,
    )


def xor_observable(name: str, support: Iterable[int]) -> Observable:
    support_tuple = tuple(support)
    return Observable(name, support_tuple, lambda bits: sum(bits) % 2 == 1)


def majority_observable(name: str, support: Iterable[int]) -> Observable:
    support_tuple = tuple(support)
    threshold = (len(support_tuple) + 1) // 2
    return Observable(name, support_tuple, lambda bits: sum(bits) >= threshold)


def exact_weight_observable(name: str, support: Iterable[int], target: int) -> Observable:
    support_tuple = tuple(support)
    return Observable(name, support_tuple, lambda bits: sum(bits) == target)


def gf2_rank(masks: Sequence[int]) -> int:
    pivots: dict[int, int] = {}
    for value in masks:
        row = value
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def random_3cnf_observable(n: int, clauses: int, rng: random.Random) -> Observable:
    formula: list[tuple[tuple[int, bool], ...]] = []
    for _ in range(clauses):
        variables = rng.sample(range(n), 3)
        formula.append(tuple((variable, bool(rng.getrandbits(1))) for variable in variables))

    def evaluate(bits: tuple[bool, ...]) -> bool:
        return all(any(bits[variable] == positive for variable, positive in clause) for clause in formula)

    return Observable(f"random-3sat-{clauses}", tuple(range(n)), evaluate)


def direct_generator_note(n: int, observables: Sequence[Observable]) -> str:
    if all(observable.name.startswith("xor") for observable in observables):
        masks = [sum(1 << variable for variable in observable.support) for observable in observables]
        rank = gf2_rank(masks)
        return f"linear-rank={rank}, algebraic-image={1 << rank}"
    if len(observables) == 1 and observables[0].name.startswith(("majority", "exact-weight")):
        return "direct-combinatorial-image<=2"
    if len(observables) == 1 and observables[0].name.startswith("random-3sat"):
        return "two output values, but true-reachability is SAT"
    return "no specialised generator supplied"


def run() -> str:
    seed = 0x51A6E
    rng = random.Random(seed)
    n = 18
    systems: list[tuple[str, list[Observable]]] = []
    systems.append(("disjoint-pair-xor", [xor_observable(f"xor-{i}", (2 * i, 2 * i + 1)) for i in range(9)]))
    systems.append(("overlapping-local-xor", [xor_observable(f"xor-{i}", (i, i + 1, i + 2)) for i in range(10)]))
    systems.append(("local-majority-triples", [majority_observable(f"maj-{i}", (i, i + 1, i + 2)) for i in range(10)]))
    random_local: list[Observable] = []
    for i in range(10):
        support = tuple(sorted(rng.sample(range(n), 3)))
        mode = rng.choice(("xor", "majority"))
        random_local.append(xor_observable(f"xor-random-{i}", support) if mode == "xor" else majority_observable(f"maj-random-{i}", support))
    systems.append(("random-local", random_local))
    systems.append(("global-parity", [xor_observable("xor-global", range(n))]))
    systems.append(("global-majority", [majority_observable("majority-global", range(n))]))
    systems.append(("global-exact-one", [exact_weight_observable("exact-weight-1", range(n), 1)]))
    systems.append(("verifier-output-feature", [random_3cnf_observable(n, 76, rng)]))

    lines = [
        "Observable reachable-image elimination experiment",
        f"seed={seed}, input-variables={n}",
        "Small image size is reported separately from the cost of generating that image.",
        "",
    ]
    for label, observables in systems:
        stats = generate_image(n, observables)
        lines.append(
            f"{label}: observables={len(observables)}, image={stats.final_image_size}, "
            f"max-rows={stats.max_rows}, max-scope={stats.max_scope}, "
            f"join-checks={stats.join_pair_checks}, factors={stats.factors_created}, "
            f"seconds={stats.elapsed_seconds:.3f}; {direct_generator_note(n, observables)}"
        )
        lines.append(f"  elimination-order={stats.order}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("observable-image-elimination-output.txt").write_text(output, encoding="utf-8")
