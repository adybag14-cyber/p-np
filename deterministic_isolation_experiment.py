#!/usr/bin/env python3
"""Exact small-instance study of formula-dependent affine witness isolation.

The experiment deliberately separates three quantities:
1. whether a low-rank affine hash with a singleton witness bucket exists;
2. how many candidate hashes are searched before one is found;
3. the exhaustive witness evaluations used to identify the unique bucket.

The third quantity is the circular part: this script can discover the target bucket
because it already enumerates the satisfying set exactly.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
import random
import sys
from typing import Callable, Iterable, Sequence


AssignmentPredicate = Callable[[int], bool]
Clause = tuple[int, int, int]


@dataclass(frozen=True)
class IsolationResult:
    rank: int | None
    maps_tested: int
    target: int | None
    witness: int | None


def gf2_rank(rows: Sequence[int]) -> int:
    basis: dict[int, int] = {}
    for row in rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return len(basis)


def affine_span_dimension(points: Sequence[int]) -> int:
    if not points:
        return 0
    anchor = points[0]
    return gf2_rank([point ^ anchor for point in points[1:]])


def signature(value: int, rows: Sequence[int]) -> int:
    result = 0
    for index, row in enumerate(rows):
        result |= ((value & row).bit_count() & 1) << index
    return result


def independent_rows(n: int, rank: int, rng: random.Random) -> tuple[int, ...]:
    rows: list[int] = []
    while len(rows) < rank:
        candidate = rng.randrange(1, 1 << n)
        if gf2_rank([*rows, candidate]) == len(rows) + 1:
            rows.append(candidate)
    return tuple(rows)


def find_affine_isolator(
    witnesses: Sequence[int],
    n: int,
    rng: random.Random,
    random_trials_per_rank: int = 2500,
) -> IsolationResult:
    if not witnesses:
        return IsolationResult(None, 0, None, None)
    if len(witnesses) == 1:
        return IsolationResult(0, 1, 0, witnesses[0])

    maps_tested = 0

    # Exhaust every rank-one linear functional.
    for row in range(1, 1 << n):
        maps_tested += 1
        counts: Counter[int] = Counter(signature(w, (row,)) for w in witnesses)
        singleton_targets = [target for target, count in counts.items() if count == 1]
        if singleton_targets:
            target = min(singleton_targets)
            witness = next(w for w in witnesses if signature(w, (row,)) == target)
            return IsolationResult(1, maps_tested, target, witness)

    # Search higher-rank maps. Rank n always succeeds, so use the identity there.
    for rank in range(2, n + 1):
        candidates: Iterable[tuple[int, ...]]
        if rank == n:
            candidates = [tuple(1 << bit for bit in range(n))]
        else:
            candidates = (
                independent_rows(n, rank, rng)
                for _ in range(random_trials_per_rank)
            )

        for rows in candidates:
            maps_tested += 1
            buckets: dict[int, list[int]] = {}
            for witness in witnesses:
                buckets.setdefault(signature(witness, rows), []).append(witness)
            singleton_targets = [target for target, bucket in buckets.items() if len(bucket) == 1]
            if singleton_targets:
                target = min(singleton_targets)
                return IsolationResult(rank, maps_tested, target, buckets[target][0])

    raise AssertionError("identity map should isolate every witness")


def eval_clause(assignment: int, clause: Clause) -> bool:
    for literal in clause:
        variable = abs(literal) - 1
        bit = bool((assignment >> variable) & 1)
        if bit == (literal > 0):
            return True
    return False


def eval_cnf(assignment: int, clauses: Sequence[Clause]) -> bool:
    return all(eval_clause(assignment, clause) for clause in clauses)


def random_clause(n: int, rng: random.Random) -> Clause:
    variables = rng.sample(range(1, n + 1), 3)
    return tuple(variable if rng.getrandbits(1) else -variable for variable in variables)  # type: ignore[return-value]


def random_cnf(n: int, clause_count: int, rng: random.Random) -> tuple[Clause, ...]:
    return tuple(random_clause(n, rng) for _ in range(clause_count))


def planted_cnf(
    n: int,
    clause_count: int,
    planted: int,
    rng: random.Random,
) -> tuple[Clause, ...]:
    clauses: list[Clause] = []
    while len(clauses) < clause_count:
        clause = random_clause(n, rng)
        if eval_clause(planted, clause):
            clauses.append(clause)
    return tuple(clauses)


def enumerate_witnesses(n: int, predicate: AssignmentPredicate) -> list[int]:
    return [assignment for assignment in range(1 << n) if predicate(assignment)]


def exact_one(n: int) -> AssignmentPredicate:
    return lambda assignment: assignment.bit_count() == 1


def even_parity(_n: int) -> AssignmentPredicate:
    return lambda assignment: assignment.bit_count() % 2 == 0


def random_truth_set(n: int, density: float, rng: random.Random) -> AssignmentPredicate:
    accepted = {
        assignment
        for assignment in range(1 << n)
        if rng.random() < density
    }
    if not accepted:
        accepted.add(rng.randrange(1 << n))
    return accepted.__contains__


def format_assignment(value: int | None, n: int) -> str:
    if value is None:
        return "-"
    return format(value, f"0{n}b")


def main() -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(newline="\n")
    rng = random.Random(0x15_01_A7E)
    n = 12

    cases: list[tuple[str, AssignmentPredicate]] = [
        ("even-parity", even_parity(n)),
        ("exact-one", exact_one(n)),
        ("random-set-1/4", random_truth_set(n, 0.25, rng)),
    ]

    for index in range(4):
        clauses = random_cnf(n, round(4.2 * n), rng)
        cases.append((f"random-3cnf-{index + 1}", lambda assignment, c=clauses: eval_cnf(assignment, c)))

    planted = rng.randrange(1 << n)
    for index in range(3):
        clauses = planted_cnf(n, round(4.6 * n), planted, rng)
        cases.append((f"planted-3cnf-{index + 1}", lambda assignment, c=clauses: eval_cnf(assignment, c)))

    print("Formula-dependent affine isolation")
    print(f"n={n}, assignment space={1 << n}")
    print()
    print("case witnesses affine-dim min-rank maps-tested target isolated-witness")

    for name, predicate in cases:
        witnesses = enumerate_witnesses(n, predicate)
        dimension = affine_span_dimension(witnesses)
        result = find_affine_isolator(witnesses, n, rng)
        rank_text = "-" if result.rank is None else str(result.rank)
        target_text = "-" if result.target is None else str(result.target)
        print(
            f"{name:20s} {len(witnesses):9d} {dimension:10d} "
            f"{rank_text:8s} {result.maps_tested:11d} {target_text:6s} "
            f"{format_assignment(result.witness, n)}"
        )

    print()
    print("Exact accounting:")
    print(f"  exhaustive verifier evaluations per case = {1 << n}")
    print("  the target bucket was selected from a complete witness histogram")
    print("  therefore low-rank isolator existence is not yet a polynomial discovery algorithm")
    print()
    print("Black-box universal bound:")
    print(f"  any fixed-target family covering all witness subsets needs at least {1 << n} tests")
    print("  with hash buckets, hashes * inspected buckets must be at least the universe size")


if __name__ == "__main__":
    main()
