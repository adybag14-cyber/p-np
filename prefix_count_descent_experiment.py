#!/usr/bin/env python3
"""Exact prefix-descent accounting for a planted 3-CNF.

The descent uses only one branch decision per input bit. Each decision is
implemented by exhaustive completion counting, exposing the difference between
query count and query cost.
"""

from __future__ import annotations

from dataclasses import dataclass
import random
import sys
from typing import Sequence

Clause = tuple[int, int, int]


@dataclass
class QueryResult:
    count: int
    evaluations: int


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
    return tuple(v if rng.getrandbits(1) else -v for v in variables)  # type: ignore[return-value]


def planted_cnf(n: int, clauses: int, planted: int, rng: random.Random) -> tuple[Clause, ...]:
    result: list[Clause] = []
    while len(result) < clauses:
        clause = random_clause(n, rng)
        if eval_clause(planted, clause):
            result.append(clause)
    return tuple(result)


def count_completions(
    n: int,
    clauses: Sequence[Clause],
    prefix_value: int,
    prefix_length: int,
) -> QueryResult:
    remaining = n - prefix_length
    count = 0
    evaluations = 1 << remaining
    for suffix in range(1 << remaining):
        assignment = prefix_value | (suffix << prefix_length)
        count += int(eval_cnf(assignment, clauses))
    return QueryResult(count, evaluations)


def greedy_witness(n: int, clauses: Sequence[Clause]) -> tuple[int | None, list[tuple[int, int, int, int]]]:
    prefix = 0
    trace: list[tuple[int, int, int, int]] = []
    total_evaluations = 0

    root = count_completions(n, clauses, prefix, 0)
    total_evaluations += root.evaluations
    if root.count == 0:
        return None, [(0, root.count, root.evaluations, total_evaluations)]

    # Choose the left/zero branch if it remains satisfiable; otherwise choose one.
    for depth in range(n):
        zero = count_completions(n, clauses, prefix, depth + 1)
        total_evaluations += zero.evaluations
        if zero.count > 0:
            chosen = 0
            surviving = zero.count
        else:
            chosen = 1
            prefix |= 1 << depth
            one = count_completions(n, clauses, prefix, depth + 1)
            total_evaluations += one.evaluations
            surviving = one.count
        trace.append((depth + 1, chosen, surviving, total_evaluations))

    return prefix, trace


def main() -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(newline="\n")
    rng = random.Random(0xC0_5A_7)
    n = 16
    planted = rng.randrange(1 << n)
    clauses = planted_cnf(n, round(4.5 * n), planted, rng)

    witness, trace = greedy_witness(n, clauses)
    total_models = count_completions(n, clauses, 0, 0)

    print("Exact prefix-count descent")
    print(f"n={n}, clauses={len(clauses)}, assignment-space={1 << n}")
    print(f"planted={planted:0{n}b}")
    print(f"model-count={total_models.count}")
    print()
    print("depth chosen-bit surviving-models cumulative-verifier-evaluations")
    for depth, chosen, surviving, evaluations in trace:
        print(f"{depth:5d} {chosen:10d} {surviving:16d} {evaluations:31d}")

    if witness is None:
        print("result=UNSAT")
    else:
        verified = eval_cnf(witness, clauses)
        print(f"result-witness={witness:0{n}b}")
        print(f"witness-verifies={verified}")

    print()
    print("Query accounting:")
    print(f"  branch levels = {n}")
    print(f"  exact branch queries <= {2 * n + 1}")
    print(f"  actual verifier evaluations = {trace[-1][3] if trace else total_models.evaluations}")
    print(f"  exhaustive root scan = {1 << n}")
    print("  few oracle calls do not imply low work when each oracle call enumerates completions")

    print()
    print("Residue examples for the exact root model count:")
    for modulus in (2, 3, 5, 7, 11, 17, 257, 65537):
        print(f"  mod {modulus:5d}: {total_models.count % modulus}")
    print("  any modulus larger than 2^n makes zero residue exact")
    print("  computing that residue for an arbitrary verifier remains the missing algorithm")


if __name__ == "__main__":
    main()
