from __future__ import annotations

import random
from itertools import combinations

from memo_dpll import brute_sat, pigeonhole
from structural_dispatch import matching_sat, recognize_exact_bipartite_matching
from symbolic_cnf import CNF, normalize_cnf

SEED = 0x5245434F47
rng = random.Random(SEED)


def matching_encoding(rows: int, columns: int, allowed: set[tuple[int, int]]) -> tuple[CNF, int]:
    edge_to_var = {edge: index + 1 for index, edge in enumerate(sorted(allowed))}
    clauses: list[tuple[int, ...]] = []
    for row in range(rows):
        row_variables = [edge_to_var[(row, column)] for column in range(columns) if (row, column) in allowed]
        if not row_variables:
            # An empty row is represented by the empty clause; the recognizer
            # should reject it and brute force reports UNSAT.
            clauses.append(())
            continue
        clauses.append(tuple(row_variables))
        clauses.extend((-a, -b) for a, b in combinations(row_variables, 2))
    for column in range(columns):
        column_variables = [edge_to_var[(row, column)] for row in range(rows) if (row, column) in allowed]
        clauses.extend((-a, -b) for a, b in combinations(column_variables, 2))
    return normalize_cnf(clauses), len(edge_to_var)


def mutate(formula: CNF, n: int) -> CNF:
    clauses = [list(clause) for clause in formula]
    mode = rng.randrange(4)
    if mode == 0 and clauses:
        del clauses[rng.randrange(len(clauses))]
    elif mode == 1:
        length = rng.randrange(1, 5)
        clause = []
        for _ in range(length):
            variable = rng.randrange(n) + 1
            clause.append(variable if rng.getrandbits(1) else -variable)
        clauses.append(clause)
    elif mode == 2 and clauses:
        index = rng.randrange(len(clauses))
        if clauses[index]:
            literal = rng.randrange(len(clauses[index]))
            clauses[index][literal] = -clauses[index][literal]
    elif mode == 3 and clauses:
        clauses.append(list(rng.choice(clauses)))
    return normalize_cnf(clauses)


def main() -> None:
    valid_checked = 0
    valid_accepted = 0
    for _ in range(1000):
        rows = rng.randrange(2, 5)
        columns = rng.randrange(2, 5)
        allowed = {
            (row, column)
            for row in range(rows)
            for column in range(columns)
            if rng.random() < 0.65
        }
        formula, n = matching_encoding(rows, columns, allowed)
        if n > 16:
            continue
        expected = brute_sat(formula, n)
        encoding = recognize_exact_bipartite_matching(formula)
        valid_checked += 1
        if encoding is not None:
            valid_accepted += 1
            actual = matching_sat(encoding)
            if actual != expected:
                raise AssertionError((rows, columns, allowed, actual, expected, formula))

    base = pigeonhole(4, 3)
    mutation_accepted = 0
    mutation_rejected = 0
    for _ in range(1000):
        formula = mutate(base, 12)
        encoding = recognize_exact_bipartite_matching(formula)
        if encoding is None:
            mutation_rejected += 1
            continue
        mutation_accepted += 1
        actual = matching_sat(encoding)
        expected = brute_sat(formula, 12)
        if actual != expected:
            raise AssertionError((actual, expected, formula))

    print(
        f"seed={SEED}; random-valid-checked={valid_checked}; "
        f"recognized-valid={valid_accepted}; mutated-accepted={mutation_accepted}; "
        f"mutated-rejected={mutation_rejected}; all accepted dispatches matched brute force"
    )


if __name__ == '__main__':
    main()
