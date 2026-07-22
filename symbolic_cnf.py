from __future__ import annotations

import itertools
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

import residual_search as rs

# A literal is an integer: +(v+1) for x_v and -(v+1) for not x_v.
Literal = int
Clause = tuple[Literal, ...]
CNF = tuple[Clause, ...]
FALSE_CNF: CNF = ((),)
TRUE_CNF: CNF = ()


def normalize_clause(literals: Iterable[Literal]) -> Clause | None:
    values = set(literals)
    if any(-lit in values for lit in values):
        return None  # tautology, so the whole clause can be dropped
    return tuple(sorted(values, key=lambda lit: (abs(lit), lit < 0)))


def normalize_cnf(clauses: Iterable[Iterable[Literal]], subsumption: bool = True) -> CNF:
    normalized: set[Clause] = set()
    for clause in clauses:
        c = normalize_clause(clause)
        if c is None:
            continue
        if len(c) == 0:
            return FALSE_CNF
        normalized.add(c)
    if not normalized:
        return TRUE_CNF
    ordered = sorted(normalized, key=lambda c: (len(c), c))
    if subsumption:
        kept: list[Clause] = []
        kept_sets: list[frozenset[int]] = []
        # A nonempty retained clause that subsumes `clause` must contain at
        # least one literal occurring in `clause`. Index retained clauses by
        # literal, then test only that candidate union. This is semantically
        # identical to the old all-pairs scan but avoids quadratic behaviour
        # on large sparse encodings such as pigeonhole CNFs.
        literal_index: dict[int, list[int]] = {}
        for clause in ordered:
            clause_set = frozenset(clause)
            candidates: set[int] = set()
            for literal in clause:
                candidates.update(literal_index.get(literal, ()))
            if any(kept_sets[index] <= clause_set for index in candidates):
                continue
            index = len(kept)
            kept.append(clause)
            kept_sets.append(clause_set)
            for literal in clause:
                literal_index.setdefault(literal, []).append(index)
        ordered = kept
    return tuple(ordered)


def restrict_cnf(formula: CNF, variable: int, value: bool) -> CNF:
    if formula in (TRUE_CNF, FALSE_CNF):
        return formula
    true_lit = variable + 1 if value else -(variable + 1)
    false_lit = -true_lit
    residual: list[Clause] = []
    for clause in formula:
        if true_lit in clause:
            continue
        reduced = tuple(lit for lit in clause if lit != false_lit)
        if len(reduced) == 0:
            return FALSE_CNF
        residual.append(reduced)
    return normalize_cnf(residual)


def eval_cnf(formula: CNF, assignment: int, n: int) -> bool:
    if formula == TRUE_CNF:
        return True
    if formula == FALSE_CNF:
        return False
    for clause in formula:
        satisfied = False
        for lit in clause:
            variable = abs(lit) - 1
            bit = bool((assignment >> (n - 1 - variable)) & 1)
            if bit == (lit > 0):
                satisfied = True
                break
        if not satisfied:
            return False
    return True


def truth_table(formula: CNF, n: int) -> np.ndarray:
    return np.fromiter((eval_cnf(formula, a, n) for a in range(1 << n)), dtype=np.uint8)


def symbolic_profile(formula: CNF, order: Sequence[int]) -> list[int]:
    states: set[CNF] = {formula}
    profile = [1]
    for variable in order:
        next_states: set[CNF] = set()
        for state in states:
            next_states.add(restrict_cnf(state, variable, False))
            next_states.add(restrict_cnf(state, variable, True))
        states = next_states
        profile.append(len(states))
    return profile


def symbolic_width(formula: CNF, order: Sequence[int]) -> int:
    return max(symbolic_profile(formula, order))


def symbolic_sat(formula: CNF, order: Sequence[int]) -> bool:
    states: set[CNF] = {formula}
    for variable in order:
        next_states: set[CNF] = set()
        for state in states:
            next_states.add(restrict_cnf(state, variable, False))
            next_states.add(restrict_cnf(state, variable, True))
        states = next_states
    return TRUE_CNF in states


def greedy_symbolic_order(formula: CNF, n: int) -> tuple[int, ...]:
    states: set[CNF] = {formula}
    remaining = set(range(n))
    order: list[int] = []
    while remaining:
        candidates: list[tuple[int, int, int]] = []
        candidate_states: dict[int, set[CNF]] = {}
        for variable in sorted(remaining):
            next_states: set[CNF] = set()
            total_literals = 0
            for state in states:
                for value in (False, True):
                    residual = restrict_cnf(state, variable, value)
                    next_states.add(residual)
            total_literals = sum(sum(len(c) for c in state) for state in next_states)
            candidates.append((len(next_states), total_literals, variable))
            candidate_states[variable] = next_states
        _, _, selected = min(candidates)
        states = candidate_states[selected]
        order.append(selected)
        remaining.remove(selected)
    return tuple(order)


def tune_symbolic_order(
    formula: CNF, n: int, rng: random.Random, restarts: int = 32
) -> tuple[tuple[int, ...], int, list[int]]:
    starts: list[tuple[int, ...]] = [tuple(range(n)), greedy_symbolic_order(formula, n)]
    for _ in range(restarts):
        order = list(range(n))
        rng.shuffle(order)
        starts.append(tuple(order))
    best_order = starts[0]
    best_width = symbolic_width(formula, best_order)
    for start in starts:
        order = start
        current = symbolic_width(formula, order)
        improved = True
        while improved:
            improved = False
            local_order = order
            local_width = current
            # Adjacent swaps preserve enough locality to keep this source-aware search cheap.
            for i in range(n - 1):
                trial = list(order)
                trial[i], trial[i + 1] = trial[i + 1], trial[i]
                trial_t = tuple(trial)
                w = symbolic_width(formula, trial_t)
                if w < local_width:
                    local_order, local_width = trial_t, w
            if local_width < current:
                order, current, improved = local_order, local_width, True
        if current < best_width:
            best_order, best_width = order, current
    return best_order, best_width, symbolic_profile(formula, best_order)


def from_random_formula(formula: Sequence[rs.Clause]) -> CNF:
    clauses: list[Clause] = []
    for clause in formula:
        literals = []
        for variable, positive in zip(clause.variables, clause.positive, strict=True):
            literals.append(variable + 1 if positive else -(variable + 1))
        clauses.append(tuple(literals))
    return normalize_cnf(clauses)


def equality_cnf(half: int) -> CNF:
    clauses: list[Clause] = []
    for i in range(half):
        a = i + 1
        b = i + half + 1
        clauses.append((-a, b))
        clauses.append((a, -b))
    return normalize_cnf(clauses)


def verify_restriction_exhaustively(formula: CNF, n: int) -> None:
    table = truth_table(formula, n)
    for variable in range(n):
        for value in (False, True):
            residual = restrict_cnf(formula, variable, value)
            for assignment in range(1 << n):
                bit = bool((assignment >> (n - 1 - variable)) & 1)
                if bit != value:
                    continue
                if eval_cnf(residual, assignment, n) != bool(table[assignment]):
                    raise AssertionError((formula, variable, value, assignment, residual))


def run() -> str:
    seed = 0x53594D434E46
    rng = random.Random(seed)
    lines = ["Symbolic CNF residual experiment", f"seed={seed}", ""]

    eq = equality_cnf(6)
    verify_restriction_exhaustively(eq, 12)
    split = tuple(range(12))
    paired = tuple(i for pair in zip(range(6), range(6, 12), strict=True) for i in pair)
    eq_table = truth_table(eq, 12)
    lines.append(
        "equality-6+6: "
        f"split symbolic={symbolic_width(eq, split)}, split semantic={rs.width(eq_table, split)}, "
        f"paired symbolic={symbolic_width(eq, paired)}, paired semantic={rs.width(eq_table, paired)}"
    )
    lines.append("")

    for index, clause_count in enumerate((24, 36, 48), start=1):
        source_formula, source_table = rs.random_k_cnf(12, clause_count, 3)
        formula = from_random_formula(source_formula)
        verify_restriction_exhaustively(formula, 12)
        table = truth_table(formula, 12)
        if not np.array_equal(table, source_table):
            raise AssertionError("CNF conversion changed the truth table")
        natural = tuple(range(12))
        symbolic_order, symbolic_best, symbolic_prof = tune_symbolic_order(
            formula, 12, rng, restarts=12
        )
        semantic_width_on_symbolic = rs.width(table, symbolic_order)
        direct_width, direct_order, direct_profile = rs.tuned_width(table, restarts=2)
        lines.append(
            f"random-3CNF-{index}: clauses={clause_count}, satisfying={int(table.sum())}/4096, "
            f"natural symbolic={symbolic_width(formula, natural)}, "
            f"natural semantic={rs.width(table, natural)}, symbolic-best={symbolic_best}, "
            f"semantic-on-symbolic-order={semantic_width_on_symbolic}, direct-semantic={direct_width}, "
            f"symbolic-order={symbolic_order}, direct-order={direct_order}, "
            f"symbolic-profile={symbolic_prof}, direct-profile={direct_profile}"
        )

    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("symbolic-cnf-output.txt").write_text(output, encoding="utf-8")
