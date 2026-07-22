from __future__ import annotations

import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from symbolic_cnf import (
    CNF,
    FALSE_CNF,
    TRUE_CNF,
    eval_cnf,
    normalize_cnf,
    restrict_cnf,
)


class NodeLimitExceeded(RuntimeError):
    pass


@dataclass
class SolveStats:
    calls: int = 0
    unique_states: int = 0
    cache_hits: int = 0
    unit_assignments: int = 0
    component_splits: int = 0
    branches: int = 0
    max_depth: int = 0
    elapsed_seconds: float = 0.0


def variables_in(formula: CNF) -> set[int]:
    return {abs(lit) - 1 for clause in formula for lit in clause}


def unit_propagate(formula: CNF) -> tuple[CNF, dict[int, bool]]:
    forced: dict[int, bool] = {}
    current = formula
    while current not in (TRUE_CNF, FALSE_CNF):
        unit = next((clause[0] for clause in current if len(clause) == 1), None)
        if unit is None:
            break
        variable = abs(unit) - 1
        value = unit > 0
        previous = forced.get(variable)
        if previous is not None and previous != value:
            return FALSE_CNF, forced
        forced[variable] = value
        current = restrict_cnf(current, variable, value)
    return current, forced


def split_components(formula: CNF) -> tuple[CNF, ...]:
    if formula in (TRUE_CNF, FALSE_CNF):
        return (formula,)
    clause_vars = [set(abs(lit) - 1 for lit in clause) for clause in formula]
    remaining = set(range(len(formula)))
    components: list[CNF] = []
    while remaining:
        seed = remaining.pop()
        indices = {seed}
        vars_seen = set(clause_vars[seed])
        changed = True
        while changed:
            changed = False
            attached = {i for i in remaining if clause_vars[i] & vars_seen}
            if attached:
                remaining -= attached
                indices |= attached
                for i in attached:
                    vars_seen |= clause_vars[i]
                changed = True
        components.append(normalize_cnf(formula[i] for i in sorted(indices)))
    return tuple(sorted(components, key=lambda f: (len(f), f)))


def choose_variable(formula: CNF) -> tuple[int, bool]:
    # Jeroslow-Wang style structural score. This uses only the CNF text.
    positive: dict[int, float] = {}
    negative: dict[int, float] = {}
    for clause in formula:
        weight = 2.0 ** (-len(clause))
        for lit in clause:
            variable = abs(lit) - 1
            target = positive if lit > 0 else negative
            target[variable] = target.get(variable, 0.0) + weight
    variables = set(positive) | set(negative)
    variable = max(
        variables,
        key=lambda v: (positive.get(v, 0.0) + negative.get(v, 0.0), -v),
    )
    preferred = positive.get(variable, 0.0) >= negative.get(variable, 0.0)
    return variable, preferred


def solve_cnf(
    formula: CNF,
    *,
    node_limit: int = 2_000_000,
    enable_components: bool = True,
) -> tuple[bool, SolveStats]:
    cache: dict[CNF, bool] = {}
    stats = SolveStats()
    started = time.perf_counter()

    def solve(state: CNF, depth: int) -> bool:
        stats.calls += 1
        stats.max_depth = max(stats.max_depth, depth)
        if stats.calls > node_limit:
            raise NodeLimitExceeded(f"node limit {node_limit} exceeded")

        state, forced = unit_propagate(state)
        stats.unit_assignments += len(forced)
        if state == TRUE_CNF:
            return True
        if state == FALSE_CNF:
            return False
        if state in cache:
            stats.cache_hits += 1
            return cache[state]

        if enable_components:
            components = split_components(state)
            if len(components) > 1:
                stats.component_splits += 1
                result = all(solve(component, depth + 1) for component in components)
                cache[state] = result
                return result

        variable, preferred = choose_variable(state)
        stats.branches += 1
        first = restrict_cnf(state, variable, preferred)
        if solve(first, depth + 1):
            cache[state] = True
            return True
        second = restrict_cnf(state, variable, not preferred)
        result = solve(second, depth + 1)
        cache[state] = result
        return result

    try:
        result = solve(normalize_cnf(formula), 0)
    finally:
        stats.elapsed_seconds = time.perf_counter() - started
        stats.unique_states = len(cache)
    return result, stats


def random_3cnf(n: int, clauses: int, rng: random.Random) -> CNF:
    output = []
    for _ in range(clauses):
        variables = rng.sample(range(n), 3)
        clause = tuple((v + 1) if rng.getrandbits(1) else -(v + 1) for v in variables)
        output.append(clause)
    return normalize_cnf(output)


def planted_3cnf(n: int, clauses: int, rng: random.Random) -> tuple[CNF, int]:
    planted = rng.getrandbits(n)
    output = []
    for _ in range(clauses):
        variables = rng.sample(range(n), 3)
        while True:
            clause = tuple((v + 1) if rng.getrandbits(1) else -(v + 1) for v in variables)
            if any(
                bool((planted >> (n - 1 - (abs(lit) - 1))) & 1) == (lit > 0)
                for lit in clause
            ):
                output.append(clause)
                break
    return normalize_cnf(output), planted


def pigeonhole(pigeons: int, holes: int) -> CNF:
    def var(p: int, h: int) -> int:
        return p * holes + h + 1

    clauses: list[tuple[int, ...]] = []
    for p in range(pigeons):
        clauses.append(tuple(var(p, h) for h in range(holes)))
    for p in range(pigeons):
        for h1 in range(holes):
            for h2 in range(h1 + 1, holes):
                clauses.append((-var(p, h1), -var(p, h2)))
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                clauses.append((-var(p1, h), -var(p2, h)))
    return normalize_cnf(clauses)


def disconnected_formula(component_count: int, component_vars: int, rng: random.Random) -> CNF:
    clauses: list[tuple[int, ...]] = []
    for component in range(component_count):
        offset = component * component_vars
        local = random_3cnf(component_vars, 4 * component_vars, rng)
        for clause in local:
            shifted = tuple((1 if lit > 0 else -1) * (abs(lit) + offset) for lit in clause)
            clauses.append(shifted)
    return normalize_cnf(clauses)


def brute_sat(formula: CNF, n: int) -> bool:
    return any(eval_cnf(formula, assignment, n) for assignment in range(1 << n))


def stats_line(label: str, n: int, result: bool | None, stats: SolveStats | None, note: str = "") -> str:
    if stats is None:
        return f"{label}: n={n}, result=cutoff, {note}"
    ratio = stats.unique_states / (2 ** n)
    return (
        f"{label}: n={n}, result={result}, unique={stats.unique_states}, calls={stats.calls}, "
        f"cache-hits={stats.cache_hits}, units={stats.unit_assignments}, "
        f"component-splits={stats.component_splits}, branches={stats.branches}, "
        f"depth={stats.max_depth}, state/2^n={ratio:.6g}, seconds={stats.elapsed_seconds:.4f}"
        + (f", {note}" if note else "")
    )


def run_benchmarks() -> str:
    seed = 0x44504C4C
    rng = random.Random(seed)
    lines = ["Memoized symbolic DPLL experiment", f"seed={seed}", ""]

    # Exhaustive correctness checks at sizes where brute force is inexpensive.
    for n in (8, 10, 12):
        formula = random_3cnf(n, round(4.2 * n), rng)
        expected = brute_sat(formula, n)
        result, stats = solve_cnf(formula)
        if result != expected:
            raise AssertionError((n, result, expected, formula))
        lines.append(stats_line(f"verified-random-{n}", n, result, stats, "checked by brute force"))
    lines.append("")

    # Random and planted near-threshold formulas.
    for family in ("random", "planted"):
        for n in (20, 30, 40, 50, 60):
            clauses = round(4.2 * n)
            if family == "random":
                formula = random_3cnf(n, clauses, rng)
                note = f"clauses={clauses}"
            else:
                formula, planted = planted_3cnf(n, clauses, rng)
                note = f"clauses={clauses}, planted-assignment-present"
            try:
                result, stats = solve_cnf(formula, node_limit=2_000_000)
                lines.append(stats_line(f"{family}-{n}", n, result, stats, note))
            except NodeLimitExceeded:
                lines.append(stats_line(f"{family}-{n}", n, None, None, note + ", node-limit=2000000"))
    lines.append("")

    for pigeons, holes in ((4, 3), (5, 4), (6, 5), (7, 6)):
        formula = pigeonhole(pigeons, holes)
        n = pigeons * holes
        try:
            result, stats = solve_cnf(formula, node_limit=2_000_000)
            lines.append(stats_line(f"pigeonhole-{pigeons}-{holes}", n, result, stats))
        except NodeLimitExceeded:
            lines.append(stats_line(f"pigeonhole-{pigeons}-{holes}", n, None, None, "node-limit=2000000"))
    lines.append("")

    formula = disconnected_formula(10, 4, rng)
    result_with, stats_with = solve_cnf(formula, enable_components=True)
    result_without, stats_without = solve_cnf(formula, enable_components=False)
    if result_with != result_without:
        raise AssertionError("component splitting changed satisfiability")
    lines.append(stats_line("disconnected-with-components", 40, result_with, stats_with))
    lines.append(stats_line("disconnected-without-components", 40, result_without, stats_without))

    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run_benchmarks()
    print(output, end="")
    Path("memo-dpll-output.txt").write_text(output, encoding="utf-8")
