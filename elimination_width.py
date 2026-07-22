from __future__ import annotations

import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable

from memo_dpll import brute_sat, pigeonhole, planted_3cnf, random_3cnf
from symbolic_cnf import CNF, FALSE_CNF, TRUE_CNF, normalize_cnf
from xor_affine import random_3xor


class ClauseLimitExceeded(RuntimeError):
    pass


@dataclass
class EliminationStats:
    order: tuple[int, ...]
    result: bool
    steps: int
    peak_clauses: int
    peak_clause_width: int
    peak_incidence_product: int
    raw_resolvents: int
    kept_resolvents: int
    elapsed_seconds: float
    cutoff: bool = False


def variables_in(formula: CNF) -> set[int]:
    return {abs(lit) - 1 for clause in formula for lit in clause}


def resolve_pair(positive: tuple[int, ...], negative: tuple[int, ...], variable: int) -> tuple[int, ...] | None:
    pos_lit = variable + 1
    neg_lit = -pos_lit
    merged = set(positive)
    merged.discard(pos_lit)
    merged.update(negative)
    merged.discard(neg_lit)
    if any(-lit in merged for lit in merged):
        return None
    return tuple(sorted(merged, key=lambda lit: (abs(lit), lit < 0)))


def elimination_preview(formula: CNF, variable: int) -> tuple[int, int, int, int]:
    lit = variable + 1
    positive = [clause for clause in formula if lit in clause]
    negative = [clause for clause in formula if -lit in clause]
    raw = len(positive) * len(negative)
    unique: set[tuple[int, ...]] = set()
    maximum_width = 0
    for p_clause in positive:
        for n_clause in negative:
            resolvent = resolve_pair(p_clause, n_clause, variable)
            if resolvent is not None:
                unique.add(resolvent)
                maximum_width = max(maximum_width, len(resolvent))
    return raw, len(unique), maximum_width, len(positive) + len(negative)


def eliminate_variable(formula: CNF, variable: int, clause_limit: int) -> tuple[CNF, int, int, int]:
    if formula in (TRUE_CNF, FALSE_CNF):
        return formula, 0, 0, 0
    lit = variable + 1
    positive = [clause for clause in formula if lit in clause]
    negative = [clause for clause in formula if -lit in clause]
    untouched = [clause for clause in formula if lit not in clause and -lit not in clause]
    raw = len(positive) * len(negative)
    resolvents: set[tuple[int, ...]] = set()
    max_width = 0
    for p_clause in positive:
        for n_clause in negative:
            resolvent = resolve_pair(p_clause, n_clause, variable)
            if resolvent is not None:
                resolvents.add(resolvent)
                max_width = max(max_width, len(resolvent))
                if len(untouched) + len(resolvents) > clause_limit:
                    raise ClauseLimitExceeded(clause_limit)
    result = normalize_cnf((*untouched, *resolvents))
    if len(result) > clause_limit:
        raise ClauseLimitExceeded(clause_limit)
    return result, raw, len(resolvents), max_width


def natural_order(formula: CNF) -> list[int]:
    return sorted(variables_in(formula))


def reverse_order(formula: CNF) -> list[int]:
    return sorted(variables_in(formula), reverse=True)


def greedy_order(formula: CNF, score_mode: str) -> list[int]:
    state = formula
    order: list[int] = []
    while state not in (TRUE_CNF, FALSE_CNF):
        variables = variables_in(state)
        if not variables:
            break
        previews = {variable: elimination_preview(state, variable) for variable in variables}
        if score_mode == "product":
            key = lambda variable: (previews[variable][0], previews[variable][1], previews[variable][2], variable)
        elif score_mode == "fill":
            key = lambda variable: (previews[variable][1], previews[variable][2], previews[variable][0], variable)
        elif score_mode == "width":
            key = lambda variable: (previews[variable][2], previews[variable][1], previews[variable][0], variable)
        else:
            raise ValueError(score_mode)
        variable = min(variables, key=key)
        order.append(variable)
        state, _raw, _kept, _width = eliminate_variable(state, variable, clause_limit=250_000)
    remaining = sorted(variables_in(formula) - set(order))
    return order + remaining


def run_order(formula: CNF, order: Iterable[int], *, clause_limit: int = 250_000) -> EliminationStats:
    state = normalize_cnf(formula)
    order_tuple = tuple(order)
    peak_clauses = len(state)
    peak_width = max((len(clause) for clause in state), default=0)
    peak_product = 0
    raw_total = 0
    kept_total = 0
    started = time.perf_counter()
    steps = 0
    try:
        for variable in order_tuple:
            if state in (TRUE_CNF, FALSE_CNF):
                break
            preview = elimination_preview(state, variable)
            peak_product = max(peak_product, preview[0])
            state, raw, kept, width = eliminate_variable(state, variable, clause_limit)
            raw_total += raw
            kept_total += kept
            peak_clauses = max(peak_clauses, len(state))
            peak_width = max(peak_width, width, max((len(clause) for clause in state), default=0))
            steps += 1
        if state not in (TRUE_CNF, FALSE_CNF):
            for variable in sorted(variables_in(state)):
                preview = elimination_preview(state, variable)
                peak_product = max(peak_product, preview[0])
                state, raw, kept, width = eliminate_variable(state, variable, clause_limit)
                raw_total += raw
                kept_total += kept
                peak_clauses = max(peak_clauses, len(state))
                peak_width = max(peak_width, width, max((len(clause) for clause in state), default=0))
                steps += 1
                if state in (TRUE_CNF, FALSE_CNF):
                    break
        result = state != FALSE_CNF
        return EliminationStats(
            order_tuple, result, steps, peak_clauses, peak_width, peak_product,
            raw_total, kept_total, time.perf_counter() - started,
        )
    except ClauseLimitExceeded:
        return EliminationStats(
            order_tuple, False, steps, peak_clauses, peak_width, peak_product,
            raw_total, kept_total, time.perf_counter() - started, cutoff=True,
        )


def equality_pairs(pair_count: int) -> CNF:
    clauses: list[tuple[int, ...]] = []
    for index in range(pair_count):
        left = index + 1
        right = pair_count + index + 1
        clauses.append((-left, right))
        clauses.append((left, -right))
    return normalize_cnf(clauses)


def exact_one_blocks(blocks: int, width: int) -> CNF:
    clauses: list[tuple[int, ...]] = []
    for block in range(blocks):
        variables = [block * width + index + 1 for index in range(width)]
        clauses.append(tuple(variables))
        for i, left in enumerate(variables):
            for right in variables[i + 1 :]:
                clauses.append((-left, -right))
    return normalize_cnf(clauses)


def validate(rng: random.Random) -> int:
    checked = 0
    for n in range(1, 11):
        for _ in range(30):
            formula = random_3cnf(n, max(1, 4 * n), rng) if n >= 3 else normalize_cnf(((1,),))
            expected = brute_sat(formula, n)
            for factory in (natural_order, reverse_order):
                stats = run_order(formula, factory(formula), clause_limit=50_000)
                if stats.cutoff or stats.result != expected:
                    raise AssertionError((n, expected, stats, formula))
                checked += 1
    return checked


def format_stats(label: str, method: str, stats: EliminationStats) -> str:
    if stats.cutoff:
        return (
            f"{label}/{method}: cutoff, steps={stats.steps}, peak-clauses={stats.peak_clauses}, "
            f"peak-width={stats.peak_clause_width}, peak-product={stats.peak_incidence_product}, "
            f"seconds={stats.elapsed_seconds:.6f}"
        )
    return (
        f"{label}/{method}: result={stats.result}, steps={stats.steps}, "
        f"peak-clauses={stats.peak_clauses}, peak-width={stats.peak_clause_width}, "
        f"peak-product={stats.peak_incidence_product}, raw-resolvents={stats.raw_resolvents}, "
        f"kept-resolvents={stats.kept_resolvents}, seconds={stats.elapsed_seconds:.6f}"
    )


def run() -> str:
    seed = 0x4450564152
    rng = random.Random(seed)
    checked = validate(rng)
    lines = [
        "Davis-Putnam elimination-width experiment",
        f"seed={seed}",
        f"brute-force validation runs={checked}",
        "",
    ]

    planted18, _ = planted_3cnf(18, 76, rng)
    planted24, _ = planted_3cnf(24, 101, rng)
    benchmarks: list[tuple[str, CNF]] = [
        ("random-3sat-18", random_3cnf(18, 76, rng)),
        ("planted-3sat-18", planted18),
        ("random-3sat-24", random_3cnf(24, 101, rng)),
        ("planted-3sat-24", planted24),
        ("pigeonhole-5-4", pigeonhole(5, 4)),
        ("pigeonhole-6-5", pigeonhole(6, 5)),
        ("exact-one-10x4", exact_one_blocks(10, 4)),
        ("equality-10+10", equality_pairs(10)),
        ("xor-24x20", random_3xor(24, 20, rng, planted=rng.getrandbits(24))),
    ]

    for label, formula in benchmarks:
        methods: list[tuple[str, Callable[[CNF], list[int]]]] = [
            ("natural", natural_order),
            ("reverse", reverse_order),
            ("min-product", lambda f: greedy_order(f, "product")),
            ("min-fill", lambda f: greedy_order(f, "fill")),
            ("min-width", lambda f: greedy_order(f, "width")),
        ]
        for method, factory in methods:
            started = time.perf_counter()
            try:
                order = factory(formula)
                order_seconds = time.perf_counter() - started
                stats = run_order(formula, order)
                stats.elapsed_seconds += order_seconds
                lines.append(format_stats(label, method, stats))
            except ClauseLimitExceeded:
                lines.append(f"{label}/{method}: order-construction cutoff")
        lines.append("")

    # Explicitly compare split and paired orders for equality.
    equality = equality_pairs(12)
    split = list(range(24))
    paired = [v for index in range(12) for v in (index, 12 + index)]
    lines.append(format_stats("equality-12+12", "split-explicit", run_order(equality, split)))
    lines.append(format_stats("equality-12+12", "paired-explicit", run_order(equality, paired)))
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("elimination-width-output.txt").write_text(output, encoding="utf-8")
