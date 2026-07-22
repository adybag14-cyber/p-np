from __future__ import annotations

import itertools
import random
import statistics
import time
from dataclasses import dataclass
from pathlib import Path

from memo_dpll import (
    NodeLimitExceeded,
    pigeonhole,
    planted_3cnf,
    random_3cnf,
    solve_cnf,
    split_components,
    variables_in,
)
from symbolic_cnf import CNF, FALSE_CNF, TRUE_CNF, restrict_cnf


@dataclass(frozen=True)
class ResidualProfile:
    variables: int
    clauses: int
    literals: int
    max_width: int
    components: int
    horn: bool
    dual_horn: bool
    two_cnf: bool
    terminal: bool
    calls: int | None
    unique_states: int | None


def apply_restriction(formula: CNF, variables: tuple[int, ...], mask: int) -> CNF:
    residual = formula
    for position, variable in enumerate(variables):
        value = bool((mask >> (len(variables) - 1 - position)) & 1)
        residual = restrict_cnf(residual, variable, value)
        if residual in (TRUE_CNF, FALSE_CNF):
            break
    return residual


def is_horn(formula: CNF) -> bool:
    return all(sum(1 for literal in clause if literal > 0) <= 1 for clause in formula)


def is_dual_horn(formula: CNF) -> bool:
    return all(sum(1 for literal in clause if literal < 0) <= 1 for clause in formula)


def profile(residual: CNF, node_limit: int = 100_000) -> ResidualProfile:
    terminal = residual in (TRUE_CNF, FALSE_CNF)
    clauses = 0 if residual == TRUE_CNF else len(residual)
    literal_count = sum(len(clause) for clause in residual)
    max_width = max((len(clause) for clause in residual), default=0)
    components = 0 if terminal else len(split_components(residual))
    calls: int | None
    unique: int | None
    try:
        _, stats = solve_cnf(residual, node_limit=node_limit)
        calls = stats.calls
        unique = stats.unique_states
    except NodeLimitExceeded:
        calls = None
        unique = None
    return ResidualProfile(
        variables=len(variables_in(residual)),
        clauses=clauses,
        literals=literal_count,
        max_width=max_width,
        components=components,
        horn=is_horn(residual),
        dual_horn=is_dual_horn(residual),
        two_cnf=max_width <= 2,
        terminal=terminal,
        calls=calls,
        unique_states=unique,
    )


def variable_scores(formula: CNF) -> list[tuple[float, int]]:
    scores: dict[int, float] = {}
    for clause in formula:
        weight = 2.0 ** (-len(clause))
        for literal in clause:
            variable = abs(literal) - 1
            scores[variable] = scores.get(variable, 0.0) + weight
    return sorted(((score, variable) for variable, score in scores.items()), reverse=True)


def selected_variables(formula: CNF, count: int, strategy: str, rng: random.Random) -> tuple[int, ...]:
    variables = sorted(variables_in(formula))
    count = min(count, len(variables))
    if strategy == "score":
        return tuple(variable for _, variable in variable_scores(formula)[:count])
    if strategy == "random":
        chosen = rng.sample(variables, count)
        return tuple(sorted(chosen))
    if strategy == "natural":
        return tuple(variables[:count])
    raise ValueError(strategy)


def summarize_profiles(profiles: list[ResidualProfile]) -> str:
    solved = [item for item in profiles if item.calls is not None]
    calls = [item.calls for item in solved if item.calls is not None]
    unique = [item.unique_states for item in solved if item.unique_states is not None]
    count = len(profiles)
    pct = lambda predicate: 100.0 * sum(1 for item in profiles if predicate(item)) / count
    return (
        f"terminal={pct(lambda p: p.terminal):.1f}%, 2-CNF={pct(lambda p: p.two_cnf):.1f}%, "
        f"Horn={pct(lambda p: p.horn):.1f}%, dual-Horn={pct(lambda p: p.dual_horn):.1f}%, "
        f"split={pct(lambda p: p.components > 1):.1f}%, "
        f"mean-vars={statistics.mean(item.variables for item in profiles):.2f}, "
        f"mean-clauses={statistics.mean(item.clauses for item in profiles):.2f}, "
        f"mean-calls={statistics.mean(calls):.2f}, max-calls={max(calls)}, "
        f"sum-calls={sum(calls)}, mean-states={statistics.mean(unique):.2f}"
    )


def exact_cover_experiment(
    label: str,
    formula: CNF,
    fixed_count: int,
    strategy: str,
    rng: random.Random,
) -> list[str]:
    selected = selected_variables(formula, fixed_count, strategy, rng)
    baseline_result, baseline_stats = solve_cnf(formula, node_limit=2_000_000)
    profiles: list[ResidualProfile] = []
    residual_results: list[bool] = []
    for mask in range(1 << len(selected)):
        residual = apply_restriction(formula, selected, mask)
        profiles.append(profile(residual))
        result, _ = solve_cnf(residual, node_limit=100_000)
        residual_results.append(result)
    cover_result = any(residual_results)
    if cover_result != baseline_result:
        raise AssertionError((label, baseline_result, cover_result))
    return [
        f"{label}/{strategy}/fix={len(selected)}/cover={1 << len(selected)}: "
        f"baseline-result={baseline_result}, baseline-calls={baseline_stats.calls}, "
        f"baseline-states={baseline_stats.unique_states}",
        "  " + summarize_profiles(profiles),
        f"  selected={selected}",
    ]


def sampled_restrictions(
    label: str,
    formula: CNF,
    fractions: tuple[float, ...],
    samples: int,
    rng: random.Random,
) -> list[str]:
    lines = [f"{label}: variables={len(variables_in(formula))}, clauses={len(formula)}"]
    all_variables = sorted(variables_in(formula))
    for fraction in fractions:
        fixed = max(1, round(len(all_variables) * fraction))
        profiles: list[ResidualProfile] = []
        for _ in range(samples):
            selected = tuple(sorted(rng.sample(all_variables, min(fixed, len(all_variables)))))
            mask = rng.randrange(1 << len(selected))
            profiles.append(profile(apply_restriction(formula, selected, mask)))
        lines.append(f"  random-fix={fixed} ({fraction:.0%}), samples={samples}: {summarize_profiles(profiles)}")
    return lines


def run() -> str:
    seed = 0x5E57_300
    rng = random.Random(seed)
    started = time.perf_counter()

    random_small = random_3cnf(18, 76, rng)
    planted_small, _ = planted_3cnf(18, 76, rng)
    pigeon = pigeonhole(7, 6)

    lines = [
        "Restriction-cover collapse experiment",
        f"seed={seed}",
        "Exact covers enumerate all assignments to a selected variable set and verify OR-of-residuals equals the original SAT answer.",
        "",
        "Exact restriction covers",
    ]
    for label, formula in (
        ("random-3sat-18", random_small),
        ("planted-3sat-18", planted_small),
        ("pigeonhole-7-into-6", pigeon),
    ):
        for strategy in ("natural", "score", "random"):
            lines.extend(exact_cover_experiment(label, formula, 6, strategy, rng))
    lines.append("")

    lines.append("Sampled larger restrictions (structural evidence only, not a complete cover)")
    random_large = random_3cnf(32, 136, rng)
    planted_large, _ = planted_3cnf(32, 136, rng)
    lines.extend(sampled_restrictions("random-3sat-32", random_large, (0.25, 0.5, 0.75), 120, rng))
    lines.extend(sampled_restrictions("planted-3sat-32", planted_large, (0.25, 0.5, 0.75), 120, rng))
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("restriction-collapse-output.txt").write_text(output, encoding="utf-8")
