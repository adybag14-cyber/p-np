from __future__ import annotations

import random
import time
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

import networkx as nx

from memo_dpll import (
    NodeLimitExceeded,
    brute_sat,
    pigeonhole,
    planted_3cnf,
    random_3cnf,
    solve_cnf,
    split_components,
)
from structural_dispatch import matching_sat, recognize_exact_bipartite_matching
from symbolic_cnf import CNF, FALSE_CNF, TRUE_CNF, normalize_cnf
from xor_affine import gaussian_sat, random_3xor, recognize_canonical_3xor


def horn_sat(formula: CNF) -> bool | None:
    """Return Horn-SAT result, or None when the formula is not Horn."""
    formula = normalize_cnf(formula)
    rules: list[tuple[frozenset[int], int | None]] = []
    for clause in formula:
        positives = [lit - 1 for lit in clause if lit > 0]
        if len(positives) > 1:
            return None
        body = frozenset(abs(lit) - 1 for lit in clause if lit < 0)
        head = positives[0] if positives else None
        rules.append((body, head))

    true_vars: set[int] = set()
    changed = True
    while changed:
        changed = False
        for body, head in rules:
            if head is not None and head not in true_vars and body <= true_vars:
                true_vars.add(head)
                changed = True
    return not any(head is None and body <= true_vars for body, head in rules)


def dual_horn_sat(formula: CNF) -> bool | None:
    """Dual-Horn SAT via complementing every variable and invoking Horn-SAT."""
    formula = normalize_cnf(formula)
    if any(sum(lit < 0 for lit in clause) > 1 for clause in formula):
        return None
    complemented = normalize_cnf(tuple(-lit for lit in clause) for clause in formula)
    result = horn_sat(complemented)
    if result is None:
        raise AssertionError("dual-Horn complement did not become Horn")
    return result


def two_sat(formula: CNF) -> bool | None:
    """Return 2-SAT result using implication-graph SCCs, or None if not 2-CNF."""
    formula = normalize_cnf(formula)
    if any(len(clause) > 2 for clause in formula):
        return None
    if formula == FALSE_CNF:
        return False
    graph = nx.DiGraph()
    variables = {abs(lit) for clause in formula for lit in clause}
    for variable in variables:
        graph.add_node(variable)
        graph.add_node(-variable)
    for clause in formula:
        if len(clause) == 0:
            return False
        if len(clause) == 1:
            a = clause[0]
            graph.add_edge(-a, a)
        else:
            a, b = clause
            graph.add_edge(-a, b)
            graph.add_edge(-b, a)
    component: dict[int, int] = {}
    for index, nodes in enumerate(nx.strongly_connected_components(graph)):
        for node in nodes:
            component[node] = index
    return all(component[v] != component[-v] for v in variables)


def exact_one_blocks_sat(formula: CNF) -> bool | None:
    """Recognize disjoint exact-one blocks and solve them without branching."""
    formula = normalize_cnf(formula)
    if formula == TRUE_CNF:
        return True
    if formula == FALSE_CNF:
        return False
    positive = [clause for clause in formula if clause and all(lit > 0 for lit in clause)]
    negative = [clause for clause in formula if len(clause) == 2 and all(lit < 0 for lit in clause)]
    if len(positive) + len(negative) != len(formula) or not positive:
        return None
    seen: set[int] = set()
    expected_negative: set[tuple[int, int]] = set()
    for clause in positive:
        variables = [lit for lit in clause]
        if len(set(variables)) != len(variables) or any(v in seen for v in variables):
            return None
        seen.update(variables)
        for i, left in enumerate(variables):
            for right in variables[i + 1 :]:
                expected_negative.add(tuple(sorted((-left, -right))))
    actual_negative = {tuple(sorted(clause)) for clause in negative}
    if actual_negative != expected_negative:
        return None
    return True


def affine_3xor_sat(formula: CNF) -> bool | None:
    system = recognize_canonical_3xor(formula)
    return None if system is None else gaussian_sat(system)


RECOGNIZERS = (
    ("affine-3xor", affine_3xor_sat),
    ("horn", horn_sat),
    ("dual-horn", dual_horn_sat),
    ("2-sat", two_sat),
    ("exact-one-blocks", exact_one_blocks_sat),
)


@dataclass
class PortfolioStats:
    routes: Counter[str] = field(default_factory=Counter)
    component_splits: int = 0
    fallback_calls: int = 0
    fallback_unique_states: int = 0
    fallback_branches: int = 0
    elapsed_seconds: float = 0.0


def solve_portfolio(formula: CNF, *, node_limit: int = 2_000_000) -> tuple[bool, PortfolioStats]:
    stats = PortfolioStats()
    started = time.perf_counter()

    def solve(state: CNF) -> bool:
        state = normalize_cnf(state)
        if state == TRUE_CNF:
            stats.routes["constant-true"] += 1
            return True
        if state == FALSE_CNF:
            stats.routes["constant-false"] += 1
            return False

        for label, recognizer in RECOGNIZERS:
            answer = recognizer(state)
            if answer is not None:
                stats.routes[label] += 1
                return answer

        matching = recognize_exact_bipartite_matching(state)
        if matching is not None:
            stats.routes["bipartite-matching"] += 1
            return matching_sat(matching)

        components = split_components(state)
        if len(components) > 1:
            stats.component_splits += 1
            stats.routes["decomposition"] += 1
            return all(solve(component) for component in components)

        stats.routes["memo-dpll"] += 1
        stats.fallback_calls += 1
        answer, fallback = solve_cnf(state, node_limit=node_limit, enable_components=True)
        stats.fallback_unique_states += fallback.unique_states
        stats.fallback_branches += fallback.branches
        return answer

    try:
        answer = solve(formula)
    finally:
        stats.elapsed_seconds = time.perf_counter() - started
    return answer, stats


def random_horn(n: int, clauses: int, rng: random.Random) -> CNF:
    output: list[tuple[int, ...]] = []
    for _ in range(clauses):
        width = rng.randint(1, min(4, n))
        variables = rng.sample(range(n), width)
        head_index = rng.randrange(width) if rng.random() < 0.65 else None
        clause = tuple(
            (variable + 1) if index == head_index else -(variable + 1)
            for index, variable in enumerate(variables)
        )
        output.append(clause)
    return normalize_cnf(output)


def random_two_sat(n: int, clauses: int, rng: random.Random) -> CNF:
    output: list[tuple[int, ...]] = []
    for _ in range(clauses):
        width = 1 if n == 1 or rng.random() < 0.08 else 2
        variables = rng.sample(range(n), width)
        output.append(tuple((v + 1) if rng.getrandbits(1) else -(v + 1) for v in variables))
    return normalize_cnf(output)


def exact_one_blocks(blocks: int, width: int) -> CNF:
    clauses: list[tuple[int, ...]] = []
    for block in range(blocks):
        variables = [block * width + i + 1 for i in range(width)]
        clauses.append(tuple(variables))
        for i, left in enumerate(variables):
            for right in variables[i + 1 :]:
                clauses.append((-left, -right))
    return normalize_cnf(clauses)


def shift_formula(formula: CNF, offset: int) -> CNF:
    return normalize_cnf(
        tuple((1 if lit > 0 else -1) * (abs(lit) + offset) for lit in clause)
        for clause in formula
    )


def compare(label: str, formula: CNF, n: int, *, plain_limit: int = 2_000_000) -> str:
    p_answer, p_stats = solve_portfolio(formula, node_limit=plain_limit)
    try:
        d_answer, d_stats = solve_cnf(formula, node_limit=plain_limit)
        if d_answer != p_answer:
            raise AssertionError((label, p_answer, d_answer))
        plain = (
            f"plain(states={d_stats.unique_states},branches={d_stats.branches},"
            f"seconds={d_stats.elapsed_seconds:.6f})"
        )
    except NodeLimitExceeded:
        plain = f"plain(cutoff={plain_limit})"
    routes = ",".join(f"{name}:{count}" for name, count in sorted(p_stats.routes.items()))
    return (
        f"{label}: n={n}, result={p_answer}, portfolio(routes={routes},"
        f"splits={p_stats.component_splits},fallback-states={p_stats.fallback_unique_states},"
        f"fallback-branches={p_stats.fallback_branches},seconds={p_stats.elapsed_seconds:.6f}), "
        f"{plain}"
    )


def exhaustive_validation(rng: random.Random) -> tuple[int, Counter[str]]:
    checked = 0
    routes: Counter[str] = Counter()
    for n in range(1, 9):
        families: list[CNF] = []
        for _ in range(40):
            families.append(random_horn(n, 4 * n, rng))
            families.append(normalize_cnf(tuple(-lit for lit in clause) for clause in random_horn(n, 4 * n, rng)))
            families.append(random_two_sat(n, 4 * n, rng))
            if n >= 3:
                families.append(random_3cnf(n, 4 * n, rng))
                max_triples = n * (n - 1) * (n - 2) // 6
                equation_count = min(n, max_triples)
                planted = rng.getrandbits(n) if rng.getrandbits(1) else None
                families.append(random_3xor(n, equation_count, rng, planted=planted))
        for formula in families:
            expected = brute_sat(formula, n)
            actual, stats = solve_portfolio(formula)
            if actual != expected:
                raise AssertionError((n, formula, actual, expected, stats))
            checked += 1
            routes.update(stats.routes)
    return checked, routes


def run() -> str:
    seed = 0x485942524944
    rng = random.Random(seed)
    checked, validation_routes = exhaustive_validation(rng)
    lines = [
        "Hybrid certified-portfolio experiment",
        f"seed={seed}",
        f"small-instance brute-force validation: checked={checked}, routes={dict(sorted(validation_routes.items()))}",
        "",
    ]

    horn = random_horn(80, 360, rng)
    dual = normalize_cnf(tuple(-lit for lit in clause) for clause in random_horn(80, 360, rng))
    two = random_two_sat(120, 520, rng)
    exact = exact_one_blocks(20, 5)
    random_formula = random_3cnf(70, round(4.2 * 70), rng)

    lines.append(compare("horn-80", horn, 80))
    lines.append(compare("dual-horn-80", dual, 80))
    lines.append(compare("2sat-120", two, 120))
    lines.append(compare("exact-one-20x5", exact, 100))
    lines.append(compare("pigeonhole-7-6", pigeonhole(7, 6), 42))
    lines.append(compare("pigeonhole-8-7", pigeonhole(8, 7), 56, plain_limit=500_000))
    lines.append(compare("random-3sat-70", random_formula, 70))

    # A satisfiable heterogeneous conjunction exercising every portfolio route.
    horn_piece = normalize_cnf((-i, -(i + 1)) for i in range(1, 40))
    dual_piece = normalize_cnf((i, i + 1) for i in range(1, 40))
    two_piece = normalize_cnf(
        clause
        for i in range(1, 40)
        for clause in ((i, i + 1), (-i, -(i + 1)))
    )
    exact_piece = exact_one_blocks(6, 4)
    xor_planted = rng.getrandbits(24)
    xor_piece = random_3xor(24, 18, rng, planted=xor_planted)
    fallback_piece, _planted = planted_3cnf(32, 130, rng)
    pieces = [
        horn_piece,
        shift_formula(dual_piece, 40),
        shift_formula(two_piece, 80),
        shift_formula(exact_piece, 120),
        shift_formula(xor_piece, 144),
        shift_formula(fallback_piece, 168),
    ]
    mixed = normalize_cnf(clause for piece in pieces for clause in piece)
    lines.append(compare("mixed-six-family-sat", mixed, 200))

    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("hybrid-portfolio-output.txt").write_text(output, encoding="utf-8")
