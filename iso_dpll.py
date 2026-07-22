from __future__ import annotations

import time
from dataclasses import dataclass
from pathlib import Path

import networkx as nx

from memo_dpll import (
    NodeLimitExceeded,
    choose_variable,
    pigeonhole,
    split_components,
    unit_propagate,
)
from symbolic_cnf import CNF, FALSE_CNF, TRUE_CNF, normalize_cnf, restrict_cnf


@dataclass
class IsoStats:
    calls: int = 0
    unique_exact_states: int = 0
    iso_representatives: int = 0
    exact_hits: int = 0
    iso_hits: int = 0
    iso_checks: int = 0
    unit_assignments: int = 0
    component_splits: int = 0
    branches: int = 0
    max_depth: int = 0
    elapsed_seconds: float = 0.0


def incidence_graph(formula: CNF) -> nx.Graph:
    graph = nx.Graph()
    variables = sorted({abs(lit) - 1 for clause in formula for lit in clause})
    for variable in variables:
        graph.add_node(("v", variable), kind="variable", length=-1)
    for index, clause in enumerate(formula):
        clause_node = ("c", index)
        graph.add_node(clause_node, kind="clause", length=len(clause))
        for lit in clause:
            variable = abs(lit) - 1
            graph.add_edge(clause_node, ("v", variable), sign=(lit > 0))
    return graph


def iso_invariant(formula: CNF) -> tuple:
    variables = sorted({abs(lit) - 1 for clause in formula for lit in clause})
    occurrence = {v: [0, 0] for v in variables}
    for clause in formula:
        for lit in clause:
            occurrence[abs(lit) - 1][0 if lit > 0 else 1] += 1
    return (
        len(variables),
        len(formula),
        tuple(sorted(map(len, formula))),
        tuple(sorted(tuple(counts) for counts in occurrence.values())),
    )


def solve_cnf_iso(
    formula: CNF,
    *,
    node_limit: int = 2_000_000,
    enable_components: bool = True,
) -> tuple[bool, IsoStats]:
    exact_cache: dict[CNF, bool] = {}
    buckets: dict[tuple, list[tuple[CNF, bool, nx.Graph]]] = {}
    stats = IsoStats()
    started = time.perf_counter()
    node_match = nx.algorithms.isomorphism.categorical_node_match(
        ["kind", "length"], [None, None]
    )
    edge_match = nx.algorithms.isomorphism.categorical_edge_match("sign", None)

    def lookup_iso(state: CNF) -> bool | None:
        if state in exact_cache:
            stats.exact_hits += 1
            return exact_cache[state]
        key = iso_invariant(state)
        candidates = buckets.get(key)
        if not candidates:
            return None
        graph = incidence_graph(state)
        for _representative, result, representative_graph in candidates:
            stats.iso_checks += 1
            matcher = nx.algorithms.isomorphism.GraphMatcher(
                graph,
                representative_graph,
                node_match=node_match,
                edge_match=edge_match,
            )
            if matcher.is_isomorphic():
                stats.iso_hits += 1
                exact_cache[state] = result
                return result
        return None

    def store(state: CNF, result: bool) -> None:
        exact_cache[state] = result
        key = iso_invariant(state)
        buckets.setdefault(key, []).append((state, result, incidence_graph(state)))

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

        cached = lookup_iso(state)
        if cached is not None:
            return cached

        if enable_components:
            components = split_components(state)
            if len(components) > 1:
                stats.component_splits += 1
                result = all(solve(component, depth + 1) for component in components)
                store(state, result)
                return result

        variable, preferred = choose_variable(state)
        stats.branches += 1
        first = restrict_cnf(state, variable, preferred)
        if solve(first, depth + 1):
            store(state, True)
            return True
        second = restrict_cnf(state, variable, not preferred)
        result = solve(second, depth + 1)
        store(state, result)
        return result

    try:
        result = solve(normalize_cnf(formula), 0)
    finally:
        stats.elapsed_seconds = time.perf_counter() - started
        stats.unique_exact_states = len(exact_cache)
        stats.iso_representatives = sum(len(values) for values in buckets.values())
    return result, stats


def stats_line(label: str, n: int, result: bool, stats: IsoStats) -> str:
    return (
        f"{label}: n={n}, result={result}, calls={stats.calls}, exact-states={stats.unique_exact_states}, "
        f"iso-representatives={stats.iso_representatives}, exact-hits={stats.exact_hits}, "
        f"iso-hits={stats.iso_hits}, iso-checks={stats.iso_checks}, units={stats.unit_assignments}, "
        f"branches={stats.branches}, component-splits={stats.component_splits}, "
        f"depth={stats.max_depth}, seconds={stats.elapsed_seconds:.4f}"
    )


def run() -> str:
    lines = ["Edge-labelled isomorphism-aware residual memoization", ""]
    for p in range(4, 10):
        formula = pigeonhole(p, p - 1)
        result, stats = solve_cnf_iso(formula, node_limit=2_000_000)
        lines.append(stats_line(f"pigeonhole-{p}-{p-1}", p * (p - 1), result, stats))
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("iso-dpll-output.txt").write_text(output, encoding="utf-8")
