from __future__ import annotations

import random
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from hybrid_portfolio import RECOGNIZERS, exact_one_blocks, shift_formula
from memo_dpll import (
    choose_variable,
    pigeonhole,
    random_3cnf,
    split_components,
    unit_propagate,
)
from structural_dispatch import matching_sat, recognize_exact_bipartite_matching
from symbolic_cnf import CNF, FALSE_CNF, TRUE_CNF, normalize_cnf, restrict_cnf


@dataclass(frozen=True)
class Node:
    state: CNF
    answer: bool
    kind: str
    children: tuple[int, ...] = ()
    data: Any = None


def canonical_rename(formula: CNF) -> CNF:
    """Remove irrelevant variable names while preserving satisfiability.

    This is deliberately weaker than graph isomorphism: variables are renamed
    in increasing numeric order.  It is enough to merge shifted copies of the
    same component and is easy for the certificate checker to reproduce.
    """
    formula = normalize_cnf(formula)
    if formula in (TRUE_CNF, FALSE_CNF):
        return formula
    variables = sorted({abs(lit) for clause in formula for lit in clause})
    rename = {old: new for new, old in enumerate(variables, start=1)}
    return normalize_cnf(
        tuple((1 if lit > 0 else -1) * rename[abs(lit)] for lit in clause)
        for clause in formula
    )


def recognizer_answer(formula: CNF) -> tuple[str, bool] | None:
    matching = recognize_exact_bipartite_matching(formula)
    if matching is not None:
        return "bipartite-matching", matching_sat(matching)
    for route, recognizer in RECOGNIZERS:
        result = recognizer(formula)
        if result is not None:
            return route, result
    return None


class CertificateBuilder:
    def __init__(self, node_limit: int = 2_000_000) -> None:
        self.nodes: list[Node] = []
        self.cache: dict[CNF, int] = {}
        self.node_limit = node_limit
        self.cache_hits = 0

    def add(self, node: Node) -> int:
        node_id = len(self.nodes)
        self.nodes.append(node)
        self.cache[node.state] = node_id
        if len(self.nodes) > self.node_limit:
            raise RuntimeError(f"certificate node limit {self.node_limit} exceeded")
        return node_id

    def build(self, formula: CNF) -> int:
        state = canonical_rename(formula)
        existing = self.cache.get(state)
        if existing is not None:
            self.cache_hits += 1
            return existing

        if state == TRUE_CNF:
            return self.add(Node(state, True, "true"))
        if state == FALSE_CNF:
            return self.add(Node(state, False, "false"))

        components = split_components(state)
        if len(components) > 1:
            child_ids = tuple(self.build(component) for component in components)
            answer = all(self.nodes[child].answer for child in child_ids)
            return self.add(Node(state, answer, "and-components", child_ids))

        recognized = recognizer_answer(state)
        if recognized is not None:
            route, answer = recognized
            return self.add(Node(state, answer, f"leaf:{route}"))

        residual, forced = unit_propagate(state)
        residual = canonical_rename(residual)
        if residual != state:
            child = self.build(residual)
            return self.add(
                Node(
                    state,
                    self.nodes[child].answer,
                    "unit-propagation",
                    (child,),
                    tuple(forced.items()),
                )
            )

        variable, preferred = choose_variable(state)
        first_state = canonical_rename(restrict_cnf(state, variable, preferred))
        second_state = canonical_rename(restrict_cnf(state, variable, not preferred))
        first = self.build(first_state)
        if self.nodes[first].answer:
            # A true first branch is enough for existential satisfiability.
            return self.add(
                Node(state, True, "or-short-circuit", (first,), (variable, preferred))
            )
        second = self.build(second_state)
        answer = self.nodes[first].answer or self.nodes[second].answer
        return self.add(
            Node(state, answer, "or-branch", (first, second), (variable, preferred))
        )


class CertificateVerifier:
    def __init__(self, nodes: list[Node]) -> None:
        self.nodes = nodes
        self.verified: set[int] = set()

    def verify(self, node_id: int) -> bool:
        if node_id in self.verified:
            return True
        if not 0 <= node_id < len(self.nodes):
            return False
        node = self.nodes[node_id]
        if canonical_rename(node.state) != node.state:
            return False
        if any(child >= node_id or child < 0 for child in node.children):
            return False
        if not all(self.verify(child) for child in node.children):
            return False

        if node.kind == "true":
            valid = node.state == TRUE_CNF and node.answer
        elif node.kind == "false":
            valid = node.state == FALSE_CNF and not node.answer
        elif node.kind == "and-components":
            expected = tuple(canonical_rename(c) for c in split_components(node.state))
            actual = tuple(self.nodes[c].state for c in node.children)
            valid = (
                len(expected) > 1
                and expected == actual
                and node.answer == all(self.nodes[c].answer for c in node.children)
            )
        elif node.kind.startswith("leaf:"):
            recognized = recognizer_answer(node.state)
            valid = recognized is not None and node.kind == f"leaf:{recognized[0]}" and node.answer == recognized[1]
        elif node.kind == "unit-propagation":
            residual, forced = unit_propagate(node.state)
            child = node.children[0] if len(node.children) == 1 else -1
            valid = (
                child >= 0
                and tuple(forced.items()) == node.data
                and canonical_rename(residual) == self.nodes[child].state
                and node.answer == self.nodes[child].answer
            )
        elif node.kind in ("or-branch", "or-short-circuit"):
            variable, preferred = node.data
            expected_first = canonical_rename(restrict_cnf(node.state, variable, preferred))
            first = node.children[0] if node.children else -1
            valid = first >= 0 and self.nodes[first].state == expected_first
            if valid and node.kind == "or-short-circuit":
                valid = len(node.children) == 1 and self.nodes[first].answer and node.answer
            elif valid:
                expected_second = canonical_rename(restrict_cnf(node.state, variable, not preferred))
                second = node.children[1] if len(node.children) == 2 else -1
                valid = (
                    second >= 0
                    and self.nodes[second].state == expected_second
                    and node.answer == (self.nodes[first].answer or self.nodes[second].answer)
                )
        else:
            valid = False

        if valid:
            self.verified.add(node_id)
        return valid


def unfolded_nodes(nodes: list[Node], node_id: int, memo: dict[int, int] | None = None) -> int:
    """Count the tree obtained by duplicating every shared child occurrence."""
    if memo is None:
        memo = {}
    if node_id in memo:
        return memo[node_id]
    total = 1 + sum(unfolded_nodes(nodes, child, memo) for child in nodes[node_id].children)
    memo[node_id] = total
    return total


def edge_count(nodes: list[Node]) -> int:
    return sum(len(node.children) for node in nodes)


def maximum_depth(nodes: list[Node], root: int) -> int:
    memo: dict[int, int] = {}

    def depth(node_id: int) -> int:
        if node_id in memo:
            return memo[node_id]
        value = 1 if not nodes[node_id].children else 1 + max(depth(c) for c in nodes[node_id].children)
        memo[node_id] = value
        return value

    return depth(root)


def route_counts(nodes: list[Node]) -> Counter[str]:
    return Counter(node.kind for node in nodes)


def repeated_components(component: CNF, copies: int, stride: int) -> CNF:
    pieces = [shift_formula(component, copy * stride) for copy in range(copies)]
    return normalize_cnf(clause for piece in pieces for clause in piece)


def benchmark(label: str, formula: CNF, node_limit: int = 2_000_000) -> str:
    started = time.perf_counter()
    builder = CertificateBuilder(node_limit=node_limit)
    root = builder.build(formula)
    build_seconds = time.perf_counter() - started

    verify_started = time.perf_counter()
    verifier = CertificateVerifier(builder.nodes)
    verified = verifier.verify(root)
    verify_seconds = time.perf_counter() - verify_started
    if not verified:
        raise AssertionError(f"certificate verification failed for {label}")

    tree_nodes = unfolded_nodes(builder.nodes, root)
    routes = ",".join(f"{k}:{v}" for k, v in sorted(route_counts(builder.nodes).items()))
    compression = tree_nodes / len(builder.nodes)
    return (
        f"{label}: result={builder.nodes[root].answer}, dag-nodes={len(builder.nodes)}, "
        f"tree-nodes={tree_nodes}, tree/dag={compression:.3f}, edges={edge_count(builder.nodes)}, "
        f"depth={maximum_depth(builder.nodes, root)}, cache-hits={builder.cache_hits}, "
        f"build-seconds={build_seconds:.6f}, verify-seconds={verify_seconds:.6f}, routes={{{routes}}}"
    )


def run() -> str:
    seed = 0xDACE_CE47
    rng = random.Random(seed)
    lines = ["Proof-carrying AND/OR DAG experiment", f"seed={seed}", ""]

    # Shifted identical components are semantically identical after canonical renaming.
    small_component = random_3cnf(12, 50, rng)
    lines.append(benchmark("repeated-random-component-30x12", repeated_components(small_component, 30, 12), 500_000))
    lines.append(benchmark("repeated-exact-one-50x4", exact_one_blocks(50, 4), 500_000))

    lines.append(benchmark("pigeonhole-7-6", pigeonhole(7, 6), 500_000))
    lines.append(benchmark("pigeonhole-8-7", pigeonhole(8, 7), 500_000))

    for n in (30, 40, 50, 60):
        formula = random_3cnf(n, round(4.2 * n), rng)
        lines.append(benchmark(f"random-3sat-{n}", formula, 2_000_000))

    # A mixed conjunction demonstrates AND nodes, structural leaves, and fallback branches.
    mixed = normalize_cnf(
        clause
        for piece in (
            exact_one_blocks(12, 4),
            shift_formula(pigeonhole(6, 5), 48),
            shift_formula(random_3cnf(28, 118, rng), 78),
        )
        for clause in piece
    )
    lines.append(benchmark("mixed-structural-and-random", mixed, 2_000_000))

    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("certified-dag-output.txt").write_text(output, encoding="utf-8")
