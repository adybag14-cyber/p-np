from __future__ import annotations

import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import networkx as nx

from memo_dpll import NodeLimitExceeded, pigeonhole, solve_cnf, stats_line
from symbolic_cnf import CNF, normalize_cnf


@dataclass(frozen=True)
class MatchingEncoding:
    rows: tuple[tuple[int, ...], ...]
    columns: tuple[tuple[int, ...], ...]
    variable_to_row: dict[int, int]
    variable_to_column: dict[int, int]


def _negative_pair(clause: tuple[int, ...]) -> frozenset[int] | None:
    if len(clause) != 2 or clause[0] >= 0 or clause[1] >= 0:
        return None
    return frozenset((abs(clause[0]) - 1, abs(clause[1]) - 1))


def recognize_exact_bipartite_matching(formula: CNF) -> MatchingEncoding | None:
    """Recognize a standard CNF encoding of a left-covering bipartite matching.

    Every variable denotes an allowed edge. Positive clauses require one edge
    from each row. Negative binary clauses enforce at most one edge in each row
    and in each column. The recognizer validates the *entire* clause set before
    dispatching, so a false positive cannot silently change satisfiability.
    """
    formula = normalize_cnf(formula)
    positive = [clause for clause in formula if clause and all(lit > 0 for lit in clause)]
    negative_clauses = [
        clause for clause in formula if len(clause) == 2 and all(lit < 0 for lit in clause)
    ]
    if len(positive) + len(negative_clauses) != len(formula):
        return None
    parsed_pairs = [_negative_pair(clause) for clause in negative_clauses]
    if any(pair is None for pair in parsed_pairs):
        return None
    pairs: set[frozenset[int]] = {pair for pair in parsed_pairs if pair is not None}
    if not positive:
        return None

    rows: list[tuple[int, ...]] = []
    variable_to_row: dict[int, int] = {}
    for row_index, clause in enumerate(positive):
        row = tuple(sorted(lit - 1 for lit in clause))
        if len(row) != len(set(row)) or not row:
            return None
        for variable in row:
            if variable in variable_to_row:
                return None
            variable_to_row[variable] = row_index
        rows.append(row)

    variables = set(variable_to_row)
    mentioned = {v for pair in pairs for v in pair}
    if not mentioned <= variables:
        return None

    # Every pair inside one row must be forbidden.
    row_pairs: set[frozenset[int]] = set()
    for row in rows:
        for i, left in enumerate(row):
            for right in row[i + 1 :]:
                row_pairs.add(frozenset((left, right)))
    if not row_pairs <= pairs:
        return None

    cross_pairs = pairs - row_pairs
    graph = nx.Graph()
    graph.add_nodes_from(variables)
    graph.add_edges_from(tuple(pair) for pair in cross_pairs)
    columns: list[tuple[int, ...]] = []
    variable_to_column: dict[int, int] = {}
    for component in nx.connected_components(graph):
        column = tuple(sorted(component))
        # A column is a clique and contains at most one edge from each row.
        if len({variable_to_row[v] for v in column}) != len(column):
            return None
        # Connected components have no edges between them. Therefore a
        # component is exactly a column clique iff its internal edge count is
        # choose(|column|, 2); no per-column re-scan of all conflict pairs is
        # needed.
        if graph.subgraph(component).number_of_edges() != len(column) * (len(column) - 1) // 2:
            return None
        column_index = len(columns)
        columns.append(column)
        for variable in column:
            variable_to_column[variable] = column_index

    # Isolated variables are singleton columns.
    for variable in sorted(variables):
        if variable not in variable_to_column:
            column_index = len(columns)
            columns.append((variable,))
            variable_to_column[variable] = column_index

    # No clauses besides row-at-least-one and validated negative binary clauses.
    expected_positive = {tuple(variable + 1 for variable in row) for row in rows}
    actual_positive = {tuple(sorted(clause)) for clause in positive}
    if actual_positive != expected_positive:
        return None
    if len(formula) != len(positive) + len(pairs):
        return None

    return MatchingEncoding(
        rows=tuple(rows),
        columns=tuple(columns),
        variable_to_row=variable_to_row,
        variable_to_column=variable_to_column,
    )


def matching_sat(encoding: MatchingEncoding) -> bool:
    graph = nx.Graph()
    left_nodes = [("r", row) for row in range(len(encoding.rows))]
    right_nodes = [("c", column) for column in range(len(encoding.columns))]
    graph.add_nodes_from(left_nodes, bipartite=0)
    graph.add_nodes_from(right_nodes, bipartite=1)
    for variable, row in encoding.variable_to_row.items():
        column = encoding.variable_to_column[variable]
        graph.add_edge(("r", row), ("c", column))
    matching = nx.algorithms.bipartite.maximum_matching(graph, top_nodes=left_nodes)
    return all(node in matching for node in left_nodes)


def structural_dispatch(formula: CNF) -> tuple[bool, str]:
    encoding = recognize_exact_bipartite_matching(formula)
    if encoding is not None:
        return matching_sat(encoding), "bipartite-matching"
    result, _stats = solve_cnf(formula)
    return result, "memo-dpll"


def run() -> str:
    lines = ["Certified structural-dispatch experiment", ""]
    for pigeons, holes in ((7, 6), (9, 8), (10, 9), (12, 11), (15, 14)):
        formula = pigeonhole(pigeons, holes)
        started = time.perf_counter()
        encoding = recognize_exact_bipartite_matching(formula)
        if encoding is None:
            raise AssertionError("recognizer rejected generated matching encoding")
        result = matching_sat(encoding)
        elapsed = time.perf_counter() - started
        lines.append(
            f"pigeonhole-{pigeons}-{holes}: variables={pigeons * holes}, "
            f"recognized=True, result={result}, rows={len(encoding.rows)}, "
            f"columns={len(encoding.columns)}, seconds={elapsed:.6f}"
        )

    # A mutation must be rejected rather than solved under the wrong semantics.
    base = list(pigeonhole(5, 4))
    base.append((1, 6))  # unsupported positive binary clause linking rows
    mutated = normalize_cnf(base)
    lines.append(
        f"mutated-nonmatching-encoding: recognized={recognize_exact_bipartite_matching(mutated) is not None}"
    )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("structural-dispatch-output.txt").write_text(output, encoding="utf-8")
