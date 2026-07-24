from __future__ import annotations

import random
from pathlib import Path

import networkx as nx

from circuit_cutset_conditioning import condition_all, format_image
from circuit_message_width import Circuit, brute_force_image, random_3sat_circuit, random_dag


def primal_graph(circuit: Circuit, removed: set[int]) -> nx.Graph:
    graph = nx.Graph()
    graph.add_nodes_from(variable for variable in range(circuit.next_variable) if variable not in removed)
    for gate in circuit.gates:
        scope = [variable for variable in gate.inputs + (gate.output,) if variable not in removed]
        for left_index in range(len(scope)):
            for right_index in range(left_index + 1, len(scope)):
                graph.add_edge(scope[left_index], scope[right_index])
    return graph


def fill_count(graph: nx.Graph, variable: int) -> int:
    neighbors = list(graph.neighbors(variable))
    missing = 0
    for left_index in range(len(neighbors)):
        for right_index in range(left_index + 1, len(neighbors)):
            if not graph.has_edge(neighbors[left_index], neighbors[right_index]):
                missing += 1
    return missing


def min_fill_width(circuit: Circuit, removed: set[int]) -> tuple[int, int]:
    graph = primal_graph(circuit, removed)
    maximum_bag = 1
    fill_edges = 0
    while len(graph) > 1 or (len(graph) == 1 and circuit.output not in graph):
        candidates = [node for node in graph if node != circuit.output]
        if not candidates:
            break
        variable = min(candidates, key=lambda node: (fill_count(graph, node), graph.degree[node], node))
        neighbors = list(graph.neighbors(variable))
        maximum_bag = max(maximum_bag, len(neighbors) + 1)
        for left_index in range(len(neighbors)):
            for right_index in range(left_index + 1, len(neighbors)):
                left = neighbors[left_index]
                right = neighbors[right_index]
                if not graph.has_edge(left, right):
                    graph.add_edge(left, right)
                    fill_edges += 1
        graph.remove_node(variable)
    return maximum_bag, fill_edges


def greedy_graph_cutset(circuit: Circuit, max_size: int) -> tuple[int, ...]:
    selected: list[int] = []
    available = set(range(circuit.next_variable)) - {circuit.output}
    for _ in range(max_size):
        best: tuple[int, int, int, int] | None = None
        best_variable: int | None = None
        for variable in available:
            removed = set(selected) | {variable}
            width, fills = min_fill_width(circuit, removed)
            kind_penalty = 0 if variable >= circuit.input_count else 1
            candidate = (width, fills, kind_penalty, variable)
            if best is None or candidate < best:
                best = candidate
                best_variable = variable
        if best_variable is None:
            break
        selected.append(best_variable)
        available.remove(best_variable)
    return tuple(selected)


def describe_variable(circuit: Circuit, variable: int) -> str:
    if variable < circuit.input_count:
        return f"x{variable}"
    gate_index = variable - circuit.input_count
    if 0 <= gate_index < len(circuit.gates):
        gate = circuit.gates[gate_index]
        return f"w{variable}:{gate.name}"
    return f"w{variable}"


def run() -> str:
    seed = 0x6A_7C_07
    rng = random.Random(seed)
    cases: list[tuple[str, Circuit, int]] = [
        ("random-dag-12x60", random_dag(12, 60, rng), 6),
        ("random-3sat-12x30", random_3sat_circuit(12, 30, rng), 6),
        ("random-3sat-14x45", random_3sat_circuit(14, 45, rng), 5),
    ]
    lines = [
        "Graph-guided internal-wire cutset experiment",
        f"seed={seed}",
        "The greedy score removes the variable yielding the smallest min-fill induced width; internal wires are allowed.",
        "",
    ]
    for label, circuit, max_size in cases:
        order = greedy_graph_cutset(circuit, max_size)
        baseline_width, baseline_fills = min_fill_width(circuit, set())
        brute = brute_force_image(circuit) if circuit.input_count <= 14 else ()
        lines.append(
            f"[{label}] inputs={circuit.input_count}, gates={len(circuit.gates)}, graph-width={baseline_width}, fills={baseline_fills}"
        )
        lines.append("  order=" + ", ".join(describe_variable(circuit, variable) for variable in order))
        for cut_size in range(max_size + 1):
            prefix = order[:cut_size]
            graph_width, fills = min_fill_width(circuit, set(prefix))
            stats = condition_all(circuit, prefix, cutoff=1_000_000)
            if not stats.cutoff_branches and brute and stats.image != brute:
                raise AssertionError((label, cut_size, stats.image, brute))
            lines.append(
                f"  k={cut_size}, branches={stats.branches}, graph-width={graph_width}, fills={fills}, "
                f"image={format_image(stats.image, stats.cutoff_branches)}, max-peak-rows={stats.max_peak_rows}, "
                f"max-scope={stats.max_peak_scope}, total-checks={stats.total_join_checks}, seconds={stats.seconds:.4f}"
            )
        lines.append("")
    lines.extend([
        "Interpretation:",
        "- Conditioning internal wires is logically exact because impossible wire values leave empty residual branches.",
        "- Graph width is cheap to optimize but only approximates actual relation-row cost.",
        "- The decisive objective remains 2^k times residual construction work, not width alone.",
    ])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("circuit-graph-cutset-output.txt").write_text(output, encoding="utf-8")
