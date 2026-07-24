from __future__ import annotations

import random
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from circuit_cutset_conditioning import input_reuse_order
from circuit_graph_cutset import describe_variable, greedy_graph_cutset
from circuit_message_width import Circuit, random_3sat_circuit, random_dag


@dataclass(frozen=True)
class QuotientStats:
    cut_size: int
    raw_branches: int
    reachable_branches: int
    unique_signatures: int
    impossible_branches: int
    largest_class: int
    residual_points: int


def evaluate_all_wires(circuit: Circuit, input_bits: tuple[bool, ...]) -> tuple[bool, ...]:
    values = list(input_bits) + [False] * (circuit.next_variable - circuit.input_count)
    for gate in circuit.gates:
        values[gate.output] = gate.operation(tuple(values[index] for index in gate.inputs))
    return tuple(values)


def residual_signatures(circuit: Circuit, cut_variables: tuple[int, ...]) -> QuotientStats:
    cut_inputs = tuple(variable for variable in cut_variables if variable < circuit.input_count)
    remaining_inputs = tuple(variable for variable in range(circuit.input_count) if variable not in cut_inputs)
    raw_branches = 1 << len(cut_variables)
    residual_points = 1 << len(remaining_inputs)

    # 0 = impossible, 1 = output false, 2 = output true, 3 = both outputs possible.
    tables = [bytearray(residual_points) for _ in range(raw_branches)]
    seen_branches: set[int] = set()

    for input_assignment in range(1 << circuit.input_count):
        input_bits = tuple(bool((input_assignment >> index) & 1) for index in range(circuit.input_count))
        values = evaluate_all_wires(circuit, input_bits)

        cut_index = 0
        for offset, variable in enumerate(cut_variables):
            if values[variable]:
                cut_index |= 1 << offset

        residual_index = 0
        for offset, variable in enumerate(remaining_inputs):
            if values[variable]:
                residual_index |= 1 << offset

        output_code = 2 if values[circuit.output] else 1
        tables[cut_index][residual_index] |= output_code
        seen_branches.add(cut_index)

    signature_counts = Counter(bytes(table) for table in tables)
    impossible_signature = bytes(residual_points)
    impossible_branches = signature_counts.get(impossible_signature, 0)
    reachable_signatures = {
        signature for signature in signature_counts if signature != impossible_signature
    }
    largest_class = max(signature_counts.values(), default=0)

    return QuotientStats(
        cut_size=len(cut_variables),
        raw_branches=raw_branches,
        reachable_branches=len(seen_branches),
        unique_signatures=len(reachable_signatures),
        impossible_branches=impossible_branches,
        largest_class=largest_class,
        residual_points=residual_points,
    )


def format_order(circuit: Circuit, order: tuple[int, ...], limit: int) -> str:
    return ", ".join(describe_variable(circuit, variable) for variable in order[:limit])


def run() -> str:
    seed = 0x51_6E_A7
    rng = random.Random(seed)
    cases: list[tuple[str, Circuit, int]] = [
        ("random-dag-12x40", random_dag(12, 40, rng), 7),
        ("random-dag-12x60", random_dag(12, 60, rng), 7),
        ("random-3sat-12x30", random_3sat_circuit(12, 30, rng), 7),
        ("random-3sat-14x45", random_3sat_circuit(14, 45, rng), 6),
    ]

    lines = [
        "Exact cutset residual-signature quotient experiment",
        f"seed={seed}",
        "A branch signature records the exact output relation over every remaining input assignment.",
        "Branches with identical signatures can be solved once and shared without approximation.",
        "",
    ]

    for label, circuit, max_k in cases:
        input_order = input_reuse_order(circuit)[:max_k]
        graph_order = greedy_graph_cutset(circuit, max_k)
        lines.append(f"[{label}] inputs={circuit.input_count}, gates={len(circuit.gates)}")
        for strategy, order in (("input-reuse", input_order), ("internal-graph", graph_order)):
            lines.append(f"  {strategy} order: {format_order(circuit, order, max_k)}")
            for k in range(max_k + 1):
                stats = residual_signatures(circuit, order[:k])
                saving = stats.raw_branches - stats.unique_signatures
                quotient_ratio = (
                    stats.raw_branches / stats.unique_signatures
                    if stats.unique_signatures
                    else float("inf")
                )
                lines.append(
                    f"    k={k}, raw={stats.raw_branches}, reachable={stats.reachable_branches}, "
                    f"unique-exact-residuals={stats.unique_signatures}, impossible={stats.impossible_branches}, "
                    f"saved={saving}, ratio={quotient_ratio:.2f}x, largest-class={stats.largest_class}, "
                    f"residual-points={stats.residual_points}"
                )
        lines.append("")

    lines.extend([
        "Interpretation:",
        "- The quotient is exact: signatures are complete residual input/output relations.",
        "- Internal-wire assignments can be impossible; all impossible branches share one empty signature.",
        "- Repeated reachable signatures remove part of the 2^k branch multiplier through memoization.",
        "- A polynomial algorithm still needs signatures or canonical certificates without enumerating all residual inputs.",
    ])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("cutset-residual-quotient-output.txt").write_text(output, encoding="utf-8", newline="\n")
