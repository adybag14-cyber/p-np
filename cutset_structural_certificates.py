from __future__ import annotations

import random
from collections import defaultdict
from pathlib import Path
from typing import Any

from circuit_cutset_conditioning import input_reuse_order
from circuit_graph_cutset import describe_variable
from circuit_message_width import Circuit, random_3sat_circuit, random_dag
from cutset_residual_quotient import evaluate_all_wires

Expr = tuple[Any, ...]


def const(value: bool) -> Expr:
    return ("const", value)


def variable(index: int) -> Expr:
    return ("var", index)


def negate(expr: Expr) -> Expr:
    if expr[0] == "const":
        return const(not expr[1])
    if expr[0] == "not":
        return expr[1]
    return ("not", expr)


def complement(left: Expr, right: Expr) -> bool:
    return left == negate(right) or right == negate(left)


def binary(name: str, left: Expr, right: Expr) -> Expr:
    if repr(right) < repr(left):
        left, right = right, left
    if name == "and":
        if left == const(False) or right == const(False):
            return const(False)
        if left == const(True):
            return right
        if right == const(True):
            return left
        if left == right:
            return left
        if complement(left, right):
            return const(False)
    elif name == "or":
        if left == const(True) or right == const(True):
            return const(True)
        if left == const(False):
            return right
        if right == const(False):
            return left
        if left == right:
            return left
        if complement(left, right):
            return const(True)
    elif name == "xor":
        if left == const(False):
            return right
        if right == const(False):
            return left
        if left == const(True):
            return negate(right)
        if right == const(True):
            return negate(left)
        if left == right:
            return const(False)
        if complement(left, right):
            return const(True)
    return (name, left, right)


def residual_expression(circuit: Circuit, fixed_inputs: dict[int, bool]) -> Expr:
    expressions: list[Expr] = []
    remaining_map: dict[int, int] = {}
    next_remaining = 0
    for input_index in range(circuit.input_count):
        if input_index in fixed_inputs:
            expressions.append(const(fixed_inputs[input_index]))
        else:
            remaining_map[input_index] = next_remaining
            expressions.append(variable(next_remaining))
            next_remaining += 1

    for gate in circuit.gates:
        children = tuple(expressions[index] for index in gate.inputs)
        if gate.name == "not" and len(children) == 1:
            expression = negate(children[0])
        elif gate.name in {"and", "or", "xor"} and len(children) == 2:
            expression = binary(gate.name, children[0], children[1])
        else:
            expression = (gate.name,) + children
        expressions.append(expression)
    return expressions[circuit.output]


def exact_signatures(circuit: Circuit, cut_variables: tuple[int, ...]) -> list[bytes]:
    remaining_inputs = tuple(index for index in range(circuit.input_count) if index not in cut_variables)
    tables = [bytearray(1 << len(remaining_inputs)) for _ in range(1 << len(cut_variables))]
    for assignment in range(1 << circuit.input_count):
        input_bits = tuple(bool((assignment >> index) & 1) for index in range(circuit.input_count))
        values = evaluate_all_wires(circuit, input_bits)
        cut_index = sum((1 << offset) for offset, variable_index in enumerate(cut_variables) if values[variable_index])
        residual_index = sum((1 << offset) for offset, variable_index in enumerate(remaining_inputs) if values[variable_index])
        tables[cut_index][residual_index] = 2 if values[circuit.output] else 1
    return [bytes(table) for table in tables]


def analyse(circuit: Circuit, cut_variables: tuple[int, ...]) -> tuple[int, int, int, int, float]:
    exact = exact_signatures(circuit, cut_variables)
    certificates: list[Expr] = []
    for assignment in range(1 << len(cut_variables)):
        fixed = {
            variable_index: bool((assignment >> offset) & 1)
            for offset, variable_index in enumerate(cut_variables)
        }
        certificates.append(residual_expression(circuit, fixed))

    cert_to_exact: dict[Expr, set[bytes]] = defaultdict(set)
    for certificate, signature in zip(certificates, exact):
        cert_to_exact[certificate].add(signature)
    unsafe = sum(1 for values in cert_to_exact.values() if len(values) != 1)
    if unsafe:
        raise AssertionError(f"structural certificate merged {unsafe} unequal residuals")

    raw = 1 << len(cut_variables)
    exact_unique = len(set(exact))
    cert_unique = len(set(certificates))
    exact_saving = raw - exact_unique
    cert_saving = raw - cert_unique
    capture = cert_saving / exact_saving if exact_saving else 1.0
    constants = sum(1 for certificate in set(certificates) if certificate[0] == "const")
    return raw, exact_unique, cert_unique, constants, capture


def run() -> str:
    seed = 0xC3_27_1F
    rng = random.Random(seed)
    cases: list[tuple[str, Circuit, int]] = [
        ("random-dag-12x40", random_dag(12, 40, rng), 7),
        ("random-dag-12x60", random_dag(12, 60, rng), 7),
        ("random-3sat-12x30", random_3sat_circuit(12, 30, rng), 7),
        ("random-3sat-14x45", random_3sat_circuit(14, 45, rng), 6),
    ]
    lines = [
        "Cutset structural-certificate experiment",
        f"seed={seed}",
        "Certificates are canonical constant-folded circuit expressions after input substitution.",
        "Certificate equality is syntactic and therefore safely implies identical residual functions.",
        "",
    ]
    for label, circuit, max_k in cases:
        order = input_reuse_order(circuit)[:max_k]
        lines.append(f"[{label}] order=" + ", ".join(describe_variable(circuit, variable_index) for variable_index in order))
        for k in range(max_k + 1):
            raw, exact_unique, cert_unique, constants, capture = analyse(circuit, order[:k])
            lines.append(
                f"  k={k}, raw={raw}, exact-classes={exact_unique}, structural-classes={cert_unique}, "
                f"constant-certificates={constants}, exact-saving-captured={capture:.1%}"
            )
        lines.append("")
    lines.extend([
        "Interpretation:",
        "- Structural equality never merged unequal residual functions in the exhaustive checks.",
        "- Constant folding captures many branch collapses but can miss semantic equivalences.",
        "- A safe certificate partition may be finer than the optimal semantic quotient and still reduce work.",
        "- The remaining discovery problem is to construct a polynomial number of safe certificates without enumerating all cut assignments.",
    ])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("cutset-structural-certificates-output.txt").write_text(output, encoding="utf-8")
