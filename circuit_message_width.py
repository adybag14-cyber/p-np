from __future__ import annotations

import itertools
import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Sequence


@dataclass(frozen=True)
class Gate:
    inputs: tuple[int, ...]
    output: int
    operation: Callable[[tuple[bool, ...]], bool]
    name: str


@dataclass
class Circuit:
    input_count: int
    gates: list[Gate]
    output: int
    next_variable: int

    @classmethod
    def empty(cls, input_count: int) -> "Circuit":
        return cls(input_count, [], 0, input_count)

    def add_gate(
        self,
        inputs: Sequence[int],
        operation: Callable[[tuple[bool, ...]], bool],
        name: str,
    ) -> int:
        output = self.next_variable
        self.next_variable += 1
        self.gates.append(Gate(tuple(inputs), output, operation, name))
        self.output = output
        return output

    def evaluate(self, input_bits: Sequence[bool]) -> bool:
        if len(input_bits) != self.input_count:
            raise ValueError(len(input_bits))
        values = list(input_bits) + [False] * (self.next_variable - self.input_count)
        for gate in self.gates:
            values[gate.output] = gate.operation(tuple(values[index] for index in gate.inputs))
        return values[self.output]


@dataclass
class Factor:
    scope: tuple[int, ...]
    rows: set[int]

    @property
    def mask(self) -> int:
        result = 0
        for variable in self.scope:
            result |= 1 << variable
        return result


@dataclass
class Stats:
    image: tuple[bool, ...]
    max_rows: int
    max_scope: int
    join_checks: int
    factors_created: int
    eliminated: int
    cutoff: bool
    seconds: float


class RowCutoff(RuntimeError):
    pass


def gate_factor(gate: Gate) -> Factor:
    scope = tuple(sorted(gate.inputs + (gate.output,)))
    rows: set[int] = set()
    for assignment in range(1 << len(gate.inputs)):
        input_values = tuple(bool((assignment >> offset) & 1) for offset in range(len(gate.inputs)))
        row = 0
        for offset, variable in enumerate(gate.inputs):
            if input_values[offset]:
                row |= 1 << variable
        if gate.operation(input_values):
            row |= 1 << gate.output
        rows.add(row)
    return Factor(scope, rows)


def estimated_join_rows(left: Factor, right: Factor) -> int:
    overlap = len(set(left.scope) & set(right.scope))
    return max(1, (len(left.rows) * len(right.rows)) >> overlap)


def join(left: Factor, right: Factor, cutoff: int) -> tuple[Factor, int]:
    overlap = left.mask & right.mask
    if not overlap:
        estimated = len(left.rows) * len(right.rows)
        if estimated > cutoff:
            raise RowCutoff(estimated)
        return (
            Factor(tuple(sorted(set(left.scope) | set(right.scope))), {a | b for a in left.rows for b in right.rows}),
            estimated,
        )
    if len(left.rows) > len(right.rows):
        left, right = right, left
    index: dict[int, list[int]] = {}
    for row in right.rows:
        index.setdefault(row & overlap, []).append(row)
    rows: set[int] = set()
    checks = 0
    for row in left.rows:
        matches = index.get(row & overlap, ())
        checks += len(matches)
        for other in matches:
            rows.add(row | other)
            if len(rows) > cutoff:
                raise RowCutoff(len(rows))
    return Factor(tuple(sorted(set(left.scope) | set(right.scope))), rows), checks


def project_out(factor: Factor, variable: int) -> Factor:
    mask = ~(1 << variable)
    return Factor(tuple(item for item in factor.scope if item != variable), {row & mask for row in factor.rows})


def join_bucket(factors: list[Factor], stats: dict[str, int], cutoff: int) -> Factor:
    work = list(factors)
    while len(work) > 1:
        best: tuple[int, int, int] | None = None
        for i in range(len(work)):
            for j in range(i + 1, len(work)):
                candidate = (estimated_join_rows(work[i], work[j]), i, j)
                if best is None or candidate < best:
                    best = candidate
        assert best is not None
        _, i, j = best
        right = work.pop(j)
        left = work.pop(i)
        merged, checks = join(left, right, cutoff)
        stats["checks"] += checks
        stats["created"] += 1
        stats["max_rows"] = max(stats["max_rows"], len(merged.rows))
        stats["max_scope"] = max(stats["max_scope"], len(merged.scope))
        work.append(merged)
    return work[0]


def choose_variable(factors: Sequence[Factor], remaining: set[int]) -> int:
    candidates: list[tuple[int, int, int, int]] = []
    for variable in remaining:
        bucket = [factor for factor in factors if variable in factor.scope]
        if not bucket:
            candidates.append((0, 0, 0, variable))
            continue
        union_scope = set().union(*(set(factor.scope) for factor in bucket))
        estimate = 1
        total_scope = 0
        for factor in bucket:
            estimate *= max(1, len(factor.rows))
            total_scope += len(factor.scope)
        estimate >>= max(0, total_scope - len(union_scope))
        candidates.append((len(union_scope), estimate, len(bucket), variable))
    return min(candidates)[-1]


def output_image(circuit: Circuit, cutoff: int = 1_000_000) -> Stats:
    started = time.perf_counter()
    factors = [gate_factor(gate) for gate in circuit.gates]
    stats = {
        "checks": 0,
        "created": len(factors),
        "max_rows": max((len(factor.rows) for factor in factors), default=1),
        "max_scope": max((len(factor.scope) for factor in factors), default=0),
    }
    remaining = set(range(circuit.next_variable)) - {circuit.output}
    eliminated = 0
    try:
        while remaining:
            variable = choose_variable(factors, remaining)
            remaining.remove(variable)
            bucket = [factor for factor in factors if variable in factor.scope]
            factors = [factor for factor in factors if variable not in factor.scope]
            if not bucket:
                continue
            merged = join_bucket(bucket, stats, cutoff)
            projected = project_out(merged, variable)
            stats["created"] += 1
            stats["max_rows"] = max(stats["max_rows"], len(projected.rows))
            stats["max_scope"] = max(stats["max_scope"], len(projected.scope))
            factors.append(projected)
            eliminated += 1
        final = join_bucket(factors, stats, cutoff) if factors else Factor((), {0})
        image = tuple(sorted({bool((row >> circuit.output) & 1) for row in final.rows}))
        return Stats(
            image,
            stats["max_rows"],
            stats["max_scope"],
            stats["checks"],
            stats["created"],
            eliminated,
            False,
            time.perf_counter() - started,
        )
    except RowCutoff:
        return Stats(
            (),
            max(stats["max_rows"], cutoff + 1),
            stats["max_scope"],
            stats["checks"],
            stats["created"],
            eliminated,
            True,
            time.perf_counter() - started,
        )


def op_not(bits: tuple[bool, ...]) -> bool:
    return not bits[0]


def op_and(bits: tuple[bool, ...]) -> bool:
    return bits[0] and bits[1]


def op_or(bits: tuple[bool, ...]) -> bool:
    return bits[0] or bits[1]


def op_xor(bits: tuple[bool, ...]) -> bool:
    return bits[0] != bits[1]


def op_majority(bits: tuple[bool, ...]) -> bool:
    return sum(bits) >= (len(bits) + 1) // 2


def balanced_binary_tree(input_count: int, operation: Callable[[tuple[bool, ...]], bool], name: str) -> Circuit:
    circuit = Circuit.empty(input_count)
    level = list(range(input_count))
    while len(level) > 1:
        next_level: list[int] = []
        for index in range(0, len(level), 2):
            if index + 1 == len(level):
                next_level.append(level[index])
            else:
                next_level.append(circuit.add_gate(level[index:index + 2], operation, name))
        level = next_level
    circuit.output = level[0]
    return circuit


def parity_chain(input_count: int) -> Circuit:
    circuit = Circuit.empty(input_count)
    current = 0
    for variable in range(1, input_count):
        current = circuit.add_gate((current, variable), op_xor, "xor")
    circuit.output = current
    return circuit


def majority_tree(input_count: int) -> Circuit:
    if input_count < 3:
        raise ValueError(input_count)
    circuit = Circuit.empty(input_count)
    level = list(range(input_count))
    while len(level) > 1:
        next_level: list[int] = []
        for index in range(0, len(level), 3):
            group = level[index:index + 3]
            if len(group) == 1:
                next_level.append(group[0])
            elif len(group) == 2:
                next_level.append(circuit.add_gate(group, op_and, "and"))
            else:
                next_level.append(circuit.add_gate(group, op_majority, "majority3"))
        level = next_level
    circuit.output = level[0]
    return circuit


def shared_contradiction() -> Circuit:
    circuit = Circuit.empty(1)
    negated = circuit.add_gate((0,), op_not, "not")
    output = circuit.add_gate((0, negated), op_and, "and")
    circuit.output = output
    return circuit


def relaxed_contradiction() -> Circuit:
    circuit = Circuit.empty(2)
    negated = circuit.add_gate((1,), op_not, "not")
    output = circuit.add_gate((0, negated), op_and, "and")
    circuit.output = output
    return circuit


def reconvergent_diamond(input_count: int) -> Circuit:
    circuit = Circuit.empty(input_count)
    current = 0
    for variable in range(1, input_count):
        left = circuit.add_gate((current, variable), op_xor, "xor")
        right = circuit.add_gate((current, variable), op_and, "and")
        current = circuit.add_gate((left, right), op_or, "or")
    circuit.output = current
    return circuit


def random_read_once_tree(input_count: int, rng: random.Random) -> Circuit:
    circuit = Circuit.empty(input_count)
    pool = list(range(input_count))
    operations = [(op_and, "and"), (op_or, "or"), (op_xor, "xor")]
    while len(pool) > 1:
        first_index, second_index = sorted(rng.sample(range(len(pool)), 2), reverse=True)
        first = pool.pop(first_index)
        second = pool.pop(second_index)
        operation, name = rng.choice(operations)
        pool.append(circuit.add_gate((first, second), operation, name))
    circuit.output = pool[0]
    return circuit


def random_dag(input_count: int, gate_count: int, rng: random.Random) -> Circuit:
    circuit = Circuit.empty(input_count)
    operations = [(op_and, "and"), (op_or, "or"), (op_xor, "xor")]
    available = list(range(input_count))
    for _ in range(gate_count):
        left, right = rng.sample(available, 2)
        operation, name = rng.choice(operations)
        available.append(circuit.add_gate((left, right), operation, name))
    circuit.output = available[-1]
    return circuit


def random_3sat_circuit(input_count: int, clause_count: int, rng: random.Random) -> Circuit:
    circuit = Circuit.empty(input_count)
    negated = [circuit.add_gate((variable,), op_not, "not") for variable in range(input_count)]
    clause_outputs: list[int] = []
    for _ in range(clause_count):
        variables = rng.sample(range(input_count), 3)
        literals = [variable if rng.getrandbits(1) else negated[variable] for variable in variables]
        first = circuit.add_gate((literals[0], literals[1]), op_or, "or")
        clause_outputs.append(circuit.add_gate((first, literals[2]), op_or, "or"))
    current = clause_outputs[0]
    for clause in clause_outputs[1:]:
        current = circuit.add_gate((current, clause), op_and, "and")
    circuit.output = current
    return circuit


def brute_force_image(circuit: Circuit) -> tuple[bool, ...]:
    return tuple(sorted({
        circuit.evaluate(tuple(bool((assignment >> index) & 1) for index in range(circuit.input_count)))
        for assignment in range(1 << circuit.input_count)
    }))


def validate_small(rng: random.Random) -> int:
    checked = 0
    for input_count in range(1, 8):
        for gate_count in range(1, 8):
            for _ in range(8):
                circuit = random_dag(max(2, input_count), gate_count, rng)
                exact = output_image(circuit, cutoff=200_000)
                if exact.cutoff:
                    raise AssertionError("unexpected validation cutoff")
                brute = brute_force_image(circuit)
                if exact.image != brute:
                    raise AssertionError((input_count, gate_count, exact.image, brute))
                checked += 1
    return checked


def format_stats(label: str, circuit: Circuit, stats: Stats) -> str:
    image = "cutoff" if stats.cutoff else "{" + ",".join("1" if value else "0" for value in stats.image) + "}"
    return (
        f"{label}: inputs={circuit.input_count}, gates={len(circuit.gates)}, vars={circuit.next_variable}, "
        f"image={image}, peak-rows={stats.max_rows}, peak-scope={stats.max_scope}, "
        f"join-checks={stats.join_checks}, eliminated={stats.eliminated}, seconds={stats.seconds:.4f}"
    )


def run() -> str:
    seed = 0xC1AC_017
    rng = random.Random(seed)
    validation_count = validate_small(rng)
    cases: list[tuple[str, Circuit, int]] = [
        ("balanced-and-32", balanced_binary_tree(32, op_and, "and"), 1_000_000),
        ("balanced-xor-32", balanced_binary_tree(32, op_xor, "xor"), 1_000_000),
        ("parity-chain-32", parity_chain(32), 1_000_000),
        ("majority-tree-27", majority_tree(27), 1_000_000),
        ("random-read-once-32", random_read_once_tree(32, rng), 1_000_000),
        ("shared-x-and-not-x", shared_contradiction(), 1_000_000),
        ("relaxed-independent-x-and-not-y", relaxed_contradiction(), 1_000_000),
        ("reconvergent-diamond-12", reconvergent_diamond(12), 1_000_000),
        ("random-dag-12x20", random_dag(12, 20, rng), 1_000_000),
        ("random-dag-12x40", random_dag(12, 40, rng), 1_000_000),
        ("random-dag-12x60", random_dag(12, 60, rng), 1_000_000),
        ("random-3sat-circuit-12x30", random_3sat_circuit(12, 30, rng), 1_000_000),
        ("random-3sat-circuit-14x45", random_3sat_circuit(14, 45, rng), 1_000_000),
    ]
    lines = [
        "Circuit message-width experiment",
        f"seed={seed}",
        f"small brute-force validations={validation_count}",
        "Exact gate-relation elimination preserves only the final output variable.",
        "",
    ]
    for label, circuit, cutoff in cases:
        stats = output_image(circuit, cutoff=cutoff)
        if circuit.input_count <= 14 and not stats.cutoff:
            brute = brute_force_image(circuit)
            if brute != stats.image:
                raise AssertionError((label, brute, stats.image))
        lines.append(format_stats(label, circuit, stats))
    lines.extend([
        "",
        "Interpretation:",
        "- Read-once trees keep tiny intermediate tables even for global outputs.",
        "- Shared inputs require equality coupling; dropping it changes satisfiability.",
        "- Reconvergence and CNF-variable reuse increase separator scope and table width.",
        "- A final two-value output image does not imply cheap construction.",
    ])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("circuit-message-width-output.txt").write_text(output, encoding="utf-8")
