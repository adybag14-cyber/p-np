from __future__ import annotations

import itertools
import math
import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from circuit_cutset_conditioning import input_reuse_order
from circuit_message_width import Circuit, random_3sat_circuit, random_dag

Cube = tuple[int, ...]  # -1 = unset, 0 = false, 1 = true


@dataclass(frozen=True)
class CoverResult:
    terms: tuple[Cube, ...]
    literals: int
    exact: bool
    seconds: float


@dataclass(frozen=True)
class MtResult:
    nodes: int
    decision_nodes: int
    terminals: int
    order: tuple[int, ...]


def residual_signature(circuit: Circuit, cut_variables: Sequence[int], cut_assignment: int) -> int:
    cut_index = {variable: index for index, variable in enumerate(cut_variables)}
    remaining = [variable for variable in range(circuit.input_count) if variable not in cut_index]
    signature = 0
    for residual_assignment in range(1 << len(remaining)):
        inputs = [False] * circuit.input_count
        for variable, position in cut_index.items():
            inputs[variable] = bool((cut_assignment >> position) & 1)
        for position, variable in enumerate(remaining):
            inputs[variable] = bool((residual_assignment >> position) & 1)
        if circuit.evaluate(inputs):
            signature |= 1 << residual_assignment
    return signature


def signature_table(circuit: Circuit, cut_variables: Sequence[int]) -> tuple[int, ...]:
    return tuple(
        residual_signature(circuit, cut_variables, assignment)
        for assignment in range(1 << len(cut_variables))
    )


def cube_cover_mask(cube: Cube) -> int:
    k = len(cube)
    result = 0
    for assignment in range(1 << k):
        if all(value < 0 or value == ((assignment >> index) & 1) for index, value in enumerate(cube)):
            result |= 1 << assignment
    return result


def safe_cubes(labels: Sequence[int]) -> tuple[dict[Cube, tuple[int, int]], tuple[Cube, ...]]:
    k = (len(labels) - 1).bit_length()
    safe: dict[Cube, tuple[int, int]] = {}
    for cube in itertools.product((-1, 0, 1), repeat=k):
        cover = cube_cover_mask(cube)
        first = (cover & -cover).bit_length() - 1
        label = labels[first]
        remaining = cover
        monochromatic = True
        while remaining:
            bit = remaining & -remaining
            assignment = bit.bit_length() - 1
            if labels[assignment] != label:
                monochromatic = False
                break
            remaining ^= bit
        if monochromatic:
            safe[cube] = (label, cover)

    primes: list[Cube] = []
    for cube, (label, _) in safe.items():
        has_safe_parent = False
        for index, value in enumerate(cube):
            if value < 0:
                continue
            parent = cube[:index] + (-1,) + cube[index + 1 :]
            parent_data = safe.get(parent)
            if parent_data is not None and parent_data[0] == label:
                has_safe_parent = True
                break
        if not has_safe_parent:
            primes.append(cube)
    return safe, tuple(primes)


def literal_count(cube: Cube) -> int:
    return sum(value >= 0 for value in cube)


def greedy_cover(universe: int, candidates: Sequence[tuple[Cube, int]]) -> tuple[Cube, ...]:
    uncovered = universe
    chosen: list[Cube] = []
    while uncovered:
        cube, cover = max(
            candidates,
            key=lambda item: ((item[1] & uncovered).bit_count(), -literal_count(item[0])),
        )
        gain = cover & uncovered
        if not gain:
            raise AssertionError("candidate family does not cover universe")
        chosen.append(cube)
        uncovered &= ~cover
    return tuple(chosen)


def minimum_cover(universe: int, candidates: Sequence[tuple[Cube, int]], timeout: float = 30.0) -> CoverResult:
    started = time.perf_counter()
    # A cube whose region is contained in another candidate is never needed for term minimisation.
    unique: dict[int, Cube] = {}
    for cube, cover in candidates:
        previous = unique.get(cover)
        if previous is None or literal_count(cube) < literal_count(previous):
            unique[cover] = cube
    reduced: list[tuple[Cube, int]] = []
    items = [(cube, cover) for cover, cube in unique.items()]
    for cube, cover in items:
        if any(cover != other and cover & ~other == 0 for _, other in items):
            continue
        reduced.append((cube, cover))

    greedy = greedy_cover(universe, reduced)
    best_terms = list(greedy)
    best_score = (len(best_terms), sum(map(literal_count, best_terms)))
    by_assignment: dict[int, list[int]] = {}
    for assignment in range(universe.bit_length()):
        if (universe >> assignment) & 1:
            by_assignment[assignment] = [
                index for index, (_, cover) in enumerate(reduced) if (cover >> assignment) & 1
            ]
    memo: dict[int, int] = {}
    timed_out = False

    def search(uncovered: int, chosen: list[int], literal_total: int) -> None:
        nonlocal best_terms, best_score, timed_out
        if time.perf_counter() - started > timeout:
            timed_out = True
            return
        if not uncovered:
            terms = [reduced[index][0] for index in chosen]
            score = (len(terms), literal_total)
            if score < best_score:
                best_score = score
                best_terms = terms
            return
        if len(chosen) >= best_score[0]:
            return
        prior = memo.get(uncovered)
        if prior is not None and prior <= len(chosen):
            return
        memo[uncovered] = len(chosen)
        maximum_gain = max((cover & uncovered).bit_count() for _, cover in reduced)
        lower = math.ceil(uncovered.bit_count() / maximum_gain)
        if len(chosen) + lower > best_score[0]:
            return
        uncovered_assignments = [index for index in by_assignment if (uncovered >> index) & 1]
        pivot = min(
            uncovered_assignments,
            key=lambda assignment: sum(bool(reduced[index][1] & uncovered) for index in by_assignment[assignment]),
        )
        options = sorted(
            by_assignment[pivot],
            key=lambda index: (
                -(reduced[index][1] & uncovered).bit_count(),
                literal_count(reduced[index][0]),
            ),
        )
        for index in options:
            cube, cover = reduced[index]
            gain = cover & uncovered
            if not gain:
                continue
            search(uncovered & ~cover, chosen + [index], literal_total + literal_count(cube))
            if timed_out:
                return

    search(universe, [], 0)
    return CoverResult(tuple(best_terms), best_score[1], not timed_out, time.perf_counter() - started)


def exact_dnf_cover(labels: Sequence[int], primes: Sequence[Cube]) -> CoverResult:
    started = time.perf_counter()
    all_terms: list[Cube] = []
    total_literals = 0
    exact = True
    for label in sorted(set(labels)):
        universe = sum(1 << assignment for assignment, value in enumerate(labels) if value == label)
        candidates = [(cube, cube_cover_mask(cube)) for cube in primes if labels[(cube_cover_mask(cube) & -cube_cover_mask(cube)).bit_length() - 1] == label]
        result = minimum_cover(universe, candidates)
        all_terms.extend(result.terms)
        total_literals += result.literals
        exact = exact and result.exact
    # Independent verification of the returned cover and monochromaticity.
    covered = 0
    for cube in all_terms:
        mask = cube_cover_mask(cube)
        covered |= mask
        values = {labels[index] for index in range(len(labels)) if (mask >> index) & 1}
        if len(values) != 1:
            raise AssertionError((cube, values))
    if covered != (1 << len(labels)) - 1:
        raise AssertionError("cover incomplete")
    return CoverResult(tuple(all_terms), total_literals, exact, time.perf_counter() - started)


def mtbdd_size(labels: Sequence[int], order: Sequence[int]) -> tuple[int, int, int]:
    terminal_ids: dict[int, int] = {}
    unique_nodes: dict[tuple[int, int, int], int] = {}
    next_id = 0

    def terminal(label: int) -> int:
        nonlocal next_id
        if label not in terminal_ids:
            terminal_ids[label] = next_id
            next_id += 1
        return terminal_ids[label]

    def build(depth: int, assignments: tuple[int, ...]) -> int:
        nonlocal next_id
        first_label = labels[assignments[0]]
        if all(labels[index] == first_label for index in assignments):
            return terminal(first_label)
        variable = order[depth]
        low = tuple(index for index in assignments if ((index >> variable) & 1) == 0)
        high = tuple(index for index in assignments if ((index >> variable) & 1) == 1)
        low_id = build(depth + 1, low)
        high_id = build(depth + 1, high)
        if low_id == high_id:
            return low_id
        key = (variable, low_id, high_id)
        node = unique_nodes.get(key)
        if node is None:
            node = next_id
            next_id += 1
            unique_nodes[key] = node
        return node

    build(0, tuple(range(len(labels))))
    return next_id, len(unique_nodes), len(terminal_ids)


def optimal_mtbdd(labels: Sequence[int]) -> MtResult:
    k = (len(labels) - 1).bit_length()
    best: MtResult | None = None
    for order in itertools.permutations(range(k)):
        nodes, decisions, terminals = mtbdd_size(labels, order)
        candidate = MtResult(nodes, decisions, terminals, tuple(order))
        if best is None or (candidate.nodes, candidate.decision_nodes, candidate.order) < (
            best.nodes,
            best.decision_nodes,
            best.order,
        ):
            best = candidate
    assert best is not None
    return best


def describe_cube(cube: Cube, cut_variables: Sequence[int]) -> str:
    literals = []
    for index, value in enumerate(cube):
        if value >= 0:
            literals.append(("" if value else "~") + f"x{cut_variables[index]}")
    return "1" if not literals else "&".join(literals)


def run() -> str:
    seed = 0x5E_AA_1C
    rng = random.Random(seed)
    cases: list[tuple[str, Circuit, int]] = [
        ("random-dag-12x40", random_dag(12, 40, rng), 8),
        ("random-dag-12x60", random_dag(12, 60, rng), 8),
        ("random-3sat-12x30", random_3sat_circuit(12, 30, rng), 8),
        ("random-3sat-14x45", random_3sat_circuit(14, 45, rng), 7),
    ]
    lines = [
        "Exact semantic residual DNF and MTBDD experiment",
        f"seed={seed}",
        "A cube is accepted only when all of its full cut assignments induce the identical exact residual truth function.",
        "Minimum DNF covers are solved over prime monochromatic cubes; MTBDDs are minimised over every fixed cut-variable order.",
        "",
    ]
    for name, circuit, maximum_k in cases:
        order = input_reuse_order(circuit)
        lines.append(f"[{name}] inputs={circuit.input_count}, gates={len(circuit.gates)}, cut-order={order[:maximum_k]}")
        for k in range(3, maximum_k + 1):
            cut_variables = order[:k]
            labels = signature_table(circuit, cut_variables)
            safe, primes = safe_cubes(labels)
            cover = exact_dnf_cover(labels, primes)
            mtbdd = optimal_mtbdd(labels)
            examples = ",".join(describe_cube(cube, cut_variables) for cube in cover.terms[:4])
            lines.append(
                f"  k={k}, raw={1 << k}, semantic-classes={len(set(labels))}, safe-cubes={len(safe)}, "
                f"prime-cubes={len(primes)}, min-dnf-terms={len(cover.terms)}, literals={cover.literals}, "
                f"cover-exact={cover.exact}, mtbdd-nodes={mtbdd.nodes}, decisions={mtbdd.decision_nodes}, "
                f"terminals={mtbdd.terminals}, mtbdd-order={mtbdd.order}, examples={examples}"
            )
        lines.append("")
    lines.extend(
        [
            "Interpretation:",
            "- Semantic quotient cardinality is only a lower bound on representation size.",
            "- A DNF term is a partial cut assignment whose entire subcube has one residual signature.",
            "- The exact cube cover can overlap for SAT; model counting would additionally require disjointness or inclusion-exclusion.",
            "- MTBDD and DNF sizes expose different geometries of the same residual-label function.",
        ]
    )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    with Path("residual-dnf-cover-output.txt").open("w", encoding="utf-8", newline="\n") as stream:
        stream.write(output)
