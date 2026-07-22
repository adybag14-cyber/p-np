from __future__ import annotations

import random
import time
from dataclasses import dataclass
from pathlib import Path

from memo_dpll import NodeLimitExceeded, brute_sat, solve_cnf
from symbolic_cnf import CNF, normalize_cnf


@dataclass(frozen=True)
class AffineSystem:
    variable_count: int
    equations: tuple[tuple[int, int], ...]  # (bit mask, rhs)
    immediate_contradiction: bool = False


def clause_forbidden_assignment(clause: tuple[int, ...]) -> tuple[tuple[int, ...], int] | None:
    """Return sorted variables and the unique assignment falsifying a full clause."""
    if len(clause) != 3:
        return None
    variables = tuple(sorted(abs(lit) - 1 for lit in clause))
    if len(set(variables)) != 3:
        return None
    by_variable = {abs(lit) - 1: (lit < 0) for lit in clause}
    bits = 0
    for index, variable in enumerate(variables):
        if by_variable[variable]:
            bits |= 1 << index
    return variables, bits


def recognize_canonical_3xor(formula: CNF) -> AffineSystem | None:
    """Recognize complete four-clause encodings of 3-variable XOR equations.

    For a fixed variable triple, exactly four assignments have the wrong parity.
    The canonical CNF contains one clause excluding each wrong assignment. A
    group containing all eight clauses is a directly recognized contradiction.
    Any partial/noncanonical group is rejected and left to the fallback solver.
    """
    formula = normalize_cnf(formula)
    groups: dict[tuple[int, ...], set[int]] = {}
    maximum_variable = -1
    for clause in formula:
        parsed = clause_forbidden_assignment(clause)
        if parsed is None:
            return None
        variables, forbidden = parsed
        maximum_variable = max(maximum_variable, *variables)
        groups.setdefault(variables, set()).add(forbidden)

    equations: list[tuple[int, int]] = []
    contradiction = False
    for variables, forbidden_set in groups.items():
        if len(forbidden_set) == 8:
            contradiction = True
            continue
        if len(forbidden_set) != 4:
            return None
        forbidden_parities = {forbidden.bit_count() & 1 for forbidden in forbidden_set}
        if len(forbidden_parities) != 1:
            return None
        forbidden_parity = next(iter(forbidden_parities))
        expected = {bits for bits in range(8) if (bits.bit_count() & 1) == forbidden_parity}
        if forbidden_set != expected:
            return None
        required_parity = forbidden_parity ^ 1
        mask = sum(1 << variable for variable in variables)
        equations.append((mask, required_parity))

    return AffineSystem(
        variable_count=maximum_variable + 1,
        equations=tuple(equations),
        immediate_contradiction=contradiction,
    )


def gaussian_sat(system: AffineSystem) -> bool:
    if system.immediate_contradiction:
        return False
    pivots: dict[int, tuple[int, int]] = {}
    for original_mask, original_rhs in system.equations:
        mask, rhs = original_mask, original_rhs
        while mask:
            pivot = mask.bit_length() - 1
            previous = pivots.get(pivot)
            if previous is None:
                pivots[pivot] = (mask, rhs)
                break
            mask ^= previous[0]
            rhs ^= previous[1]
        if mask == 0 and rhs:
            return False
    return True


def encode_3xor_equation(variables: tuple[int, int, int], rhs: int) -> CNF:
    clauses: list[tuple[int, ...]] = []
    for bits in range(8):
        if (bits.bit_count() & 1) == rhs:
            continue
        clause: list[int] = []
        for index, variable in enumerate(variables):
            value = (bits >> index) & 1
            clause.append(-(variable + 1) if value else variable + 1)
        clauses.append(tuple(clause))
    return normalize_cnf(clauses)


def random_3xor(
    n: int,
    equation_count: int,
    rng: random.Random,
    *,
    planted: int | None = None,
) -> CNF:
    triples: set[tuple[int, int, int]] = set()
    clauses: list[tuple[int, ...]] = []
    while len(triples) < equation_count:
        triple = tuple(sorted(rng.sample(range(n), 3)))
        if triple in triples:
            continue
        triples.add(triple)
        if planted is None:
            rhs = rng.getrandbits(1)
        else:
            rhs = sum((planted >> variable) & 1 for variable in triple) & 1
        clauses.extend(encode_3xor_equation(triple, rhs))
    return normalize_cnf(clauses)


def validate() -> int:
    rng = random.Random(0x584F5256414C)
    checked = 0
    for n in range(3, 11):
        for _ in range(50):
            equation_count = min(2 * n, n * (n - 1) * (n - 2) // 6)
            planted = rng.getrandbits(n) if rng.getrandbits(1) else None
            formula = random_3xor(n, equation_count, rng, planted=planted)
            recognized = recognize_canonical_3xor(formula)
            if recognized is None:
                raise AssertionError("generated XOR formula was not recognized")
            actual = gaussian_sat(recognized)
            expected = brute_sat(formula, n)
            if actual != expected:
                raise AssertionError((n, actual, expected, formula, recognized))
            checked += 1
    return checked


def compare(label: str, formula: CNF, n: int, limit: int) -> str:
    started = time.perf_counter()
    system = recognize_canonical_3xor(formula)
    if system is None:
        raise AssertionError("benchmark was not recognized")
    affine_answer = gaussian_sat(system)
    affine_seconds = time.perf_counter() - started
    try:
        dpll_answer, stats = solve_cnf(formula, node_limit=limit)
        if dpll_answer != affine_answer:
            raise AssertionError((label, affine_answer, dpll_answer))
        dpll = (
            f"dpll(result={dpll_answer},states={stats.unique_states},branches={stats.branches},"
            f"seconds={stats.elapsed_seconds:.6f})"
        )
    except NodeLimitExceeded:
        dpll = f"dpll(cutoff={limit})"
    return (
        f"{label}: n={n}, equations={len(system.equations)}, result={affine_answer}, "
        f"gaussian(seconds={affine_seconds:.6f}), {dpll}"
    )


def run() -> str:
    checked = validate()
    rng = random.Random(0x414646494E45)
    lines = [
        "Canonical 3-XOR affine-dispatch experiment",
        f"brute-force validation: checked={checked}",
        "",
    ]
    planted_30 = rng.getrandbits(30)
    planted_40 = rng.getrandbits(40)
    lines.append(compare("planted-xor-30x45", random_3xor(30, 45, rng, planted=planted_30), 30, 300_000))
    lines.append(compare("planted-xor-40x60", random_3xor(40, 60, rng, planted=planted_40), 40, 300_000))
    lines.append(compare("random-xor-30x45", random_3xor(30, 45, rng), 30, 300_000))
    lines.append(compare("random-xor-40x60", random_3xor(40, 60, rng), 40, 300_000))

    # Conflicting duplicate equation yields all eight clauses for one triple.
    conflict = normalize_cnf(
        list(encode_3xor_equation((0, 1, 2), 0))
        + list(encode_3xor_equation((0, 1, 2), 1))
    )
    lines.append(compare("direct-conflicting-xor", conflict, 3, 1000))
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("xor-affine-output.txt").write_text(output, encoding="utf-8")
