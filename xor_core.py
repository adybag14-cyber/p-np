from __future__ import annotations

import random
import statistics
import time
from collections import deque
from dataclasses import dataclass
from pathlib import Path

from xor_affine import AffineSystem, gaussian_sat, random_3xor, recognize_canonical_3xor


@dataclass(frozen=True)
class PeelResult:
    original_variables: int
    original_equations: int
    peeled_variables: int
    peeled_equations: int
    core_variables: int
    core_equations: int
    core: AffineSystem


def peel_affine_system(system: AffineSystem) -> PeelResult:
    equations = list(system.equations)
    active_equations = [True] * len(equations)
    incident: list[set[int]] = [set() for _ in range(system.variable_count)]
    for equation_index, (mask, _rhs) in enumerate(equations):
        bits = mask
        while bits:
            low = bits & -bits
            variable = low.bit_length() - 1
            incident[variable].add(equation_index)
            bits ^= low

    queue = deque(variable for variable, edges in enumerate(incident) if len(edges) == 1)
    peeled_variables: set[int] = set()
    peeled_equations = 0

    while queue:
        variable = queue.popleft()
        live = [edge for edge in incident[variable] if active_equations[edge]]
        if len(live) != 1:
            continue
        equation_index = live[0]
        active_equations[equation_index] = False
        peeled_variables.add(variable)
        peeled_equations += 1
        mask, _rhs = equations[equation_index]
        bits = mask
        while bits:
            low = bits & -bits
            neighbor = low.bit_length() - 1
            incident[neighbor].discard(equation_index)
            if len(incident[neighbor]) == 1:
                queue.append(neighbor)
            bits ^= low

    remaining = tuple(
        equation for index, equation in enumerate(equations) if active_equations[index]
    )
    core_variable_set: set[int] = set()
    for mask, _rhs in remaining:
        bits = mask
        while bits:
            low = bits & -bits
            core_variable_set.add(low.bit_length() - 1)
            bits ^= low

    core = AffineSystem(
        variable_count=system.variable_count,
        equations=remaining,
        immediate_contradiction=system.immediate_contradiction,
    )
    return PeelResult(
        original_variables=system.variable_count,
        original_equations=len(equations),
        peeled_variables=len(peeled_variables),
        peeled_equations=peeled_equations,
        core_variables=len(core_variable_set),
        core_equations=len(remaining),
        core=core,
    )


def validate() -> int:
    rng = random.Random(0x5045454C56414C)
    checked = 0
    for n in range(3, 22):
        maximum = n * (n - 1) * (n - 2) // 6
        for _ in range(40):
            equations = min(maximum, rng.randint(1, max(1, 2 * n)))
            planted = rng.getrandbits(n) if rng.getrandbits(1) else None
            formula = random_3xor(n, equations, rng, planted=planted)
            system = recognize_canonical_3xor(formula)
            if system is None:
                raise AssertionError("generated formula was not recognized")
            peeled = peel_affine_system(system)
            full_answer = gaussian_sat(system)
            core_answer = gaussian_sat(peeled.core)
            if full_answer != core_answer:
                raise AssertionError((n, equations, full_answer, core_answer, peeled))
            checked += 1
    return checked


def run_density_experiment() -> list[str]:
    rng = random.Random(0x5045454C434F5245)
    n = 240
    trials = 24
    ratios = (0.25, 0.40, 0.55, 0.70, 0.80, 0.90, 1.00, 1.10, 1.25, 1.50)
    lines = [
        f"random-density experiment: variables={n}, trials-per-ratio={trials}",
        "ratio | equations | mean-core-vars | mean-core-equations | empty-core-rate | sat-rate | mean-seconds",
        "------+-----------+----------------+---------------------+-----------------+----------+-------------",
    ]
    for ratio in ratios:
        equation_count = round(ratio * n)
        core_variables: list[int] = []
        core_equations: list[int] = []
        empty_count = 0
        sat_count = 0
        elapsed: list[float] = []
        for _ in range(trials):
            formula = random_3xor(n, equation_count, rng)
            system = recognize_canonical_3xor(formula)
            if system is None:
                raise AssertionError("recognition failure")
            started = time.perf_counter()
            peeled = peel_affine_system(system)
            answer = gaussian_sat(peeled.core)
            elapsed.append(time.perf_counter() - started)
            core_variables.append(peeled.core_variables)
            core_equations.append(peeled.core_equations)
            empty_count += peeled.core_equations == 0
            sat_count += answer
        lines.append(
            f"{ratio:>4.2f} | {equation_count:>9} | "
            f"{statistics.mean(core_variables):>14.2f} | "
            f"{statistics.mean(core_equations):>19.2f} | "
            f"{empty_count / trials:>15.3f} | {sat_count / trials:>8.3f} | "
            f"{statistics.mean(elapsed):>11.6f}"
        )
    return lines


def run_planted_experiment() -> list[str]:
    rng = random.Random(0x504C414E544544)
    n = 500
    lines = ["", f"planted systems: variables={n}"]
    for ratio in (0.5, 0.8, 1.0, 1.25, 1.5, 2.0):
        equation_count = round(ratio * n)
        planted = rng.getrandbits(n)
        formula = random_3xor(n, equation_count, rng, planted=planted)
        system = recognize_canonical_3xor(formula)
        if system is None:
            raise AssertionError("recognition failure")
        peeled = peel_affine_system(system)
        answer = gaussian_sat(peeled.core)
        lines.append(
            f"ratio={ratio:.2f}, equations={equation_count}, "
            f"peeled-equations={peeled.peeled_equations}, "
            f"core-vars={peeled.core_variables}, core-equations={peeled.core_equations}, "
            f"core-sat={answer}"
        )
    return lines


def run() -> str:
    checked = validate()
    lines = [
        "Private-variable peeling and affine-core experiment",
        f"full-vs-core validation cases={checked}",
        "",
    ]
    lines.extend(run_density_experiment())
    lines.extend(run_planted_experiment())
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("xor-core-output.txt").write_text(output, encoding="utf-8")
