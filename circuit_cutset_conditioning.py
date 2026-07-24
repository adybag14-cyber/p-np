from __future__ import annotations

import random
import time
from dataclasses import dataclass
from pathlib import Path

from circuit_message_width import (
    Circuit,
    Factor,
    RowCutoff,
    Stats,
    brute_force_image,
    choose_variable,
    gate_factor,
    join_bucket,
    project_out,
    random_3sat_circuit,
    random_dag,
    shared_contradiction,
)


@dataclass
class CutsetStats:
    cut_size: int
    branches: int
    image: tuple[bool, ...]
    max_peak_rows: int
    max_peak_scope: int
    total_join_checks: int
    total_created: int
    cutoff_branches: int
    seconds: float


def restrict_factor(factor: Factor, fixed: dict[int, bool]) -> Factor:
    fixed_in_scope = tuple(variable for variable in factor.scope if variable in fixed)
    if not fixed_in_scope:
        return factor
    kept_rows: set[int] = set()
    clear_mask = -1
    for variable in fixed_in_scope:
        clear_mask &= ~(1 << variable)
    for row in factor.rows:
        if all(bool((row >> variable) & 1) == fixed[variable] for variable in fixed_in_scope):
            kept_rows.add(row & clear_mask)
    return Factor(tuple(variable for variable in factor.scope if variable not in fixed), kept_rows)


def output_image_fixed(
    circuit: Circuit,
    fixed: dict[int, bool],
    cutoff: int,
) -> Stats:
    started = time.perf_counter()
    factors = [restrict_factor(gate_factor(gate), fixed) for gate in circuit.gates]
    factors = [factor for factor in factors if factor.scope or factor.rows != {0}]
    counters = {
        "checks": 0,
        "created": len(factors),
        "max_rows": max((len(factor.rows) for factor in factors), default=1),
        "max_scope": max((len(factor.scope) for factor in factors), default=0),
    }
    remaining = set(range(circuit.next_variable)) - {circuit.output} - set(fixed)
    eliminated = 0
    try:
        while remaining:
            variable = choose_variable(factors, remaining)
            remaining.remove(variable)
            bucket = [factor for factor in factors if variable in factor.scope]
            factors = [factor for factor in factors if variable not in factor.scope]
            if not bucket:
                continue
            merged = join_bucket(bucket, counters, cutoff)
            projected = project_out(merged, variable)
            counters["created"] += 1
            counters["max_rows"] = max(counters["max_rows"], len(projected.rows))
            counters["max_scope"] = max(counters["max_scope"], len(projected.scope))
            factors.append(projected)
            eliminated += 1
        final = join_bucket(factors, counters, cutoff) if factors else Factor((), {0})
        image = tuple(sorted({bool((row >> circuit.output) & 1) for row in final.rows}))
        return Stats(
            image=image,
            max_rows=counters["max_rows"],
            max_scope=counters["max_scope"],
            join_checks=counters["checks"],
            factors_created=counters["created"],
            eliminated=eliminated,
            cutoff=False,
            seconds=time.perf_counter() - started,
        )
    except RowCutoff:
        return Stats(
            image=(),
            max_rows=max(counters["max_rows"], cutoff + 1),
            max_scope=counters["max_scope"],
            join_checks=counters["checks"],
            factors_created=counters["created"],
            eliminated=eliminated,
            cutoff=True,
            seconds=time.perf_counter() - started,
        )


def input_reuse_order(circuit: Circuit) -> tuple[int, ...]:
    degree = [0] * circuit.input_count
    for gate in circuit.gates:
        for variable in set(gate.inputs):
            if variable < circuit.input_count:
                degree[variable] += 1
    return tuple(sorted(range(circuit.input_count), key=lambda variable: (-degree[variable], variable)))


def condition_all(
    circuit: Circuit,
    cut_variables: tuple[int, ...],
    cutoff: int,
) -> CutsetStats:
    started = time.perf_counter()
    union_image: set[bool] = set()
    max_peak_rows = 0
    max_peak_scope = 0
    total_join_checks = 0
    total_created = 0
    cutoff_branches = 0
    for assignment in range(1 << len(cut_variables)):
        fixed = {
            variable: bool((assignment >> index) & 1)
            for index, variable in enumerate(cut_variables)
        }
        stats = output_image_fixed(circuit, fixed, cutoff)
        max_peak_rows = max(max_peak_rows, stats.max_rows)
        max_peak_scope = max(max_peak_scope, stats.max_scope)
        total_join_checks += stats.join_checks
        total_created += stats.factors_created
        if stats.cutoff:
            cutoff_branches += 1
        else:
            union_image.update(stats.image)
    return CutsetStats(
        cut_size=len(cut_variables),
        branches=1 << len(cut_variables),
        image=tuple(sorted(union_image)),
        max_peak_rows=max_peak_rows,
        max_peak_scope=max_peak_scope,
        total_join_checks=total_join_checks,
        total_created=total_created,
        cutoff_branches=cutoff_branches,
        seconds=time.perf_counter() - started,
    )


def format_image(image: tuple[bool, ...], cutoff_branches: int) -> str:
    values = "{" + ",".join("1" if value else "0" for value in image) + "}"
    return values + (f"+{cutoff_branches}-unknown" if cutoff_branches else "")


def run() -> str:
    seed = 0xC075_E7
    rng = random.Random(seed)
    cases: list[tuple[str, Circuit, int, int]] = [
        ("shared-x-and-not-x", shared_contradiction(), 1, 1_000_000),
        ("random-dag-12x40", random_dag(12, 40, rng), 6, 1_000_000),
        ("random-dag-12x60", random_dag(12, 60, rng), 6, 1_000_000),
        ("random-3sat-12x30", random_3sat_circuit(12, 30, rng), 6, 1_000_000),
        ("random-3sat-14x45", random_3sat_circuit(14, 45, rng), 5, 1_000_000),
    ]
    lines = [
        "Circuit cutset-conditioning experiment",
        f"seed={seed}",
        "Cut variables are ordered by input reuse count; every 2^k branch is solved exactly.",
        "",
    ]
    for label, circuit, max_k, cutoff in cases:
        order = input_reuse_order(circuit)
        lines.append(
            f"[{label}] inputs={circuit.input_count}, gates={len(circuit.gates)}, cut-order={order[:max_k]}"
        )
        brute = brute_force_image(circuit) if circuit.input_count <= 14 else ()
        for cut_size in range(max_k + 1):
            stats = condition_all(circuit, order[:cut_size], cutoff)
            if not stats.cutoff_branches and brute and stats.image != brute:
                raise AssertionError((label, cut_size, stats.image, brute))
            lines.append(
                f"  k={cut_size}, branches={stats.branches}, image={format_image(stats.image, stats.cutoff_branches)}, "
                f"max-peak-rows={stats.max_peak_rows}, max-scope={stats.max_peak_scope}, "
                f"total-checks={stats.total_join_checks}, created={stats.total_created}, seconds={stats.seconds:.4f}"
            )
        lines.append("")
    lines.extend([
        "Interpretation:",
        "- Conditioning can sharply lower the worst residual table width.",
        "- The exact total cost must still include every one of the 2^k branches.",
        "- A useful cutset needs logarithmic size or enough width reduction to offset its branch multiplier.",
        "- High input reuse is a heuristic, not a universal certificate of an optimal cutset.",
    ])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("circuit-cutset-conditioning-output.txt").write_text(output, encoding="utf-8")
