from __future__ import annotations

import random
import time
from dataclasses import dataclass
from pathlib import Path

from memo_dpll import NodeLimitExceeded, solve_cnf
from xor_affine import gaussian_sat, random_3xor, recognize_canonical_3xor


@dataclass
class Record:
    label: str
    n: int
    equations: int
    seed: int
    result: bool
    states: int
    branches: int
    seconds: float
    cutoff: bool = False


def search_family(n: int, equations: int, trials: int, base_seed: int, planted_mode: bool) -> list[Record]:
    records: list[Record] = []
    for trial in range(trials):
        seed = base_seed + trial
        rng = random.Random(seed)
        planted = rng.getrandbits(n) if planted_mode else None
        formula = random_3xor(n, equations, rng, planted=planted)
        system = recognize_canonical_3xor(formula)
        if system is None:
            raise AssertionError("recognition failure")
        expected = gaussian_sat(system)
        started = time.perf_counter()
        try:
            result, stats = solve_cnf(formula, node_limit=250_000)
            if result != expected:
                raise AssertionError((seed, result, expected))
            records.append(Record(
                label="planted" if planted_mode else "random",
                n=n,
                equations=equations,
                seed=seed,
                result=result,
                states=stats.unique_states,
                branches=stats.branches,
                seconds=time.perf_counter() - started,
            ))
        except NodeLimitExceeded:
            records.append(Record(
                label="planted" if planted_mode else "random",
                n=n,
                equations=equations,
                seed=seed,
                result=expected,
                states=250_000,
                branches=250_000,
                seconds=time.perf_counter() - started,
                cutoff=True,
            ))
            break
    return records


def run() -> str:
    all_records: list[Record] = []
    configurations = [
        (22, 18, 80),
        (22, 22, 80),
        (26, 21, 60),
        (26, 26, 60),
        (30, 24, 40),
        (30, 30, 40),
    ]
    for index, (n, equations, trials) in enumerate(configurations):
        for planted in (True, False):
            all_records.extend(search_family(
                n, equations, trials,
                base_seed=0x584F520000 + index * 10000 + (5000 if planted else 0),
                planted_mode=planted,
            ))

    ranked = sorted(all_records, key=lambda r: (r.cutoff, r.states, r.seconds), reverse=True)
    lines = ["Sparse 3-XOR DPLL hard-instance search", f"instances tested={len(all_records)}", ""]
    for record in ranked[:20]:
        lines.append(
            f"{record.label}-xor-{record.n}x{record.equations}: seed={record.seed}, "
            f"result={record.result}, states={record.states}, branches={record.branches}, "
            f"seconds={record.seconds:.6f}, cutoff={record.cutoff}"
        )
    lines.append("")
    for n, equations, _ in configurations:
        subset = [r for r in all_records if r.n == n and r.equations == equations]
        states = sorted(r.states for r in subset)
        lines.append(
            f"summary-{n}x{equations}: count={len(subset)}, median-states={states[len(states)//2]}, "
            f"max-states={max(states)}, cutoffs={sum(r.cutoff for r in subset)}"
        )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("xor-hard-search-output.txt").write_text(output, encoding="utf-8")
