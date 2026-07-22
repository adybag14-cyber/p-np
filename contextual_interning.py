from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from pathlib import Path

from adaptive_policy_search import build_policy_dag, verify_policy
from optimal_obdd import best_obdd


def exact_best_order(table: int, n: int) -> tuple[int, ...]:
    return best_obdd(table, n, itertools.permutations(range(n))).order


def deterministic_tables(n: int, count: int, seed: int) -> list[int]:
    rng = random.Random(seed)
    limit = 1 << (1 << n)
    tables = {0, limit - 1}
    while len(tables) < count:
        tables.add(rng.randrange(limit))
    return sorted(tables)


def analyse_table(table: int, n: int) -> tuple[Counter[str], list[str]]:
    order = exact_best_order(table, n)
    baseline = build_policy_dag(table, n, order, {})
    verify_policy(table, n, baseline)
    base_keys = frozenset(baseline.nodes.values())
    counts: Counter[str] = Counter()
    examples: list[str] = []

    for signature in baseline.reachable:
        variables, _pattern = signature
        if len(variables) <= 1:
            continue
        baseline_variable = next(variable for variable in order if variable in variables)
        for variable in variables:
            if variable == baseline_variable:
                continue
            trial = build_policy_dag(table, n, order, {signature: variable})
            verify_policy(table, n, trial)
            trial_keys = frozenset(trial.nodes.values())

            node_delta = trial.size - baseline.size
            semantic_delta = len(trial.reachable) - len(baseline.reachable)
            key_added = len(trial_keys - base_keys)
            key_removed = len(base_keys - trial_keys)
            terminal_delta = len(trial.terminals) - len(baseline.terminals)
            if node_delta != key_added - key_removed + terminal_delta:
                raise AssertionError("node-key accounting mismatch")

            if node_delta < 0:
                counts["improvement"] += 1
                if semantic_delta < 0:
                    category = "semantic-shrink"
                elif semantic_delta == 0:
                    category = "same-semantic-better-interning"
                else:
                    category = "semantic-growth-better-interning"
                counts[category] += 1
                if len(examples) < 20:
                    examples.append(
                        f"table=0x{table:0{1 << max(0, n - 2)}x}, n={n}, "
                        f"size={baseline.size}->{trial.size}, "
                        f"reachable={len(baseline.reachable)}->{len(trial.reachable)}, "
                        f"keys_added={key_added}, keys_removed={key_removed}, "
                        f"terminal_delta={terminal_delta}, category={category}"
                    )
            elif node_delta == 0:
                counts["equal"] += 1
            else:
                counts["worse"] += 1

            sign_semantic = -1 if semantic_delta < 0 else 0 if semantic_delta == 0 else 1
            sign_node = -1 if node_delta < 0 else 0 if node_delta == 0 else 1
            counts[f"sign_{sign_semantic}_{sign_node}"] += 1
    return counts, examples


def merge(target: Counter[str], source: Counter[str]) -> None:
    for key, value in source.items():
        target[key] += value


def run() -> str:
    started = time.perf_counter()
    lines = [
        "Contextual interning experiment",
        "Exact node cost is decomposed into added decision keys, removed decision keys, and terminal change.",
        "",
    ]
    total: Counter[str] = Counter()
    examples: list[str] = []
    suites = [
        (4, deterministic_tables(4, 768, 0xC017_181)),
        (5, deterministic_tables(5, 36, 0xC017_182)),
    ]
    for n, tables in suites:
        suite: Counter[str] = Counter()
        suite_examples: list[str] = []
        for table in tables:
            counts, found = analyse_table(table, n)
            merge(suite, counts)
            suite_examples.extend(found)
        merge(total, suite)
        examples.extend(suite_examples)
        tested = suite["improvement"] + suite["equal"] + suite["worse"]
        lines.append(
            f"n={n}, tables={len(tables)}, overrides={tested}, "
            f"improved={suite['improvement']}, equal={suite['equal']}, worse={suite['worse']}"
        )
        lines.append(
            "improvement mechanisms: "
            f"semantic-shrink={suite['semantic-shrink']}, "
            f"same-semantic-better-interning={suite['same-semantic-better-interning']}, "
            f"semantic-growth-better-interning={suite['semantic-growth-better-interning']}"
        )
        lines.append("")

    lines.append("combined improvement mechanisms:")
    lines.append(
        f"semantic-shrink={total['semantic-shrink']}, "
        f"same-semantic-better-interning={total['same-semantic-better-interning']}, "
        f"semantic-growth-better-interning={total['semantic-growth-better-interning']}"
    )
    lines.append("")
    lines.append("semantic-sign versus node-sign matrix (-1 shrink, 0 equal, 1 grow):")
    for semantic_sign in (-1, 0, 1):
        lines.append(
            f"semantic {semantic_sign}: "
            + ", ".join(
                f"node {node_sign}={total[f'sign_{semantic_sign}_{node_sign}']}"
                for node_sign in (-1, 0, 1)
            )
        )
    lines.append("")
    lines.append("strict-improvement examples:")
    lines.extend(examples[:20] if examples else ["none"])
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("contextual-interning-output.txt").write_text(output, encoding="utf-8")
