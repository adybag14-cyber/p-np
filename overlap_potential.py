from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from pathlib import Path

from adaptive_policy_search import PolicyDag, build_policy_dag, verify_policy
from adaptive_semantic_dag import Signature, cofactor_signature
from optimal_obdd import best_obdd


def choose_variable(
    signature: Signature,
    fallback_order: tuple[int, ...],
    overrides: dict[Signature, int],
) -> tuple[int, int]:
    variables, _pattern = signature
    overridden = overrides.get(signature)
    if overridden is not None and overridden in variables:
        return variables.index(overridden), overridden
    for variable in fallback_order:
        if variable in variables:
            return variables.index(variable), variable
    raise AssertionError("terminal signature has no variable")


def semantic_closure(
    root: Signature,
    fallback_order: tuple[int, ...],
    overrides: dict[Signature, int],
) -> frozenset[Signature]:
    memo: dict[Signature, frozenset[Signature]] = {}

    def visit(signature: Signature) -> frozenset[Signature]:
        previous = memo.get(signature)
        if previous is not None:
            return previous
        variables, _pattern = signature
        if not variables:
            result = frozenset((signature,))
            memo[signature] = result
            return result
        position, _variable = choose_variable(signature, fallback_order, overrides)
        low = cofactor_signature(signature, position, 0)
        high = cofactor_signature(signature, position, 1)
        result = frozenset((signature,)) | visit(low) | visit(high)
        memo[signature] = result
        return result

    return visit(root)


def branch_potential(
    signature: Signature,
    variable: int,
    fallback_order: tuple[int, ...],
    overrides: dict[Signature, int],
) -> tuple[int, int, int]:
    variables, _pattern = signature
    position = variables.index(variable)
    low = cofactor_signature(signature, position, 0)
    high = cofactor_signature(signature, position, 1)
    low_states = semantic_closure(low, fallback_order, overrides)
    high_states = semantic_closure(high, fallback_order, overrides)
    child_sum = len(low_states) + len(high_states)
    overlap = len(low_states & high_states)
    union = len(low_states | high_states)
    if union + overlap != child_sum:
        raise AssertionError("finite-set overlap identity failed")
    return child_sum, overlap, union


def exact_best_order(table: int, n: int) -> tuple[int, ...]:
    return best_obdd(table, n, itertools.permutations(range(n))).order


def classify_table(table: int, n: int) -> tuple[Counter[str], list[str]]:
    order = exact_best_order(table, n)
    overrides: dict[Signature, int] = {}
    baseline = build_policy_dag(table, n, order, overrides)
    verify_policy(table, n, baseline)
    counts: Counter[str] = Counter()
    examples: list[str] = []

    for signature in baseline.reachable:
        variables, _pattern = signature
        if len(variables) <= 1:
            continue
        _base_position, base_variable = choose_variable(signature, order, overrides)
        base_sum, base_overlap, base_union = branch_potential(
            signature, base_variable, order, overrides
        )
        for variable in variables:
            if variable == base_variable:
                continue
            trial_overrides = {signature: variable}
            trial: PolicyDag = build_policy_dag(table, n, order, trial_overrides)
            verify_policy(table, n, trial)
            candidate_sum, candidate_overlap, candidate_union = branch_potential(
                signature, variable, order, trial_overrides
            )
            global_delta = trial.size - baseline.size
            potential_delta = candidate_union - base_union
            overlap_gain = candidate_overlap - base_overlap
            sum_delta = candidate_sum - base_sum

            actual = global_delta < 0
            predicted = potential_delta < 0
            overlap_predicted = overlap_gain > 0 and sum_delta <= overlap_gain
            counts[f"actual_{actual}"] += 1
            counts[f"potential_{predicted}"] += 1
            counts[f"pair_{actual}_{predicted}"] += 1
            counts[f"overlap_pair_{actual}_{overlap_predicted}"] += 1

            if actual and len(examples) < 12:
                examples.append(
                    f"table=0x{table:0{1 << max(0, n - 2)}x}, n={n}, "
                    f"baseline={baseline.size}, trial={trial.size}, "
                    f"variable={base_variable}->{variable}, "
                    f"global_delta={global_delta}, potential_delta={potential_delta}, "
                    f"overlap_gain={overlap_gain}, child_sum_delta={sum_delta}"
                )
    return counts, examples


def merge_counts(target: Counter[str], source: Counter[str]) -> None:
    for key, value in source.items():
        target[key] += value


def metrics(counts: Counter[str], prefix: str) -> str:
    tp = counts[f"{prefix}_True_True"]
    fp = counts[f"{prefix}_False_True"]
    fn = counts[f"{prefix}_True_False"]
    tn = counts[f"{prefix}_False_False"]
    precision = tp / (tp + fp) if tp + fp else 0.0
    recall = tp / (tp + fn) if tp + fn else 0.0
    accuracy = (tp + tn) / (tp + fp + fn + tn) if tp + fp + fn + tn else 0.0
    return (
        f"tp={tp}, fp={fp}, fn={fn}, tn={tn}, "
        f"precision={precision:.3f}, recall={recall:.3f}, accuracy={accuracy:.3f}"
    )


def deterministic_tables(n: int, count: int, seed: int) -> list[int]:
    rng = random.Random(seed)
    limit = 1 << (1 << n)
    tables = {0, limit - 1}
    while len(tables) < count:
        tables.add(rng.randrange(limit))
    return sorted(tables)


def run() -> str:
    started = time.perf_counter()
    lines = [
        "Overlap-potential predictor experiment",
        "A candidate is evaluated at one residual against the exact optimal OBDD baseline.",
        "Potential = size of the union of the two semantic descendant closures.",
        "",
    ]

    all_counts: Counter[str] = Counter()
    examples: list[str] = []
    suites = [
        (4, deterministic_tables(4, 768, 0x0A11_166)),
        (5, deterministic_tables(5, 36, 0x0A11_167)),
    ]
    for n, tables in suites:
        suite_counts: Counter[str] = Counter()
        suite_examples: list[str] = []
        for table in tables:
            counts, found = classify_table(table, n)
            merge_counts(suite_counts, counts)
            suite_examples.extend(found)
        merge_counts(all_counts, suite_counts)
        examples.extend(suite_examples)
        lines.append(f"n={n}, tables={len(tables)}, tested overrides={suite_counts['actual_True'] + suite_counts['actual_False']}")
        lines.append("local-union predictor: " + metrics(suite_counts, "pair"))
        lines.append("overlap inequality predictor: " + metrics(suite_counts, "overlap_pair"))
        lines.append("")

    lines.append("combined local-union predictor: " + metrics(all_counts, "pair"))
    lines.append("combined overlap inequality predictor: " + metrics(all_counts, "overlap_pair"))
    lines.append("")
    lines.append("strict global improvements observed:")
    lines.extend(examples[:20] if examples else ["none"])
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("overlap-potential-output.txt").write_text(output, encoding="utf-8")
