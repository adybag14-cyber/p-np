from __future__ import annotations

import itertools
import random
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from optimal_obdd import function_table


@dataclass(frozen=True)
class Feature:
    name: str
    table: int
    eval_cost: int


def bit(value: int, n: int, index: int) -> int:
    return (value >> (n - 1 - index)) & 1


def table_from_predicate(n: int, predicate: Callable[[tuple[int, ...]], bool]) -> int:
    return function_table(n, lambda bits: predicate(tuple(int(x) for x in bits)))


def feature_pool(n: int, nonlinear: bool) -> list[Feature]:
    features: dict[int, Feature] = {}

    def add(name: str, table: int, cost: int) -> None:
        previous = features.get(table)
        candidate = Feature(name, table, cost)
        if previous is None or (cost, name) < (previous.eval_cost, previous.name):
            features[table] = candidate

    # All nonzero parity masks. This includes ordinary variables.
    for mask in range(1, 1 << n):
        indices = tuple(i for i in range(n) if mask & (1 << (n - 1 - i)))
        table = 0
        for assignment in range(1 << n):
            value = sum(bit(assignment, n, i) for i in indices) & 1
            table |= value << assignment
        add("xor(" + ",".join(map(str, indices)) + ")", table, len(indices))

    if nonlinear:
        for degree in (2, 3):
            for indices in itertools.combinations(range(n), degree):
                and_table = 0
                majority_table = 0
                for assignment in range(1 << n):
                    values = [bit(assignment, n, i) for i in indices]
                    and_table |= int(all(values)) << assignment
                    majority_table |= int(sum(values) * 2 >= degree + 1) << assignment
                add("and(" + ",".join(map(str, indices)) + ")", and_table, degree)
                if degree == 3:
                    add("maj(" + ",".join(map(str, indices)) + ")", majority_table, degree)

        # Globally symmetric but cheap observables.
        for threshold in range(1, n + 1):
            ge_table = table_from_predicate(n, lambda bits, t=threshold: sum(bits) >= t)
            eq_table = table_from_predicate(n, lambda bits, t=threshold: sum(bits) == t)
            add(f"weight>={threshold}", ge_table, n)
            add(f"weight=={threshold}", eq_table, n)

    return sorted(features.values(), key=lambda f: (f.eval_cost, f.name))


def signature_partition(n: int, selected: tuple[Feature, ...]) -> dict[int, list[int]]:
    blocks: dict[int, list[int]] = {}
    for assignment in range(1 << n):
        signature = 0
        for feature in selected:
            signature = (signature << 1) | ((feature.table >> assignment) & 1)
        blocks.setdefault(signature, []).append(assignment)
    return blocks


def ambiguity_score(relation: int, blocks: dict[int, list[int]]) -> tuple[int, int, int]:
    mixed_pairs = 0
    mixed_mass = 0
    for assignments in blocks.values():
        positives = sum((relation >> assignment) & 1 for assignment in assignments)
        negatives = len(assignments) - positives
        if positives and negatives:
            mixed_pairs += positives * negatives
            mixed_mass += len(assignments)
    return mixed_pairs, mixed_mass, len(blocks)


def exact_signature(relation: int, blocks: dict[int, list[int]]) -> bool:
    return ambiguity_score(relation, blocks)[0] == 0


@dataclass
class FeatureResult:
    selected: tuple[Feature, ...]
    image_size: int
    exact: bool

    @property
    def eval_cost(self) -> int:
        return sum(feature.eval_cost for feature in self.selected)


def greedy_features(relation: int, n: int, pool: list[Feature]) -> FeatureResult:
    selected: tuple[Feature, ...] = ()
    remaining = list(pool)
    while True:
        blocks = signature_partition(n, selected)
        if exact_signature(relation, blocks):
            return FeatureResult(selected, len(blocks), True)
        current_score = ambiguity_score(relation, blocks)
        best: tuple[tuple[int, int, int, int, str], Feature] | None = None
        for feature in remaining:
            trial = selected + (feature,)
            score = ambiguity_score(relation, signature_partition(n, trial))
            key = (score[0], score[1], score[2], feature.eval_cost, feature.name)
            if best is None or key < best[0]:
                best = (key, feature)
        if best is None or best[0][:2] >= current_score[:2]:
            return FeatureResult(selected, len(blocks), False)
        chosen = best[1]
        selected += (chosen,)
        remaining.remove(chosen)


def beam_features(
    relation: int,
    n: int,
    pool: list[Feature],
    *,
    width: int = 96,
    max_features: int = 6,
) -> FeatureResult:
    beam: list[tuple[Feature, ...]] = [()]
    seen_partitions: set[tuple[tuple[int, ...], ...]] = set()
    best_exact: FeatureResult | None = None

    for _depth in range(max_features + 1):
        scored: list[tuple[tuple[int, int, int, int, tuple[str, ...]], tuple[Feature, ...]]] = []
        for selected in beam:
            blocks = signature_partition(n, selected)
            partition_key = tuple(sorted(tuple(group) for group in blocks.values()))
            if partition_key in seen_partitions:
                continue
            seen_partitions.add(partition_key)
            mixed_pairs, mixed_mass, image_size = ambiguity_score(relation, blocks)
            result = FeatureResult(selected, image_size, mixed_pairs == 0)
            if result.exact:
                if best_exact is None or (
                    len(result.selected), result.image_size, result.eval_cost
                ) < (
                    len(best_exact.selected), best_exact.image_size, best_exact.eval_cost
                ):
                    best_exact = result
                continue
            if len(selected) >= max_features:
                continue
            used = {feature.table for feature in selected}
            for feature in pool:
                if feature.table in used:
                    continue
                trial = selected + (feature,)
                trial_blocks = signature_partition(n, trial)
                score = ambiguity_score(relation, trial_blocks)
                key = (
                    score[0],
                    score[1],
                    score[2],
                    sum(item.eval_cost for item in trial),
                    tuple(item.name for item in trial),
                )
                scored.append((key, trial))
        if best_exact is not None:
            return best_exact
        scored.sort(key=lambda item: item[0])
        beam = [trial for _key, trial in scored[:width]]
        if not beam:
            break

    if best_exact is not None:
        return best_exact
    greedy = greedy_features(relation, n, pool)
    return greedy


def verify_result(relation: int, n: int, result: FeatureResult) -> None:
    blocks = signature_partition(n, result.selected)
    if not exact_signature(relation, blocks):
        raise AssertionError("mixed acceptance fiber")
    if result.image_size != len(blocks):
        raise AssertionError("incorrect feature image size")


def run() -> str:
    seed_value = 0x0B5E_7A8E
    rng = random.Random(seed_value)
    started = time.perf_counter()
    n = 6
    functions: list[tuple[str, int]] = [
        ("parity-6", function_table(n, lambda bits: sum(bits) % 2 == 1)),
        ("majority-6", function_table(n, lambda bits: sum(bits) >= 3)),
        ("exact-one-6", function_table(n, lambda bits: sum(bits) == 1)),
        ("exact-two-6", function_table(n, lambda bits: sum(bits) == 2)),
        ("equality-halves-3+3", function_table(n, lambda bits: bits[:3] == bits[3:])),
        (
            "inner-product-3",
            function_table(
                n,
                lambda bits: sum(int(bits[i] and bits[i + 3]) for i in range(3)) % 2 == 1,
            ),
        ),
    ]
    functions.extend((f"random-6-{i + 1}", rng.getrandbits(1 << n)) for i in range(12))

    linear_pool = feature_pool(n, nonlinear=False)
    nonlinear_pool = feature_pool(n, nonlinear=True)
    lines = [
        "Nonlinear observable quotient experiment",
        f"seed={seed_value}",
        f"linear-features={len(linear_pool)}, nonlinear-pool={len(nonlinear_pool)}",
        "A feature set is accepted only when every signature fiber has a constant truth value.",
        "",
    ]

    for label, relation in functions:
        linear = beam_features(relation, n, linear_pool, width=72, max_features=6)
        nonlinear = beam_features(relation, n, nonlinear_pool, width=128, max_features=6)
        verify_result(relation, n, linear)
        verify_result(relation, n, nonlinear)
        lines.append(
            f"{label}: linear-k={len(linear.selected)}, linear-image={linear.image_size}, "
            f"nonlinear-k={len(nonlinear.selected)}, nonlinear-image={nonlinear.image_size}, "
            f"eval-cost={nonlinear.eval_cost}, features=[{', '.join(f.name for f in nonlinear.selected)}]"
        )

    lines.append(f"total-seconds={time.perf_counter() - started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("nonlinear-observable-search-output.txt").write_text(output, encoding="utf-8")
