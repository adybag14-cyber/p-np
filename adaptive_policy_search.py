from __future__ import annotations

import itertools
import random
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from adaptive_semantic_dag import Signature, cofactor_signature, reduce_signature
from memo_dpll import random_3cnf
from optimal_obdd import best_obdd, cnf_table, function_table


@dataclass
class PolicyDag:
    root: int
    nodes: dict[int, tuple[int, int, int]]
    terminals: frozenset[int]
    reachable: frozenset[Signature]

    @property
    def size(self) -> int:
        return len(self.nodes) + len(self.terminals)

    def evaluate(self, assignment: int, n: int) -> bool:
        node = self.root
        while node >= 2:
            variable, low, high = self.nodes[node]
            bit = bool((assignment >> (n - 1 - variable)) & 1)
            node = high if bit else low
        return bool(node)


def build_policy_dag(
    table: int,
    n: int,
    fallback_order: tuple[int, ...],
    overrides: dict[Signature, int],
) -> PolicyDag:
    root_signature = reduce_signature(tuple(range(n)), table)
    semantic_memo: dict[Signature, int] = {}
    intern: dict[tuple[int, int, int], int] = {}
    nodes: dict[int, tuple[int, int, int]] = {}
    terminals: set[int] = set()
    reachable: set[Signature] = set()

    def choose(signature: Signature) -> tuple[int, int]:
        variables, _pattern = signature
        overridden = overrides.get(signature)
        if overridden is not None and overridden in variables:
            return variables.index(overridden), overridden
        for variable in fallback_order:
            if variable in variables:
                return variables.index(variable), variable
        raise AssertionError("nonterminal signature has no policy variable")

    def build(signature: Signature) -> int:
        previous = semantic_memo.get(signature)
        if previous is not None:
            return previous
        reachable.add(signature)
        variables, pattern = signature
        if not variables:
            terminal = 1 if pattern & 1 else 0
            terminals.add(terminal)
            semantic_memo[signature] = terminal
            return terminal
        position, variable = choose(signature)
        low_signature = cofactor_signature(signature, position, 0)
        high_signature = cofactor_signature(signature, position, 1)
        low = build(low_signature)
        high = build(high_signature)
        if low == high:
            semantic_memo[signature] = low
            return low
        key = (variable, low, high)
        node = intern.get(key)
        if node is None:
            node = len(nodes) + 2
            intern[key] = node
            nodes[node] = key
        semantic_memo[signature] = node
        return node

    root = build(root_signature)
    return PolicyDag(root, nodes, frozenset(terminals), frozenset(reachable))


def verify_policy(table: int, n: int, dag: PolicyDag) -> None:
    for assignment in range(1 << n):
        expected = bool((table >> assignment) & 1)
        actual = dag.evaluate(assignment, n)
        if actual != expected:
            raise AssertionError((assignment, expected, actual))


def improve_policy(
    table: int,
    n: int,
    best_order: tuple[int, ...],
    *,
    pair_search: bool,
    max_rounds: int = 20,
) -> tuple[PolicyDag, dict[Signature, int], int]:
    overrides: dict[Signature, int] = {}
    current = build_policy_dag(table, n, best_order, overrides)
    baseline_size = current.size

    for _round in range(max_rounds):
        best_trial: tuple[int, dict[Signature, int], PolicyDag] | None = None
        for signature in current.reachable:
            variables, _pattern = signature
            if not variables:
                continue
            for variable in variables:
                trial_overrides = dict(overrides)
                trial_overrides[signature] = variable
                trial = build_policy_dag(table, n, best_order, trial_overrides)
                candidate = (trial.size, trial_overrides, trial)
                if trial.size < current.size and (
                    best_trial is None or candidate[0] < best_trial[0]
                ):
                    best_trial = candidate
        if best_trial is None and pair_search:
            states = [s for s in current.reachable if s[0]]
            for i, first in enumerate(states):
                for second in states[i + 1 :]:
                    for first_var in first[0]:
                        for second_var in second[0]:
                            trial_overrides = dict(overrides)
                            trial_overrides[first] = first_var
                            trial_overrides[second] = second_var
                            trial = build_policy_dag(table, n, best_order, trial_overrides)
                            candidate = (trial.size, trial_overrides, trial)
                            if trial.size < current.size and (
                                best_trial is None or candidate[0] < best_trial[0]
                            ):
                                best_trial = candidate
        if best_trial is None:
            break
        _size, overrides, current = best_trial

    verify_policy(table, n, current)
    if current.size > baseline_size:
        raise AssertionError("monotone policy search worsened the baseline")
    return current, overrides, baseline_size


def format_distribution(distribution: Counter[int]) -> str:
    total = sum(distribution.values())
    return ", ".join(
        f"{value}: {count} ({100.0 * count / total:.2f}%)"
        for value, count in sorted(distribution.items())
    )


def exact_four_variable_search() -> tuple[Counter[int], list[str]]:
    orders = tuple(itertools.permutations(range(4)))
    improvements: Counter[int] = Counter()
    strongest: list[tuple[int, int, int, int]] = []
    max_improvement = -1
    known_hard = [0x0168, 0x0186, 0x0192, 0x0194, 0x0196, 0x0249, 0x0261, 0x0268]
    tables = list(range(0, 1 << 16, 32)) + known_hard
    for table in dict.fromkeys(tables):
        ordered = best_obdd(table, 4, orders)
        improved, overrides, baseline = improve_policy(
            table, 4, ordered.order, pair_search=False, max_rounds=8
        )
        if baseline != ordered.size:
            raise AssertionError((table, baseline, ordered.size, ordered.order))
        improvement = ordered.size - improved.size
        improvements[improvement] += 1
        if improvement > max_improvement:
            max_improvement = improvement
            strongest = [(table, ordered.size, improved.size, len(overrides))]
        elif improvement == max_improvement and len(strongest) < 12:
            strongest.append((table, ordered.size, improved.size, len(overrides)))
    lines = [
        f"table=0x{table:04x}/ordered={ordered}/adaptive={adaptive}/overrides={count}"
        for table, ordered, adaptive, count in strongest
    ]
    return improvements, lines


def sampled_search(
    n: int, samples: int, rng: random.Random
) -> tuple[Counter[int], Counter[int]]:
    orders = tuple(itertools.permutations(range(n)))
    improvements: Counter[int] = Counter()
    override_counts: Counter[int] = Counter()
    for _ in range(samples):
        table = rng.getrandbits(1 << n)
        ordered = best_obdd(table, n, orders)
        improved, overrides, baseline = improve_policy(
            table, n, ordered.order, pair_search=False, max_rounds=10
        )
        if baseline != ordered.size:
            raise AssertionError((baseline, ordered.size))
        improvements[ordered.size - improved.size] += 1
        override_counts[len(overrides)] += 1
    return improvements, override_counts


def structured_search() -> list[str]:
    n = 8
    orders = tuple(itertools.permutations(range(n)))
    functions = {
        "parity-8": function_table(n, lambda bits: sum(bits) % 2 == 1),
        "majority-8": function_table(n, lambda bits: sum(bits) >= 4),
        "exact-one-8": function_table(n, lambda bits: sum(bits) == 1),
        "equality-halves-4+4": function_table(n, lambda bits: bits[:4] == bits[4:]),
        "inner-product-4": function_table(
            n,
            lambda bits: sum(int(bits[i] and bits[i + 4]) for i in range(4)) % 2 == 1,
        ),
    }
    lines: list[str] = []
    for label, table in functions.items():
        ordered = best_obdd(table, n, orders)
        improved, overrides, baseline = improve_policy(
            table, n, ordered.order, pair_search=False, max_rounds=20
        )
        lines.append(
            f"{label}: ordered={ordered.size}, adaptive={improved.size}, "
            f"improvement={ordered.size-improved.size}, overrides={len(overrides)}"
        )
    return lines


def cnf_search(rng: random.Random) -> list[str]:
    n = 8
    orders = tuple(itertools.permutations(range(n)))
    lines: list[str] = []
    for index, ratio in enumerate((3.0, 4.2, 5.5), start=1):
        formula = random_3cnf(n, round(ratio * n), rng)
        table = cnf_table(formula, n)
        ordered = best_obdd(table, n, orders)
        improved, overrides, baseline = improve_policy(
            table, n, ordered.order, pair_search=False, max_rounds=20
        )
        lines.append(
            f"random-3cnf-{index}: clauses={len(formula)}, sat={table.bit_count()}/256, "
            f"ordered={ordered.size}, adaptive={improved.size}, "
            f"improvement={ordered.size-improved.size}, overrides={len(overrides)}"
        )
    return lines


def run() -> str:
    seed = 0xB011_C150
    rng = random.Random(seed)
    started = time.perf_counter()
    lines = [
        "Monotone global adaptive-policy search",
        f"seed={seed}",
        "Every search starts from the exact best OBDD order and accepts only smaller DAGs.",
        "",
    ]

    improvements4, strongest = exact_four_variable_search()
    lines.append("Deterministic 2,056-table four-variable sample plus known hardest OBDD tables")
    lines.append("ordered-minus-adaptive: " + format_distribution(improvements4))
    lines.append("strongest: " + ", ".join(strongest))
    lines.append("")

    for n, samples in ((5, 60), (6, 15)):
        improvements, override_counts = sampled_search(n, samples, rng)
        lines.append(f"{samples} random {n}-variable functions")
        lines.append("ordered-minus-adaptive: " + format_distribution(improvements))
        lines.append("accepted override counts: " + format_distribution(override_counts))
        lines.append("")

    lines.append("Structured eight-variable functions")
    lines.extend(structured_search())
    lines.append("")

    lines.append("Eight-variable CNFs")
    lines.extend(cnf_search(rng))
    lines.append("")
    lines.append(f"total-seconds={time.perf_counter()-started:.3f}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    output = run()
    print(output, end="")
    Path("adaptive-policy-search-output.txt").write_text(output, encoding="utf-8")
