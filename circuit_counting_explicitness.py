#!/usr/bin/env python3
"""Exact small-circuit enumeration and asymptotic counting profiles."""
from __future__ import annotations

from dataclasses import dataclass
from math import log10
from pathlib import Path


@dataclass(frozen=True)
class ExactProfile:
    variables: int
    max_gates: int
    total_functions: int
    reachable_by_gate: tuple[int, ...]
    first_missing: int | None


def projection_table(n: int, variable: int) -> int:
    table = 0
    for assignment in range(1 << n):
        bit = (assignment >> variable) & 1
        table |= bit << assignment
    return table


def exact_min_gate_functions(n: int, max_gates: int) -> ExactProfile:
    mask = (1 << (1 << n)) - 1
    exact: list[set[int]] = [set() for _ in range(max_gates + 1)]
    minimum: dict[int, int] = {}

    base = {0, mask}
    base.update(projection_table(n, i) for i in range(n))
    exact[0] = base
    minimum.update({table: 0 for table in base})

    for gates in range(1, max_gates + 1):
        candidates: set[int] = set()

        for value in exact[gates - 1]:
            candidates.add(mask ^ value)

        for left_cost in range(gates):
            right_cost = gates - 1 - left_cost
            for left in exact[left_cost]:
                for right in exact[right_cost]:
                    candidates.add(left & right)
                    candidates.add(left | right)
                    candidates.add(left ^ right)

        new_values = {value for value in candidates if value not in minimum}
        exact[gates] = new_values
        minimum.update({table: gates for table in new_values})

    cumulative: list[int] = []
    seen: set[int] = set()
    for level in exact:
        seen.update(level)
        cumulative.append(len(seen))

    total = 1 << (1 << n)
    missing = next((table for table in range(total) if table not in seen), None)
    return ExactProfile(n, max_gates, total, tuple(cumulative), missing)


def decimal_digits_of_power_of_two(exponent: int) -> int:
    return int(exponent * log10(2)) + 1


def truth_table_bits(value: int, n: int) -> str:
    width = 1 << n
    return format(value, f"0{width}b")[::-1]


def main() -> None:
    profiles = [
        exact_min_gate_functions(3, 4),
        exact_min_gate_functions(4, 4),
    ]

    lines: list[str] = []
    lines.append("Exact small-circuit counting and explicitness")
    lines.append("gates use NOT, AND, OR, XOR; constants and projections cost zero")
    lines.append("")

    for profile in profiles:
        lines.append(
            f"n={profile.variables}, Boolean functions={profile.total_functions}, "
            f"gate budget={profile.max_gates}"
        )
        for gates, reachable in enumerate(profile.reachable_by_gate):
            missing = profile.total_functions - reachable
            lines.append(
                f"  gates<= {gates}: reachable={reachable:6d}, missing={missing:6d}"
            )
        if profile.first_missing is None:
            lines.append("  first missing truth table: none at this budget")
        else:
            lines.append(
                "  lexicographically first missing truth table: "
                + truth_table_bits(profile.first_missing, profile.variables)
            )
        lines.append("")

    lines.append("Asymptotic description counting")
    lines.append("n code-bits=n^2 log2(all-functions)=2^n counting-gap")
    for n in range(2, 17):
        code_bits = n * n
        function_log2 = 1 << n
        lines.append(
            f"{n:2d} {code_bits:13d} {function_log2:22d} "
            f"{'yes' if code_bits < function_log2 else 'no'}"
        )

    lines.append("")
    lines.append("Exhaustive lexicographic-selection scale")
    lines.append("n truth-table-bits number-of-candidate-functions decimal-digits")
    for n in (4, 8, 12, 16, 20):
        table_bits = 1 << n
        digits = decimal_digits_of_power_of_two(table_bits)
        lines.append(f"{n:2d} {table_bits:16d} 2^(2^{n}) {digits:14d}")

    lines.append("")
    lines.append("Interpretation:")
    lines.append("  counting proves missing functions once code bits < 2^n")
    lines.append("  exact enumeration can select one for tiny n")
    lines.append("  the selected object is supplied as a 2^n-bit truth table")
    lines.append("  exhaustive lexicographic construction scans up to 2^(2^n) candidates")
    lines.append("  neither step provides a uniform polynomial-time NP language")

    output = "\n".join(lines) + "\n"
    print(output, end="")
    Path(__file__).with_name("circuit-counting-explicitness-output.txt").write_text(
        output, encoding="utf-8", newline="\n"
    )


if __name__ == "__main__":
    main()
