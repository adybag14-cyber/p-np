#!/usr/bin/env python3
"""Build and verify exact nonimage certificates for tiny circuit-function universes."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class CertificateProfile:
    variables: int
    gate_budget: int
    represented_functions: int
    total_functions: int
    hard_table: int
    distinguishing_inputs: tuple[int, ...]


def projection_table(n: int, variable: int) -> int:
    value = 0
    for assignment in range(1 << n):
        value |= ((assignment >> variable) & 1) << assignment
    return value


def reachable_functions(n: int, max_gates: int) -> set[int]:
    mask = (1 << (1 << n)) - 1
    exact: list[set[int]] = [set() for _ in range(max_gates + 1)]
    minimum: dict[int, int] = {}

    base = {0, mask}
    base.update(projection_table(n, variable) for variable in range(n))
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

    return set(minimum)


def first_difference(left: int, right: int, width: int) -> int:
    difference = left ^ right
    if difference == 0:
        raise ValueError("tables are equal")
    for index in range(width):
        if (difference >> index) & 1:
            return index
    raise AssertionError("nonzero difference had no bit")


def make_profile(n: int, gate_budget: int) -> CertificateProfile:
    represented = reachable_functions(n, gate_budget)
    total = 1 << (1 << n)
    hard = next(table for table in range(total) if table not in represented)
    width = 1 << n
    ordered = tuple(sorted(represented))
    witnesses = tuple(first_difference(table, hard, width) for table in ordered)

    for table, input_index in zip(ordered, witnesses, strict=True):
        assert ((table >> input_index) & 1) != ((hard >> input_index) & 1)

    return CertificateProfile(
        variables=n,
        gate_budget=gate_budget,
        represented_functions=len(ordered),
        total_functions=total,
        hard_table=hard,
        distinguishing_inputs=witnesses,
    )


def table_bits(value: int, n: int) -> str:
    return format(value, f"0{1 << n}b")[::-1]


def main() -> None:
    profiles = [make_profile(3, 4), make_profile(4, 4)]
    lines: list[str] = []
    lines.append("Exact range-avoidance certificates")
    lines.append("certificate stores one distinguishing input per represented function")
    lines.append("")

    for profile in profiles:
        input_bits_per_entry = profile.variables
        certificate_bits = profile.represented_functions * input_bits_per_entry
        table_storage = 1 << profile.variables
        histogram: dict[int, int] = {}
        for witness in profile.distinguishing_inputs:
            histogram[witness] = histogram.get(witness, 0) + 1

        lines.append(
            f"n={profile.variables}, gates<={profile.gate_budget}, "
            f"represented={profile.represented_functions}, total={profile.total_functions}"
        )
        lines.append(
            "  selected hard table: " + table_bits(profile.hard_table, profile.variables)
        )
        lines.append(f"  stored hard-table bits: {table_storage}")
        lines.append(f"  certificate entries: {profile.represented_functions}")
        lines.append(f"  distinguishing-input bits: {certificate_bits}")
        lines.append(f"  independently verified entries: {len(profile.distinguishing_inputs)}")
        lines.append(
            "  witness-index histogram: "
            + ", ".join(f"{index}:{count}" for index, count in sorted(histogram.items()))
        )
        lines.append("")

    lines.append("Asymptotic raw-certificate scale for b=n^2 code bits")
    lines.append("n code-bits entries=2^b distinguishing-input-bits=n*2^b")
    for n in range(2, 9):
        code_bits = n * n
        entries = 1 << code_bits
        cert_bits = n * entries
        lines.append(f"{n:2d} {code_bits:9d} {entries:20d} {cert_bits:35d}")

    lines.append("")
    lines.append("Interpretation:")
    lines.append("  a complete nonimage proof is easy to check entry by entry")
    lines.append("  but the raw proof has one entry for every candidate code")
    lines.append("  the tiny exact experiments already need more certificate bits than table bits")
    lines.append("  at b=n^2 the raw proof grows as n*2^(n^2)")
    lines.append("  a P-versus-NP separation needs a succinct locally checkable replacement")

    output = "\n".join(lines) + "\n"
    print(output, end="")
    Path(__file__).with_name("range-avoidance-certificate-output.txt").write_text(
        output, encoding="utf-8", newline="\n"
    )


if __name__ == "__main__":
    main()
