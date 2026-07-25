#!/usr/bin/env python3
"""Exact arithmetic profiles for padding and polynomial-exponent diagonalisation."""
from __future__ import annotations

from pathlib import Path


def main() -> None:
    lines: list[str] = []
    lines.append("Padding and diagonalisation obstruction profiles")
    lines.append("")

    lines.append("Exponential-time language padded by its full runtime")
    lines.append("n original-time padded-length simulation/padded-length")
    for n in (4, 8, 12, 16, 20):
        original = 1 << n
        padded = original
        lines.append(f"{n:2d} {original:13d} {padded:13d} {original // padded:24d}")

    lines.append("")
    lines.append("Underpadding by n^3 leaves exponential history outside the bound")
    lines.append("n original-time padded-length=n^3 original/padded")
    for n in (8, 12, 16, 20, 24, 32):
        original = 1 << n
        padded = n**3
        lines.append(f"{n:2d} {original:13d} {padded:17d} {original / padded:15.3f}")

    lines.append("")
    lines.append("Unbounded polynomial exponents at the fixed input length two")
    lines.append("fixed-bound-exponent attacking-exponent fixed-cost attack-cost factor")
    for fixed in range(1, 9):
        attacking = fixed + 1
        fixed_cost = 2**fixed
        attack_cost = 2**attacking
        lines.append(
            f"{fixed:20d} {attacking:18d} {fixed_cost:10d} "
            f"{attack_cost:11d} {attack_cost // fixed_cost:6d}"
        )

    lines.append("")
    lines.append("Per-stage candidate versus one uniform candidate")
    lines.append("target-exponent selected-stage selected-stage-beats-target fixed-stage-5-beats-target")
    fixed_candidate = 5
    for target in range(0, 10):
        selected = target + 1
        lines.append(
            f"{target:15d} {selected:14d} "
            f"{str(target < selected)} {str(target < fixed_candidate)}"
        )

    lines.append("")
    lines.append("Interpretation:")
    lines.append("  padding to the original runtime makes direct simulation degree one")
    lines.append("  smaller polynomial padding does not fit the full deterministic history")
    lines.append("  no fixed exponent simulates machines whose exponents are unbounded")
    lines.append("  choosing a new hard language for every exponent does not yield one NP language")
    lines.append("  the missing theorem must combine one fixed verifier with hardness against all P exponents")

    output = "\n".join(lines) + "\n"
    print(output, end="")
    Path(__file__).with_name("padding-diagonalization-output.txt").write_text(
        output, encoding="utf-8", newline="\n"
    )


if __name__ == "__main__":
    main()
