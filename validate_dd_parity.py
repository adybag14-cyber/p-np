#!/usr/bin/env python3
"""Validate parity BDD sizes using the optional tulip-control/dd package.

This script is intentionally not part of the default experiment runner because `dd`
is an external dependency. Run it from an isolated environment containing the exact
external checkout recorded in `dd-parity-validation-output.txt`.
"""

from __future__ import annotations

import importlib.metadata
from itertools import product

from dd import autoref


def expected_parity(bits: tuple[int, ...]) -> bool:
    result = False
    for bit in bits:
        result ^= bool(bit)
    return result


def build_parity(n: int) -> tuple[autoref.BDD, autoref.Function]:
    manager = autoref.BDD()
    names = [f"x{i}" for i in range(n)]
    manager.declare(*names)
    root = manager.false
    for name in names:
        root = root ^ manager.var(name)
    return manager, root


def validate(manager: autoref.BDD, root: autoref.Function, n: int) -> None:
    names = [f"x{i}" for i in range(n)]
    for values in product((0, 1), repeat=n):
        assignment = {name: bool(value) for name, value in zip(names, values, strict=True)}
        reduced = manager.let(assignment, root)
        observed = reduced == manager.true
        expected = expected_parity(values)
        if observed != expected:
            raise AssertionError((n, values, observed, expected))


def main() -> None:
    print("tulip-control/dd complemented-edge parity validation")
    print(f"installed-dd-version={importlib.metadata.version('dd')}")
    print("external-git-commit=2596de454f95031f6f92d9796aab41fc8e273947")
    print("external-git-date=2025-10-16T09:43:00+03:00")
    print("backend=dd.autoref (pure Python, signed/complemented node references)")
    print()
    print("n root_node root_negated reachable_dag_nodes manager_nodes exhaustive")

    for n in range(1, 33):
        manager, root = build_parity(n)
        if n <= 12:
            validate(manager, root, n)
            status = "verified"
        else:
            status = "construction"
        expected = n + 1
        if root.dag_size != expected:
            raise AssertionError((n, root.dag_size, expected))
        print(
            f"{n:2d} {root.node:9d} {str(root.negated):12s} "
            f"{root.dag_size:19d} {len(manager):13d} {status}"
        )

    print()
    print("Result: reachable complemented-edge parity BDD nodes = n + 1.")
    print("The count includes one terminal and one decision node per variable.")
    print("Manager node counts are larger because intermediate construction nodes remain allocated.")


if __name__ == "__main__":
    main()
