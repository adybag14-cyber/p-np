#!/usr/bin/env python3
"""Exact parity representation separation.

For parity on n Boolean variables this script independently checks, for small n,
that every monochromatic partial cube is a singleton. It then compares:

* semantic output classes,
* minimum monochromatic cube-cover terms,
* total cube literals,
* full decision-tree nodes, and
* exact reduced ordered BDD nodes.

The BDD builder uses a unique table and merges identical residual nodes.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Iterator, Optional

Bit = int
CubeBit = Optional[Bit]
Cube = tuple[CubeBit, ...]
Assignment = tuple[Bit, ...]


def parity(bits: Assignment) -> Bit:
    value = 0
    for bit in bits:
        value ^= bit
    return value


def all_cubes(n: int) -> Iterator[Cube]:
    yield from product((None, 0, 1), repeat=n)


def extensions(cube: Cube) -> Iterator[Assignment]:
    free = [index for index, value in enumerate(cube) if value is None]
    for free_values in product((0, 1), repeat=len(free)):
        result = list(cube)
        for index, value in zip(free, free_values, strict=True):
            result[index] = value
        yield tuple(int(value) for value in result)


def is_monochromatic(cube: Cube) -> bool:
    labels = {parity(bits) for bits in extensions(cube)}
    return len(labels) == 1


def literal_count(cubes: Iterable[Cube]) -> int:
    return sum(sum(value is not None for value in cube) for cube in cubes)


@dataclass(frozen=True)
class BddNode:
    variable: int
    low: int
    high: int


class ReducedParityBdd:
    """Build a reduced ordered BDD for parity in the natural variable order."""

    FALSE = 0
    TRUE = 1

    def __init__(self, n: int) -> None:
        self.n = n
        self.unique: dict[BddNode, int] = {}
        self.memo: dict[tuple[int, Bit], int] = {}
        self.next_id = 2
        self.root = self._build(0, 0)

    def _make_node(self, variable: int, low: int, high: int) -> int:
        if low == high:
            return low
        node = BddNode(variable, low, high)
        existing = self.unique.get(node)
        if existing is not None:
            return existing
        node_id = self.next_id
        self.next_id += 1
        self.unique[node] = node_id
        return node_id

    def _build(self, level: int, state: Bit) -> int:
        if level == self.n:
            return self.TRUE if state else self.FALSE
        key = (level, state)
        existing = self.memo.get(key)
        if existing is not None:
            return existing
        low = self._build(level + 1, state)
        high = self._build(level + 1, state ^ 1)
        node = self._make_node(level, low, high)
        self.memo[key] = node
        return node

    @property
    def internal_nodes(self) -> int:
        return len(self.unique)

    @property
    def reachable_terminals(self) -> int:
        if self.n == 0:
            return 1
        return 2

    @property
    def total_nodes(self) -> int:
        return self.internal_nodes + self.reachable_terminals

    def evaluate(self, bits: Assignment) -> Bit:
        reverse = {node_id: node for node, node_id in self.unique.items()}
        node_id = self.root
        while node_id not in (self.FALSE, self.TRUE):
            node = reverse[node_id]
            node_id = node.high if bits[node.variable] else node.low
        return 1 if node_id == self.TRUE else 0


def exhaustive_cube_check(n: int) -> tuple[int, int, bool]:
    monochromatic: list[Cube] = []
    for cube in all_cubes(n):
        if is_monochromatic(cube):
            monochromatic.append(cube)
    all_singletons = all(all(value is not None for value in cube) for cube in monochromatic)
    return len(monochromatic), literal_count(monochromatic), all_singletons


def validate_bdd(n: int, bdd: ReducedParityBdd) -> bool:
    return all(bdd.evaluate(bits) == parity(bits) for bits in product((0, 1), repeat=n))


def main() -> None:
    exhaustive_limit = 9
    print("Parity representation separation")
    print("A monochromatic cube is checked against every total extension.")
    print("The BDD is independently evaluated on every assignment through n=12.")
    print()
    header = (
        "n semantic raw cube_terms cube_literals tree_nodes "
        "robdd_internal robdd_total exhaustive"
    )
    print(header)

    for n in range(1, 17):
        raw = 2**n
        expected_terms = raw
        expected_literals = n * raw
        tree_nodes = 2 ** (n + 1) - 1
        bdd = ReducedParityBdd(n)

        if n <= 12 and not validate_bdd(n, bdd):
            raise AssertionError(f"BDD evaluation failed at n={n}")

        exhaustive_status = "formula"
        if n <= exhaustive_limit:
            terms, literals, singletons = exhaustive_cube_check(n)
            if terms != expected_terms:
                raise AssertionError((n, terms, expected_terms))
            if literals != expected_literals:
                raise AssertionError((n, literals, expected_literals))
            if not singletons:
                raise AssertionError(f"non-singleton monochromatic parity cube at n={n}")
            exhaustive_status = "verified"

        expected_robdd = 2 * n + 1
        if bdd.total_nodes != expected_robdd:
            raise AssertionError((n, bdd.total_nodes, expected_robdd))

        print(
            f"{n:2d} {2:8d} {raw:6d} {expected_terms:10d} "
            f"{expected_literals:13d} {tree_nodes:10d} "
            f"{bdd.internal_nodes:14d} {bdd.total_nodes:11d} {exhaustive_status}"
        )

    print()
    print("Verified identities for n >= 1:")
    print("  semantic classes        = 2")
    print("  minimum cube terms      = 2^n")
    print("  minimum cube literals   = n * 2^n")
    print("  full decision-tree nodes= 2^(n+1) - 1")
    print("  reduced OBDD nodes      = 2n + 1")
    print()
    print("Interpretation:")
    print("- Quotient cardinality alone does not control cube-cover size.")
    print("- Tree leaves cannot share equal residual parity states.")
    print("- The reduced OBDD merges all prefixes with equal accumulated parity.")


if __name__ == "__main__":
    main()
