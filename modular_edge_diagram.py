#!/usr/bin/env python3
"""Exact modular-sum representation experiment."""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from math import ceil, log2
from typing import Dict, Optional, Sequence, Tuple

Cube = Tuple[Optional[int], ...]

def residue(bits: Sequence[int], modulus: int) -> int:
    return sum(bits) % modulus

def extends(bits: Sequence[int], cube: Cube) -> bool:
    return all(value is None or bits[i] == value for i, value in enumerate(cube))

def cube_outputs(cube: Cube, modulus: int) -> set[int]:
    return {
        residue(bits, modulus)
        for bits in product((0, 1), repeat=len(cube))
        if extends(bits, cube)
    }

def exhaustive_cube_profile(n: int, modulus: int) -> tuple[int, int, int]:
    monochromatic = 0
    nonsingleton = 0
    total = 0
    for cube in product((None, 0, 1), repeat=n):
        total += 1
        outputs = cube_outputs(cube, modulus)
        if len(outputs) == 1:
            monochromatic += 1
            if any(value is None for value in cube):
                nonsingleton += 1
    return total, monochromatic, nonsingleton

@dataclass(frozen=True)
class Node:
    level: int
    low: int
    high: int

class MTBDD:
    def __init__(self, modulus: int) -> None:
        self.modulus = modulus
        self.terminals: Dict[int, int] = {}
        self.nodes: Dict[Node, int] = {}
        self.next_id = 0

    def terminal(self, value: int) -> int:
        value %= self.modulus
        if value not in self.terminals:
            self.terminals[value] = self.next_id
            self.next_id += 1
        return self.terminals[value]

    def node(self, level: int, low: int, high: int) -> int:
        if low == high:
            return low
        key = Node(level, low, high)
        if key not in self.nodes:
            self.nodes[key] = self.next_id
            self.next_id += 1
        return self.nodes[key]

    def build(self, n: int) -> int:
        values = tuple(
            residue(bits, self.modulus)
            for bits in product((0, 1), repeat=n)
        )

        def rec(level: int, table: tuple[int, ...]) -> int:
            if level == n:
                if len(table) != 1:
                    raise AssertionError("terminal table must have one value")
                return self.terminal(table[0])
            half = len(table) // 2
            low = rec(level + 1, table[:half])
            high = rec(level + 1, table[half:])
            return self.node(level, low, high)

        return rec(0, values)

    @property
    def internal_count(self) -> int:
        return len(self.nodes)

    @property
    def terminal_count(self) -> int:
        return len(self.terminals)

    @property
    def total_count(self) -> int:
        return self.internal_count + self.terminal_count

def expected_mtbdd_nodes(n: int, modulus: int) -> tuple[int, int, int]:
    internal = sum(min(modulus, depth + 1) for depth in range(n))
    terminals = min(modulus, n + 1)
    return internal, terminals, internal + terminals

def edge_chain_eval(bits: Sequence[int], modulus: int) -> int:
    state = 0
    for bit in bits:
        state = (state + bit) % modulus
    return state

def validate_edge_chain(n: int, modulus: int) -> None:
    for bits in product((0, 1), repeat=n):
        actual = edge_chain_eval(bits, modulus)
        expected = residue(bits, modulus)
        if actual != expected:
            raise AssertionError((n, modulus, bits, actual, expected))

def main() -> None:
    print("Modular-sum edge-valued decision diagram experiment")
    print("All counts include reachable nodes only.\n")
    print(
        "q  n semantic raw cube_terms cube_literals "
        "mtbdd_internal mtbdd_terminals mtbdd_total "
        "ev_nodes label_bits ev_label_storage check"
    )

    cases = [(2, n) for n in range(1, 17)]
    cases += [(3, n) for n in (2, 4, 8, 12, 16)]
    cases += [(4, n) for n in (3, 5, 8, 12, 16)]
    cases += [(5, n) for n in (4, 8, 12, 16)]
    cases += [(7, n) for n in (6, 8, 12, 16)]

    for modulus, n in cases:
        bdd = MTBDD(modulus)
        bdd.build(n)
        expected = expected_mtbdd_nodes(n, modulus)
        actual = (bdd.internal_count, bdd.terminal_count, bdd.total_count)
        if actual != expected:
            raise AssertionError((modulus, n, actual, expected))

        validate_edge_chain(n, modulus)
        raw = 2 ** n
        label_bits = max(1, ceil(log2(modulus)))
        check = "formula"
        if n <= 8:
            total, mono, nonsingleton = exhaustive_cube_profile(n, modulus)
            if (total, mono, nonsingleton) != (3 ** n, 2 ** n, 0):
                raise AssertionError(
                    (modulus, n, total, mono, nonsingleton)
                )
            check = "exhaustive"

        print(
            f"{modulus:2d} {n:2d} {min(modulus, n + 1):8d} {raw:6d} "
            f"{raw:10d} {n * raw:13d} "
            f"{bdd.internal_count:14d} {bdd.terminal_count:15d} "
            f"{bdd.total_count:11d} {n + 1:8d} {label_bits:10d} "
            f"{2 * n * label_bits:16d} {check}"
        )

    print("\nVerified identities:")
    print("  exact safe cube terms      = 2^n")
    print("  exact safe cube literals   = n * 2^n")
    print("  MTBDD internal nodes       = sum_{k=0}^{n-1} min(q, k+1)")
    print("  MTBDD reachable terminals  = min(q, n+1)")
    print("  additive EV diagram nodes  = n + 1")
    print("  additive EV edge labels    = 2n values, each ceil(log2 q) bits")
    print("\nInterpretation:")
    print("- Edge values factor cyclic semantic state away from physical nodes.")
    print("- The factorisation remains honest only when label bits and arithmetic are charged.")
    print("- Fully sensitive modular outputs defeat every monochromatic subcube cover.")

if __name__ == "__main__":
    main()
